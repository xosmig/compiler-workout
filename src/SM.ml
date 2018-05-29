open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show

(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

let intToBool x = x != 0
let boolToInt b = if b then 1 else 0

let binOpSemantic op = fun x y -> match op with
| "+" -> x + y
| "-" -> x - y
| "*" -> x * y
| "/" -> x / y
| "%" -> x mod y
| ">" -> boolToInt (x > y)
| "<" -> boolToInt (x < y)
| ">=" -> boolToInt (x >= y)
| "<=" -> boolToInt (x <= y)
| "==" -> boolToInt (x == y)
| "!=" -> boolToInt (x <> y)
| "&&" -> boolToInt (intToBool x && intToBool y)
| "!!" -> boolToInt (intToBool x || intToBool y)
| _ -> failwith ("Unknown binary operation: '" ^ op ^ "'")

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let rec eval env config =
  let (cstack, stack, state) = config in
  let (varState, ins, outs) = state in
  let evalBinOp f stack = match stack with
  |  y::x::stack -> Value.of_int (f (Value.to_int x) (Value.to_int y)) :: stack
  |  _ -> failwith "BINOP: No operands on stack"
  in
  (* straight order of evaluation: last argument is on top of the stack *)
  let bindList varNames varState stack =
    List.fold_right begin fun argName (varState, stack) ->
      let value::stack' = stack in
      State.update argName value varState, stack'
    end varNames (varState, stack)
  in
  let evalSimple cmd progTail =
    let config' = match cmd with
    | BINOP op   -> cstack, evalBinOp (binOpSemantic op) stack, state
    | CONST x    -> cstack, (Value.of_int x)::stack, state
    | STRING str -> cstack, (Value.of_string str)::stack, state
    | SEXP (tag, compN) ->
      let compValues, stack' = split compN stack in
      cstack, (Value.sexp tag (List.rev compValues))::stack', state
    | LD var     -> cstack, (State.eval varState var)::stack, state
    | ST var     -> begin match stack with
      | x::stack' -> cstack, stack', ((State.update var x varState), ins, outs)
      | _         -> failwith "ST: No argument on stack"
      end
    | STA (varName, numOfIndexes) -> begin match stack with
      | value::stack' ->
        let rec collectIndexes stack' acc: (int -> Value.t list * Value.t list) = function
        | 0   -> stack', acc
        | len -> begin match stack' with
          | x::stack' -> collectIndexes stack' (x::acc) (len - 1)
          | _         -> failwith "STA: Not enough indexes on stack"
          end
        in
        let stack', indexes = (collectIndexes stack' [] numOfIndexes) in
        cstack, stack', ((Stmt.update varState varName value indexes), ins, outs)
      | _ -> failwith "STA: No value on stack"
      end
    | LABEL _ -> config
    | DROP    -> cstack, (List.tl stack), state
    | DUP     -> cstack, (List.hd stack)::stack, state
    | SWAP    -> cstack, (let x::y::stack' = stack in y::x::stack'), state
    | TAG tag ->
      let res = match List.hd stack with
      | Value.Sexp (valueTag, _) when valueTag = tag -> 1
      | _ -> 0
      in
      cstack, (Value.of_int res)::(List.tl stack), state
    (*doesn't pop anything from stack, doesn't do any bindings, just allocates a new state frame*)
    | ENTER varNames -> cstack, stack, (State.push varState State.undefined varNames, ins, outs)
    | LEAVE -> cstack, stack, (State.drop varState, ins, outs)
    | _       -> failwith "Internal error 2"
    in eval env config' progTail
  in
  function
  | [] -> config
  | cmd::progTail -> begin match cmd with
    | JMP label -> eval env config (env#labeled label)
    | CJMP (tp, label) -> begin match stack with
      | x::stack' ->
        let x = Value.to_int x in
        let shouldJump = (match tp with "z" -> x == 0 | "nz" -> x != 0 | _ -> failwith "Unknown CJmp type") in
        eval env (cstack, stack', state) (if shouldJump then (env#labeled label) else progTail)
      | _ -> failwith "CJMP: Empty stack"
      end
    | BEGIN (_, argNames, locals) ->
      let varState' = State.enter varState (argNames @ locals) in
      let varState', stack' = bindList argNames varState' stack in
      eval env (cstack, stack', (varState', ins, outs)) progTail
    | END   -> begin match cstack with
      | (retProg, retVarState)::cstack' ->
        let varState' = State.leave varState retVarState in
        eval env (cstack', stack, (varState', ins, outs)) retProg
      | _ -> config
      end
    | CALL (fname, numOfArgs, isProcedure) ->
      let fLabel = "L" ^ fname in
      if env#is_label fLabel
        then eval env ((progTail, varState)::cstack, stack, state) (env#labeled fLabel)
        else let conf' = env#builtin config fname numOfArgs isProcedure in
          eval env conf' progTail
    | RET _ -> eval env config (END::progTail)
    | _ -> evalSimple cmd progTail
    end

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) =
  let label s = "L" ^ s in
  let rec call fname args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (fname, List.length args, p)]
  and pattern env lfail = function
  | Stmt.Pattern.Wildcard       -> env, false, [], [DROP]
  | Stmt.Pattern.Ident varName  -> env, false, [varName], [ST varName]
  | Stmt.Pattern.Sexp (pTag, compPatterns) ->
    let rec subpatterns env lfalse i = function
    | []          -> env, false, [], []
    | head::tail  ->
      let env, useLfalse1, headVars, headMatchCode = pattern env lfalse head in
      let env, useLfalse2, tailVars, tailCode = subpatterns env lfalse (i + 1) tail in
      env, useLfalse1 || useLfalse2, headVars @ tailVars,
        [DUP; CONST i; CALL (".elem", 2, false)] @ headMatchCode @ tailCode
    in
    let lfalse, env = env#get_label in
    let ltrue,  env = env#get_label in
    let env, useLfail, varNames, subMatchCode = subpatterns env lfalse 0 compPatterns in
    env, true, varNames,
      [DUP; TAG pTag; CJMP ("nz", ltrue)]
      @ [LABEL lfalse; DROP; JMP lfail]
      @ [LABEL ltrue] @ subMatchCode @ [DROP]
  and expr = function
  | Expr.Const n                      -> [CONST n]
  | Expr.Array valueExprs             -> expr (Expr.Call (".array", valueExprs))
  | Expr.String str                   -> [STRING str]
  | Expr.Sexp (tag, compExprs)        -> exprList compExprs @ [SEXP (tag, List.length compExprs)]
  | Expr.Var  x                       -> [LD x]
  | Expr.Binop (op, x, y)             -> expr x @ expr y @ [BINOP op]
  | Expr.Elem (arrayExpr, indexExpr)  -> expr (Expr.Call (".elem", [arrayExpr; indexExpr]))
  | Expr.Length objExpr               -> expr (Expr.Call (".length", [objExpr]))
  | Expr.Call (fname, argExprs)       -> exprList argExprs @ [CALL (fname, List.length argExprs, false)]
  (* first argument evaluated first *)
  and exprList es = List.flatten @@ List.map (fun e -> expr e) es
  in
  let tryLabel lname useLabel = if useLabel then [LABEL lname] else [] in
  let rec compile_stmt env lend = function
  | Stmt.Assign (varName, indexExprs, valueExpr) -> env, false, begin match indexExprs with
    | [] -> expr valueExpr @ [ST varName]
    | _  -> exprList indexExprs @ expr valueExpr @ [STA (varName, List.length indexExprs)]
    end
  | Stmt.Seq (s1, s2)   ->
    let lend1, env = env#get_label in
    let env, useLend1, sm1 = compile_stmt env lend1 s1 in
    let env, useLend,  sm2 = compile_stmt env lend  s2 in
    env, useLend, sm1 @ (tryLabel lend1 useLend1) @ sm2
  | Stmt.Skip           -> env, false, []
  | Stmt.If (e, st, sf) ->
    let lelse, env = env#get_label in
    let env, _, smt = compile_stmt env lend st in
    let env, _, smf = compile_stmt env lend sf in
    env, true, expr e @ [CJMP ("z", lelse)] @ smt @ [JMP lend] @ [LABEL lelse] @ smf
  | Stmt.While (e, st) ->
    let lloop, env = env#get_label in
    let lcheck, env = env#get_label in
    let env, _, smt = compile_stmt env lcheck st in
    env, false, [JMP lcheck; LABEL lloop] @ smt @ [LABEL lcheck] @ expr e @ [CJMP ("nz", lloop)]
  | Stmt.Repeat (st, e) ->
    let lloop,  env = env#get_label in
    let lcheck, env = env#get_label in
    let env, useLcheck, smt = compile_stmt env lcheck st in
    env, false, [LABEL lloop] @ smt @ (tryLabel lcheck useLcheck) @ expr e @ [CJMP ("z", lloop)]
  | Stmt.Case (e, branches) ->
    let compileBranch env (patt, body) =
      let lfail, env = env#get_label in
      let env, canFail, matchVars, matchCode = pattern env lfail patt in
      let env, _, bodyCode = compile_stmt env lend body in
      env,
        [DUP; ENTER matchVars]  (* Duplicate the value for matching and create new state frame *)
        @ matchCode             (* Try to match the value with the pattern. Consumes the duplicate of the value *)
        (* If matching succeeded, drop the original value and exit *)
        @ [DROP] @ bodyCode @ [JMP lend]
        (* Otherwise, drop the state frame and proceed to the next branch *)
        @ if canFail then [LABEL lfail; LEAVE] else []
    in
    let rec compileBranches env = function
    | [] -> env, []
    | head::tail ->
      let env, codeHead = compileBranch   env head in
      let env, codeTail = compileBranches env tail in
      env, codeHead @ codeTail
    in
    let env, matchCode = compileBranches env branches in
    env, true, expr e @ matchCode @ [STRING "Case failed"; CALL (".panic", 1, true)]
  | Stmt.Return eOpt ->
      let smCode = match eOpt with
      | Some e -> (expr e)@[RET true]
      | None -> [RET false]
      in
      env, false, smCode
  | Stmt.Call (fname, argExprs) ->
    env, false, exprList argExprs @ [CALL (fname, List.length argExprs, true)]
  in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env          = env#get_label in
    let env, useLend, code = compile_stmt env lend stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    tryLabel lend useLend @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      begin fun (env, code) (name, others) ->
        let env, code' = compile_def env (label name, others) in
        env, code'::code
      end
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt env lend p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code)

