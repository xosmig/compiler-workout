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
  let evalSimple cmd progTail =
    let config' = match cmd with
    | BINOP op   -> cstack, evalBinOp (binOpSemantic op) stack, state
    | CONST x    -> cstack, (Value.of_int x)::stack, state
    | STRING str -> cstack, (Value.of_string str)::stack, state
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
    | CALL (fname, numOfArgs, isProcedure) ->
      let fLabel = "L" ^ fname in
      if env#is_label fLabel
        then eval env ((progTail, varState)::cstack, stack, state) (env#labeled fLabel)
        else let conf' = env#builtin config fname numOfArgs isProcedure in
          eval env conf' progTail
    | BEGIN (_, argNames, locals) ->
      (* last argument is on top of the stack *)
      let bindArg argName (varState', stack') = match stack' with
      | x::stack' -> State.update argName x varState', stack'
      | _ -> failwith "BEGIN: empty stack"
      in
      let varState' = State.enter varState (argNames @ locals) in
      let varState', stack' = List.fold_right bindArg argNames (varState', stack) in
      eval env (cstack, stack', (varState', ins, outs)) progTail
    | RET _ -> eval env config (END::progTail)
    | END   -> begin match cstack with
      | (retProg, retVarState)::cstack' ->
        let varState' = State.leave varState retVarState in
        eval env (cstack', stack, (varState', ins, outs)) retProg
      | _ -> config
      end
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
  and pattern lfalse = function
  | Stmt.Pattern.Wildcard       -> false, [DROP]
  | Stmt.Pattern.Ident varName  -> false, [ST varName]
  | Stmt.Pattern.Sexp (pTag, subPatterns) -> true,
    [DUP; TAG pTag; CJMP ("z", lfalse)] @ begin
      List.flatten @@ List.mapi
      begin fun i patt ->
        [DUP; CONST i; CALL (".elem", 2, false)] @
        snd @@ pattern lfalse patt
      end
      subPatterns
    end
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
    | _  -> exprList indexExprs @ expr valueExpr @ [STA (varName, List.length indexExprs)]
    | [] -> expr valueExpr @ [ST varName]
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

