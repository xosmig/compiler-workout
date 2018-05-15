open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
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

let functionLabelPrefix = "L_FUNCTION_"
let functionLabel fname = functionLabelPrefix ^ fname
let functionLabelPrefixLength = String.length functionLabelPrefix

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
  |  (y::x::stack) -> Value.of_int (f (Value.to_int x) (Value.to_int y)) :: stack
  |  _ -> failwith "BINOP: No operands on stack"
  in
  let evalSimple cmd progTail =
    let config' = match cmd with
    | BINOP op   -> cstack, evalBinOp (binOpSemantic op) stack, state
    | CONST x    -> cstack, (Value.of_int x)::stack, state
    | STRING str -> cstack, (Value.of_string str)::stack, state
    | LD var     -> cstack, (State.eval varState var)::stack, state
    | ST var     -> begin match stack with
      | (x::stack') -> cstack, stack', ((State.update var x varState), ins, outs)
      | _ -> failwith "ST: No argument on stack"
      end
    | STA (varName, numOfIndexes) -> begin match stack with
      | (value::stack') ->
        let rec collectIndexes stack' acc: (int -> Value.t list * Value.t list) = function
        | 0   -> stack', acc
        | len -> begin match stack' with
          | (x::stack') -> collectIndexes stack' (x::acc) (len - 1)
          | _           -> failwith "STA: Not enough indexes on stack"
          end
        in
        let stack', indexes = (collectIndexes stack' [] numOfIndexes) in
        cstack, stack', ((Stmt.update varState varName value indexes), ins, outs)
      | _ -> failwith "STA: No value on stack"
      end
    | LABEL _ -> config
    | _ -> failwith "Internal error 2"
    in eval env config' progTail
  in
  function
  | [] -> config
  | cmd::progTail -> (match cmd with
    | JMP label -> eval env config (env#labeled label)
    | CJMP (tp, label) -> (match stack with
      | (x::stack') ->
        let x = Value.to_int x in
        let shouldJump = (match tp with "z" -> x == 0 | "nz" -> x != 0 | _ -> failwith "Unknown CJmp type") in
        eval env (cstack, stack', state) (if shouldJump then (env#labeled label) else progTail)
      | _ -> failwith "CJMP: Empty stack")
    | CALL (fname, numOfArgs, isProcedure) ->
      let fLabel = functionLabel fname in
      if env#is_label fLabel
        then eval env ((progTail, varState)::cstack, stack, state) (env#labeled fLabel)
        else let conf' = env#builtin config fname numOfArgs isProcedure in
          eval env conf' progTail
    | BEGIN (_, argNames, locals) ->
      let bindArg (vs, st) arg = (match st with
      | (x::st') -> State.update arg x vs, st'
      | _ -> failwith "BEGIN: empty stack")
      in
      let varState' = State.enter varState (argNames @ locals) in
      let varState', stack' = List.fold_left bindArg (varState', stack) argNames in
      eval env (cstack, stack', (varState', ins, outs)) progTail
    | RET _ -> eval env config (END::progTail)
    | END -> (match cstack with
      | ((retProg, retVarState)::cstack') ->
        let varState' = State.leave varState retVarState in
        eval env (cstack', stack, (varState', ins, outs)) retProg
      | _ -> config)
    | _ -> evalSimple cmd progTail)


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
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
        method builtin (cstack, stack, (st, i, o)) f n isProcedure =
          let args, stack' = split n stack in
          let args = List.rev args in
          let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
          let stack'' = if isProcedure then stack' else let Some r = r in r::stack' in
          (cstack, stack'', (st, i, o))
      end)
      ([], [], (State.empty, i, []))
      p
  in
  o

class labelGen =
  object (self)
    val nextLabelNum = 0
    method getLabel = {< nextLabelNum = nextLabelNum + 1 >}, Printf.sprintf "L_GEN_%d" nextLabelNum
  end

let tryLabel lname useLabel = if useLabel then [LABEL lname] else []

let rec compileImpl env lend =
(* first argument must be evaluated last *)
let rec evalArgs argExprs = List.fold_left (fun code argExpr -> expr argExpr @ code) [] argExprs
and expr = function
| Expr.Var   x          -> [LD x]
| Expr.Const n          -> [CONST n]
| Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
| Expr.String str       -> [STRING str]
| Expr.Array valueExprs -> expr (Expr.Call ("$array", valueExprs))
| Expr.Length objExpr   -> expr (Expr.Call ("$length", [objExpr]))
| Expr.Elem (arrayExpr, indexExpr) -> expr (Expr.Call ("$elem", [arrayExpr; indexExpr]))
| Expr.Call (fname, argExprs) ->
  evalArgs argExprs @ [CALL (fname, List.length argExprs, false)]
in
function
| Stmt.Seq (s1, s2)   ->
  let env, lend1 = env#getLabel in
  let env, sm1, useLend1 = compileImpl env lend1 s1 in
  let env, sm2, useLend = compileImpl env lend  s2 in
  env, sm1 @ (tryLabel lend1 useLend1) @ sm2, useLend
| Stmt.Assign (varName, indexesExpr, valueExpr) ->
  env, List.flatten (List.map expr indexesExpr) @ expr valueExpr @ [STA (varName, List.length indexesExpr)], false
| Stmt.Skip           -> env, [], false
| Stmt.If (e, st, sf) ->
  let env, lelse = env#getLabel in
  let env, smt, _ = compileImpl env lend st in
  let env, smf, _ = compileImpl env lend sf in
  env, expr e @ [CJMP ("z", lelse)] @ smt @ [JMP lend] @ [LABEL lelse] @ smf, true
| Stmt.While (e, st) ->
  let env, lloop = env#getLabel in
  let env, lcheck = env#getLabel in
  let env, smt, _ = compileImpl env lcheck st in
  env, [JMP lcheck; LABEL lloop] @ smt @ [LABEL lcheck] @ expr e @ [CJMP ("nz", lloop)], false
| Stmt.Repeat (st, e) ->
  let env, lloop = env#getLabel in
  let env, lcheck = env#getLabel in
  let env, smt, useLcheck = compileImpl env lcheck st in
  env, [LABEL lloop] @ smt @ (tryLabel lcheck useLcheck) @ expr e @ [CJMP ("z", lloop)], false
| Stmt.Call (fname, argExprs) ->
  env, evalArgs argExprs @ [CALL (fname, List.length argExprs, true)], false
| Stmt.Return eOpt ->
  let smCode = match eOpt with
  | Some e -> (expr e)@[RET true]
  | None -> [RET false]
  in
  env, smCode, false

let compileImplFinished env prog =
  let env, lend = env#getLabel in
  let env, smProg, useLend = compileImpl env lend prog in
  env, smProg @ (tryLabel lend useLend)

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, mainProg) =
  let compileFun (env, smCode) (fname, (argNames, locals, funProg)) =
    let env, funSMCode = compileImplFinished env funProg in
    env, [LABEL (functionLabel fname); BEGIN (fname, argNames, locals)] @ funSMCode @ [END] @ smCode
  in
  let env, mainSMCode = compileImplFinished (new labelGen) mainProg in
  let env, funsSMCode = List.fold_left compileFun (env, []) defs in
  mainSMCode @ [END] @ funsSMCode
