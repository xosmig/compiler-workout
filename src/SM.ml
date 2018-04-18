open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

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

let evalBinOp f stack = match stack with
|  (y::x::stack) -> (f x y)::stack
|  _ -> failwith "BINOP: No operands on stack"

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
let rec eval env config =
  let (stack, state) = config in
  let (varState, ins, outs) = state in
  let evalSimple cmd progTail =
    let config' = (match cmd with
    | BINOP op -> (evalBinOp (binOpSemantic op) stack, state)
    | CONST x -> (x::stack, state)
    | READ -> (match ins with
      | (x::ins') -> (x::stack, (varState, ins', outs))
      | _ -> failwith "READ: Empty input stream")
    | WRITE -> (match stack with
      | (x::stack') -> (stack', (varState, ins, outs@[x]))
      | _ -> failwith "WRITE: No argument on stack")
    | LD var -> ((varState var)::stack, state)
    | ST var -> (match stack with
      | (x::stack') -> (stack', ((Language.Expr.update var x varState), ins, outs))
      | _ -> failwith "ST: No argument on stack")
    | LABEL _ -> config
    | _ -> failwith "Internal error")
    in eval env config' progTail
  in
  function
  | [] -> config
  | cmd::progTail -> (match cmd with
    | JMP label -> eval env config (env#labeled label)
    | CJMP (tp, label) -> (match stack with
      | (x::stack') ->
        let shouldJump = (match tp with "z" -> x == 0 | "nz" -> x != 0 | _ -> failwith "Unknown CJmp type") in
        eval env (stack', state) (if shouldJump then (env#labeled label) else progTail)
      | _ -> failwith "CJMP: Empty stack")
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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o


class labelGen =
  object (self)
    val nextLabelNum = 0
    method getLabel = {< nextLabelNum = nextLabelNum + 1 >}, Printf.sprintf "SML%d" nextLabelNum
  end

let rec compileImpl env =
let rec expr = function
| Expr.Var   x          -> [LD x]
| Expr.Const n          -> [CONST n]
| Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
in
function
| Stmt.Seq (s1, s2)   ->
  let env, sm1 = compileImpl env s1 in
  let env, sm2 = compileImpl env s2 in
  env, sm1 @ sm2
| Stmt.Read x         -> env, [READ; ST x]
| Stmt.Write e        -> env, expr e @ [WRITE]
| Stmt.Assign (x, e)  -> env, expr e @ [ST x]
| Stmt.Skip           -> env, []
| Stmt.If (e, st, sf) ->
  let env, lelse = env#getLabel in
  let env, lend = env#getLabel in
  let env, smt = compileImpl env st in
  let env, smf = compileImpl env sf in
  env, expr e @ [CJMP ("z", lelse)] @ smt @ [JMP lend] @ [LABEL lelse] @ smf @ [LABEL lend]
| Stmt.While (e, st)  ->
  let env, lloop = env#getLabel in
  let env, lcheck = env#getLabel in
  let env, smt = compileImpl env st in
  env, [JMP lcheck; LABEL lloop] @ smt @ [LABEL lcheck] @ expr e @ [CJMP ("nz", lloop)]
| Stmt.Until (e, st)  ->
  let env, lloop = env#getLabel in
  let env, smt = compileImpl env st in
  env, [LABEL lloop] @ smt @ expr e @ [CJMP ("z", lloop)]

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile stmt = let _, smProg = compileImpl (new labelGen) stmt in smProg
