open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

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

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
let rec eval ((stack, state) as config) prog =
  let (varState, ins, outs) = state in
  match prog with
  | [] -> config
  | cmd::progTail -> eval (match cmd with
    | BINOP op -> (evalBinOp (binOpSemantic op) stack, state)
    | CONST x -> (x::stack, state)
    | READ -> (match ins with
      | (x::ins) -> (x::stack, (varState, ins, outs))
      | _ -> failwith "READ: Empty input stream")
    | WRITE -> (match stack with
      | (x::stack) -> (stack, (varState, ins, outs@[x]))
      | _ -> failwith "WRITE: No argument on stack")
    | LD var -> ((varState var)::stack, state)
    | ST var -> (match stack with
      | (x::stack) -> (stack, ((Language.Expr.update var x varState), ins, outs))
      | _ -> failwith "ST: No argument on stack")
    ) progTail

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

let rec compileExprAcc expr acc = match expr with
  | Language.Expr.Const x -> (CONST x)::acc
  | Language.Expr.Var var -> (LD var)::acc
  | Language.Expr.Binop (op, left, right) -> compileExprAcc left @@ compileExprAcc right @@ (BINOP op)::acc

let rec compileAcc stmt acc = match stmt with
  | Language.Stmt.Read var -> READ::(ST var)::acc
  | Language.Stmt.Write (expr) -> compileExprAcc expr (WRITE::acc)
  | Language.Stmt.Assign (var, expr) -> compileExprAcc expr ((ST var)::acc)
  | Language.Stmt.Seq (stmt1, stmt2) -> compileAcc stmt1 (compileAcc stmt2 acc)

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let compile stmt = compileAcc stmt []
