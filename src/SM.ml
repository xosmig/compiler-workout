open GT

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
type config = int list * Syntax.Stmt.config

let intToBool x = x != 0
let boolToInt b = if b then 1 else 0

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
let rec eval ((stack, state) as config) prog =
  let (varState, ins, outs) = state in
  match prog with
  | [] -> config
  | cmd::progTail -> eval (match cmd with
    | BINOP "+" -> let (y::x::stack) = stack in ((x + y)::stack, state)
    | BINOP "-" -> let (y::x::stack) = stack in ((x - y)::stack, state)
    | BINOP "*" -> let (y::x::stack) = stack in ((x * y)::stack, state)
    | BINOP "/" -> let (y::x::stack) = stack in ((x / y)::stack, state)
    | BINOP "%" -> let (y::x::stack) = stack in ((x mod y)::stack, state)
    | BINOP ">" -> let (y::x::stack) = stack in ((boolToInt (x > y))::stack, state)
    | BINOP "<" -> let (y::x::stack) = stack in ((boolToInt (x < y))::stack, state)
    | BINOP ">=" -> let (y::x::stack) = stack in ((boolToInt (x >= y))::stack, state)
    | BINOP "<=" -> let (y::x::stack) = stack in ((boolToInt (x <= y))::stack, state)
    | BINOP "==" -> let (y::x::stack) = stack in ((boolToInt (x == y))::stack, state)
    | BINOP "!=" -> let (y::x::stack) = stack in ((boolToInt (x <> y))::stack, state)
    | BINOP "&&" -> let (y::x::stack) = stack in ((boolToInt (intToBool x && intToBool y))::stack, state)
    | BINOP "!!" -> let (y::x::stack) = stack in ((boolToInt (intToBool x || intToBool y))::stack, state)
    | CONST x -> (x::stack, state)
    | READ -> let (x::ins) = ins in (x::stack, (varState, ins, outs))
    | WRITE -> let (x::stack) = stack in (stack, (varState, ins, x::outs))
    | LD var -> ((varState var)::stack, state)
    | ST var -> let (x::stack) = stack in (stack, ((Syntax.Expr.update var x varState), ins, outs))
    ) progTail

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compileExprAcc expr acc = match expr with
  | Syntax.Expr.Const x -> (CONST x)::acc
  | Syntax.Expr.Var var -> (LD var)::acc
  | Syntax.Expr.Binop (op, left, right) -> compileExprAcc left @@ compileExprAcc right @@ (BINOP op)::acc

let rec compileAcc stmt acc = match stmt with
  | Syntax.Stmt.Read var -> READ::(ST var)::acc
  | Syntax.Stmt.Write (expr) -> compileExprAcc expr (WRITE::acc)
  | Syntax.Stmt.Assign (var, expr) -> compileExprAcc expr ((ST var)::acc)
  | Syntax.Stmt.Seq (stmt1, stmt2) -> compileAcc stmt1 (compileAcc stmt2 acc)

let compile stmt = compileAcc stmt []

