(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* State: a partial map from variables to integer values. *)
    type state = string -> int

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    let boolToInt b = if b then 1 else 0
    let intToBool x = x != 0

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let rec eval state expr = match expr with
      | Const (x) -> x
      | Var (name) -> state name
      | Binop (op, left, right) -> match op with
        | "+" -> eval state left + eval state right
        | "-" -> eval state left - eval state right
        | "*" -> eval state left * eval state right
        | "/" -> eval state left / eval state right
        | "%" -> eval state left mod eval state right
        | "==" -> boolToInt (eval state left = eval state right)
        | "!=" -> boolToInt (eval state left <> eval state right)
        | "<" -> boolToInt (eval state left < eval state right)
        | ">" -> boolToInt (eval state left > eval state right)
        | "<=" -> boolToInt (eval state left <= eval state right)
        | ">=" -> boolToInt (eval state left >= eval state right)
        | "&&" -> boolToInt (intToBool (eval state left) && intToBool (eval state right))
        | "!!" -> boolToInt (intToBool (eval state left) || intToBool (eval state right))
        | _ -> failwith (Printf.sprintf "Undefined operator %s" op)


    let binopParser op = (ostap($(op)), fun x y -> Binop (op, x, y))
    let binopParserList ops = List.map binopParser ops

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    ostap (
      expr:
        !(Ostap.Util.expr
          (fun x -> x)
          [|
            `Lefta, binopParserList ["!!"];
            `Lefta, binopParserList ["&&"];
            `Nona , binopParserList ["!="; "=="; "<="; ">="; "<"; ">"];
            `Lefta, binopParserList ["+"; "-"];
            `Lefta, binopParserList ["*"; "/"; "%"];
          |]
          primary
        );

      primary: x:DECIMAL {Const x} | var:IDENT {Var var} | -"(" expr -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((state, ins, outs) as config) stmt = match stmt with
      | Read (var) -> (match ins with
        | (x::ins) -> ((Expr.update var x state), ins, outs)
        | _ -> failwith "Trying to read from an empty input stream")
      | Write (expr) -> state, ins, outs@[Expr.eval state expr]
      | Assign (var, expr) -> (Expr.update var (Expr.eval state expr) state), ins, outs
      | Seq (stmt1, stmt2) -> eval (eval config stmt1) stmt2

    (* Statement parser *)
    ostap (
      primary:
        -"write" -"(" expr:!(Expr.expr) -")" {Write expr} |
        -"read" -"(" var:IDENT -")" {Read var} |
        var:IDENT -":=" expr:!(Expr.expr) {Assign (var, expr)};

      stmt:
        !(Ostap.Util.expr
          (fun x -> x)
          [| `Lefta, [ostap (";"), fun left right -> Seq (left, right)] |]
          primary
        )
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.stmt
