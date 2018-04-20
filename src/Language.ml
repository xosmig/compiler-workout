(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    let emptyMap s = fun var -> failwith (Printf.sprintf "Undefined %s variable %s" s var)

    (* Empty state *)
    let empty = {g = emptyMap "global"; l = emptyMap "local"; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let updateMap x v m = fun y -> if y = x then v else m y in
      if List.mem x s.scope then {s with l = updateMap x v s.l}
                            else {s with g = updateMap x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x =  if List.mem x s.scope then s.l x else s.g x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {st with l = emptyMap "local"; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option

    let boolToInt = function true -> 1 | false -> 0
    let intToBool b = b <> 0

    let to_func op =
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> boolToInt |> (< )
      | "<=" -> boolToInt |> (<=)
      | ">"  -> boolToInt |> (> )
      | ">=" -> boolToInt |> (>=)
      | "==" -> boolToInt |> (= )
      | "!=" -> boolToInt |> (<>)
      | "&&" -> fun x y -> boolToInt (intToBool x && intToBool y)
      | "!!" -> fun x y -> boolToInt (intToBool x || intToBool y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)

    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns a pair: the return value for the call and the resulting configuration
    *)
    let rec eval env conf expr =
      let (st, i, o, _) = conf in
      match expr with
      | Const n -> st, i, o, Some n
      | Var   x -> st, i, o, Some (State.eval st x)
      | Binop (op, lhs, rhs) ->
        let conf', vl = evalChecked env conf  lhs in
        let conf', vr = evalChecked env conf' rhs in
        let st', i', o', _ = conf' in
        st', i', o', Some (to_func op vl vr)
      | Call (fname, argExprs) ->
        let evalArg argExpr (conf', argVals) =
          let conf', argVal = evalChecked env conf' argExpr in
          conf', argVal::argVals
        in
        let conf', argVals = List.fold_right evalArg argExprs (conf, []) in
        env#definition env fname argVals conf'
    and evalChecked env conf expr =
      let (st, i, o, ret) = eval env conf expr in
      match ret with | Some x -> (st, i, o, None), x | None -> failwith "Internal error"

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

      primary:
        x:DECIMAL {Const x} |
        fname:IDENT -"(" argExprs:!(Ostap.Util.list0)[expr] -")" { Call (fname, argExprs) } |
        var:IDENT {Var var} |
        -"(" expr -")"
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
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list
    with show

    (* Statement evaluator

         val eval : env -> config -> t -> t -> config

       Takes an environment, a configuration, continuation and a statement, and returns another configuration. The
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env (st, i, o, ret) cont =
      let concat a b = if (b = Skip) then a else Seq (a, b) in
      let conf' = (st, i, o, None) in
      let evalCont conf' = eval env conf' Skip cont in
      function
      | Seq (s1, s2)  -> eval env conf' (concat s2 cont) s1
      | Return eOpt   -> (match eOpt with | None -> conf' | Some e -> Expr.eval env conf' e)
      | Read   x      -> (match i with
        | z::i' -> evalCont (State.update x z st, i', o, None)
        | _ -> failwith "Unexpected end of input")
      | Write  e      ->
        let (st', i', o', _), v = Expr.evalChecked env conf' e in
        evalCont (st', i', o'@[v], None)
      | Skip          -> if (cont = Skip) then conf' else evalCont conf'
      | Assign (x, e) ->
        let (st', i', o', _), v = Expr.evalChecked env conf' e in
        evalCont (State.update x v st', i', o', None)
      | If (e, thenStmt, elseStmt) ->
        let conf', v = Expr.evalChecked env conf' e in
        if (Expr.intToBool v)
          then eval env conf' cont thenStmt
          else eval env conf' cont elseStmt
      | While (e, body) as loop    ->
        let conf', v = Expr.evalChecked env conf' e in
        if (Expr.intToBool v)
          then eval env conf' (concat loop cont) body
          else evalCont conf'
      | Repeat (body, e)       -> eval env conf' (concat (While (Expr.Binop ("==", e, Expr.Const 0), body)) cont) body
      | Call (fname, argExprs) -> evalCont (Expr.eval env conf' (Expr.Call (fname, argExprs)))

    (* Statement parser *)
    ostap (
      primary:
        -"write" -"(" expr:!(Expr.expr) -")" { Write expr } |
        -"read" -"(" var:IDENT -")" { Read var } |
        -"return" exprOpt:!(Expr.expr)? { Return exprOpt } |
        -"skip" { Skip } |
        ifStmt |
        -"while" expr:!(Expr.expr) -"do" st:stmt -"od" { While (expr, st) } |
        -"repeat" st:stmt -"until" expr:!(Expr.expr) { Repeat (st, expr) } |
        forStmt |
        var:IDENT -":=" expr:!(Expr.expr) { Assign (var, expr) } |
        fname:IDENT -"(" argExprs:!(Ostap.Util.list0)[Expr.expr] -")" { Call (fname, argExprs) };

      ifRec: expr:!(Expr.expr) -"then" st:stmt sf:(-"else" stmt -"fi" | -"elif" ifRec | -"fi" { Skip })
        { If (expr, st, sf) };
      ifStmt: -"if" ifRec;

      forStmt: -"for" init:stmt -"," cond:!(Expr.expr) -"," turn:stmt -"do" body:stmt -"od"
        { Seq (init, While (cond, Seq (body, turn))) };

      stmt:
        !(Ostap.Util.expr
          (fun x -> x)
          [| `Lefta, [ostap (";"), fun left right -> Seq (left, right)] |]
          primary
        )
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      ident: IDENT;

      funDef:
        -"fun" fname:IDENT -"(" argNames:!(Util.list0)[ident] -")"
        locals:(-"local" !(Util.list)[ident] | empty {[]})
        -"{" body:!(Stmt.stmt) -"}"
        {fname, (argNames, locals, body)}
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap ( !(Definition.funDef)* !(Stmt.stmt) )
