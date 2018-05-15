(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let listInit (len : int) (gen : int -> 'a) : 'a list =
  let rec initRec len acc = match len with
  | 0 -> acc
  | _ -> initRec (len - 1) ((gen (len - 1))::acc)
  in
  initRec len []

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function
    | Int n -> n
    | _ -> failwith "int value expected"

    let to_string = function
    | String s -> s
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = listInit    (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

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

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option

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
      | Const n -> st, i, o, Some (Value.of_int n)
      | Array valuesExpr ->
        let st', i', o', values = eval_list env conf valuesExpr in
        env#definition env "$array" values (st', i', o', None)
      | Elem (arrayExpr, indexExpr) ->
        let conf', array = evalChecked env conf arrayExpr in
        let conf', index = evalChecked env conf' indexExpr in
        env#definition env "$elem" [array; index] conf'
      | Length objExpr ->
        let conf', obj = evalChecked env conf objExpr in
        env#definition env "$length" [obj] conf'
      | String str -> st, i, o, Some (Value.of_string str)
      | Var   x -> st, i, o, Some (State.eval st x)
      | Binop (op, lhs, rhs) ->
        let conf', vl = evalChecked env conf  lhs in
        let conf', vr = evalChecked env conf' rhs in
        let st', i', o', _ = conf' in
        st', i', o', Some (Value.Int (to_func op (Value.to_int vl) (Value.to_int vr)))
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
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)

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
          atomicExpression
        );

      arrayLiteral: "[" indexesExpr:!(Util.list0)[expr] "]" { Array indexesExpr };
      stringLiteral: str:STRING { String (String.sub str 1 (String.length str - 2)) };
      charLiteral: ch:CHAR { Const (Char.code ch) };

      atomicExpression: withLength;

      withLength: obj:withIndexes ".length" { Length obj } | withIndexes;
      withIndexes:
        obj:primary indexes:(-"[" expr -"]")+
          { List.fold_left (fun obj idx -> Elem (obj, idx)) obj indexes } |
        primary;

      primary:
        x:DECIMAL {Const x} |
        fname:IDENT -"(" argExprs:!(Ostap.Util.list0)[expr] -")" { Call (fname, argExprs) } |
        var:IDENT {Var var} |
        arrayLiteral | stringLiteral | charLiteral |
        -"(" expr -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list

    let update st x v is =
      let rec update a v = function
      | []    -> v
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          )
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

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
      | Skip          -> if (cont = Skip) then conf' else evalCont conf'
      | Assign (varName, indexesExpr, e) ->
        let st', i', o', indexes = Expr.eval_list env conf' indexesExpr in
        let (st', i', o', _), newVal = Expr.evalChecked env (st', i', o', None) e in
        let st' = update st varName newVal indexes in
        evalCont (st', i', o', None)
      | If (e, thenStmt, elseStmt) ->
        let conf', v = Expr.evalChecked env conf' e in
        if (Expr.intToBool (Value.to_int v))
          then eval env conf' cont thenStmt
          else eval env conf' cont elseStmt
      | While (e, body) as loop    ->
        let conf', v = Expr.evalChecked env conf' e in
        if (Expr.intToBool (Value.to_int v))
          then eval env conf' (concat loop cont) body
          else evalCont conf'
      | Repeat (body, e)       -> eval env conf' (concat (While (Expr.Binop ("==", e, Expr.Const 0), body)) cont) body
      | Call (fname, argExprs) -> evalCont (Expr.eval env conf' (Expr.Call (fname, argExprs)))

    (* Statement parser *)
    ostap (
      primary:
        -"return" exprOpt:!(Expr.expr)? { Return exprOpt } |
        -"skip" { Skip } |
        ifStmt |
        -"while" expr:!(Expr.expr) -"do" st:stmt -"od" { While (expr, st) } |
        -"repeat" st:stmt -"until" expr:!(Expr.expr) { Repeat (st, expr) } |
        forStmt |
        var:IDENT ixs:(idx*) -":=" expr:!(Expr.expr) { Assign (var, ixs, expr) } |
        fname:IDENT -"(" argExprs:!(Ostap.Util.list0)[Expr.expr] -")" { Call (fname, argExprs) };

      idx: -"[" !(Expr.expr) -"]";

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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap ( !(Definition.funDef)* !(Stmt.stmt) )
