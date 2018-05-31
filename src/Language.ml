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

let optionDefault default = function
| Some(x) -> x
| None    -> default

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function
    | Int n -> n
    | _ -> failwith "int value expected"

    let to_string = function
    | String s -> s
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = listInit    (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e

  end

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))
    | fname      -> failwith (Printf.sprintf "Undefined builtin call: %s" fname)

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

    let boolToInt b = if b then 1 else 0
    let intToBool x = x <> 0

    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns a pair: the return value for the call and the resulting configuration
    *)
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

    let rec eval env conf expr =
      let (st, i, o, _) = conf in
      match expr with
      | Const n           -> st, i, o, Some (Value.of_int n)
      | Array valuesExpr  ->
        let st', i', o', values = eval_list env conf valuesExpr in
        env#definition env ".array" values (st', i', o', None)
      | String str          -> st, i, o, Some (Value.of_string str)
      | Sexp   (tag, exprs) ->
        let st', i', o', vals = eval_list env conf exprs in
        st', i', o', Some (Value.sexp tag vals)
      | Var    x            -> st, i, o, Some (State.eval st x)
      | Binop (op, lhs, rhs) ->
              let conf', vl = evalChecked env conf  lhs in
              let conf', vr = evalChecked env conf' rhs in
              let st', i', o', _ = conf' in
              st', i', o', Some (Value.Int (to_func op (Value.to_int vl) (Value.to_int vr)))
      | Elem (arrayExpr, indexExpr) ->
        let conf', array = evalChecked env conf arrayExpr in
        let conf', index = evalChecked env conf' indexExpr in
        env#definition env ".elem" [array; index] conf'
      | Length objExpr ->
        let conf', obj = evalChecked env conf objExpr in
        env#definition env ".length" [obj] conf'
      | Call (fname, argExprs) ->
        (* first argument evaluated first *)
        let st', i', o', argVals = eval_list env conf argExprs in
        env#definition env fname argVals (st', i', o', None)
    and evalChecked env conf expr =
      let st, i, o, ret = eval env conf expr in
      let Some(retValue)  = ret in (st, i, o, None), retValue
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

    let binopParser     op  = ostap($(op)), fun x y -> Binop (op, x, y)
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

      atomicExpression: withLength;

      withLength:
        obj:withIndexes lengthCall:".length"? {
          begin match lengthCall with
          | None -> obj
          | _    -> Length obj
          end
        };

      withIndexes:
        obj:primary indexes:(-"[" expr -"]")* {
          begin match indexes with
          | [] -> obj
          | _  -> List.fold_left (fun obj idx -> Elem (obj, idx)) obj indexes
          end
        };

      primary:
        x:DECIMAL {Const x} |
        fname:IDENT -"(" argExprs:!(Util.list0)[expr] -")" { Call (fname, argExprs) } |
        var:IDENT {Var var} |
        arrayLiteral | stringLiteral | charLiteral |
        symbolicExpression |
        -"(" expr -")";

      arrayLiteral: "[" indexesExpr:!(Util.list0)[expr] "]" { Array indexesExpr };
      stringLiteral: str:STRING { String (String.sub str 1 (String.length str - 2)) };
      charLiteral: ch:CHAR { Const (Char.code ch) };

      symbolicExpression: "`" tag:IDENT components:(-"(" !(Util.list)[expr] -")")?
        { Sexp (tag, optionDefault [] components) }
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)
        ostap (
          pattern:
            "_" { Wildcard } |
            "`" tag:IDENT components:(-"(" !(Util.list)[pattern] -")")?
              { Sexp (tag, optionDefault [] components) } |
            ident:IDENT { Ident ident }
        )

        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p

      end

    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list
    (* leave a scope                    *) | Leave  with show

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)
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

    let rec eval env (st, i, o, ret) cont =
      let concat a b = if (b = Skip) then a else Seq (a, b) in
      let conf' = (st, i, o, None) in
      let evalCont conf' = eval env conf' Skip cont in
      function
      | Assign (varName, indexesExpr, e) ->
        let st', i', o', indexes = Expr.eval_list env conf' indexesExpr in
        let (st', i', o', _), newVal = Expr.evalChecked env (st', i', o', None) e in
        let st' = update st varName newVal indexes in
        evalCont (st', i', o', None)
      | Seq (s1, s2)  -> eval env conf' (concat s2 cont) s1
      | Skip          -> if (cont = Skip) then conf' else evalCont conf'
      | If (e, thenStmt, elseStmt) ->
        let conf', v = Expr.evalChecked env conf' e in
        if (Expr.intToBool (Value.to_int v))
          then eval env conf' cont thenStmt
          else eval env conf' cont elseStmt
      | While (e, body) as loop ->
        let conf', v = Expr.evalChecked env conf' e in
        if (Expr.intToBool (Value.to_int v))
          then eval env conf' (concat loop cont) body
          else evalCont conf'
      | Repeat (body, e) ->
        let cont' = concat (While (Expr.Binop ("==", e, Expr.Const 0), body)) cont in
        eval env conf' cont' body
      | Case (e, branches) ->
        let rec matchPatt (varMap, varList as stateFrame) value = function
        | Pattern.Wildcard      -> Some stateFrame
        | Pattern.Ident varName -> Some (State.bind varName value varMap, varName::varList)
        | Pattern.Sexp (pTag, subPatterns) -> begin match value with
          | Value.Sexp (vTag, vComps) when pTag = vTag ->
            matchList stateFrame subPatterns vComps
          | _ -> None
          end
        and matchList stateFrame patterns values = match patterns, values with
        | [], []                  -> Some stateFrame
        | (p::pTail), (v::vTail)  -> begin match (matchPatt stateFrame v p) with
          | Some stateFrame'  -> matchList stateFrame' pTail vTail
          | None              -> None
          end
        | _ -> None
        in
        let conf', v = Expr.evalChecked env conf' e in
        let rec matchBranches = function
        | []            -> failwith "Case failure: no suitable patterns"
        | (pattern, body)::bTail ->
          begin match (matchPatt (State.undefined, []) v pattern) with
          | Some stateFrame -> stateFrame, body
          | None            -> matchBranches bTail
          end
        in
        let (varMap, varList), body = matchBranches branches in
        let conf' = (State.push st varMap varList), i, o, None in
        eval env conf' cont (concat body Leave)
      | Return eOpt   -> (match eOpt with | None -> conf' | Some e -> Expr.eval env conf' e)
      | Call (fname, argExprs) -> evalCont (Expr.eval env conf' (Expr.Call (fname, argExprs)))
      | Leave -> evalCont (State.drop st, i, o, None)

    (* Statement parser *)
    ostap (
      stmt:
        !(Ostap.Util.expr
          (fun x -> x)
          [| `Lefta, [ostap (";"), fun left right -> Seq (left, right)] |]
          primary
        );

      primary:
        "return" exprOpt:!(Expr.expr)? { Return exprOpt } |
        "skip" { Skip } |
        ifStmt | forStmt | caseStmt |
        "while" expr:!(Expr.expr) "do" st:stmt "od" { While (expr, st) } |
        "repeat" st:stmt "until" expr:!(Expr.expr) { Repeat (st, expr) } |
        var:IDENT ixs:(idx*) ":=" expr:!(Expr.expr) { Assign (var, ixs, expr) } |
        fname:IDENT "(" argExprs:!(Ostap.Util.list0)[Expr.expr] ")" { Call (fname, argExprs) };

      idx: -"[" !(Expr.expr) -"]";

      ifRec: expr:!(Expr.expr) "then" st:stmt sf:(-"else" stmt -"fi" | -"elif" ifRec | -"fi" { Skip })
        { If (expr, st, sf) };
      ifStmt: -"if" ifRec;

      forStmt: "for" init:stmt "," cond:!(Expr.expr) "," turn:stmt "do" body:stmt "od"
        { Seq (init, While (cond, Seq (body, turn))) };

      caseVariant:
        !(Pattern.pattern) -"->" stmt;
      caseStmt:
        "case" e:!(Expr.expr) "of"
          variants:!(Util.listBy)[ostap("|")][caseVariant]
        "esac"
        { Case (e, variants) }
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.stmt) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
let parse = ostap (!(Definition.parse)* !(Stmt.stmt))
