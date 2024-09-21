type ty = Types.t
type ident = Types.ident
type path = Types.path
type item = path * ident

module Literal = struct
  type t =
    | Unit
    | Int of (int64 * ty)
    | Float of (float * ty)
    | Bool of bool
    | String of string
    | Ident of item
end

type literal = Literal.t

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Eq
  | Ne
  | Gt
  | Ge
  | Lt
  | Le
  | And
  | Or

type monop = Not | Neg

type pattern =
  | PWildcard
  | PLit of literal
  | PRange of literal * literal
  | PRangeInclusive of literal * literal
  | PStruct of (ident * pattern) list
  | PTuple of pattern list
  | PArray of pattern list
  | PVariant of item * pattern

type lvalue =
  | LIdent of ident
  | LTupleAccess of lvalue * int
  | LFieldAccess of lvalue * ident
  | LIndex of lvalue * expr

and expr =
  | Lit of literal
  | Array of expr list
  | Repeat of expr * expr
  | Tuple of expr list
  | Struct of (ident * expr) list
  | TupleAccess of expr * int
  | FieldAccess of expr * ident
  | Index of expr * expr
  | Def of ident * ty * expr
  | Assign of lvalue * expr
  | MethodCall of expr * string * expr list
  | Call of expr * expr list
  | Binop of binop * expr * expr
  | Monop of monop * expr
  | If of { cond : expr; then_branch : expr; else_branch : expr }
  | While of { cond : expr; body : expr }
  | Match of expr * (pattern * expr) list
  | Seq of expr * expr
  | Block of expr
  | Return of expr
  | Break

let const_unit = Lit Literal.Unit
let const_bool b = Lit (Literal.Bool b)
let const_int n = Lit (Literal.Int (n, Types.varint ()))
let const_ident id = Lit (Literal.Ident ([], id))
let const_item path id = Lit (Literal.Ident (path, id))
let const_float f = Lit (Literal.Float (f, Types.varfloat ()))
let const_string s = Lit (Literal.String s)
let tmp_var () = Utils.unique_string "$tmp"

let rec make_seq = function
  | [] -> const_unit
  | [ a ] -> a
  | a :: q -> Seq (a, make_seq q)

type const_def = { const_name : ident; ty : ty; expr : expr }

type fun_def = {
  fun_name : ident;
  params : (string * ty) list;
  ret : ty;
  body : expr;
}

type extern_def = { val_name : ident; ty : ty; symbol : string }

type toplevel =
  | Const of const_def
  | Function of string list * fun_def
  | Typedef of ident * Types.def
  | Implementation of string list * ty * toplevel list
  | Use of item
  | ExternDef of extern_def

type program = toplevel list

let rec expr_of_lvalue = function
  | LIdent id -> const_ident id
  | LTupleAccess (lval, i) -> TupleAccess (expr_of_lvalue lval, i)
  | LFieldAccess (lval, s) -> FieldAccess (expr_of_lvalue lval, s)
  | LIndex (lval, e) -> Index (expr_of_lvalue lval, e)

let rec transform_lvalue f = function
  | LIdent id -> LIdent id
  | LTupleAccess (lval, i) -> LTupleAccess (transform_lvalue f lval, i)
  | LFieldAccess (lval, s) -> LFieldAccess (transform_lvalue f lval, s)
  | LIndex (lval, e) -> LIndex (transform_lvalue f lval, transform_expr f (f e))

and transform_expr f e =
  let rec sub e = e |> f |> g |> f
  and g = function
    | Lit l -> Lit l
    | Array lst -> Array (List.map sub lst)
    | Repeat (e, len) -> Repeat (sub e, sub len)
    | Tuple lst -> Tuple (List.map sub lst)
    | Struct lst -> Struct (List.map (fun (field, e) -> (field, sub e)) lst)
    | TupleAccess (e, i) -> TupleAccess (sub e, i)
    | FieldAccess (e, s) -> FieldAccess (sub e, s)
    | Index (e, idx) -> Index (sub e, sub idx)
    | Def (id, ty, e) -> Def (id, ty, sub e)
    | Assign (lval, e) -> Assign (transform_lvalue f lval, sub e)
    | MethodCall (e, f, args) -> MethodCall (sub e, f, List.map sub args)
    | Call (func, args) -> Call (sub func, List.map sub args)
    | Binop (op, e1, e2) -> Binop (op, sub e1, sub e2)
    | Monop (op, e) -> Monop (op, sub e)
    | If { cond = c; then_branch = t; else_branch = e } ->
        If { cond = sub c; then_branch = sub t; else_branch = sub e }
    | While { cond = c; body = b } -> While { cond = sub c; body = sub b }
    | Match (expr, pat) ->
        Match (sub expr, List.map (fun (p, e) -> (p, sub e)) pat)
    | Seq (e1, e2) -> Seq (sub e1, sub e2)
    | Block e -> Block (sub e)
    | Return e -> Return (sub e)
    | Break -> Break
  in
  sub e

and transform_toplevel f = function
  | Const { const_name; ty; expr } ->
      Const { const_name; ty; expr = transform_expr f (f expr) }
  | Function (vars, { fun_name; params; ret; body }) ->
      Function
        (vars, { fun_name; params; ret; body = transform_expr f (f body) })
  | Typedef (vars, def) -> Typedef (vars, def)
  | Implementation (vars, ty, lst) ->
      Implementation (vars, ty, List.map (transform_toplevel f) lst)
  | Use it -> Use it
  | ExternDef def -> ExternDef def

and transform_program f (program : program) : program =
  List.map (transform_toplevel f) program
