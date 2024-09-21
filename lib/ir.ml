type ty = Types.t
type ident = Ast.ident

let pp_ty = Printers.pp_type

type ir =
  | Unit
  | Bool of bool
  | Int of int64 * ty
  | Float of float * ty
  | String of string
  | Ident of (Ast.item[@printer Printers.pp_item]) * ty
  | Array of ir list * ty
  | Tuple of ir list * ty
  | Struct of (string * ir) list * ty
  | TupleAccess of ir * int * ty
  | FieldAccess of ir * string * ty
  | Def of string * ir * ty
  | Assign of lvalue * ir * ty
  | Call of ir * ir list * ty
  | AdressCall of ir * ir list * ty
  | If of ir * (ir * ir) * ty
  | While of ir * ir
  | Match of ir * ((Ast.pattern[@printer Printers.pp_pattern]) * ir) list * ty
  | Seq of ir * ir * ty
  | Block of ir * ty
  | Return of ir
  | Break

and lvalue =
  | LIdent of string * ty
  | LTupleAccess of lvalue * int * ty
  | LFieldAccess of lvalue * string * ty
  | LIndex of lvalue * ir * ty
[@@deriving show { with_path = false }]

type obj =
  | Const of ty * ir
  | Function of ((string * ty) list * ty * ir)
  | Method of ((string * ty) list * ty * ir)
  | Constructor of string * ty * ty
  | Extern of string * ty
  | Intrinsic of string * ty
[@@deriving show { with_path = false }]

let ir_type = function
  | Unit | Def _ | Assign _ | While _ | Return _ | Break -> Types.unit
  | Bool _ -> Types.bool
  | String _ -> Types.str
  | Int (_, ty)
  | Float (_, ty)
  | Ident (_, ty)
  | Array (_, ty)
  | Tuple (_, ty)
  | Struct (_, ty)
  | TupleAccess (_, _, ty)
  | FieldAccess (_, _, ty)
  | Call (_, _, ty)
  | AdressCall (_, _, ty)
  | If (_, _, ty)
  | Match (_, _, ty)
  | Seq (_, _, ty)
  | Block (_, ty) ->
      ty

let lvalue_type = function
  | LIdent (_, ty)
  | LTupleAccess (_, _, ty)
  | LFieldAccess (_, _, ty)
  | LIndex (_, _, ty) ->
      ty

let obj_type = function
  | Const (ty, _) | Constructor (_, _, ty) | Extern (_, ty) | Intrinsic (_, ty)
    ->
      ty
  | Function (args, ret, _) | Method (args, ret, _) ->
      Types.Function (List.map snd args, ret)

let rec ir_of_lvalue = function
  | LIdent (s, ty) -> Ident (([], s), ty)
  | LTupleAccess (l, i, ty) -> TupleAccess (ir_of_lvalue l, i, ty)
  | LFieldAccess (l, f, ty) -> FieldAccess (ir_of_lvalue l, f, ty)
  | LIndex (l, ir, ty) ->
      let lt = lvalue_type l in
      Call
        ( Ident
            ( Types.item_of_type lt "index",
              Types.Function ([ lt; ir_type ir ], ty) ),
          [ ir_of_lvalue l; ir ],
          ty )

let rec apply subst ir =
  let mu t = Subst.apply t subst in
  let lmu l =
    Ast.Literal.(
      match l with
      | Int (i, ty) -> Int (i, mu ty)
      | Float (f, ty) -> Float (f, mu ty)
      | Ident (path, id) -> Ident (List.map mu path, id)
      | _ -> l)
  in
  let rec pmu p =
    Ast.(
      match p with
      | PLit l -> PLit (lmu l)
      | PRange (a, b) -> PRange (lmu a, lmu b)
      | PRangeInclusive (a, b) -> PRangeInclusive (lmu a, lmu b)
      | PArray lst -> PArray (List.map pmu lst)
      | PTuple lst -> PTuple (List.map pmu lst)
      | PStruct lst -> PStruct (List.map (fun (n, p) -> (n, pmu p)) lst)
      | PVariant ((path, id), pat) -> PVariant ((List.map mu path, id), pmu pat)
      | PWildcard -> PWildcard)
  in
  let rec lvalmu lval =
    match lval with
    | LIdent (id, ty) -> LIdent (id, mu ty)
    | LTupleAccess (lval, i, ty) -> LTupleAccess (lvalmu lval, i, mu ty)
    | LFieldAccess (lval, s, ty) -> LFieldAccess (lvalmu lval, s, mu ty)
    | LIndex (lval, ir, ty) -> LIndex (lvalmu lval, apply subst ir, mu ty)
  in
  match ir with
  | Unit | Bool _ | String _ | Break -> ir
  | Int (i, ty) -> Int (i, mu ty)
  | Float (f, ty) -> Float (f, mu ty)
  | Ident ((path, id), ty) -> Ident ((List.map mu path, id), mu ty)
  | Array (ir, ty) -> Array (List.map (apply subst) ir, mu ty)
  | Tuple (ir, ty) -> Tuple (List.map (apply subst) ir, mu ty)
  | Struct (ir, ty) ->
      Struct (List.map (fun (n, ir) -> (n, apply subst ir)) ir, mu ty)
  | TupleAccess (ir, i, ty) -> TupleAccess (apply subst ir, i, mu ty)
  | FieldAccess (ir, s, ty) -> FieldAccess (apply subst ir, s, mu ty)
  | Call (ir, args, ty) ->
      Call (apply subst ir, List.map (apply subst) args, mu ty)
  | AdressCall (ir, args, ty) ->
      AdressCall (apply subst ir, List.map (apply subst) args, mu ty)
  | If (ir, (t, e), ty) ->
      If (apply subst ir, (apply subst t, apply subst e), mu ty)
  | Match (ir, pat, ty) ->
      Match
        ( apply subst ir,
          List.map (fun (p, ir) -> (pmu p, apply subst ir)) pat,
          mu ty )
  | Def (name, ir, ty) -> Def (name, apply subst ir, mu ty)
  | Assign (lval, ir, ty) -> Assign (lvalmu lval, apply subst ir, mu ty)
  | While (ir, body) -> While (apply subst ir, apply subst body)
  | Seq (ir1, ir2, ty) -> Seq (apply subst ir1, apply subst ir2, mu ty)
  | Block (ir, ty) -> Block (apply subst ir, mu ty)
  | Return ir -> Return (apply subst ir)

let apply_obj subst obj =
  let mu t = Subst.apply t subst in
  let imu ir = apply subst ir in
  match obj with
  | Const (ty, ir) -> Const (mu ty, imu ir)
  | Function (args, ret, ir) ->
      Function (List.map (fun (n, t) -> (n, mu t)) args, mu ret, imu ir)
  | Method (args, ret, ir) ->
      Method (List.map (fun (n, t) -> (n, mu t)) args, mu ret, imu ir)
  | Constructor (n, t1, t2) -> Constructor (n, mu t1, mu t2)
  | Extern (sym, ty) -> Extern (sym, mu ty)
  | Intrinsic (sym, ty) -> Intrinsic (sym, mu ty)

module SymbolTable = Map.Make (String)
