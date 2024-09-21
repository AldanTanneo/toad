exception UnresolvedTypevar of string

type ident = string
(** Toad identifier *)

and path = t list
(** Type path *)

and item = path * ident
(** Complete type path *)

(** Types *)
and t =
  | Array of t
  | Tuple of t list
  | Function of t list * t
  | Typename of item * t list
  | Var of string
  | VarInt of string
  | VarFloat of string

(** Creates a new unique type var *)
let new_type x = Var (Utils.unique_string x)

let const_typename name = Typename (([], name), [])
let core = "$core"
let core_ns = const_typename core
let root = "$root"
let root_ns = const_typename root
let self = "$self"
let self_type = const_typename "Self"
let core_type ?(vars = []) name = Typename (([ core_ns ], name), vars)
let option t = core_type "Option" ~vars:[ t ]
let unit = core_type "unit"
let bool = core_type "bool"
let varint () = VarInt (Utils.unique_string "int")
let i8 = core_type "i8"
let u8 = core_type "u8"
let i16 = core_type "i16"
let u16 = core_type "u16"
let i32 = core_type "i32"
let u32 = core_type "u32"
let i64 = core_type "u64"
let u64 = core_type "i64"
let isize = core_type "isize"
let usize = core_type "usize"
let varfloat () = VarInt (Utils.unique_string "float")
let f32 = core_type "f32"
let f64 = core_type "f64"
let str = core_type "str"
let is_varint = function VarInt _ -> true | _ -> false
let is_varfloat = function VarFloat _ -> true | _ -> false

let is_signed = function
  | t -> is_varint t || List.mem t [ i8; i16; i32; i64; isize ]

let is_int t =
  is_varint t
  || List.mem t [ i8; u8; i16; u16; i32; u32; i64; u64; isize; usize ]

let is_float t = is_varfloat t || List.mem t [ f32; f64 ]
let is_var = function Var _ -> true | _ -> false

let item_of_type ty id =
  match ty with
  | Typename ((path, t), vars) -> (path @ [ Typename (([], t), vars) ], id)
  | other -> ([ other ], id)

let make_local = function
  | Typename ((_, name), vars) -> Typename (([], name), vars)
  | ty -> ty

let type_params = function Typename (_, vars) -> vars | _ -> []

let with_params params = function
  | Typename (it, _) -> Typename (it, params)
  | _ -> failwith "no type params in type"

(** Type expression *)
type expr =
  | Extern of string
  | Alias of t
  | Sum of (ident * t) list
  | Struct of (ident * t) list

type def = string list * expr
(** Type definition *)

let get_var_string = function
  | Var x -> x
  | _ -> raise (Invalid_argument "cannot get the variable string")

(** Checks if a variable name appears in a type *)
let appear_in_ty v_name ty =
  let rec appear = function
    | Array ty -> appear ty
    | Tuple comps -> List.exists appear comps
    | Function (args, ret) -> appear ret || List.exists appear args
    | Typename ((path, _), args) ->
        List.exists appear path || List.exists appear args
    | Var v_name' -> v_name = v_name'
    | _ -> false
  in
  appear ty

let appear_in_ty_expr v_name ty_expr =
  let rec rec_appear = function
    | [] -> false
    | (_, a) :: q -> appear_in_ty v_name a || rec_appear q
  in
  match ty_expr with
  | Sum q | Struct q -> rec_appear q
  | Alias ty -> appear_in_ty v_name ty
  | Extern _ -> false

type schema = string list * t

module Env = struct
  (* Environnements de typage. *)
  type ('a, 'b) env = {
    bindings : (ident * 'a) list;
    types : (ident * 'b) list;
    ns : (t * ('a, 'b) namespace) list;
  }

  and ('a, 'b) namespace = Ref of ('a, 'b) env ref | Redirect of t

  let new_binding env name item =
    { env with bindings = (name, item) :: env.bindings }

  and new_type env name ty = { env with types = (name, ty) :: env.types }
  and new_ns env ty namespace = { env with ns = (ty, namespace) :: env.ns }

  and add_global (env : ('a, 'b) env) curr_ns f key value =
    curr_ns := f !curr_ns key value;
    f env key value

  let init = { bindings = []; types = []; ns = [] }
end

type ('a, 'b) env = ('a, 'b) Env.env

let deep_copy_ty var_mapping ty =
  let rec deep_copy ty =
    match ty with
    | Array ty -> Array (deep_copy ty)
    | Tuple comps -> Tuple (List.map deep_copy comps)
    | Function (args, ret) -> Function (List.map deep_copy args, deep_copy ret)
    | Typename ((path, name), args) ->
        Typename ((List.map deep_copy path, name), List.map deep_copy args)
    | Var x -> ( try List.assoc x var_mapping with Not_found -> ty)
    | _ -> ty
  in
  deep_copy ty

(* Retourne une instance fraîche de schéma de type. *)
let instance (sch : schema) =
  let var_mapping = List.map (fun v -> (v, new_type "")) (fst sch) in
  deep_copy_ty var_mapping (snd sch)

let generalize_global ty vars =
  let rec find_gen_vars acc = function
    | Array ty -> find_gen_vars acc ty
    | Tuple lst -> List.fold_left find_gen_vars acc lst
    | Function (args, ret) ->
        List.fold_left find_gen_vars (find_gen_vars acc ret) args
    | Typename ((p, _n), v) ->
        List.fold_left find_gen_vars (List.fold_left find_gen_vars acc p) v
    | Var x -> if List.mem x vars || List.mem x acc then acc else x :: acc
    | _ -> acc
  in
  (find_gen_vars [] ty, ty)

(* Retourne un schéma de type trivial (pas de généralisation). *)
let trivial_sch ty : schema = ([], ty)

type ord = Less | Eq | Greater

let rev_ord = function Less -> Greater | Eq -> Eq | Greater -> Less
let rev_partial_ord = Option.map rev_ord

let rec partial_ord a b =
  if a = b then Some Eq
  else
    match (a, b) with
    | Array a, Array b -> partial_ord a b
    | Tuple [], Tuple [] -> Some Eq
    | Tuple (a :: q), Tuple (b :: r) -> (
        match partial_ord a b with
        | Some Eq -> partial_ord (Tuple q) (Tuple r)
        | Some ord ->
            let rest_ord = partial_ord (Tuple q) (Tuple r) in
            if rest_ord = Some Eq || rest_ord = Some ord then Some ord else None
        | None -> None)
    | Function (a, t), Function (b, u) ->
        partial_ord (Tuple (t :: a)) (Tuple (u :: b))
    | Typename ((a, n1), q), Typename ((b, n2), r) ->
        if n1 = n2 then
          partial_ord (Tuple [ Tuple a; Tuple q ]) (Tuple [ Tuple b; Tuple r ])
        else None
    | VarInt _, Typename (_, _) -> if is_int b then Some Greater else None
    | Typename (_, _), VarInt _ -> if is_int a then Some Less else None
    | VarFloat _, Typename (_, _) -> if is_float b then Some Greater else None
    | Typename (_, _), VarFloat _ -> if is_float a then Some Less else None
    | Var _, Var _ -> Some Eq
    | Var _, _ -> Some Greater
    | _, Var _ -> Some Less
    | _ -> None

let compatible a b =
  match partial_ord a b with
  | Some (Less | Eq) -> true
  | Some Greater | None -> false
