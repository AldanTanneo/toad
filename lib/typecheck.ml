open Types
open Utils

exception UnknownField of Ast.ty * string
exception UnknownMethod of Ast.ty * string
exception OverlyConstrained of Ast.item * string * Ast.ty
exception BindingInRangePattern of Ast.ident
exception UnknownConstructor of Ast.item

type typing_env = (schema, schema * expr) env

type state = {
  path : path;
  curr_ns : typing_env ref;
  vars : string list;
  hint : Ast.ty option;
  return_type : Ast.ty option;
}

let dbg env = Format.eprintf "@[%a@]@?\n%!" Printers.pp_typing_env env

let dbg_bindings (env : typing_env) =
  Format.eprintf "bindings = %a\n%!"
    (Printers.pp_list
       (Printers.pp_pair (Format.pp_print_string, Printers.pp_schema)))
    env.bindings

let generalize_local ty (env : typing_env) vars =
  let appear_in_bindings x { Env.bindings; _ } =
    List.exists (fun (_, (_, ty)) -> appear_in_ty x ty) bindings
  in
  let rec find_gen_vars acc = function
    | Array ty -> find_gen_vars acc ty
    | Tuple lst -> List.fold_left find_gen_vars acc lst
    | Function (args, ret) ->
        List.fold_left find_gen_vars (find_gen_vars acc ret) args
    | Typename ((p, _n), v) ->
        List.fold_left find_gen_vars (List.fold_left find_gen_vars acc p) v
    | Var x | VarInt x | VarFloat x ->
        if List.mem x vars || List.mem x acc || appear_in_bindings x env then
          acc
        else x :: acc
  in
  (find_gen_vars [] ty, ty)

let rec apply mu ty =
  match mu with
  | [] -> ty
  | transf :: rest -> apply rest (Subst.apply_one transf ty)

let apply_def mu = function
  | Alias t -> Alias (apply mu t)
  | Sum lst -> Sum (List.map (fun (v, t) -> (v, apply mu t)) lst)
  | Struct lst -> Struct (List.map (fun (f, t) -> (f, apply mu t)) lst)
  | Extern sym -> Extern sym

let apply_bindings bindings mu =
  List.map
    (fun (name, (gen_vars, ty)) -> (name, (gen_vars, Subst.apply ty mu)))
    bindings

let rec apply_ns mu = function
  | Env.Ref env -> Env.Ref (ref (apply_env mu !env))
  | Env.Redirect ty -> Env.Redirect (apply mu ty)

and apply_env mu ({ bindings; types; ns } : typing_env) =
  {
    bindings = apply_bindings bindings mu;
    types =
      List.map
        (fun (name, ((gen_vars, ty), def)) ->
          (name, ((gen_vars, apply mu ty), apply_def mu def)))
        types;
    ns = List.map (fun (ty, ns) -> (apply mu ty, apply_ns mu ns)) ns;
  }

let rec has_free_vars vars = function
  | Array ty -> has_free_vars vars ty
  | Tuple lst -> List.exists (has_free_vars vars) lst
  | Function (args, ret) ->
      List.exists (has_free_vars vars) args || has_free_vars vars ret
  | Typename (_, params) -> List.exists (has_free_vars vars) params
  | Var x | VarInt x | VarFloat x -> not (List.mem x vars)

let empty_env = { Env.bindings = []; types = []; ns = [] }

let find_item current_env state item =
  let rec aux (env : typing_env) (item : Ast.item) :
      (schema * Subst.subst) option =
    match (item, env) with
    | ([], id), _ ->
        let+ sch = List.assoc_opt id env.bindings in
        (sch, Subst.empty)
    | ((Typename ((_ :: _, _), []) as _p) :: _rest, _id), _ ->
        failwith
          "invariant broken: an item path should not contain namespaced types"
    | (p :: rest, id), { ns = (t, env') :: other; _ } -> (
        let mu =
          try Some (Unify.unify state.vars p t)
          with _ -> (
            match p with
            | Typename (it, []) -> (
                let p' =
                  Typename (it, List.map (fun _ -> new_type "p") (type_params t))
                in
                try Some (Unify.unify state.vars p' t) with _ -> None)
            | _ -> None)
        in
        match mu with
        | Some mu -> (
            let def =
              match apply_ns mu env' with
              | Ref env' -> aux !env' (rest, id)
              | Redirect ty ->
                  let path, id = item_of_type ty id in
                  aux current_env (path @ rest, id)
            in
            match def with
            | None -> aux { env with ns = other } item
            | Some (sch, subst) ->
                Some
                  ((fst sch, Subst.apply (snd sch) mu), Subst.compose mu subst))
        | None -> aux { env with ns = other } item)
    | (_ :: _, _), { ns = []; _ } -> None
  in
  match aux current_env item with
  | Some v -> v
  | None -> raise (Canonicalize.UnboundIdentifier item)

let find_type_def (current_env : typing_env) state ty =
  let rec aux (env : typing_env) (ty : Ast.ty) =
    match (ty, env) with
    | (Array _ | Tuple _ | Function _ | Var _ | VarInt _ | VarFloat _), _ ->
        None
    | Typename (([], name), params), _ -> (
        let* def = List.assoc_opt name env.types in
        match def with
        | (vars, Typename (item, params')), Struct lst ->
            if List.length vars = List.length params then
              let subst = zip vars params in
              Some
                ( subst,
                  Typename (item, List.map (apply subst) params'),
                  Struct (List.map (fun (n, t) -> (n, apply subst t)) lst) )
            else None
        | (vars, Typename (item, params')), Sum lst ->
            if List.length vars = List.length params then
              let subst = zip vars params in
              Some
                ( subst,
                  Typename (item, List.map (apply subst) params'),
                  Sum (List.map (fun (n, t) -> (n, apply subst t)) lst) )
            else None
        | _ -> None)
    | Typename ((p :: rest, id), args), { ns = (t, env') :: other; _ } -> (
        try
          let mu = Unify.unify state.vars p t in
          match apply_ns mu env' with
          | Ref env' -> (
              match aux !env' (Typename ((rest, id), args)) with
              | None -> aux { env with ns = other } ty
              | Some (theta, ty, expr) -> Some (Subst.compose theta mu, ty, expr)
              )
          | Redirect ty -> (
              let path, id = item_of_type ty id in
              match aux current_env (Typename ((path @ rest, id), args)) with
              | None -> aux { env with ns = other } ty
              | Some (theta, ty, expr) -> Some (Subst.compose theta mu, ty, expr)
              )
        with _ -> aux { env with ns = other } ty)
    | Typename ((_ :: _, _), _), { ns = []; _ } -> None
  in
  aux current_env ty

let type_lit (env : typing_env) state =
  Ast.Literal.(
    function
    | Unit -> (Ir.Unit, unit, Subst.empty)
    | Int (i, ty) -> (Ir.Int (i, ty), ty, Subst.empty)
    | Bool b -> (Ir.Bool b, bool, Subst.empty)
    | Float (f, ty) -> (Ir.Float (f, ty), ty, Subst.empty)
    | String s -> (Ir.String s, str, Subst.empty)
    | Ident id ->
        let sch, subst = find_item env state id in
        let ty = instance sch in
        (Ir.Ident (id, ty), ty, subst))

let rec type_array_expr (env : typing_env) (state : state) arr =
  let rec aux env = function
    | [] -> ([], new_type "elt", Subst.empty)
    | elt :: rest ->
        let elt_ir, elt_t, elt_s = type_expr env state elt in
        let rest_ir, rest_t, rest_s = aux (apply_env elt_s env) rest in
        let comp = Subst.compose elt_s rest_s in
        let theta = Unify.unify state.vars rest_t (Subst.apply elt_t rest_s) in
        (elt_ir :: rest_ir, Subst.apply rest_t theta, Subst.compose comp theta)
  in
  let ir, ty, subst = aux env arr in
  (ir, ty, subst)

and type_tuple_expr (env : typing_env) (state : state) comps =
  let rec aux env state comps =
    match (state.hint, comps) with
    | _, [] -> ([], [], Subst.empty)
    | Some (Tuple (hint :: rest_hint)), elt :: rest ->
        let elt_ir, elt_t, elt_s =
          type_expr env { state with hint = Some hint } elt
        in
        let rest_ir, rest_t, rest_s =
          aux (apply_env elt_s env)
            { state with hint = Some (Tuple rest_hint) }
            rest
        in
        ( elt_ir :: rest_ir,
          Subst.apply elt_t rest_s :: rest_t,
          Subst.compose elt_s rest_s )
    | _, elt :: rest ->
        let elt_ir, elt_t, elt_s =
          type_expr env { state with hint = None } elt
        in
        let rest_ir, rest_t, rest_s =
          aux (apply_env elt_s env) { state with hint = None } rest
        in
        ( elt_ir :: rest_ir,
          Subst.apply elt_t rest_s :: rest_t,
          Subst.compose elt_s rest_s )
  in
  let ir, ty, subst = aux env state comps in
  (ir, ty, subst)

and type_struct_expr env state fields =
  let rec matches_expr env def fields =
    match (fields, def) with
    | [], [] -> Some ([], Subst.empty)
    | [], _ :: _ | _ :: _, [] -> None
    | (name, expr) :: rest, _ ->
        let* ty = List.assoc_opt name def in
        let* expr_ir, expr_t, expr_s =
          try Some (type_expr env { state with hint = Some ty } expr)
          with _ -> None
        in
        let* mu =
          try Some (Unify.unify state.vars expr_t ty) with _ -> None
        in
        let comp = Subst.compose expr_s mu in
        let d' =
          List.map
            (fun (n, t) -> (n, apply comp t))
            (List.remove_assoc name def)
        in
        let* rest_ir, rest_s = matches_expr (apply_env comp env) d' rest in
        Some ((name, expr_ir) :: rest_ir, Subst.compose comp rest_s)
  in

  let hint =
    let* t = state.hint in
    let* def = find_type_def env state t in
    match def with _, t, Struct lst -> Some (t, lst) | _ -> None
  in
  let possible_types : (t * (ident * t) list) list =
    let tmp =
      List.filter_map
        (function
          | _, (sch, Struct lst) ->
              let var_mapping =
                List.map (fun v -> (v, new_type (reverse_unique v))) (fst sch)
              in
              let ty' = deep_copy_ty var_mapping (snd sch) in
              Some
                ( ty',
                  List.map (fun (n, t) -> (n, deep_copy_ty var_mapping t)) lst
                )
          | _ -> None)
        env.types
    in
    match hint with Some (t, lst) -> (t, lst) :: tmp | None -> tmp
  in
  match
    List.find_map
      (fun (t, def) ->
        Option.map
          (fun (ir, mu) -> (ir, Subst.apply t mu, mu))
          (matches_expr env def fields))
      possible_types
  with
  | Some res -> res
  | None -> failwith "Unknown struct literal"

and type_lvalue (env : typing_env) (state : state) lval =
  match lval with
  | Ast.LIdent id ->
      let sch, subst = find_item env state ([], id) in
      let ty = instance sch in
      (Ir.LIdent (id, ty), ty, subst)
  | Ast.LTupleAccess (lval, i) ->
      let lval_ir, lval_t, lval_s = type_lvalue env state lval in
      let comp_t = new_type "comp" in
      let mu = Unify.unify_tuple_component state.vars comp_t lval_t i in
      let comp_t = Subst.apply comp_t mu in
      (Ir.LTupleAccess (lval_ir, i, comp_t), comp_t, Subst.compose lval_s mu)
  | Ast.LFieldAccess (lval, f) -> (
      let lval_ir, lval_t, lval_s =
        type_lvalue env { state with hint = None } lval
      in
      match find_type_def (apply_env lval_s env) state lval_t with
      | Some (mu, _, Struct fields) -> (
          match List.assoc_opt f fields with
          | Some ty ->
              (Ir.LFieldAccess (lval_ir, f, ty), ty, Subst.compose lval_s mu)
          | None -> raise (UnknownField (lval_t, f)))
      | _ -> raise (UnknownField (lval_t, f)))
  | Ast.LIndex (lval, idx) ->
      let idx_ir, idx_t, idx_s = type_expr env { state with hint = None } idx in
      let lval_ir, lval_t, lval_s =
        type_lvalue (apply_env idx_s env) { state with hint = None } lval
      in
      let comp = Subst.compose idx_s lval_s in
      let method_t, method_s =
        find_item (apply_env comp env) state (item_of_type lval_t "set_index")
      in
      let elt_t = new_type "elt" in
      let comp2 = Subst.compose comp method_s in
      let lval_t = Subst.apply lval_t method_s in
      let theta =
        Unify.unify state.vars (instance method_t)
          (Function ([ lval_t; idx_t; elt_t ], unit))
      in
      let comp3 = Subst.compose comp2 theta in
      let elt_t = Subst.apply elt_t comp3 in
      (Ir.LIndex (lval_ir, idx_ir, elt_t), elt_t, comp3)

and type_pattern_matching env state expr cases =
  let rec collect_enum_bindings (bindings, subst) ty ((path, cons), arg) =
    let enum_t =
      match List.rev path with
      | Typename (([], n), v) :: q -> Typename ((List.rev q, n), v)
      | _ -> raise (UnknownConstructor (path, cons))
    in
    let mu = Unify.unify state.vars ty enum_t in
    let comp = Subst.compose subst mu in
    let theta, variants =
      match
        find_type_def (apply_env comp env) state (Subst.apply enum_t comp)
      with
      | Some (theta, _, Sum v) -> (theta, v)
      | _ -> raise (UnknownConstructor (path, cons))
    in
    let arg_t =
      match List.assoc_opt cons variants with
      | Some t -> t
      | _ -> raise (UnknownConstructor (path, cons))
    in
    collect_bindings (bindings, Subst.compose comp theta) arg_t arg
  and collect_struct_bindings (bindings, subst) ty fields =
    let matches_expr def =
      let rec aux (b, s) d f =
        match (f, d) with
        | [], [] -> Some (b, s)
        | [], _ :: _ | _ :: _, [] -> None
        | (name, pat) :: rest, _ ->
            let* field_t = List.assoc_opt name d in
            let* b', s' =
              try Some (collect_bindings (b, s) field_t pat) with _ -> None
            in
            let d' =
              List.map
                (fun (n, t) -> (n, apply s' t))
                (List.remove_assoc name d)
            in
            aux (b', s') d' rest
      in
      aux (bindings, subst) def fields
    in
    let hint =
      let* def = find_type_def env state ty in
      match def with _, t, Struct lst -> Some (t, lst) | _ -> None
    in
    let possible_types : (t * (ident * t) list) list =
      let tmp =
        List.filter_map
          (function
            | _, (sch, Struct lst) ->
                let var_mapping =
                  List.map (fun v -> (v, new_type (reverse_unique v))) (fst sch)
                in
                let ty' = deep_copy_ty var_mapping (snd sch) in
                Some
                  ( ty',
                    List.map (fun (n, t) -> (n, deep_copy_ty var_mapping t)) lst
                  )
            | _ -> None)
          env.types
      in
      match hint with Some v -> v :: tmp | None -> tmp
    in
    match
      List.find_map
        (fun (t, def) -> Option.map (fun res -> (t, res)) (matches_expr def))
        possible_types
    with
    | Some (struct_t, (bindings, subst)) ->
        let mu = Unify.unify state.vars struct_t ty in
        (bindings, Subst.compose subst mu)
    | None -> failwith "Unknown struct literal"
  and collect_bindings (bindings, subst) ty = function
    | Ast.PWildcard -> (bindings, subst)
    | Ast.PLit (Ast.Literal.Ident ([], id)) ->
        (* pattern binding *)
        ((id, trivial_sch ty) :: bindings, subst)
    | Ast.PLit lit ->
        (* constant value *)
        let _, lit_t, lit_s = type_lit env state lit in
        let mu = Unify.unify state.vars lit_t ty in
        (bindings, Subst.compose (Subst.compose subst lit_s) mu)
    | Ast.PRange (Ast.Literal.Ident ([], id), _)
    | Ast.PRange (_, Ast.Literal.Ident ([], id))
    | Ast.PRangeInclusive (Ast.Literal.Ident ([], id), _)
    | Ast.PRangeInclusive (_, Ast.Literal.Ident ([], id)) ->
        raise (BindingInRangePattern id)
    | Ast.PRange (a, b) | Ast.PRangeInclusive (a, b) ->
        let _, a_t, a_s = type_lit env state a in
        let _, b_t, b_s = type_lit (apply_env a_s env) state b in
        let comp = Subst.compose a_s b_s in
        let a_t = Subst.apply a_t b_s in
        let mu = Unify.unify state.vars (Subst.apply a_t b_s) b_t in
        let comp2 = Subst.compose comp mu in
        let c_t = Subst.apply a_t mu in
        let theta = Unify.unify state.vars c_t (varint ()) in
        (bindings, Subst.compose comp2 theta)
    | Ast.PArray lst ->
        let elt_t = new_type "elt" in
        let mu = Unify.unify state.vars (Array elt_t) ty in
        let elt_t = Subst.apply elt_t mu in
        let bindings', subst', _ =
          List.fold_left
            (fun (b, s, ty) elt ->
              let b', s' = collect_bindings (b, s) ty elt in
              (b', s', Subst.apply ty s'))
            (bindings, Subst.compose subst mu, elt_t)
            lst
        in
        (bindings', subst')
    | Ast.PStruct lst -> collect_struct_bindings (bindings, subst) ty lst
    | Ast.PTuple lst ->
        let lst_t = List.map (fun _ -> new_type "comp") lst in
        let mu = Unify.unify state.vars (Tuple lst_t) ty in
        List.fold_left2
          (fun (b, s) comp ty ->
            collect_bindings (b, s) (Subst.apply ty s) comp)
          (bindings, Subst.compose subst mu)
          lst lst_t
    | Ast.PVariant (cons, arg) ->
        collect_enum_bindings (bindings, subst) ty (cons, arg)
  in

  let expr_ir, expr_t, expr_s = type_expr env { state with hint = None } expr in
  let body_t_init = new_type "match" in

  let ir, body_t, subst =
    List.fold_left
      (fun (body_ir, body_t, body_s) (pat, body) ->
        let bindings, subst =
          collect_bindings ([], body_s) (Subst.apply expr_t body_s) pat
        in
        let env' =
          List.fold_left
            (fun e (name, sch) -> Env.new_binding e name sch)
            (apply_env subst env)
            (apply_bindings bindings subst)
        in
        let body_ir', body_t', body_s' =
          type_expr env'
            {
              state with
              hint = (if body_t = body_t_init then state.hint else Some body_t);
            }
            body
        in
        let comp = Subst.compose subst body_s' in
        let mu = Unify.unify state.vars body_t' (Subst.apply body_t comp) in
        ( (pat, body_ir') :: body_ir,
          Subst.apply body_t' mu,
          Subst.compose comp mu ))
      ([], body_t_init, expr_s) cases
  in
  (Ir.Match (expr_ir, List.rev ir, body_t), body_t, subst)

and type_expr (env : typing_env) (state : state) = function
  | Ast.Lit lit -> type_lit env state lit
  | Ast.Array elts ->
      let elt_hint =
        match state.hint with Some (Array ty) -> Some ty | _ -> None
      in
      let elt_ir, elt_t, elt_s =
        type_array_expr env { state with hint = elt_hint } elts
      in
      (Ir.Array (elt_ir, Array elt_t), Array elt_t, elt_s)
  | Ast.Repeat (expr, len) ->
      let len_ir, len_t, len_s = type_expr env { state with hint = None } len in
      let mu = Unify.unify state.vars usize len_t in
      let comp = Subst.compose len_s mu in
      let expr_ir, expr_t, expr_s =
        type_expr (apply_env comp env)
          {
            state with
            hint =
              (match state.hint with Some (Array ty) -> Some ty | _ -> None);
          }
          expr
      in
      let comp2 = Subst.compose comp expr_s in
      let arr_t = Array expr_t in
      let fun_t = Function ([ expr_t; Subst.apply len_t comp2 ], arr_t) in
      ( Ir.Call
          ( Ir.Ident (item_of_type arr_t "repeat", fun_t),
            [ expr_ir; len_ir ],
            arr_t ),
        arr_t,
        comp2 )
  | Ast.Tuple comps ->
      let comps_ir, comps_t, comps_s = type_tuple_expr env state comps in
      (Ir.Tuple (comps_ir, Tuple comps_t), Tuple comps_t, comps_s)
  | Ast.If { cond; then_branch; else_branch } ->
      let cond_ir, cond_t, cond_s =
        type_expr env { state with hint = None } cond
      in
      let mu = Unify.unify state.vars cond_t bool in
      let comp = Subst.compose cond_s mu in
      let then_ir, then_t, then_s =
        type_expr (apply_env comp env) state then_branch
      in
      let comp2 = Subst.compose comp then_s in
      let else_ir, else_t, else_s =
        type_expr (apply_env comp2 env) state else_branch
      in
      let comp3 = Subst.compose comp2 else_s in
      let theta = Unify.unify state.vars else_t (Subst.apply then_t else_s) in
      let final_t = Subst.apply else_t theta in
      ( Ir.If (cond_ir, (then_ir, else_ir), final_t),
        final_t,
        Subst.compose comp3 theta )
  | Ast.Seq (Def (name, ty, expr), rest) ->
      let expr_ir, expr_t, expr_s =
        type_expr env { state with hint = Some ty } expr
      in
      let mu = Unify.unify state.vars expr_t (Subst.apply ty expr_s) in
      let comp = Subst.compose expr_s mu in
      let env' = apply_env comp env in
      let rest_ir, rest_t, rest_s =
        type_expr (Env.new_binding env' name (trivial_sch expr_t)) state rest
      in
      let comp2 = Subst.compose comp rest_s in
      ( Ir.Seq
          (Ir.Def (name, expr_ir, Subst.apply expr_t comp2), rest_ir, rest_t),
        rest_t,
        comp2 )
  | Ast.Seq (e1, e2) ->
      let e1_ir, _, e1_s = type_expr env { state with hint = None } e1 in
      let env' = apply_env e1_s env in
      let e2_ir, e2_t, e2_s = type_expr env' state e2 in
      (Ir.Seq (e1_ir, e2_ir, e2_t), e2_t, Subst.compose e1_s e2_s)
  | Ast.Block e ->
      let ir, t, s = type_expr env state e in
      (Ir.Block (ir, t), t, s)
  | Ast.Def (name, ty, expr) ->
      let expr_ir, expr_t, expr_s =
        type_expr env { state with hint = Some ty } expr
      in
      let mu = Unify.unify state.vars ty expr_t in
      ( Ir.Def (name, expr_ir, Subst.apply expr_t mu),
        unit,
        Subst.compose expr_s mu )
  | Ast.Call (func, args) ->
      let args_ir, args_t, args_s =
        type_tuple_expr env { state with hint = None } args
      in
      let ret = new_type "ret" in
      let func_ir, func_t, func_s =
        type_expr (apply_env args_s env) { state with hint = None } func
      in
      let comp = Subst.compose args_s func_s in
      let args_t = List.map (fun t -> Subst.apply t func_s) args_t in
      let theta, by_adr =
        (Unify.unify state.vars (Function (args_t, ret)) func_t, false)
      in
      ( (if by_adr then Ir.AdressCall (func_ir, args_ir, Subst.apply ret theta)
         else Ir.Call (func_ir, args_ir, Subst.apply ret theta)),
        Subst.apply ret theta,
        Subst.compose comp theta )
  | Ast.Index (expr, idx) ->
      let idx_ir, idx_t, idx_s = type_expr env { state with hint = None } idx in
      let expr_ir, expr_t, expr_s =
        type_expr (apply_env idx_s env) { state with hint = None } expr
      in
      let comp = Subst.compose idx_s expr_s in
      let method_t, method_s =
        find_item (apply_env comp env) state (item_of_type expr_t "index")
      in
      let elt_t = new_type "elt" in
      let comp2 = Subst.compose comp method_s in
      let expr_t = Subst.apply expr_t method_s in
      let theta =
        Unify.unify state.vars (instance method_t)
          (Function ([ expr_t; idx_t ], elt_t))
      in
      let comp3 = Subst.compose comp2 theta in
      let expr_t = Subst.apply expr_t comp3 in
      let elt_t = Subst.apply elt_t comp3 in
      let fun_t = Function ([ expr_t; Subst.apply idx_t comp3 ], elt_t) in
      ( Ir.AdressCall
          ( Ir.Ident (item_of_type expr_t "index", fun_t),
            [ expr_ir; idx_ir ],
            elt_t ),
        elt_t,
        comp3 )
  | Ast.TupleAccess (expr, i) ->
      let expr_ir, expr_t, expr_s = type_expr env state expr in
      let comp_t = new_type "comp" in
      let mu = Unify.unify_tuple_component state.vars comp_t expr_t i in
      let comp_t = Subst.apply comp_t mu in
      (Ir.TupleAccess (expr_ir, i, comp_t), comp_t, Subst.compose expr_s mu)
  | Ast.While { cond; body } ->
      let cond_ir, cond_t, cond_s =
        type_expr env { state with hint = None } cond
      in
      let mu = Unify.unify state.vars cond_t bool in
      let comp = Subst.compose cond_s mu in
      let body_ir, _, body_s = type_expr (apply_env comp env) state body in
      (Ir.While (cond_ir, body_ir), unit, Subst.compose comp body_s)
  | Ast.Binop (o_name, e1, e2) -> (
      match o_name with
      | Ast.Add | Ast.Sub | Ast.Div | Ast.Mul | Ast.Mod ->
          let e1_ir, e1_t, e1_s = type_expr env state e1 in
          let env' = apply_env e1_s env in
          let e2_ir, e2_t, e2_s = type_expr env' state e2 in
          let e1_t = Subst.apply e1_t e2_s in
          let comp = Subst.compose e1_s e2_s in
          let mu = Unify.unify state.vars e1_t e2_t in
          let comp2 = Subst.compose comp mu in
          let e1_t = Subst.apply e1_t mu in
          let method_name =
            Ast.(
              match o_name with
              | Add -> "add"
              | Sub -> "sub"
              | Div -> "div"
              | Mul -> "mul"
              | Mod -> "mod"
              | _ -> failwith "unreachable")
          in
          let sigma =
            if is_varint e1_t then Unify.unify state.vars e1_t i64
            else if is_varfloat e1_t then Unify.unify state.vars e1_t f64
            else Subst.empty
          in
          let e1_t' = Subst.apply e1_t sigma in
          let method_sch, method_s =
            find_item (apply_env comp2 env) state
              (item_of_type e1_t' method_name)
          in
          let comp3 = Subst.compose comp2 method_s in
          let method_t = instance method_sch in
          let theta =
            Unify.unify state.vars method_t (Function ([ e1_t'; e1_t' ], e1_t'))
          in

          let comp4 = Subst.compose comp3 theta in
          let e1_t = Subst.apply e1_t comp4 in
          let e1_t' = Subst.apply e1_t' comp4 in
          let method_t = Function ([ e1_t; e1_t ], e1_t) in
          ( Ir.AdressCall
              ( Ir.Ident (item_of_type e1_t' method_name, method_t),
                [ e1_ir; e2_ir ],
                e1_t ),
            e1_t,
            comp4 )
      | Ast.And | Ast.Or ->
          let e1_ir, e1_t, e1_s = type_expr env { state with hint = None } e1 in
          let e2_ir, e2_t, e2_s =
            type_expr (apply_env e1_s env) { state with hint = None } e2
          in
          let comp = Subst.compose e1_s e2_s in
          let e1_t = Subst.apply e1_t e2_s in
          let u1 = Unify.unify state.vars e1_t bool in
          let u2 = Unify.unify state.vars e2_t bool in
          let ir =
            if o_name = Ast.And then Ir.If (e1_ir, (e2_ir, Ir.Bool false), bool)
            else Ir.If (e1_ir, (Ir.Bool true, e2_ir), bool)
          in
          (ir, bool, Subst.compose (Subst.compose comp u1) u2)
      | Ast.Eq | Ast.Ne ->
          let e1_ir, e1_t, e1_s = type_expr env { state with hint = None } e1 in
          let e2_ir, e2_t, e2_s =
            type_expr (apply_env e1_s env) { state with hint = None } e2
          in
          let comp = Subst.compose e1_s e2_s in
          let mu = Unify.unify state.vars (Subst.apply e1_t e2_s) e2_t in
          let e_t = Subst.apply e2_t mu in
          let fun_t = Function ([ e_t; e_t ], bool) in
          ( Ir.AdressCall
              (Ir.Ident (item_of_type e_t "eq", fun_t), [ e1_ir; e2_ir ], bool),
            bool,
            Subst.compose comp mu )
      | Ast.Lt | Ast.Le | Ast.Gt | Ast.Ge ->
          let e1_ir, e1_t, e1_s = type_expr env state e1 in
          let env' = apply_env e1_s env in
          let e2_ir, e2_t, e2_s = type_expr env' state e2 in
          let e1_t = Subst.apply e1_t e2_s in
          let comp = Subst.compose e1_s e2_s in
          let mu = Unify.unify state.vars e1_t e2_t in
          let comp2 = Subst.compose comp mu in
          let e1_t = Subst.apply e1_t mu in
          let sigma =
            if is_varint e1_t then Unify.unify state.vars e1_t i64
            else if is_varfloat e1_t then Unify.unify state.vars e1_t f64
            else Subst.empty
          in
          let e1_t' = Subst.apply e1_t sigma in
          let mname =
            Ast.(
              match o_name with
              | Lt -> "lt"
              | Le -> "le"
              | Gt -> "gt"
              | Ge | _ -> "ge")
          in
          let method_t, method_s =
            find_item (apply_env comp2 env) state (item_of_type e1_t' mname)
          in
          let comp3 = Subst.compose comp2 method_s in
          let theta =
            Unify.unify state.vars (instance method_t)
              (Function ([ e1_t'; e1_t' ], Types.bool))
          in
          let comp4 = Subst.compose comp3 theta in
          let e_t = Subst.apply e1_t comp4 in
          let ir =
            Ir.AdressCall
              ( Ir.Ident
                  (item_of_type e_t mname, Function ([ e_t; e_t ], Types.bool)),
                [ e1_ir; e2_ir ],
                Types.bool )
          in
          (ir, bool, Subst.compose comp3 theta))
  | Ast.Monop (op, e) ->
      let e_ir, e_t, e_s = type_expr env state e in
      let method_name = match op with Ast.Neg -> "neg" | Ast.Not -> "not" in
      let sigma =
        if is_varint e_t then Unify.unify state.vars e_t i64
        else if is_varfloat e_t then Unify.unify state.vars e_t f64
        else Subst.empty
      in
      let e_t' = Subst.apply e_t sigma in
      let method_t, method_s =
        find_item (apply_env e_s env) state (item_of_type e_t' method_name)
      in
      let comp = Subst.compose e_s method_s in
      let mu =
        Unify.unify state.vars (instance method_t) (Function ([ e_t' ], e_t'))
      in
      let comp2 = Subst.compose comp mu in
      let e_t = Subst.apply e_t mu in
      let ir =
        Ir.AdressCall
          ( Ir.Ident (item_of_type e_t method_name, Function ([ e_t ], e_t)),
            [ e_ir ],
            e_t )
      in
      (ir, e_t, comp2)
  | Ast.Struct fields ->
      let ir, t, subst = type_struct_expr env state fields in
      (Ir.Struct (ir, t), t, subst)
  | Ast.MethodCall (expr, f, args) ->
      let expr_ir, expr_t, expr_s =
        type_expr env { state with hint = None } expr
      in
      let env' = apply_env expr_s env in
      let func_t, func_s = find_item env' state (item_of_type expr_t f) in
      let func_t = instance func_t in
      let comp = Subst.compose expr_s func_s in
      let args_ir, args_t, args_s =
        type_tuple_expr (apply_env func_s env') { state with hint = None } args
      in
      let comp2 = Subst.compose comp args_s in
      let ret = new_type "ret" in
      let mu =
        Unify.unify state.vars (Subst.apply func_t comp2)
          (Function (Subst.apply expr_t args_s :: args_t, ret))
      in
      let comp3 = Subst.compose comp2 mu in
      let expr_t = Subst.apply expr_t comp3 in
      let args_t = List.map (fun t -> Subst.apply t comp3) args_t in
      let ret = Subst.apply ret mu in
      let func_t = Function (expr_t :: args_t, ret) in
      let ir =
        Ir.AdressCall
          (Ir.Ident (item_of_type expr_t f, func_t), expr_ir :: args_ir, ret)
      in
      (ir, ret, comp3)
  | Ast.FieldAccess (expr, id) -> (
      let expr_ir, expr_t, expr_s =
        type_expr env { state with hint = None } expr
      in
      match find_type_def (apply_env expr_s env) state expr_t with
      | Some (mu, _, Struct fields) -> (
          match List.assoc_opt id fields with
          | Some ty ->
              (Ir.FieldAccess (expr_ir, id, ty), ty, Subst.compose expr_s mu)
          | None -> raise (UnknownField (expr_t, id)))
      | _ -> raise (UnknownField (expr_t, id)))
  | Ast.Assign (lval, expr) ->
      let lval_ir, lval_t, lval_s =
        type_lvalue env { state with hint = None } lval
      in
      let expr_ir, expr_t, expr_s =
        type_expr (apply_env lval_s env) { state with hint = Some lval_t } expr
      in
      let comp = Subst.compose lval_s expr_s in
      let mu = Unify.unify state.vars expr_t (Subst.apply lval_t expr_s) in
      ( Ir.Assign (lval_ir, expr_ir, Subst.apply expr_t mu),
        unit,
        Subst.compose comp mu )
  | Ast.Match (expr, cases) -> type_pattern_matching env state expr cases
  | Ast.Return expr -> (
      match state.return_type with
      | Some ret_t ->
          let expr_ir, expr_t, expr_s =
            type_expr env { state with hint = Some ret_t } expr
          in
          let mu = Unify.unify state.vars expr_t ret_t in
          (Ir.Return expr_ir, new_type "div", Subst.compose expr_s mu)
      | None -> failwith "Cannot use return outside of function body!")
  | Break -> (Ir.Break, new_type "div", Subst.empty)

let rec type_toplevel env state = function
  | [] -> ([], [], env)
  | Ast.Const { const_name; ty; expr } :: rest ->
      let expr_ir, expr_t, expr_s =
        type_expr env { state with hint = Some ty } expr
      in
      let mu = Unify.unify state.vars expr_t ty in
      let comp = Subst.compose expr_s mu in
      let rest_decls, rest_types, rest_env =
        type_toplevel
          (Env.add_global env state.curr_ns Env.new_binding const_name
             (generalize_global ty state.vars))
          state rest
      in
      ( ((state.path, const_name), Ir.Const (ty, Ir.apply comp expr_ir))
        :: rest_decls,
        rest_types,
        rest_env )
  | Ast.Function (vars, { fun_name; params; ret; body }) :: rest -> (
      try
        let new_vars = vars @ state.vars in
        let fun_t =
          generalize_global (Function (List.map snd params, ret)) state.vars
        in
        let env' =
          Env.add_global env state.curr_ns Env.new_binding fun_name fun_t
        in
        let local_env =
          List.fold_left
            (fun acc (n, t) -> Env.new_binding acc n (trivial_sch t))
            env' params
        in
        let body_ir, body_t, body_s =
          type_expr local_env
            {
              state with
              hint = Some ret;
              vars = new_vars;
              return_type = Some ret;
            }
            body
        in
        let mu = Unify.unify new_vars ret body_t in
        let comp = Subst.compose body_s mu in
        let rest_decls, rest_types, rest_env = type_toplevel env' state rest in
        let func =
          match List.nth_opt params 0 with
          | Some (name, _) when name = Types.self ->
              Ir.Method (params, ret, Ir.apply comp body_ir)
          | _ -> Ir.Function (params, ret, Ir.apply comp body_ir)
        in
        let path =
          match List.hd (List.rev state.path) with
          | Typename _ -> state.path
          | ty -> [ ty ]
        in
        (((path, fun_name), func) :: rest_decls, rest_types, rest_env)
      with e ->
        let () =
          Format.eprintf "in %a\n%!" Printers.pp_item (state.path, fun_name)
        in
        raise e)
  | Ast.Typedef (_, (_, Alias _)) :: _ ->
      failwith "There should be no alias definitions in the AST at this point"
  | Ast.Typedef (name, (vars, Struct fields)) :: rest ->
      let vars' = List.map (fun v -> Var v) vars in
      let env' =
        Env.add_global env state.curr_ns Env.new_type name
          ((vars, Typename ((state.path, name), vars')), Struct fields)
      in
      let rest_decls, rest_types, rest_env = type_toplevel env' state rest in
      ( rest_decls,
        (Typename ((state.path, name), vars'), Struct fields) :: rest_types,
        rest_env )
  | Ast.Typedef (name, (vars, Sum variants)) :: rest ->
      let vars' = List.map (fun v -> Var v) vars in
      let full_ty = Typename ((state.path, name), vars') in
      let env' =
        Env.add_global env state.curr_ns Env.new_type name
          (generalize_global full_ty state.vars, Sum variants)
      in
      let local_ty = Typename (([], name), vars') in
      let constructors = ref Env.init in
      let env'' =
        Env.add_global env' state.curr_ns Env.new_ns local_ty
          (Env.Ref constructors)
      in
      let new_vars = vars @ state.vars in
      let _ =
        (* add constructors to the inner namespace *)
        List.fold_left
          (fun acc (variant_name, variant_ty) ->
            Env.add_global acc constructors Env.new_binding variant_name
              (generalize_global
                 (match variant_ty with
                 | Tuple lst -> Function (lst, full_ty)
                 | _ ->
                     if variant_ty = unit then full_ty
                     else Function ([ variant_ty ], full_ty))
                 new_vars))
          env'' variants
      in
      let rest_decls, rest_types, rest_env = type_toplevel env'' state rest in
      let constructors =
        List.map
          (fun (v, ty) ->
            ((state.path @ [ local_ty ], v), Ir.Constructor (v, ty, full_ty)))
          variants
      in
      ( constructors @ rest_decls,
        (Typename ((state.path, name), vars'), Sum variants) :: rest_types,
        rest_env )
  | Ast.Typedef (type_name, (vars, Extern symbol)) :: rest ->
      let vars' = List.map (fun v -> Var v) vars in
      let env' =
        Env.add_global env state.curr_ns Env.new_type type_name
          ( generalize_global
              (Typename ((state.path, type_name), vars'))
              state.vars,
            Extern symbol )
      in
      let rest_decls, rest_types, rest_env = type_toplevel env' state rest in
      ( rest_decls,
        (Typename ((state.path, type_name), vars'), Extern symbol) :: rest_types,
        rest_env )
  | Ast.Implementation (vars, ty, decls) :: rest ->
      let inner_env = ref empty_env in
      let env' =
        Env.add_global env state.curr_ns Env.new_ns (make_local ty)
          (Env.Ref inner_env)
      in
      let decls, types, _ =
        type_toplevel env'
          {
            state with
            path = state.path @ [ make_local ty ];
            curr_ns = inner_env;
            vars = vars @ state.vars;
          }
          decls
      in
      let rest_decls, rest_types, rest_env = type_toplevel env' state rest in
      (decls @ rest_decls, types @ rest_types, rest_env)
  | Ast.Use _ :: _ ->
      failwith "There should be no use statements in the AST at this point"
  | Ast.ExternDef { val_name; ty; symbol } :: rest ->
      let env' =
        Env.add_global env state.curr_ns Env.new_binding val_name
          (generalize_global ty state.vars)
      in
      let rest_decls, rest_types, rest_env = type_toplevel env' state rest in
      ( ( ( (match List.hd (List.rev state.path) with
            | Typename _ -> state.path
            | ty -> [ ty ]),
            val_name ),
          if String.starts_with ~prefix:"@" symbol then
            Ir.Intrinsic (String.sub symbol 1 (String.length symbol - 1), ty)
          else Ir.Extern (symbol, ty) )
        :: rest_decls,
        rest_types,
        rest_env )

let type_program module_name program init_env =
  let module_ns = const_typename module_name in
  let module_env = ref Env.init in
  let env =
    Env.add_global !init_env init_env Env.new_ns module_ns (Ref module_env)
  in
  let ir, types, env' =
    type_toplevel
      (Env.new_ns env root_ns (Ref module_env))
      {
        path = [ module_ns ];
        curr_ns = module_env;
        vars = [];
        hint = None;
        return_type = None;
      }
      program
  in
  (ir, types, { env' with ns = List.remove_assoc root_ns env'.ns })
