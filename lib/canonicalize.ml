open Types
open Utils

exception UnboundIdentifier of Ast.item
exception UnboundType of Ast.ty
exception DuplicatePatternBinding of Ast.ident
exception UnspecifiedType of Ast.ty
exception ImplNonLocal of Ast.ty

type canonical_env = (Ast.path, Types.schema) env

type state = {
  path : Types.path;
  curr_ns : canonical_env ref;
  vars : string list;
  in_loop : bool;
}

let rec apply_ns mu = function
  | Env.Ref env -> Env.Ref (ref (apply_env mu !env))
  | Env.Redirect ty -> Env.Redirect (Subst.apply ty mu)

and apply_env mu ({ bindings; types; ns } : canonical_env) =
  {
    bindings =
      List.map
        (fun (n, p) -> (n, List.map (fun t -> Subst.apply t mu) p))
        bindings;
    types = List.map (fun (n, (v, t)) -> (n, (v, Subst.apply t mu))) types;
    ns = List.map (fun (ty, ns) -> (Subst.apply ty mu, apply_ns mu ns)) ns;
  }

let rec has_free_vars vars = function
  | Array ty -> has_free_vars vars ty
  | Tuple lst -> List.exists (has_free_vars vars) lst
  | Function (args, ret) ->
      List.exists (has_free_vars vars) args || has_free_vars vars ret
  | Typename (_, params) -> List.exists (has_free_vars vars) params
  | Var x -> not (List.mem x vars)
  | VarInt i -> not (List.mem i vars)
  | VarFloat f -> not (List.mem f vars)

let find_type (current_env : canonical_env) state ty =
  let rec find_list env = function
    | [] -> Some []
    | a :: q ->
        let* a = aux env a in
        let+ q = find_list env q in
        a :: q
  and aux env (ty : Ast.ty) : Ast.ty option =
    if ty = self_type then Option.map snd (List.assoc_opt self env.Env.types)
    else
      match (ty, env) with
      | Array ty, env ->
          let+ t = aux env ty in
          Array t
      | Tuple comps, env ->
          let+ c = find_list env comps in
          Tuple c
      | Function (args, ret), env ->
          let* ret = aux env ret in
          let+ args = find_list env args in
          Function (args, ret)
      | Typename (([], name), params), _ -> (
          let* params = find_list env params in
          let* sch = List.assoc_opt name env.types in
          match sch with
          | vars, Typename (item, params') ->
              if List.length vars = List.length params then
                let mu = zip vars params in
                Some
                  (Typename (item, List.map (fun t -> Subst.apply t mu) params'))
              else None
          | other -> if params = [] then Some (snd other) else None)
      | Typename ((p :: rest, id), args), { ns = (t, env') :: other; _ } -> (
          try
            let mu = Unify.unify state.vars p t in
            let ty' =
              match apply_ns mu env' with
              | Ref env'' -> aux !env'' (Typename ((rest, id), args))
              | Redirect ty ->
                  let path, id = item_of_type ty id in
                  aux current_env (Typename ((path @ rest, id), args))
            in
            match ty' with
            | Some v -> Some v
            | None -> aux { env with ns = other } ty
          with _ -> aux { env with ns = other } ty)
      | Typename ((_ :: _, _), _), { ns = []; _ } -> None
      | Var _, _ -> Some ty
      | VarInt _, _ -> Some ty
      | VarFloat _, _ -> Some ty
  in
  match aux current_env ty with
  | Some (Typename (it, vars)) -> Typename (it, vars)
  | Some v -> v
  | None -> raise (UnboundType ty)

let rec find_item current_env state item =
  let rec aux (env : canonical_env) (item : Ast.item) : Ast.item option =
    match (item, env) with
    | ([], id), _ ->
        Option.map (fun p -> (p, id)) (List.assoc_opt id env.bindings)
    | ((Typename ((_ :: _, _), []) as p) :: rest, id), _ ->
        let full_type = find_type env state p in
        let path, _ = item_of_type full_type id in
        Some (find_item current_env state (path @ rest, id))
    | (p :: rest, id), { ns = (t, env') :: other; _ } -> (
        let mu =
          try Some (Unify.unify state.vars p t)
          with _ -> (
            match p with
            | Typename (it, []) -> (
                let p' =
                  Typename (it, List.map (fun _ -> new_type "") (type_params t))
                in
                try Some (Unify.unify state.vars p' t) with _ -> None)
            | _ -> None)
        in
        match mu with
        | Some mu -> (
            match apply_ns mu env' with
            | Ref env' -> (
                match aux !env' (rest, id) with
                | None -> aux { env with ns = other } item
                | Some v -> Some v)
            | Redirect ty -> (
                let path, id = item_of_type ty id in
                match aux current_env (path @ rest, id) with
                | None -> aux { env with ns = other } item
                | Some v -> Some v))
        | None -> aux { env with ns = other } item)
    | (_ :: _, _), { ns = []; _ } -> None
  in
  match aux current_env item with
  | Some v -> v
  | None -> raise (UnboundIdentifier item)

open Ast

let canonicalize module_name program init_env =
  (* let new_names = Hashtbl.create 5 in
     let append a b = if not (Hashtbl.mem new_names a) then Hashtbl.add new_names a b in *)
  let canonical_literal env state = function
    | Literal.Ident it -> Literal.Ident (find_item env state it)
    | l -> l
  in
  let rec bound_id env state pat =
    match pat with
    | PLit (Literal.Ident (path, id)) ->
        if path = [] then
          match
            try find_item env state ([], id)
            with UnboundIdentifier _ -> ([], id)
          with
          | [], id -> (PLit (Literal.Ident ([], id)), [ id ])
          | const -> (PVariant (const, PLit Literal.Unit), [])
        else
          let full_id = find_item env state (path, id) in
          (PVariant (full_id, PLit Literal.Unit), [])
    | PWildcard | PLit _ -> (pat, [])
    | PRange (b, e) ->
        ( PRange (canonical_literal env state b, canonical_literal env state e),
          [] )
    | PRangeInclusive (b, e) ->
        ( PRangeInclusive
            (canonical_literal env state b, canonical_literal env state e),
          [] )
    | PStruct lst ->
        let ids, lst' =
          List.fold_left_map
            (fun acc (name, pat) ->
              let pat', ids = bound_id env state pat in
              List.iter
                (fun id ->
                  if List.mem id acc then raise (DuplicatePatternBinding id))
                ids;
              (ids @ acc, (name, pat')))
            [] lst
        in
        (PStruct lst', ids)
    | PTuple lst ->
        let ids, lst' =
          List.fold_left_map
            (fun acc pat ->
              let pat', ids = bound_id env state pat in
              List.iter
                (fun id ->
                  if List.mem id acc then raise (DuplicatePatternBinding id))
                ids;
              (ids @ acc, pat'))
            [] lst
        in
        (PTuple lst', ids)
    | PArray lst ->
        let ids, lst' =
          List.fold_left_map
            (fun acc pat ->
              let pat', ids = bound_id env state pat in
              List.iter
                (fun id ->
                  if List.mem id acc then raise (DuplicatePatternBinding id))
                ids;
              (ids @ acc, pat'))
            [] lst
        in
        (PArray lst', ids)
    | PVariant (it, pat) ->
        let pat', ids = bound_id env state pat in
        (PVariant (find_item env state it, pat'), ids)
  in
  let rec canonical_pattern env state (pat, expr) =
    let pat', ids = bound_id env state pat in
    ( pat',
      canonical_expr
        (List.fold_left (fun acc n -> Env.new_binding acc n []) env ids)
        state expr )
  and canonical_lvalue env state = function
    | LIdent id ->
        let p, id = find_item env state ([], id) in
        if p = [] then LIdent id
        else failwith ("Cannot assign to global binding" ^ id)
    | LTupleAccess (lval, i) -> LTupleAccess (canonical_lvalue env state lval, i)
    | LFieldAccess (lval, s) -> LFieldAccess (canonical_lvalue env state lval, s)
    | LIndex (lval, expr) ->
        LIndex (canonical_lvalue env state lval, canonical_expr env state expr)
  and canonical_expr env state = function
    | Lit (Literal.Ident item) ->
        let path, id = find_item env state item in
        const_item path id
    | Lit l -> Lit l
    | Array lst -> Array (List.map (canonical_expr env state) lst)
    | Repeat (expr, len) ->
        Repeat (canonical_expr env state expr, canonical_expr env state len)
    | Tuple lst -> Tuple (List.map (canonical_expr env state) lst)
    | Struct lst ->
        Struct
          (List.map
             (fun (field, expr) -> (field, canonical_expr env state expr))
             lst)
    | TupleAccess (expr, i) -> TupleAccess (canonical_expr env state expr, i)
    | FieldAccess (expr, id) -> FieldAccess (canonical_expr env state expr, id)
    | Index (expr, idx) ->
        Index (canonical_expr env state expr, canonical_expr env state idx)
    | Def (id, ty, expr) ->
        Def (id, find_type env state ty, canonical_expr env state expr)
    | Assign (lval, expr) ->
        Assign (canonical_lvalue env state lval, canonical_expr env state expr)
    | MethodCall (expr, f, args) ->
        MethodCall
          ( canonical_expr env state expr,
            f,
            List.map (canonical_expr env state) args )
    | Call (expr, args) ->
        Call
          ( canonical_expr env state expr,
            List.map (canonical_expr env state) args )
    | Binop (op, e1, e2) ->
        Binop (op, canonical_expr env state e1, canonical_expr env state e2)
    | Monop (op, expr) -> Monop (op, canonical_expr env state expr)
    | If { cond; then_branch; else_branch } ->
        If
          {
            cond = canonical_expr env state cond;
            then_branch = canonical_expr env state then_branch;
            else_branch = canonical_expr env state else_branch;
          }
    | While { cond; body } ->
        While
          {
            cond = canonical_expr env state cond;
            body = canonical_expr env { state with in_loop = true } body;
          }
    | Match (expr, lst) ->
        Match
          ( canonical_expr env state expr,
            List.map (canonical_pattern env state) lst )
    | Block expr -> Block (canonical_expr env state expr)
    | Seq (Def (ident, ty, expr), rest) ->
        let ty' = find_type env state ty in
        Seq
          ( Def (ident, ty', canonical_expr env state expr),
            canonical_expr (Env.new_binding env ident []) state rest )
    | Seq (e1, e2) ->
        Seq (canonical_expr env state e1, canonical_expr env state e2)
    | Return expr -> Return (canonical_expr env state expr)
    | Break ->
        if state.in_loop then Break
        else failwith "Cannot use a break statement outside of a loop!"
  in
  let rec canonical_toplevel env state = function
    | [] -> ([], env)
    | Const { const_name; ty; expr } :: rest ->
        let full_type = find_type env state ty in
        let () =
          if has_free_vars state.vars full_type then raise (UnspecifiedType ty)
        in
        let rest', env' =
          canonical_toplevel
            (Env.add_global env state.curr_ns Env.new_binding const_name
               state.path)
            state rest
        in
        ( Const
            { const_name; ty = full_type; expr = canonical_expr env state expr }
          :: rest',
          env' )
    | Typedef (name, (vars, Alias ty)) :: rest ->
        let new_vars = vars @ state.vars in
        let full_type = find_type env { state with vars = new_vars } ty in
        let () =
          if has_free_vars new_vars full_type then raise (UnspecifiedType ty)
        in
        let env' =
          Env.add_global env state.curr_ns Env.new_type name (vars, full_type)
        in
        let ty' = Typename (([], name), List.map (fun v -> Var v) vars) in
        let ns = Env.Redirect full_type in
        canonical_toplevel
          (Env.add_global env' state.curr_ns Env.new_ns ty' ns)
          state rest
    | Typedef (name, (vars, Types.Struct fields)) :: rest ->
        let new_vars = vars @ state.vars in
        let () =
          List.iter
            (fun (_, ty) ->
              if has_free_vars new_vars ty then raise (UnspecifiedType ty))
            fields
        in
        let vars' = List.map (fun v -> Var v) vars in
        let env' =
          Env.add_global env state.curr_ns Env.new_type name
            (vars, Typename ((state.path, name), vars'))
        in
        let full_expr =
          Types.Struct
            (List.map
               (fun (name, ty) ->
                 (name, find_type env' { state with vars = new_vars } ty))
               fields)
        in
        let rest', env'' = canonical_toplevel env' state rest in
        (Typedef (name, (vars, full_expr)) :: rest', env'')
    | Typedef (name, (vars, Types.Sum variants)) :: rest ->
        let new_vars = vars @ state.vars in
        let () =
          List.iter
            (fun (_, ty) ->
              if has_free_vars new_vars ty then raise (UnspecifiedType ty))
            variants
        in
        let vars' = List.map (fun v -> Var v) vars in
        let env' =
          Env.add_global env state.curr_ns Env.new_type name
            (vars, Typename ((state.path, name), vars'))
        in
        let full_expr =
          Types.Sum
            (List.map
               (fun (name, ty) ->
                 (name, find_type env' { state with vars = new_vars } ty))
               variants)
        in
        let local_ty = Typename (([], name), vars') in
        let constructors =
          let cons_path = state.path @ [ local_ty ] in
          Env.Ref
            (ref
               {
                 Env.init with
                 bindings =
                   List.map (fun (variant, _) -> (variant, cons_path)) variants;
               })
        in
        let rest', env'' =
          canonical_toplevel
            (Env.add_global env' state.curr_ns Env.new_ns local_ty constructors)
            state rest
        in
        (Typedef (name, (vars, full_expr)) :: rest', env'')
    | Typedef (type_name, (vars, Extern symbol)) :: rest ->
        let () =
          if List.hd state.path <> core_ns && Utils.is_valid_identifier symbol
          then failwith "An extern symbol must be a valid C identifier";
          if List.hd state.path <> core_ns && vars <> [] then
            failwith "An extern type cannot have type variables"
        in
        let env' =
          Env.add_global env state.curr_ns Env.new_type type_name
            ( vars,
              Typename ((state.path, type_name), List.map (fun v -> Var v) vars)
            )
        in
        let rest', env'' = canonical_toplevel env' state rest in
        (Typedef (type_name, (vars, Extern symbol)) :: rest', env'')
    | Function (vars, { fun_name; params; ret; body }) :: rest ->
        let new_vars = vars @ state.vars in
        let find_full_type t =
          let t' = find_type env { state with vars = new_vars } t in
          if has_free_vars new_vars t' then raise (UnspecifiedType t) else t'
        in
        let params' = List.map (fun (n, ty) -> (n, find_full_type ty)) params in
        let ret' = find_full_type ret in
        let env' =
          Env.add_global env state.curr_ns Env.new_binding fun_name state.path
        in
        let body' =
          canonical_expr
            (List.fold_left
               (fun env (n, _) -> Env.new_binding env n [])
               env' params')
            { state with vars = new_vars }
            body
        in
        let rest', env'' = canonical_toplevel env' state rest in
        ( Function
            (vars, { fun_name; params = params'; ret = ret'; body = body' })
          :: rest',
          env'' )
    | Implementation (vars, ty, decls) :: rest ->
        let new_vars = vars @ state.vars in
        let full_ty =
          try find_type !(state.curr_ns) { state with vars = new_vars } ty
          with UnboundType t ->
            if t = ty then raise (ImplNonLocal ty) else raise (UnboundType t)
        in
        (if List.hd state.path <> core_ns then
           let lty = make_local full_ty in
           let name, vars =
             match lty with
             | Typename (([], name), vars) -> (name, vars)
             | _ -> raise (ImplNonLocal lty)
           in
           if
             not
               (List.exists
                  (fun (n, (v, _)) ->
                    n = name && List.length v = List.length vars)
                  !(state.curr_ns).types)
           then raise (ImplNonLocal lty));

        let inner_env = ref Env.init in
        let env' =
          Env.add_global env state.curr_ns Env.new_ns ty (Ref inner_env)
        in
        let decls', _ =
          canonical_toplevel
            (Env.new_ns
               (Env.new_type env' self ([], full_ty))
               self_type (Redirect full_ty))
            {
              state with
              path = state.path @ [ ty ];
              curr_ns = inner_env;
              vars = new_vars;
            }
            decls
        in
        let rest', env'' = canonical_toplevel env' state rest in
        (Implementation (vars, full_ty, decls') :: rest', env'')
    | Use (path, id) :: rest ->
        canonical_toplevel
          {
            env with
            bindings =
              (id, fst (find_item env state (path, id))) :: env.bindings;
          }
          state rest
    | ExternDef { val_name; ty; symbol } :: rest ->
        let full_ty = find_type env state ty in
        let () =
          if List.hd state.path <> core_ns && has_free_vars [] full_ty then
            failwith "An extern symbol cannot have a generic type";
          if List.hd state.path <> core_ns && Utils.is_valid_identifier symbol
          then failwith "An extern symbol must be a valid C identifier"
        in
        let env' =
          Env.add_global env state.curr_ns Env.new_binding val_name state.path
        in
        let rest', env'' = canonical_toplevel env' state rest in
        (ExternDef { val_name; ty = full_ty; symbol } :: rest', env'')
  in
  let module_ns = const_typename module_name in
  let module_env = ref Env.init in
  let env =
    Env.add_global !init_env init_env Env.new_ns module_ns (Ref module_env)
  in
  let canonicalized_program, env' =
    canonical_toplevel
      (Env.new_ns env root_ns (Ref module_env))
      { path = [ module_ns ]; curr_ns = module_env; vars = []; in_loop = false }
      program
  in
  (canonicalized_program, { env' with ns = List.remove_assoc root_ns env'.ns })

let debug filename =
  canonicalize
    (Filename.remove_extension (Filename.basename filename))
    (Parser.program Lexer.lex (Lexing.from_channel (open_in filename)))
