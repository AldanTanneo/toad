open Ast

(* Exception pour signeler les 2 cas d'erreurs d'unification. *)
exception Cycle of (ident * ty)
exception Conflict of (ty * ty)
exception DifferentSizes
exception AnnotationNeeded
exception PartialConflict of (int * ty)
exception RefConflict of ty * ty

let rec unify_list vars a b =
  match (a, b) with
  | [], [] -> Subst.empty
  | a :: q, b :: r ->
      let s1 = unify vars a b in
      let q' = List.map (fun t -> Subst.apply t s1) q
      and r' = List.map (fun t -> Subst.apply t s1) r in
      Subst.compose (unify_list vars q' r') s1
  | [], _ :: _ | _ :: _, [] -> raise DifferentSizes

and unify_partial_tuple vars partial_t full_t =
  if Types.Tuple partial_t = full_t then Subst.empty
  else
    match (partial_t, full_t) with
    | [], Types.Tuple _ -> Subst.empty
    | a :: q, Types.Tuple (b :: r) ->
        let s1 = unify vars a b in
        let q' = List.map (fun t -> Subst.apply t s1) q
        and r' = Subst.apply (Types.Tuple r) s1 in
        Subst.compose (unify_partial_tuple vars q' r') s1
    | _, Types.Var _ -> raise AnnotationNeeded
    | _, _ -> raise DifferentSizes

and unify_tuple_component vars comp_t tuple_t i =
  match (i, tuple_t) with
  | i, Types.Tuple lst ->
      unify vars comp_t
        (match List.nth_opt lst i with
        | Some v -> v
        | None -> raise (PartialConflict (i, tuple_t)))
  | _, Types.Var _ -> raise AnnotationNeeded
  | _, _ -> raise (PartialConflict (i, tuple_t))

and unify vars t1 t2 =
  if t1 = t2 then Subst.empty
  else
    match (t1, t2) with
    | Types.Array a, Types.Array b -> unify vars a b
    | Types.Tuple a, Types.Tuple b -> (
        try unify_list vars a b
        with DifferentSizes -> raise (Conflict (t1, t2)))
    | Types.Function (args1, ret1), Types.Function (args2, ret2) ->
        let s1 =
          try unify_list vars args1 args2
          with DifferentSizes -> raise (Conflict (t1, t2))
        in
        (* s1 est la substitution nécessaire pour que args1 et args2 collent. *)
        let ret1' = Subst.apply ret1 s1 in
        let ret2' = Subst.apply ret2 s1 in
        Subst.compose (unify vars ret1' ret2') s1
    | ( Types.Typename ((path1, name1), args1),
        Types.Typename ((path2, name2), args2) ) ->
        if name1 <> name2 then raise (Conflict (t1, t2))
        else
          let s1 =
            try unify_list vars path1 path2
            with DifferentSizes -> raise (Conflict (t1, t2))
          in
          let args1' = List.map (fun t -> Subst.apply t s1) args1
          and args2' = List.map (fun t -> Subst.apply t s1) args2 in
          Subst.compose (unify_list vars args1' args2') s1
    | Types.Var v1, Types.Var v2 ->
        if v1 = v2 then Subst.empty
        else if List.mem v1 vars then
          if List.mem v2 vars then raise (Conflict (t1, t2))
          else [ (v2, Var v1) ]
        else [ (v1, Var v2) ]
    | Types.VarInt v1, Types.VarInt v2 ->
        if v1 = v2 then Subst.empty
        else if List.mem v1 vars then
          if List.mem v2 vars then raise (Conflict (t1, t2))
          else [ (v2, VarInt v1) ]
        else [ (v1, VarInt v2) ]
    | Types.VarFloat v1, Types.VarFloat v2 ->
        if v1 = v2 then Subst.empty
        else if List.mem v1 vars then
          if List.mem v2 vars then raise (Conflict (t1, t2))
          else [ (v2, VarFloat v1) ]
        else [ (v1, VarFloat v2) ]
    | Types.VarInt v, Types.Typename (_, _) ->
        if Types.is_int t2 then Subst.singleton v t2
        else raise (Conflict (t1, t2))
    | Types.Typename (_, _), Types.VarInt v ->
        if Types.is_int t1 then Subst.singleton v t1
        else raise (Conflict (t1, t2))
    | Types.VarFloat v, Types.Typename (_, _) ->
        if Types.is_float t2 then Subst.singleton v t2
        else raise (Conflict (t1, t2))
    | Types.Typename (_, _), Types.VarFloat v ->
        if Types.is_float t1 then Subst.singleton v t1
        else raise (Conflict (t1, t2))
    | Types.Var v, other | other, Types.Var v ->
        if List.mem v vars then raise (Conflict (t1, t2))
        else if Types.appear_in_ty v other then raise (Cycle (v, other));
        Subst.singleton v other
    | _ -> raise (Conflict (t1, t2))
