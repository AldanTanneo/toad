open Ast

(* Type des substitutions. *)
type subst = (ident * ty) list

(* Substitution vide. *)
let empty : subst = []
let singleton var_name ty : subst = [ (var_name, ty) ]

(* Applique une seule transformation à un type : c'est l'étape élémentaire
   d'une substitution. *)
let rec apply_one transf = function
  | Types.Array ty -> Types.Array (apply_one transf ty)
  | Types.Tuple components ->
      Types.Tuple (List.map (apply_one transf) components)
  | Types.Typename ((path, name), args) ->
      Types.Typename
        ( (List.map (apply_one transf) path, name),
          List.map (apply_one transf) args )
  | Types.Function (args, ret) ->
      Types.Function (List.map (apply_one transf) args, apply_one transf ret)
  | Types.Var name -> if fst transf = name then snd transf else Types.Var name
  | Types.VarInt name ->
      if fst transf = name then snd transf else Types.VarInt name
  | Types.VarFloat name ->
      if fst transf = name then snd transf else Types.VarFloat name

(* Applique une substitution à un type. *)
let rec apply ty (subst : subst) =
  match subst with [] -> ty | h :: q -> apply (apply_one h ty) q

(* Applique une substitution à tous les types d'un environnement de typage
   et retourne le nouvel environnement. *)
let rec subst_namespace subst =
  Types.(
    function
    | Env.Ref env -> Env.Ref (ref (subst_env subst !env))
    | Env.Redirect ty -> Env.Redirect (apply ty subst))

and subst_env subst (env : (Types.schema, Types.def) Types.env) =
  {
    env with
    bindings =
      List.map
        (fun (name, (gen_vars, ty)) -> (name, (gen_vars, apply ty subst)))
        env.bindings;
    ns =
      List.map (fun (name, env') -> (name, subst_namespace subst env')) env.ns;
  }

(* Retourne la substitution subst1 restreinte à tout ce qui n'est pas dans
   le domaine de subst2. *)
let restrict subst1 subst2 =
  List.filter (fun (name, _) -> not (List.mem_assoc name subst1)) subst2

(** Composition de 2 substitutions.
   Retourne une nouvelle substitution qui aura le même effet que si l'on
   applique subst1 puis subst2 (donc subst2 rond subst1). *)
let compose (subst1 : subst) (subst2 : subst) : subst =
  let theta = List.map (fun (name, ty) -> (name, apply ty subst1)) subst2 in
  (* On retire de subst2 ce qui appartient au domaine de subst1 puisque ça
     ne sert plus, subst1 ayant été apliquée en premier, ses modifications
     sont "prioritaires". *)
  let subst2_minus_subst1 = restrict subst2 subst1 in
  theta @ subst2_minus_subst1
