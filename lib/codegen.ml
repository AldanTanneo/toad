open Ir

exception ImplMoreGeneral of (Ast.item * Ast.item)
exception DifferentSignature of ((Ast.item * Ast.ty) * (Ast.item * Ast.ty))

type alignment = A8 | A4 | A2 | A1 | A0

(* check specializations. skip core. *)
let rec sanity_check = function
  | ((path, name), obj) :: rest ->
      let obj_t = Ir.obj_type obj in
      let rec aux = function
        | ((p, n), obj') :: rest ->
            if List.hd p = List.hd path then
              if n = name then
                try
                  let mu = Unify.unify [] (Types.Tuple p) (Types.Tuple path) in
                  let () =
                    match
                      Types.partial_ord (Types.Tuple path) (Types.Tuple p)
                    with
                    | Some Types.Less -> ()
                    | _ -> raise (ImplMoreGeneral ((path, name), (p, n)))
                  in
                  let obj_t' = Ir.obj_type obj' in
                  if Subst.apply obj_t mu <> Subst.apply obj_t' mu then
                    raise
                      (DifferentSignature
                         (((path, name), obj_t), ((p, n), obj_t')))
                  else ()
                with _ -> ()
              else aux rest
        | [] -> ()
      in
      if List.hd path <> Types.core_ns then aux rest;
      sanity_check rest
  | [] -> ()

let rec _mangle ty =
  let cpt = ref 0 in
  let map = Hashtbl.create 16 in
  let f oc ty =
    let f o ty = Format.fprintf o "%s" (_mangle ty) in
    let pp_seq =
      Format.pp_print_list
        ~pp_sep:(fun _ _ -> ())
        (fun o ty -> Format.fprintf o "%s" (_mangle ty))
    in
    match Hashtbl.find_opt map ty with
    | Some i -> Format.fprintf oc "S%d_" i
    | None -> (
        Hashtbl.add map ty !cpt;
        cpt := !cpt + 1;
        match ty with
        | Types.Array ty -> Format.fprintf oc "A%s" (_mangle ty)
        | Types.Tuple lst -> Format.fprintf oc "T%aE" pp_seq lst
        | Types.Function (args, ret) ->
            Format.fprintf oc "F%aE_%s" pp_seq args (_mangle ret)
        | Types.Typename (([], name), []) ->
            Format.fprintf oc "%d%s" (String.length name) name
        | Types.Typename (([], name), lst) ->
            Format.fprintf oc "%d%sI%aE" (String.length name) name pp_seq lst
        | Types.Typename ((path, name), []) ->
            Format.fprintf oc "%aN%d%s"
              (Format.pp_print_list
                 ~pp_sep:(fun oc () -> Format.pp_print_string oc "N")
                 f)
              path (String.length name) name
        | Types.Typename ((path, name), lst) ->
            Format.fprintf oc "%aN%d%sI%aE"
              (Format.pp_print_list
                 ~pp_sep:(fun oc () -> Format.pp_print_string oc "N")
                 f)
              path (String.length name) name pp_seq lst
        | Types.Var _ -> f oc Types.unit
        | Types.VarInt _ -> f oc Types.i64
        | Types.VarFloat _ -> f oc Types.f64)
  in
  Format.asprintf "%a" f ty

let mangle_item (path, name) ty =
  match path with
  | [] -> "_o" ^ string_of_int (String.length name) ^ name ^ "_" ^ _mangle ty
  | ns :: rest ->
      let first = if ns = Types.core_ns then "_c" else "_o" ^ _mangle ns in
      List.fold_left (fun acc t -> acc ^ _mangle t ^ "N") first rest
      ^ string_of_int (String.length name)
      ^ name ^ "_" ^ _mangle ty

let mangle_type ty = "_t" ^ _mangle ty

let mangle_type =
  let map = Hashtbl.create 16 in
  let rec aux ty =
    let key = mangle_type ty in
    let res =
      match Hashtbl.find_opt map key with
      | Some sym -> sym
      | None ->
          Utils.unique_string
            (match ty with
            | Types.Array t -> Utils.reverse_unique (aux t) ^ "_list"
            | Types.Tuple lst ->
                List.fold_left
                  (fun acc x -> acc ^ "_" ^ Utils.reverse_unique (aux x))
                  "tuple" lst
            | Types.Function _ -> "func"
            | Types.Typename ((_, name), args) ->
                List.fold_left
                  (fun acc x -> acc ^ "_" ^ Utils.reverse_unique (aux x))
                  name args
            | Types.Var _ -> aux Types.unit
            | Types.VarInt _ -> aux Types.i64
            | Types.VarFloat _ -> aux Types.f64)
    in
    Hashtbl.add map key res;
    res
  in
  aux

let mangle_item =
  let map = Hashtbl.create 16 in
  let aux (path, name) ty =
    let key = mangle_item (path, name) ty in
    let res =
      match Hashtbl.find_opt map key with
      | Some sym -> sym
      | None ->
          "T_"
          ^ List.fold_left
              (fun acc t -> acc ^ Utils.reverse_unique (mangle_type t) ^ "_")
              "" path
          ^ Utils.unique_string name
    in
    Hashtbl.add map key res;
    res
  in
  aux

let mangle_type x = "T_" ^ mangle_type x
let mangle_obj (it, o) = mangle_item it (Ir.obj_type o)
let generated_obj : (string, unit) Hashtbl.t = Hashtbl.create 16
let is_generated sym = Hashtbl.mem generated_obj sym

let mark_generated sym =
  if is_generated sym then false
  else (
    Hashtbl.add generated_obj sym ();
    true)

let generated_ty : (string, alignment) Hashtbl.t =
  let table = Hashtbl.create 16 in
  Hashtbl.add table (mangle_type Types.bool) A0;
  Hashtbl.add table (mangle_type Types.u8) A1;
  Hashtbl.add table (mangle_type Types.i8) A1;
  Hashtbl.add table (mangle_type Types.u16) A2;
  Hashtbl.add table (mangle_type Types.i16) A2;
  Hashtbl.add table (mangle_type Types.u32) A4;
  Hashtbl.add table (mangle_type Types.i32) A4;
  Hashtbl.add table (mangle_type Types.f32) A4;
  Hashtbl.add table (mangle_type Types.u64) A8;
  Hashtbl.add table (mangle_type Types.i64) A8;
  Hashtbl.add table (mangle_type Types.f64) A8;
  Hashtbl.add table (mangle_type Types.usize) A8;
  Hashtbl.add table (mangle_type Types.isize) A8;
  table

let get_alignment tsym =
  Option.value ~default:A8 (Hashtbl.find_opt generated_ty tsym)

let set_alignment tsym a = Hashtbl.replace generated_ty tsym a

let max_align a1 a2 =
  match (a1, a2) with
  | A8, _ | _, A8 -> A8
  | A4, _ | _, A4 -> A4
  | A2, _ | _, A2 -> A2
  | A1, _ | _, A1 -> A1
  | _ -> A0

let cmp_alignment s1 s2 =
  match (get_alignment s1, get_alignment s2) with
  | A8, _ -> 8
  | _, A8 -> -8
  | A4, _ -> 4
  | _, A4 -> -4
  | A2, _ -> 2
  | _, A2 -> -2
  | A1, _ -> 1
  | _, A1 -> -1
  | A0, A0 -> 0

let make_tmp_local name =
  if String.length name = 0 then Utils.unique_string "local"
  else Utils.unique_string name

let find_type types ty =
  (let sch = Types.generalize_global ty [] in
   if fst sch <> [] then
     failwith
       ("Cannot find type: '" ^ List.hd (fst sch) ^ " is not concretised."));
  let apply_def mu = function
    | Types.Struct lst ->
        Types.Struct (List.map (fun (n, t) -> (n, Subst.apply t mu)) lst)
    | Types.Sum lst ->
        Types.Sum (List.map (fun (n, t) -> (n, Subst.apply t mu)) lst)
    | Types.Extern s -> Types.Extern s
    | Types.Alias t -> Types.Alias (Subst.apply t mu)
  in
  let rec aux types =
    match types with
    | [] -> failwith "type not found"
    | (t, def) :: rest -> (
        try
          let mu = Unify.unify [] ty t in
          apply_def mu def
        with _ -> aux rest)
  in
  aux types

let find_obj ir (path, name) =
  (let sch = Types.generalize_global (Tuple path) [] in
   if fst sch <> [] then
     failwith ("Cannot find obj: '" ^ List.hd (fst sch) ^ " is not concretised."));
  let rec aux ir =
    match ir with
    | [] ->
        failwith
          (let _ = Format.flush_str_formatter () in
           Format.fprintf Format.str_formatter "item not found %a"
             Printers.pp_item (path, name);
           Format.flush_str_formatter ())
    | ((p, n), obj) :: rest ->
        if n = name then
          try
            let mu = Unify.unify [] (Types.Tuple path) (Types.Tuple p) in
            Ir.apply_obj mu obj
          with _ -> aux rest
        else aux rest
  in
  aux ir

let intrinsic_type oc tsym symbol vars =
  match vars with
  | [] -> (
      match symbol with
      | "unit" ->
          Format.fprintf oc "typedef struct {} %s;@," tsym;
          set_alignment tsym A0
      | "str" ->
          Format.fprintf oc "typedef struct { char * data; size_t len; } %s;@,"
            tsym;
          set_alignment tsym A8
      | _ -> failwith ("unknown intrinsic type " ^ symbol))
  | [ t ] ->
      if symbol = "box" then
        Format.fprintf oc "typedef (%s*) %s;@," (mangle_type t) tsym;
      set_alignment tsym A8
  | _ -> failwith ("unknown intrinsic type " ^ symbol)

let rec intrinsic_value oc types vsym symbol ty =
  let args, ret =
    match ty with
    | Types.Function (args, ret) -> (args, ret)
    | _ -> failwith "unknown intrinsic"
  in
  let rsym = create_type oc types ret in
  match symbol with
  | "box_new" ->
      let asym = create_type oc types (List.hd args) in
      Format.fprintf oc
        "static %s %s(%s value) { %s box = __toad_gcalloc(sizeof(value)); *box \
         = value; return box; }@;"
        rsym vsym asym rsym
  | "box_get" ->
      Format.fprintf oc "@?\n#define %s(value) (*value)\n@;@[<v>" vsym
  | "unsafe_index" ->
      Format.fprintf oc "@;#define %s(arr, i) ((arr)->data[(i)])@;" vsym
  | "panic" ->
      Format.fprintf oc
        "@;\
         @?\n\
         #define %s(msg) {}; ({ fwrite(msg.data, 1, msg.len, \
         stderr);fflush(stderr);abort();})\n\
         @[<v>"
        vsym
  | "print" ->
      let ssym = create_type oc types (List.hd args) in
      Format.fprintf oc
        "static void %s(%s s) {@;\
         <1 2>@[fwrite(s.data, 1, s.len, stdout);@;\
         fflush(stdout);@]@;\
         }@;"
        vsym ssym
  | "println" ->
      let ssym = create_type oc types (List.hd args) in
      Format.fprintf oc
        "static void %s(%s s) {@;\
         <1 2>@[fwrite(s.data, 1, s.len, stdout);@;\
         fwrite(\"\\n\", 1, 1, stdout);@;\
         fflush(stdout);@]@;\
         }@;"
        vsym ssym
  | "print_byte" ->
      let ssym = create_type oc types (List.hd args) in
      Format.fprintf oc
        "static void %s(%s s) {@;\
         <1 2>@[printf(\"%%d\", s);@;\
         fflush(stdout);@]@;\
         }@;"
        vsym ssym
  | "args" ->
      let ssym = create_type oc types Types.str in
      Format.fprintf oc
        "static %s %s() {@;\
         <1 2>@[%s * res = (%s *)__toad_gcalloc(__toad_argc * sizeof(%s));@;\
         for (int i = 0; i < __toad_argc; ++i)@;\
        \  res[i] = (%s){.data = __toad_argv[i], .len = \
         strlen(__toad_argv[i])};@;\
         return ((%s){ .data = res, .len = __toad_argc });@;\
         @]@;\
         }@;"
        rsym vsym ssym ssym ssym ssym rsym
  | "len" -> Format.fprintf oc "@;#define %s(arr) ((arr)->len)@;" vsym
  | "add" -> Format.fprintf oc "@;#define %s(a, b) ((*a) + (b))@;" vsym
  | "mul" -> Format.fprintf oc "@;#define %s(a, b) ((*a) * (b))@;" vsym
  | "sub" -> Format.fprintf oc "@;#define %s(a, b) ((*a) - (b))@;" vsym
  | "div" -> Format.fprintf oc "@;#define %s(a, b) ((*a) / (b))@;" vsym
  | "mod" -> Format.fprintf oc "@;#define %s(a, b) ((*a) %% (b))@;" vsym
  | "neg" -> Format.fprintf oc "@;#define %s(a) (-(*a))@;" vsym
  | "not" -> Format.fprintf oc "@;#define %s(a) (!(*a))@;" vsym
  | "le" -> Format.fprintf oc "@;#define %s(a, b) ((*a) <= (b))@;" vsym
  | "lt" -> Format.fprintf oc "@;#define %s(a, b) ((*a) < (b))@;" vsym
  | "ge" -> Format.fprintf oc "@;#define %s(a, b) ((*a) >= (b))@;" vsym
  | "gt" -> Format.fprintf oc "@;#define %s(a, b) ((*a) > (b))@;" vsym
  | "eq" -> Format.fprintf oc "@;#define %s(a, b) ((*a) == (b))@;" vsym
  | _ -> failwith ("unknown intrinsic " ^ symbol)

and create_obj oc ir types obj =
  let vsym = mangle_obj obj in
  (if mark_generated vsym then
     match snd obj with
     | Extern (symbol, ty) ->
         let _ = create_type oc types ty in
         Format.fprintf oc "#define %s(args...) %s(args)\n" vsym symbol
     | Function (args, ret, body) | Method (args, ret, body) ->
         let is_method = match snd obj with Method _ -> true | _ -> false in
         let asyms =
           List.map (fun (n, t) -> (n, create_type oc types t)) args
         in
         let rsym =
           if ret = Types.unit then "void" else create_type oc types ret
         in
         let buf = Buffer.create 64 in
         let body_oc = Format.formatter_of_buffer buf in
         let args =
           List.map
             (fun (n, _) ->
               if is_method && n = Types.self then (n, "*self")
               else
                 let n' = Utils.unique_string n in
                 (n, n'))
             args
         in
         let () =
           Format.fprintf body_oc "static %s %s(@[%a@]) {@;@[" rsym vsym
             (Format.pp_print_list
                ~pp_sep:(fun oc () -> Format.fprintf oc ",@;")
                (fun oc (n, s) -> Format.fprintf oc "%s %s" s n))
             (List.map2 (fun (_, s) (_, t) -> (s, t)) args asyms)
         in
         let valsym = create_value oc body_oc args ir types body in
         let () =
           if rsym <> "void" then
             Format.fprintf body_oc "return ((%s)%s);@]@;}@," rsym valsym
           else Format.fprintf body_oc "return;@]@;}@,"
         in
         let () = Format.pp_print_newline body_oc () in
         Format.fprintf oc "\n@[/* %a */@]\n" Printers.pp_item (fst obj);
         Format.fprintf oc "%s" (Buffer.contents buf)
     | Constructor (id, arg, ty) -> (
         let tsym = create_type oc types ty in
         let asym = create_type oc types arg in
         Format.fprintf oc "\n@[/* %a */@]\n" Printers.pp_item (fst obj);
         match arg with
         | Types.Tuple lst ->
             let asyms =
               List.mapi (fun i t -> (i, create_type oc types t)) lst
             in
             Format.fprintf oc
               "static inline %s %s(%a) { return (%s){ .discrim = %s_d%s, .%s \
                = (%s){%a} }; }@;"
               tsym vsym
               (Format.pp_print_list
                  ~pp_sep:(fun o () -> Format.fprintf o ", ")
                  (fun o (i, s) -> Format.fprintf o "%s _%d" s i))
               asyms tsym tsym id id asym
               (Format.pp_print_list
                  ~pp_sep:(fun o () -> Format.fprintf o ", ")
                  (fun o (i, _) -> Format.fprintf o "._%d = _%d" i i))
               asyms
         | t when t = Types.unit ->
             Format.fprintf oc
               "#define %s ((%s){ .discrim = %s_d%s, .%s = {} })@;" vsym tsym
               tsym id id
         | _ ->
             Format.fprintf oc
               "static inline %s %s(%s v) { return (%s){ .discrim = %s_d%s, \
                .%s = v }; }@;"
               tsym vsym asym tsym tsym id id)
     | Const _ -> failwith "const evaluation is not implemented"
     | Intrinsic (symbol, ty) -> intrinsic_value oc types vsym symbol ty);
  vsym

and create_type oc types ty =
  if Types.is_varint ty then create_type oc types Types.i64
  else if Types.is_varfloat ty then create_type oc types Types.f64
  else
    let tsym = mangle_type ty in
    if mark_generated tsym then (
      let buf = Buffer.create 64 in
      let def_oc = Format.formatter_of_buffer buf in
      let () =
        let () = Format.fprintf def_oc "\n/* %a */\n" pp_ty ty in
        match ty with
        | Types.Typename ((path, _name), vars) -> (
            let () =
              List.iter
                (fun t ->
                  let _ = create_type oc types t in
                  ())
                (List.tl path @ vars)
            in
            match find_type types ty with
            | Types.Extern symbol ->
                if String.starts_with ~prefix:"@" symbol then
                  intrinsic_type def_oc tsym
                    (String.sub symbol 1 (String.length symbol - 1))
                    vars
                else Format.fprintf def_oc "typedef %s %s;@," symbol tsym
            | Types.Struct lst ->
                let fsyms =
                  List.map (fun (f, t) -> (f, create_type oc types t)) lst
                in
                Format.fprintf def_oc "typedef struct {@;@[%a@]@;}  %s;@,"
                  (Format.pp_print_list
                     ~pp_sep:(fun oc () -> Format.fprintf oc "@;")
                     (fun oc (f, s) -> Format.fprintf oc "%s %s;" s f))
                  (List.sort (fun (_, s1) (_, s2) -> cmp_alignment s1 s2) fsyms)
                  tsym;
                let alignement =
                  List.fold_left
                    (fun a (_, s) -> max_align a (get_alignment s))
                    A0 fsyms
                in
                set_alignment tsym alignement
            | Types.Sum lst ->
                let vsyms =
                  List.map (fun (v, t) -> (v, create_type oc types t)) lst
                in
                let discrims = List.map (fun (v, _) -> tsym ^ "_d" ^ v) lst in
                Format.fprintf def_oc
                  "enum {@;\
                   <1 2>@[%a@]@;\
                   };@;\
                   @;\
                   typedef struct {@;\
                   <1 2>@[union {@;\
                   <1 2>@[%a@]@;\
                   };@;\
                   char discrim;@]@;\
                   } %s;@;"
                  (Format.pp_print_list
                     ~pp_sep:(fun oc () -> Format.fprintf oc ",@;")
                     Format.pp_print_string)
                  discrims
                  (Format.pp_print_list
                     ~pp_sep:(fun oc () -> Format.fprintf oc "@;")
                     (fun oc (v, s) -> Format.fprintf oc "%s %s;" s v))
                  vsyms tsym;
                let alignement =
                  List.fold_left
                    (fun a (_, s) -> max_align a (get_alignment s))
                    A1 vsyms
                in
                set_alignment tsym alignement
            | Types.Alias _ -> failwith "There should be no aliases in IR.")
        | Types.Array elt ->
            let eltsym = create_type oc types elt in
            let align = get_alignment eltsym in
            if align = A0 then (
              Format.fprintf def_oc
                "typedef struct {@;<1 2>@[size_t len;@;%s data[];@]@;} %s;@,"
                eltsym tsym;
              set_alignment tsym A0)
            else
              Format.fprintf def_oc
                "typedef struct {@;<1 2>@[size_t len;@;%s * data;@]@;} %s;@,"
                eltsym tsym;
            set_alignment tsym A8
        | Types.Tuple lst ->
            let tsyms =
              List.mapi (fun i t -> (i, create_type oc types t)) lst
            in
            let tsyms =
              List.sort (fun (_, s1) (_, s2) -> cmp_alignment s1 s2) tsyms
            in
            Format.fprintf def_oc "typedef struct {@;<1 2>@[%a@]@;} %s;@,"
              (Format.pp_print_list (fun oc (i, s) ->
                   Format.fprintf oc "%s _%d;@;" s i))
              tsyms tsym;
            let alignement =
              List.fold_left
                (fun a (_, s) -> max_align a (get_alignment s))
                A0 tsyms
            in
            set_alignment tsym alignement
        | Types.Function (args, ret) ->
            let asyms = List.map (create_type oc types) args in
            let rsym = create_type oc types ret in
            Format.fprintf def_oc "typedef %s (*%s)(%a);@," rsym tsym
              (Format.pp_print_list
                 ~pp_sep:(fun oc () -> Format.fprintf oc ", ")
                 Format.pp_print_string)
              asyms;
            set_alignment tsym A8
        | Types.(Var _ | VarInt _ | VarFloat _) -> ()
      in
      Format.pp_print_flush def_oc ();
      Format.fprintf oc "%s" (Buffer.contents buf));
    tsym

and create_value toplevel_oc oc locals ir types expr =
  match expr with
  | Unit -> ""
  | Bool b -> string_of_bool b
  | Int (i, ty) ->
      let ty = if Types.is_varint ty then Types.i64 else ty in
      let tsym = create_type toplevel_oc types ty in
      Printf.sprintf "(%s)%sLL" tsym (Int64.to_string i)
  | Float (f, ty) ->
      let ty = if Types.is_varfloat ty then Types.f64 else ty in
      let tsym = create_type toplevel_oc types ty in
      Printf.sprintf "(%s)%g" tsym f
  | String s ->
      let tsym = create_type toplevel_oc types Types.str in
      Format.asprintf "((%s){@;@[.data = %a,@;.len = %d@]@;})" tsym
        Printers.pp_c_string s (String.length s)
  | Ident (([], id), _) -> List.assoc id locals
  | Ident (it, _) ->
      let obj = find_obj ir it in
      create_obj toplevel_oc ir types (it, obj)
  | Array (lst, (Types.Array elt_t as ty)) ->
      let n = List.length lst in
      let esym = create_type toplevel_oc types elt_t in
      let tsym = create_type toplevel_oc types ty in
      let eali = get_alignment esym in
      if eali = A0 then Printf.sprintf "((%s){ .len = %d })" tsym n
      else if n = 0 then Printf.sprintf "((%s){ .data = NULL, .len = 0 })" tsym
      else
        let lsyms =
          List.map (create_value toplevel_oc oc locals ir types) lst
        in
        let asym = make_tmp_local "data" in
        let () =
          Format.fprintf oc "%s * %s = __toad_gcalloc(%d * sizeof(%s));@;" esym
            asym n esym
        in
        (if n <= 5 then
           List.iteri
             (fun i s -> Format.fprintf oc "%s[%d] = %s;@;" asym i s)
             lsyms
         else
           let tmp = make_tmp_local "tmp" in
           Format.fprintf oc
             "%s %s[%d] = {@;\
              @[%a@]@;\
              };@;\
              if (%d * sizeof(%s)) { memcpy(%s, %s, %d * sizeof(%s)); }@;"
             esym tmp n
             (Format.pp_print_list
                ~pp_sep:(fun o () -> Format.fprintf o ",@;")
                Format.pp_print_string)
             lsyms n esym asym tmp n esym);
        let final = make_tmp_local "arr" in
        Format.fprintf oc "%s %s = (%s){ .data = %s, .len = %d };@;" tsym final
          tsym asym n;
        final
  | Array (_, _) -> failwith "Invariant broken"
  | Tuple (lst, ty) ->
      let tsym = create_type toplevel_oc types ty in
      let lsyms =
        List.mapi
          (fun i c -> (i, create_value toplevel_oc oc locals ir types c))
          lst
      in
      let local = make_tmp_local "tpl" in
      Format.fprintf oc "%s %s = (%s){@[%a@]};@;" tsym local tsym
        (Format.pp_print_list
           ~pp_sep:(fun o () -> Format.fprintf o ",@;")
           (fun o (i, s) -> Format.fprintf o "._%d = %s" i s))
        lsyms;
      local
  | Struct (lst, ty) ->
      let tsym = create_type toplevel_oc types ty in
      let lsyms =
        List.map
          (fun (f, v) -> (f, create_value toplevel_oc oc locals ir types v))
          lst
      in
      let local = make_tmp_local "strct" in
      Format.fprintf oc "%s %s = (%s){@[%a@]};@;" tsym local tsym
        (Format.pp_print_list
           ~pp_sep:(fun o () -> Format.fprintf o ",@;")
           (fun o (f, s) -> Format.fprintf o ".%s = %s" f s))
        lsyms;
      local
  | TupleAccess (e, i, _) ->
      let esym = create_value toplevel_oc oc locals ir types e in
      Format.sprintf "((%s)._%d)" esym i
  | FieldAccess (e, f, _) ->
      let esym = create_value toplevel_oc oc locals ir types e in
      Format.sprintf "((%s).%s)" esym f
  | Def (id, e, ty) ->
      let tsym = create_type toplevel_oc types ty in
      let esym = create_value toplevel_oc oc locals ir types e in
      let isym = make_tmp_local id in
      Format.fprintf oc "%s %s = %s;@;" tsym isym esym;
      ""
  | Assign (lval, e, _) ->
      let esym = create_value toplevel_oc oc locals ir types e in
      let rec assign_lvalue esym = function
        | LIdent (id, _) ->
            Format.fprintf oc "%s = %s;@;" (List.assoc id locals) esym
        | LFieldAccess (l, f, _) ->
            let e = Ir.ir_of_lvalue l in
            let lsym = create_value toplevel_oc oc locals ir types e in
            let () = Format.fprintf oc "(%s).%s = %s;@;" lsym f esym in
            let lsym = create_value toplevel_oc oc locals ir types e in
            assign_lvalue lsym l
        | LTupleAccess (l, i, _) ->
            let e = Ir.ir_of_lvalue l in
            let lsym = create_value toplevel_oc oc locals ir types e in
            let () = Format.fprintf oc "(%s)._%d = %s;@;" lsym i esym in
            let lsym = create_value toplevel_oc oc locals ir types e in
            assign_lvalue lsym l
        | LIndex (l, i, ty) ->
            let lsym = create_value toplevel_oc oc locals ir types e in
            let func = Types.item_of_type ty "set_index" in
            let obj = find_obj ir func in
            let fsym = create_obj toplevel_oc ir types (func, obj) in
            let isym = create_value toplevel_oc oc locals ir types i in
            let () =
              Format.fprintf oc "%s(&%s, %s, %s);@;" fsym lsym isym esym
            in
            let lsym = create_value toplevel_oc oc locals ir types e in
            assign_lvalue lsym l
      in
      assign_lvalue esym lval;
      ""
  | Call (func, params, ty) ->
      let tsym = create_type toplevel_oc types ty in
      let fsym = create_value toplevel_oc oc locals ir types func in
      let psyms =
        List.map (create_value toplevel_oc oc locals ir types) params
      in
      if ty = Types.unit then (
        Format.fprintf oc "%s(%a);@;" fsym
          (Format.pp_print_list
             ~pp_sep:(fun o () -> Format.fprintf o ", ")
             Format.pp_print_string)
          psyms;
        "")
      else
        let res = make_tmp_local "res" in
        Format.fprintf oc "%s %s = %s(%a);@;" tsym res fsym
          (Format.pp_print_list
             ~pp_sep:(fun o () -> Format.fprintf o ", ")
             Format.pp_print_string)
          psyms;
        res
  | AdressCall (func, params, ty) ->
      let tsym = create_type toplevel_oc types ty in
      let fsym = create_value toplevel_oc oc locals ir types func in
      let psyms =
        List.map (create_value toplevel_oc oc locals ir types) params
      in
      if ty = Types.unit then (
        Format.fprintf oc "%s(&%a);@;" fsym
          (Format.pp_print_list
             ~pp_sep:(fun o () -> Format.fprintf o ", ")
             Format.pp_print_string)
          psyms;
        "")
      else
        let res = make_tmp_local "res" in
        Format.fprintf oc "%s %s = %s(&%a);@;" tsym res fsym
          (Format.pp_print_list
             ~pp_sep:(fun o () -> Format.fprintf o ", ")
             Format.pp_print_string)
          psyms;
        res
  | If (cond, (th, el), ty) ->
      if ty = Types.unit then
        let csym = create_value toplevel_oc oc locals ir types cond in
        let () = Format.fprintf oc "if (%s) {@;<1 2>@[" csym in
        let _ = create_value toplevel_oc oc locals ir types th in
        let () = Format.fprintf oc "@]@;} else {@;<1 2>@[" in
        let _ = create_value toplevel_oc oc locals ir types el in
        let () = Format.fprintf oc "@]@;}@;" in
        ""
      else
        let tsym = create_type toplevel_oc types ty in
        let csym = create_value toplevel_oc oc locals ir types cond in
        let res = make_tmp_local "ifres" in
        let () = Format.fprintf oc "%s %s;@;if (%s) {@;<1 2>@[" tsym res csym in
        let thsym = create_value toplevel_oc oc locals ir types th in
        let () = Format.fprintf oc "@]%s = %s;@;} else {@;<1 2>@[" res thsym in
        let elsym = create_value toplevel_oc oc locals ir types el in
        let () = Format.fprintf oc "@]%s = %s;@;}@;" res elsym in
        res
  | Seq (Def (id, ex, tex), rest, _) ->
      let texsym = create_type toplevel_oc types tex in
      let loc = make_tmp_local id in
      let exsym = create_value toplevel_oc oc locals ir types ex in
      let () = Format.fprintf oc "%s %s = %s;@;" texsym loc exsym in
      create_value toplevel_oc oc ((id, loc) :: locals) ir types rest
  | Seq (e1, e2, _) ->
      let _ = create_value toplevel_oc oc locals ir types e1 in
      create_value toplevel_oc oc locals ir types e2
  | While (cond, body) ->
      let b = create_type toplevel_oc types Types.bool in
      let cinit = create_value toplevel_oc oc locals ir types cond in
      let cvar = make_tmp_local "loop" in
      let () =
        Format.fprintf oc "%s %s = %s;@;while (%s) {@;<1 2>@[" b cvar cinit cvar
      in
      let bodysym = create_value toplevel_oc oc locals ir types body in
      let () = Format.fprintf oc "%s;@;" bodysym in
      let cnext = create_value toplevel_oc oc locals ir types cond in
      let () = Format.fprintf oc "%s = %s;@]@;}@;" cvar cnext in
      ""
  | Block (body, _) -> create_value toplevel_oc oc locals ir types body
  | Match (expr, patterns, _) ->
      let ety = ir_type expr in
      let esym = create_value toplevel_oc oc locals ir types expr in
      codegen_match toplevel_oc oc locals ir types patterns esym ety
  | Break ->
      Format.fprintf oc "break;@;";
      ""
  | Return v ->
      let vsym = create_value toplevel_oc oc locals ir types v in
      Format.fprintf oc "return (%s);@;" vsym;
      ""

and codegen_match toplevel_oc oc locals ir types patterns esym ety =
  let not_implemented =
    Format.fprintf Format.str_formatter
      "pattern matching is not implemented except for basic option cases.\n%a"
      (Printers.pp_list (Printers.pp_pair (Printers.pp_pattern, Ir.pp_ir)))
      patterns;
    Format.flush_str_formatter ()
  in
  let etsym = create_type toplevel_oc types ety in
  let option_pattern = function
    | Ast.PVariant
        ( ( [
              Types.Typename (([], "$core"), []);
              Types.Typename (([], "Option"), [ t ]);
            ],
            (("Some" | "None") as discrim) ),
          (( Ast.PWildcard
           | Ast.PLit Ast.Literal.Unit
           | Ast.PLit (Ast.Literal.Ident ([], _)) ) as pat) ) ->
        ( Some (t, discrim),
          if discrim = "Some" then
            match pat with
            | Ast.PWildcard -> None
            | Ast.PLit (Ast.Literal.Ident ([], v)) -> Some v
            | _ -> failwith not_implemented
          else if pat = Ast.PLit Ast.Literal.Unit then None
          else failwith not_implemented )
    | Ast.PWildcard -> (None, None)
    | Ast.PLit (Ast.Literal.Ident ([], v)) -> (None, Some v)
    | _ -> failwith not_implemented
  in
  match patterns with
  | [ (pat, body) ] ->
      let dsym, binding = option_pattern pat in
      if dsym = None then
        match binding with
        | None -> create_value toplevel_oc oc locals ir types body
        | Some v ->
            let vsym = make_tmp_local v in
            let () = Format.fprintf oc "%s %s = %s;@;" etsym vsym esym in
            create_value toplevel_oc oc ((v, vsym) :: locals) ir types body
      else failwith not_implemented
  | [ (p1, b1); (p2, b2) ] -> (
      let p1 = option_pattern p1 and p2 = option_pattern p2 in
      match (p1, p2) with
      | (Some (t, "Some"), Some v), (Some (_, "None"), None) ->
          let vsym = make_tmp_local v in
          let gen_res = ir_type b1 <> Types.unit in
          let resym = make_tmp_local "res" in
          let ret_t = create_type toplevel_oc types (ir_type b1) in
          let inner = create_type toplevel_oc types t in
          let () =
            if gen_res then Format.fprintf oc "%s %s /* hello */;@;" ret_t resym
          in
          let () =
            Format.fprintf oc
              "if (%s.discrim == %s_dSome) {@;<1 2>@[%s %s = %s.Some;@;" esym
              etsym inner vsym esym
          in
          let ret =
            create_value toplevel_oc oc ((v, vsym) :: locals) ir types b1
          in
          let () = if gen_res then Format.fprintf oc "%s = %s;" resym ret in
          let () = Format.fprintf oc "@]@;} else {@;<1 2>@[" in
          let ret = create_value toplevel_oc oc locals ir types b2 in
          let () = if gen_res then Format.fprintf oc "%s = %s;" resym ret in
          let () = Format.fprintf oc "@]@;}@;" in
          if gen_res then resym else ""
      | _ -> failwith not_implemented)
  | _ -> failwith not_implemented

let gen oc ir types =
  let () = sanity_check ir in

  let main_obj, params, ret =
    match List.hd ir with
    | ( (([ Types.Typename (([], _), []) ], "main") as it),
        (Function (params, ret, _) as obj) ) ->
        ((it, obj), params, ret)
    | _ ->
        failwith
          "No entry point detected! The last definition must be a function \
           called `main`."
  in
  let params_t = List.map snd params in
  let main_t = Types.Function (params_t, ret) in

  if Typecheck.has_free_vars [] main_t then
    failwith "The entry point must have a concrete type."
  else if ret <> Types.unit && Types.is_int ret then
    failwith "The entry point must return either () or an integer."
  else if params_t <> [] then failwith "The entry point cannot take parameters.";

  create_obj oc ir types main_obj
