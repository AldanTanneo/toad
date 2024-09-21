let todo () = failwith "TODO"

let pp_token oc tok =
  Parser.(
    Format.fprintf oc "%s"
      (match tok with
      | Eof -> "Eof"
      | Int n -> Int64.to_string n
      | IntSuffix (n, ty) -> Int64.to_string n ^ ty
      | Float f -> string_of_float f
      | FloatSuffix (f, ty) -> string_of_float f ^ ty
      | True -> "true"
      | False -> "false"
      | Ident id -> id
      | String s -> Format.sprintf "%S" s
      | Equal -> "="
      | Arrow -> "->"
      | Wildcard -> "_"
      | While -> "while"
      | For -> "for"
      | In -> "in"
      | Let -> "let"
      | Const -> "const"
      | Fn -> "fn"
      | Impl -> "impl"
      | Use -> "use"
      | Extern -> "extern"
      | If -> "if"
      | Else -> "else"
      | Match -> "match"
      | Amp -> "&"
      | Pipe -> "|"
      | Return -> "return"
      | Break -> "break"
      | Type -> "type"
      | Struct -> "struct"
      | Enum -> "enum"
      | SelfT -> "Self"
      | Self -> "self"
      | Bang -> "!"
      | Plus -> "+"
      | Minus -> "-"
      | Star -> "*"
      | Slash -> "/"
      | Modulo -> "%"
      | EqualEqual -> "=="
      | NotEqual -> "!="
      | Greater -> ">"
      | Smaller -> "<"
      | GreaterEqual -> ">="
      | SmallerEqual -> "<="
      | AmpAmp -> "&&"
      | PipePipe -> "||"
      | Lpar -> "("
      | Rpar -> ")"
      | Begin -> "{"
      | End -> "}"
      | Lbracket -> "["
      | Rbracket -> "]"
      | Semi -> ";"
      | Colon -> ":"
      | Comma -> ","
      | Dot -> "."
      | DotDot -> ".."
      | DotDotEq -> "..="
      | ColCol -> "::"))

let pp_sep sep pp =
  let rec f oc =
    Format.(
      function
      | [] -> ()
      | [ a ] -> fprintf oc "%a" pp a
      | a :: q -> fprintf oc "%a%a%a" pp a sep () f q)
  in
  f

let pp_comma_sep pp = pp_sep (fun oc () -> Format.fprintf oc ", ") pp

let pp_list pp oc lst =
  Format.(
    let rec f oc = function
      | [] -> ()
      | [ a ] -> fprintf oc "%a" pp a
      | a :: q -> fprintf oc "%a;@;%a" pp a f q
    in
    fprintf oc "@[<1>[%a]@]" f lst)

let pp_pair (ppa, ppb) oc =
  Format.(fun (a, b) -> fprintf oc "@[(%a,@;<1 1>%a)@]" ppa a ppb b)

let pp_tyvar oc x = Format.fprintf oc "'%s" x (*Utils.reverse_unique x*)

let rec pp_path oc =
  Format.(
    function
    | [] -> ()
    | [ root ] ->
        if root = Types.root_ns then pp_print_string oc "root"
        else if root = Types.core_ns then pp_print_string oc "core"
        else fprintf oc "%a" pp_type root
    | root :: path ->
        if root = Types.root_ns then fprintf oc "root::%a" pp_path path
        else if root = Types.core_ns then fprintf oc "core::%a" pp_path path
        else fprintf oc "%a::%a" pp_type root pp_path path)

and pp_item oc item =
  Format.(
    let pp oc = function
      | [], id -> fprintf oc "%s" id
      | path, id -> fprintf oc "%a::%s" pp_path path id
    in
    fprintf oc "@[<h>%a@]" pp item)

and pp_type oc =
  Format.(
    function
    | Types.Array ty -> fprintf oc "[%a]" pp_type ty
    | Types.Tuple [ ty ] -> fprintf oc "(%a,)" pp_type ty
    | Types.Tuple lst -> fprintf oc "(%a)" (pp_comma_sep pp_type) lst
    | Types.Function (args, ret) ->
        fprintf oc "<fn(%a) -> %a>" (pp_comma_sep pp_type) args pp_type ret
    | Types.Typename (name, []) -> fprintf oc "%a" pp_item name
    | Types.Typename (name, lst) ->
        fprintf oc "%a<%a>" pp_item name (pp_comma_sep pp_type) lst
    | Types.Var x -> fprintf oc "%a" pp_tyvar x
    | Types.VarInt x -> fprintf oc "{%s}" x
    | Types.VarFloat x -> fprintf oc "{%s}" x)

let pp_lit oc =
  Format.(
    Ast.(
      function
      | Literal.Unit -> pp_print_string oc "()"
      | Literal.Bool b -> fprintf oc "%b" b
      | Literal.Int (n, ty) ->
          fprintf oc "%s%a" (Int64.to_string n)
            (fun oc t ->
              if Types.is_varint t then () else fprintf oc "%a" pp_type ty)
            ty
      | Literal.Float (f, ty) ->
          fprintf oc "%s%a"
            (let x = Format.sprintf "%F" f in
             if String.ends_with ~suffix:"." x then x ^ "0" else x)
            (fun oc t ->
              if Types.is_varfloat t then () else fprintf oc "%a" pp_type ty)
            ty
      | Literal.String s -> fprintf oc "%S" s
      | Literal.Ident id -> fprintf oc "%a" pp_item id))

let pp_binop oc op =
  Format.pp_print_string oc
    Ast.(
      match op with
      | Add -> "+"
      | Sub -> "-"
      | Mul -> "*"
      | Div -> "/"
      | Mod -> "%%"
      | Eq -> "=="
      | Ne -> "!="
      | Gt -> ">"
      | Ge -> ">="
      | Lt -> "<"
      | Le -> "<="
      | And -> "&&"
      | Or -> "||")

let pp_monop oc =
  Format.(Ast.(function Not -> fprintf oc "!" | Neg -> fprintf oc "-"))

let rec pp_pattern oc =
  Format.(
    function
    | Ast.PWildcard -> fprintf oc "_"
    | Ast.PLit lit -> fprintf oc "%a" pp_lit lit
    | Ast.PRange (s, e) -> fprintf oc "%a..%a" pp_lit s pp_lit e
    | Ast.PRangeInclusive (s, e) -> fprintf oc "%a..=%a" pp_lit s pp_lit e
    | Ast.PStruct lst ->
        fprintf oc "{%a}"
          (pp_comma_sep (fun oc (id, e) -> fprintf oc "%s: %a" id pp_pattern e))
          lst
    | Ast.PTuple lst ->
        fprintf oc "(%a)"
          (pp_sep (fun oc () -> fprintf oc ",@;<1 1>") pp_pattern)
          lst
    | Ast.PArray lst -> fprintf oc "[%a]" (pp_comma_sep pp_pattern) lst
    | Ast.PVariant (name, pat) ->
        fprintf oc "@[%a(%a)@]" pp_item name pp_pattern pat)

let rec pp_lvalue oc =
  Format.(
    function
    | Ast.LIdent id -> fprintf oc "%s" id
    | Ast.LTupleAccess (lval, idx) -> fprintf oc "%a.%d" pp_lvalue lval idx
    | Ast.LFieldAccess (lval, field) -> fprintf oc "%a.%s" pp_lvalue lval field
    | Ast.LIndex (lval, expr) -> fprintf oc "%a[%a]" pp_lvalue lval pp_expr expr)

and pp_expr oc =
  Format.(
    function
    | Ast.Lit lit -> pp_lit oc lit
    | Ast.Array lst -> fprintf oc "[%a]" (pp_comma_sep pp_expr) lst
    | Ast.Repeat (expr, len) -> fprintf oc "[%a; %a]" pp_expr expr pp_expr len
    | Ast.Tuple lst -> fprintf oc "(%a,)" (pp_comma_sep pp_expr) lst
    | Ast.Struct lst ->
        fprintf oc "{@;<1 2>@[<hv>%a@]@;}@]"
          (pp_sep
             (fun oc () -> fprintf oc ",@;")
             (fun oc (id, e) -> fprintf oc "%s: %a" id pp_expr e))
          lst
    | Ast.TupleAccess (e, i) -> fprintf oc "(%a.%d)" pp_expr e i
    | Ast.FieldAccess (e, id) -> fprintf oc "(%a.%s)" pp_expr e id
    | Ast.Index (e, i) -> fprintf oc "%a[%a]" pp_expr e pp_expr i
    | Ast.Def (name, ty, e) ->
        fprintf oc "@[let %s: %a = %a;@]" name pp_type ty pp_expr e
    | Ast.Assign (lhs, rhs) -> fprintf oc "%a = %a;" pp_lvalue lhs pp_expr rhs
    | Ast.MethodCall (expr, f, args) ->
        fprintf oc "@[%a@;<0 2>.%s(%a)@]" pp_expr expr f (pp_comma_sep pp_expr)
          args
    | Ast.Call (f, args) ->
        fprintf oc "@[%a(%a)@]" pp_expr f (pp_comma_sep pp_expr) args
    | Ast.Binop (op, lhs, rhs) ->
        fprintf oc "(%a %a %a)" pp_expr lhs pp_binop op pp_expr rhs
    | Ast.Monop (op, e) -> fprintf oc "(%a %a)" pp_monop op pp_expr e
    | Ast.If { cond; then_branch; else_branch } ->
        fprintf oc "@[<v>if @[%a@] {@;<1 2>@[%a@]@;} else {@;<1 2>@[%a@]@;}@]"
          pp_expr cond pp_expr then_branch pp_expr else_branch
    | Ast.While { cond; body } ->
        fprintf oc "@[<v>while @[%a@] {@;<1 2>@[%a@]@;}@]" pp_expr cond pp_expr
          body
    | Ast.Match (e, lst) ->
        fprintf oc "@[<v>match @[%a@] {@;<1 2>%a@;}@]" pp_expr e
          (pp_sep
             (fun oc () -> fprintf oc ",@;<1 2>")
             (fun oc (pat, e) ->
               fprintf oc "@[<v 2>%a -> @[%a@]@]" pp_pattern pat pp_expr e))
          lst
    | Ast.Seq (e1, e2) -> fprintf oc "@[<v>%a@;%a@]" pp_expr e1 pp_expr e2
    | Ast.Block e -> fprintf oc "{@;<1 2>%a@;}" pp_expr e
    | Ast.Return e -> fprintf oc "@[return %a;@]" pp_expr e
    | Ast.Break -> ())

let pp_type_vars oc = function
  | [] -> ()
  | vars -> Format.fprintf oc "<%a>" (pp_comma_sep pp_tyvar) vars

let pp_typedef oc =
  Format.(
    function
    | name, (vars, Types.Alias ty) ->
        fprintf oc "type %s%a = @[%a@]" name pp_type_vars vars pp_type ty
    | name, (vars, Types.Sum lst) ->
        fprintf oc "enum %s%a @[{@;<1 2>@[%a@]@;}@]" name pp_type_vars vars
          (pp_sep
             (fun oc () -> fprintf oc ",@;")
             (fun oc variant ->
               match variant with
               | name, ty -> fprintf oc "%s(%a)" name pp_type ty))
          lst
    | name, (vars, Types.Struct lst) ->
        fprintf oc "struct %s%a @[{@;<1 2>@[%a@]@;}@]" name pp_type_vars vars
          (pp_sep
             (fun oc () -> fprintf oc ",@;")
             (fun oc (name, ty) -> fprintf oc "%s: %a" name pp_type ty))
          lst
    | name, (_, Types.Extern symbol) ->
        fprintf oc "extern type %s = %S" name symbol)

let rec pp_toplevel oc =
  Format.(
    function
    | Ast.Const { const_name; ty; expr } ->
        fprintf oc "@[const %s: %a = %a@]" const_name pp_type ty pp_expr expr
    | Ast.Function (vars, { fun_name; params; ret; body }) ->
        fprintf oc "@[fn %s%a(%a) -> %a {@;<1 2>@[%a@]@;}@]" fun_name
          pp_type_vars vars
          (pp_comma_sep (fun oc (id, ty) -> fprintf oc "%s: %a" id pp_type ty))
          params pp_type ret pp_expr body
    | Ast.Typedef (name, def) -> fprintf oc "%a" pp_typedef (name, def)
    | Ast.Implementation (vars, ty, lst) ->
        fprintf oc "@[impl%a %a {@;<1 2>@[<v>%a@]@;}@]" pp_type_vars vars
          pp_type ty
          (Format.pp_print_list
             ~pp_sep:(fun oc () -> fprintf oc "@;")
             (fun oc tl ->
               open_box 0;
               fprintf oc "%a" pp_toplevel tl;
               close_box ()))
          lst
    | Ast.Use it -> fprintf oc "@[use %a@]" pp_item it
    | Ast.ExternDef { val_name; ty; symbol } ->
        fprintf oc "@[extern %s: %a = %S@]" val_name pp_type ty symbol)

let pp_program oc : Ast.program -> unit =
  List.iter (fun ast -> Format.fprintf oc "@[%a@]@?\n%!" pp_toplevel ast)

let pp_schema oc (vars, ty) =
  Format.fprintf oc "@[(@[%a@],@;%a)@]" (pp_list pp_tyvar) vars pp_type ty

let rec pp_env ppa ppb oc { Types.Env.bindings; types; ns } =
  Format.(
    fprintf oc
      "@[{@;\
       <1 2>bindings = @[%a@];@;\
       <1 2>types = @[%a@];@;\
       <1 2>ns = @[%a@]@;\
       <1 0>}@]"
      (pp_list (fun oc (name, a) -> fprintf oc "@[(%s,@;<1 1>%a)@]" name ppa a))
      bindings
      (pp_list (fun oc (name, b) -> fprintf oc "@[(%s,@;<1 1>%a)@]" name ppb b))
      types
      (pp_list (fun oc (ty, e) ->
           fprintf oc "@[(@[%a@],@;<1 1>%a)@]" pp_type ty (pp_namespace ppa ppb)
             e))
      ns)

and pp_namespace ppa ppb oc =
  Format.(
    function
    | Types.Env.Redirect ty -> fprintf oc "@ %a" pp_type ty
    | Types.Env.Ref env -> fprintf oc "%a" (pp_env ppa ppb) !env)

let pp_canonical_env = pp_env pp_path pp_schema

let pp_anon_typedef oc =
  Format.(
    function
    | Types.Alias t -> fprintf oc "Alias(%a)" pp_type t
    | Types.Struct lst ->
        fprintf oc "struct @[{@;<1 2>@[<v>%a@]@;}@]"
          (pp_sep
             (fun oc () -> fprintf oc ",@;")
             (fun oc (name, ty) -> fprintf oc "%s: %a" name pp_type ty))
          lst
    | Types.Sum lst ->
        fprintf oc "enum @[{@;<1 2>@[<v>%a@]@;}@]"
          (pp_sep
             (fun oc () -> fprintf oc ",@;")
             (fun oc variant ->
               match variant with
               | name, ty -> fprintf oc "%s(%a)" name pp_type ty))
          lst
    | Types.Extern symbol -> fprintf oc "extern %S" symbol)

let pp_typing_env = pp_env pp_schema (pp_pair (pp_schema, pp_anon_typedef))
let pp_subst = pp_list (pp_pair (pp_tyvar, pp_type))

let pp_c_string oc s =
  let () = Format.pp_print_string oc "\"" in
  let () =
    String.iter
      (fun c ->
        match c with
        | '"' -> Format.pp_print_string oc "\\\""
        | '\\' -> Format.pp_print_string oc "\\\\"
        | ' ' .. '~' -> Format.pp_print_char oc c
        | _ -> Format.fprintf oc "\\x%02x" (Char.code c))
      s
  in
  Format.pp_print_string oc "\""
