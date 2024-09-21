%{
  open Ast

  exception DuplicateTypeVar of string
  exception DuplicateVariant of string
  exception DuplicateField of string

  let rec ensure_unicity (e: 'a -> exn) = function
    | [] -> ()
    | (a, _) :: q -> if List.mem_assoc a q then raise (e a) else ensure_unicity e q

  let rec lvalue_of_expr = function
    | Lit (Literal.Ident ([], id)) -> LIdent id
    | TupleAccess (e, i) -> LTupleAccess (lvalue_of_expr e, i)
    | FieldAccess (e, id) -> LFieldAccess (lvalue_of_expr e, id)
    | Index (e1, e2) -> LIndex (lvalue_of_expr e1, e2)
    | _ -> failwith "invalid lvalue"

  let type_with_vars vars ty =
    let () = ensure_unicity (fun v -> DuplicateTypeVar v) vars in
    let rec use_var x ty =
        match ty with
        | Types.Array t -> Types.Array (use_var x t)
        | Types.Tuple lst -> Types.Tuple (List.map (use_var x) lst)
        | Types.Function (args, ret) -> 
            Types.Function (List.map (use_var x) args, use_var x ret)
        | Types.Typename (([], t), []) -> if (fst x) = t then snd x else ty
        | Types.Typename ((path, name), v) ->
            Types.Typename((List.map (use_var x) path, name), List.map (use_var x) v)
        | Types.Var _ -> ty
        | _ -> ty
    in
    List.fold_left (fun t x -> use_var x t) ty vars
  
  let type_expr_with_vars vars = function
    | Types.Sum variants -> Types.Sum 
        (List.map
        (fun (name, ty) -> name, type_with_vars vars ty)
        variants)
    | Types.Struct fields -> Types.Struct
        (List.map
        (fun (name, ty) -> name, type_with_vars vars ty)
        fields)
    | Types.Alias ty -> Types.Alias (type_with_vars vars ty)
    | Types.Extern symbol -> Types.Extern symbol

  let expr_with_vars vars = let f = function
    | Def (id, ty, expr) -> Def (id, type_with_vars vars ty, expr)
    | e -> e
    in transform_expr f

  let rec toplevel_with_vars vars = function
    | Const { const_name; ty; expr } -> Const {
        const_name;
        ty = type_with_vars vars ty;
        expr = expr_with_vars vars expr
    }
    | Function (vars', { fun_name; params; ret; body }) -> Function (vars', {
        fun_name;
        params = List.map (fun (name, ty) -> name, type_with_vars vars ty) params;
        ret = type_with_vars vars ret;
        body = expr_with_vars vars body
    })
    | Typedef (type_name, (vars', def)) -> Typedef (type_name, (vars', type_expr_with_vars vars def))
    | Implementation (vars', ty, lst) -> Implementation (
        vars',
        type_with_vars vars ty,
        List.map (toplevel_with_vars vars) lst
      )
    | Use (path, id) -> Use (List.map (type_with_vars vars) path, id)
    | ExternDef { val_name; ty; symbol } -> ExternDef { val_name; ty = type_with_vars vars ty; symbol }

  let put_at_root ty = function
    | Types.Typename ((path, name), args) -> Types.Typename ((ty :: path, name), args)
    | _ -> failwith "cannot put at root of builtin type"

  let make_float (f, ty) =
    let t = match ty with
      | "f32" -> Types.f32
      | "f64" -> Types.f64
      | _ -> Types.varfloat ()
    in Literal.Float (f, t)
   
  let make_int (i, ty) =
    if String.length ty <> 0 && ty.[0] = 'u' && i < 0L then
      failwith ("Invalid int literal: negative integer with unsigned type " ^ ty)
    else
    let t = match ty with
      | "i8" -> Types.i8
      | "u8" -> Types.u8
      | "i16" -> Types.i16
      | "u16" -> Types.u16
      | "i32" -> Types.i32
      | "u32" -> Types.u32
      | "i64" -> Types.i64
      | "u64" -> Types.u64
      | "isize" -> Types.isize
      | "usize" -> Types.usize
      | _ -> Types.varint ()
    in Literal.Int (i, t)
%}

%token Eof
%token <int64> Int
%token <int64 * string> IntSuffix
%token <float> Float
%token <float * string> FloatSuffix
%token True False
%token <Ast.ident> Ident
%token <string> String
%token Equal Arrow Wildcard DotDot DotDotEq
%token While For In Let Const Use Fn Impl If Else Match Amp Pipe Return Break
%token Type Struct Enum Extern
%token SelfT Self
%token Bang Plus
%token Minus Star Slash Modulo
%token EqualEqual NotEqual Greater Smaller GreaterEqual SmallerEqual
%token AmpAmp PipePipe
%token Lpar Rpar Begin End Lbracket Rbracket Semi Colon Comma Dot ColCol

%nonassoc Equal
%left PipePipe
%left AmpAmp
%nonassoc EqualEqual NotEqual Greater Smaller GreaterEqual SmallerEqual
%left Plus Minus
%left Star Slash Modulo
%nonassoc Uminus Bang

%nonassoc Tupleized

%start program
%type <Ast.program> program

%type <Ast.item> item
%type <Ast.program> toplevel_list
%type <Ast.toplevel> toplevel
%type <Ast.ty> return_type
%type <Ast.ident list> type_vars 
%type <Ast.ident list> ident_list
%type <Ast.ty> type_expr
%type <Ast.ty list> type_list
%type <Ast.ty> type_item
%type <Ast.ty> type_path_part

%type <Ast.item list> use_item

%%

program:
| toplevel_list Eof { $1 }
;

toplevel_list:
| /* empty */ { [] }
| Use items = use_item Semi rest = toplevel_list { List.map (fun t -> Ast.Use t) items @ rest }
| toplevel toplevel_list { $1 :: $2 }
;

%inline toplevel:
| Const const_name = Ident Colon ty = type_item Equal expr = expr Semi {
    Ast.Const { const_name; ty; expr }
  }
| Fn fun_name = Ident vars = type_vars Lpar params = function_params Rpar ret = return_type Begin body = body End {
    let vars' = List.map Types.new_type vars in
    let cvars = List.map2 (fun a b -> a, b) vars vars' in
    Ast.Function (List.map Types.get_var_string vars', {
      fun_name;
      params = List.map (fun (name, ty) -> name, type_with_vars cvars ty) params;
      ret = type_with_vars cvars ret;
      body = expr_with_vars cvars body
    })
  }
| Struct type_name = Ident vars = type_vars Begin def = typed_idents End {
    let vars' = List.map Types.new_type vars in
    let cvars = List.map2 (fun a b -> a, b) vars vars' in
    let () = ensure_unicity (fun n -> DuplicateField n) def in
    Ast.Typedef (type_name, (List.map Types.get_var_string vars', type_expr_with_vars cvars (Types.Struct def)))
  }
| Enum type_name = Ident vars = type_vars Begin def = variants End {
    let vars' = List.map Types.new_type vars in
    let cvars = List.map2 (fun a b -> a, b) vars vars' in
    let () = ensure_unicity (fun n -> DuplicateVariant n) def in
    Ast.Typedef (type_name, (List.map Types.get_var_string vars', type_expr_with_vars cvars (Types.Sum def)))
  }
| Type type_name = Ident vars = type_vars Equal def = type_item Semi {
    let vars' = List.map Types.new_type vars in
    let cvars = List.map2 (fun a b -> a, b) vars vars' in
    Ast.Typedef (type_name, (List.map Types.get_var_string vars', type_expr_with_vars cvars (Types.Alias def)))
  }
| Impl vars = type_vars ty = type_expr Begin items = toplevel_list End {
    let vars' = List.map Types.new_type vars in
    let cvars = List.map2 (fun a b -> a, b) vars vars' in
    Ast.Implementation (
      List.map Types.get_var_string vars',
      type_with_vars cvars ty,
      List.map (toplevel_with_vars cvars) items
    )
  }
| Extern val_name = Ident Colon ty = type_item Equal symbol = String Semi {
    Ast.ExternDef { val_name; ty; symbol }
  }
| Extern Type type_name = Ident vars = type_vars Equal symbol = String Semi {
    Ast.Typedef (type_name, (List.map (Utils.unique_string) vars, Types.Extern symbol))
  }
;

return_type:
| /* empty */ { Types.unit }
| Arrow ty = type_item { ty }
;

type_vars:
| /* empty */ { [] }
| Smaller ident_list Greater { $2 }
;

ident_list:
| Ident Comma? { [ $1 ] }
| Ident Comma ident_list { $1 :: $3 }
;

function_params:
| /* empty */ { [] }
| Self pair(Colon, SelfT)? rest = loption(preceded(Comma, typed_idents)) { (Types.self, Types.self_type) :: rest }
| name = Ident Colon ty = type_item rest = loption(preceded(Comma, typed_idents)) { (name, ty) :: rest }
;

typed_idents:
| /* empty */ { [] }
| Ident Colon type_item { [ $1, $3 ] }
| Ident Colon type_item Comma typed_idents { ($1, $3) :: $5 }
;

typename:
| Ident { Types.Typename (([], $1), []) }
| Ident Smaller type_list Greater { Types.Typename (([], $1), $3) }
;

type_expr:
| Wildcard { Types.new_type "" }
| SelfT { Types.self_type }
| Lbracket type_item Rbracket { Types.Array $2 }
| Lpar type_list Rpar %prec Tupleized {
    match $2 with
    | [] -> Types.unit 
    | [ t ] -> t
    | _ -> Types.Tuple $2
  }
| Fn Lpar args = type_list Rpar Arrow ret = type_item { Types.Function (args, ret) }
| typename { $1 }
;

type_list:
| /* empty */ { [] }
| type_item rest = loption(preceded(Comma, type_list)) { $1 :: rest }
;

type_item_helper:
| ty = typename { ty }
| ty = typename ColCol it = type_item_helper { put_at_root ty it }
;

type_item:
| ty = type_expr ColCol it = type_item_helper { put_at_root ty it }
| ty = type_expr { ty }
;

variants:
| variant { [ $1 ] }
| variant Comma variants { $1 :: $3 }
;

variant:
| Ident { ($1, Types.unit) }
| Ident Lpar Rpar { ($1, Types.unit) }
| Ident Lpar type_item Rpar { ($1, $3) }
| Ident Lpar type_list Rpar { ($1, Types.Tuple $3) }
;

body:
| /* empty */ { const_unit }
| statements { $1 }
;

statements:
| statement { $1 }
| statement statements { Seq ($1, $2) }
| expr { $1 }
| expr Semi { Seq($1, const_unit) }
| expr Semi statements { Seq ($1, $3) }
;

statement:
| Return expr Semi? { Ast.Return $2 }
| Break Semi? { Ast.Break }
| While cond = expr Begin body = body End { Ast.While { cond; body } }
| For var = Ident In range = expr Begin body = body End /* { /* Ast.For { var; range; body } } */ {
    let tmp_range = tmp_var () in
    let tmp_iter = tmp_var () in
    let tmp_cond = tmp_var () in
    let tmp_var = tmp_var () in
    let iter_t = Types.new_type "it" in
    let option_t = Types.core_type ~vars:[iter_t] "Option" in
    let range_id = const_ident tmp_range
    and iter_id = const_ident tmp_iter
    and cond_id = const_ident tmp_cond
    and var_id = const_ident tmp_var in
    Block (make_seq [
        Def (tmp_range, Types.new_type "", MethodCall (range, "iter", []));
        Def (tmp_cond, Types.bool, const_bool true);
        Ast.While {
            cond = cond_id;
            body = Seq (
                Def (tmp_iter, option_t, MethodCall (range_id, "next", [])),
                Ast.Match ( iter_id, [
                    PVariant ((Types.item_of_type option_t "Some"), PLit (Literal.Ident ([], tmp_var))),
                        Block(Seq(Def (var, iter_t, var_id), body));
                    PLit (Literal.Ident (Types.item_of_type option_t "None")),
                        Block(Assign (LIdent tmp_cond, const_bool false));
                ])
            )
        }
    ])
  }
| For var = Ident In
  startval = expr cmp = midrule(DotDot { Lt } | DotDotEq { Le }) endval = expr
  Begin body = body End {
    let tmp_iter = tmp_var () and iter_t = Types.usize in
    let tmp_end = tmp_var () in
    let iter_id = const_ident tmp_iter and end_id = const_ident tmp_end in
    Block (make_seq [
      Def (tmp_iter, iter_t, startval);
      Def (tmp_end, iter_t, endval);
      Ast.While {
        cond = Binop (cmp, iter_id, end_id);
        body = Seq (
          Seq (Def (var, iter_t, iter_id), body),
          Assign (LIdent tmp_iter, Binop (Add, iter_id, const_int 1L))
        )
      }
    ])
  }
| Let id = Ident ty = type_annotation Equal expr = expr Semi { Def (id, ty, expr) }
| expr Equal expr Semi { Assign (lvalue_of_expr $1, $3) }
;

type_annotation:
| /* empty */ { Types.new_type "" }
| Colon type_item { $2 }
;

expr:
| Begin End { Ast.Struct ([]) }
| Begin f = Ident Colon e = expr rest = loption(preceded(Comma, named_exprs)) End { Ast.Struct ((f,e) :: rest) }
| Begin Ident body End { Block (Seq (const_ident $2, $3)) }
| Begin statements End { Block $2 }
| If expr Begin body End Else Begin body End {
    Ast.If { cond = $2; then_branch = $4; else_branch = $8 }
  }
| If expr Begin body End { Ast.If { cond = $2; then_branch = $4; else_branch = const_unit } }
| Match arith_expr Begin match_cases End { Ast.Match ($2, $4) }
| arith_expr { $1 }
;

named_exprs:
| /* empty */ { [] }
| field = Ident Colon value = expr { [ field, value ] }
| field = Ident Colon value = expr Comma rest = named_exprs { (field, value) :: rest }
;

%inline match_cases:
| /* empty */ { [] }
| pat = pattern Arrow e = expr rest = loption(preceded(Comma, match_cases)) { (List.map (fun p -> (p, e)) pat) @ rest }
;

pattern:
| pattern_base loption(preceded(Pipe, pattern)) { $1 @ $2 }
;

pattern_base:
| Wildcard { [ PWildcard ] }
| literal { [ PLit $1 ] }
| literal DotDot literal { [ PRange ($1, $3) ] }
| literal DotDotEq literal { [ PRangeInclusive ($1, $3) ] }
| Lpar pattern Rpar { $2 }
| Lpar pattern_base Comma pattern_list Rpar {
    List.flatten (List.map (fun first -> List.map (fun rest -> PTuple (first :: rest)) $4) $2)
  }
| Lbracket pattern_list Rbracket { List.map (fun p -> PArray p) $2 }
| cons = item Lpar args = pattern_list Rpar {
    List.map
    (fun arg -> match arg with
      | [] -> PLit (Literal.Ident cons)
      | [ty] -> PVariant (cons, ty)
      | lst -> PVariant(cons, PTuple lst))
    args
  }
| Begin named_patterns End { List.map (fun p -> PStruct p) $2 }
;

named_patterns:
| /* empty */ { [] }
| Ident Colon pattern_base { List.map (fun p -> [ $1, p ]) $3 }
| id = Ident Colon pat = pattern_base Comma rest = named_patterns {
    List.flatten (List.map (fun first -> List.map (fun rest -> (id, first) :: rest) rest) pat)
  }
;

pattern_list:
| /* empty */ { [] }
| pattern_base { [ $1 ] }
| pattern_base Comma pattern_list { $1 :: $3 }
;

arith_expr:
| expr Plus expr { Binop (Add, $1, $3) }
| expr Minus expr { Binop (Sub, $1, $3) }
| expr Star expr { Binop (Mul, $1, $3) }
| expr Slash expr { Binop (Div, $1, $3) }
| expr Modulo expr { Binop (Mod, $1, $3) }
| expr EqualEqual expr { Binop (Eq, $1, $3) }
| expr NotEqual expr { Binop (Ne, $1, $3) }
| expr Greater expr { Binop (Gt, $1, $3) }
| expr GreaterEqual expr { Binop (Ge, $1, $3) }
| expr Smaller expr { Binop (Lt, $1, $3) }
| expr SmallerEqual expr { Binop (Le, $1, $3) }
| expr AmpAmp expr { Binop (And, $1, $3) }
| expr PipePipe expr { Binop (Or, $1, $3) }
| Minus expr %prec Uminus { Monop (Neg, $2) }
| Bang expr { Monop (Not, $2) }
| atom { $1 }
;

atom:
| Lpar expr Rpar { $2 }
| Lpar expr Comma expr_list Rpar { Tuple ($2 :: $4) }
| Lbracket expr_list Rbracket { Array $2 }
| atom Dot Int { TupleAccess ($1, Int64.to_int $3) }
| atom Dot Ident { FieldAccess ($1, $3) }
| atom Dot Ident Lpar expr_list Rpar { MethodCall ($1, $3, $5) }
| atom Lpar expr_list Rpar  { Call ($1, $3) }
| atom Lbracket expr Rbracket { Index ($1, $3) }
| literal { Lit $1 }
;

expr_list:
| /* empty */ { [] }
| expr { [ $1 ] }
| expr Comma expr_list { $1 :: $3 }
;

literal:
| Int { make_int ($1, "") }
| IntSuffix { make_int $1 }
| True { Literal.Bool true }
| False { Literal.Bool false }
| Lpar Rpar { Literal.Unit }
| String { Literal.String $1 }
| Float { make_float ($1, "") }
| FloatSuffix { make_float $1 }
| Self { Literal.Ident ([], Types.self) }
| Minus Int { make_int (Int64.neg $2, "") }
| Minus IntSuffix { make_int (Int64.neg (fst $2), snd $2) }
| Minus Float { make_float (-. $2, "") }
| Minus FloatSuffix { make_float (-. (fst $2), snd $2) }
| item { Literal.Ident $1 }
;

item:
| id = Ident { ([], id) }
| ty = Ident ColCol it = item {
    let (path, id) = it in ((Types.Typename (([], ty), [])) :: path, id)
  }
| ty = Ident ColCol Smaller vars = type_list Greater ColCol it = item {
    let (path, id) = it in ((Types.Typename (([], ty), vars)) :: path, id)
  }
| ty = type_path_part ColCol it = item { let (path, id) = it in ((ty :: path), id) }
;

type_path_part:
| Smaller Lpar Rpar Greater { Types.unit }
| SelfT { Types.self_type }
| Smaller Lbracket ty = type_item Rbracket Greater { Types.Array ty }
| Smaller Lpar comps = type_list Rpar Greater { Types.Tuple comps }
| Smaller Fn Lpar args = type_list Rpar Arrow ret = type_item Greater { Types.Function (args, ret) }
;

use_item:
| Begin lst = separated_nonempty_list(Comma, use_item) End { List.flatten lst }
| id = Ident { [ ([], id) ] }
| ty = Ident ColCol it = use_item {
    List.map (fun (path, id) -> (Types.Typename (([], ty), [])) :: path, id) it
  }
| ty = Ident ColCol Smaller vars = type_list Greater ColCol it = use_item {
    List.map (fun (path, id) -> (Types.Typename (([], ty), vars)) :: path, id) it
  }
| ty = type_path_part ColCol it = use_item {
     List.map (fun (path, id) -> (ty :: path), id) it
  }
;
