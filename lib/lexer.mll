{
  open Parser
  exception Eoi

  let pc c = Printf.eprintf "Lu '%c'\n%!" c;;
  let ps c = Printf.eprintf "Lu '%s'\n%!" c;;

  (* Emprunté de l'analyseur lexical du compilateur OCaml *)
  (* To buffer string literals *)
  let initial_string_buffer = Bytes.create 256;;
  let string_buff = ref initial_string_buffer;;
  let string_index = ref 0;;

  let reset_string_buffer () =
    string_buff := initial_string_buffer;
    string_index := 0;;

  let store_string_char c =
    if !string_index >= Bytes.length (!string_buff) then begin
      let new_buff = Bytes.create (Bytes.length (!string_buff) * 2) in
      Bytes.blit (!string_buff) 0 new_buff 0 (Bytes.length (!string_buff));
      string_buff := new_buff
    end;
    Bytes.unsafe_set (!string_buff) (!string_index) c;
    incr string_index;;

  let get_stored_string () =
    let s = Bytes.to_string (Bytes.sub (!string_buff) 0 (!string_index)) in
    string_buff := initial_string_buffer;
    s;;

  (* To translate escape sequences *)
  let char_for_backslash c = match c with
  | 'n' -> '\n'
  | 'r' -> '\r'
  | 'b' -> '\b'
  | 't' -> '\t'
  | c   -> c

  let char_for_decimal_code lexbuf i =
    let c = 100 * (Char.code(Lexing.lexeme_char lexbuf i) - 48) +
             10 * (Char.code(Lexing.lexeme_char lexbuf (i+1)) - 48) +
                  (Char.code(Lexing.lexeme_char lexbuf (i+2)) - 48) in
    if (c < 0 || c > 255)
    then raise (Failure ("Illegal_escape: " ^ (Lexing.lexeme lexbuf)))
    else Char.chr c;;

  let char_for_hexadecimal_code lexbuf i =
    let d1 = Char.code (Lexing.lexeme_char lexbuf i) in
    let val1 = if d1 >= 97 then d1 - 87
               else if d1 >= 65 then d1 - 55
               else d1 - 48
    in
    let d2 = Char.code (Lexing.lexeme_char lexbuf (i+1)) in
    let val2 = if d2 >= 97 then d2 - 87
               else if d2 >= 65 then d2 - 55
               else d2 - 48
    in
    Char.chr (val1 * 16 + val2);;

  let string_start = ref Lexing.dummy_pos

  exception LexError of (string * Lexing.position * Lexing.position);;
  let report_error msg lexbuf = raise (LexError (
    msg, lexbuf.Lexing.lex_start_p,
    lexbuf.Lexing.lex_curr_p))
}

let newline = '\n' | '\r' | "\r\n"
let whitespace = ' ' | '\t' | newline

let decimal = ['0'-'9' '_']
let hex = ['0'-'9' 'a'-'f' 'A'-'F' '_']
let oct = ['0'-'7' '_']
let bin = ['0' '1' '_']
let int = ((['1'-'9'] decimal*) | '0')
          | ("0x" ['0'-'9' 'a'-'f' 'A'-'F'] hex*)
          | ("0o" ['0'-'7'] oct*)
          | ("0b" ['0' '1'] bin*)

let float = ((['1'-'9'] decimal*) | '0') ('.' decimal+)? ('e' ['+' '-']? decimal+)?

let isuffix = ("i8" | "u8" | "i16" | "u16" | "i32" | "u32" | "i64" | "u64" | "isize" | "usize")
let fsuffix = ("f32" | "f64")

let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*

rule lex = parse
| [' ' '\t'] { lex lexbuf }
| newline { MenhirLib.LexerUtil.newline lexbuf; lex lexbuf }
| int { Int (Int64.of_string (Lexing.lexeme lexbuf)) }
| (int as i) ((isuffix | fsuffix) as s) {
    match s.[0] with
    | 'i' | 'u' -> IntSuffix (Int64.of_string i, s)
    | 'f' -> FloatSuffix (float_of_string i, s)
    | _ -> failwith "unreachable"
  }
| float { Float (float_of_string (Lexing.lexeme lexbuf)) }
| (float as f) (fsuffix as s) { FloatSuffix (float_of_string f, s) }
| ident {
    match Lexing.lexeme lexbuf with
    | "_" -> Wildcard
    | "true" -> True
    | "false" -> False
    | "while" -> While
    | "for" -> For
    | "in" -> In
    | "let" -> Let
    | "const" -> Const
    | "fn" -> Fn
    | "impl" -> Impl
    | "use" -> Use
    | "if" -> If
    | "else" -> Else
    | "match" -> Match
    | "return" -> Return
    | "break" -> Break
    | "type" -> Type
    | "struct" -> Struct
    | "enum" -> Enum
    | "Self" -> SelfT
    | "self" -> Self
    | "extern" -> Extern
    (* Weak keywords: These keywords have special meaning only in certain contexts. *)
    | "root" -> Ident "$root"
    | "core" -> Ident "$core"
    | lxm -> Ident lxm
  }
| "==" { EqualEqual }
| "!=" { NotEqual }
| ">=" { GreaterEqual }
| "<=" { SmallerEqual }
| "->" { Arrow }
| "..=" { DotDotEq }
| ".." { DotDot }
| "=" { Equal }
| "&&" { AmpAmp }
| "||" { PipePipe }
| "::" { ColCol }
| "&" { Amp }
| "|" { Pipe }
| ">" { Greater }
| "<" { Smaller }
| "+" { Plus }
| "-" { Minus }
| "*" { Star }
| "/" { Slash }
| "%" { Modulo }
| "!" { Bang }
| "(" { Lpar }
| ")" { Rpar }
| "{" { Begin }
| "}" { End }
| "[" { Lbracket }
| "]" { Rbracket }
| ";" { Semi }
| ":" { Colon }
| "," { Comma }
| "." { Dot }
| '"' {
    reset_string_buffer();
    string_start := lexbuf.Lexing.lex_curr_p;
    in_string lexbuf;
    String (get_stored_string())
  }
| "//" { line_comment lexbuf }
| "/*" { block_comment 0 lexbuf }
| eof { Eof }
| _ as c { report_error ("Invalid character: " ^ (String.make 1 c)) lexbuf }

and in_string = parse
| '"' { () }
| '\\' ['\\' '\'' '"' 'n' 't' 'b' 'r' ' '] {
    store_string_char(char_for_backslash(Lexing.lexeme_char lexbuf 1));
    in_string lexbuf }
| '\\' decimal decimal decimal {
    store_string_char(char_for_decimal_code lexbuf 1);
    in_string lexbuf }
| '\\' 'x' hex hex {
    store_string_char(char_for_hexadecimal_code lexbuf 2);
    in_string lexbuf }
| '\\' _ as chars { skip_to_eol lexbuf; report_error ("Illegal escape: " ^ chars) lexbuf }
| newline as s {
    MenhirLib.LexerUtil.newline lexbuf;
    for i = 0 to String.length s - 1 do
        store_string_char s.[i];
    done;
    in_string lexbuf }
| eof { raise (LexError (
    "Unexpected end of file in string literal",
    !string_start, lexbuf.Lexing.lex_curr_p))
  }
| _ as c { store_string_char c; in_string lexbuf }

and line_comment = parse
| newline { lex lexbuf }
| _ { line_comment lexbuf }
| eof { Eof }

and block_comment n = parse
| "*/" { if n = 0 then lex lexbuf else block_comment (n-1) lexbuf }
| "/*" { block_comment (n+1) lexbuf }
| _ { block_comment n lexbuf }
| eof { report_error "Unexpected end of file in block comment" lexbuf }

and skip_to_eol = parse
| newline { () }
| _ { skip_to_eol lexbuf }
