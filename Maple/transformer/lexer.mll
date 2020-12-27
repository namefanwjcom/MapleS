{
open Lexing
open Parser

exception LexError of string

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let currentLoc (lb: lexbuf) =
  let p = Lexing.lexeme_start_p lb in
  MapleAST.({ lineno   = p.Lexing.pos_lnum;
              filename = p.Lexing.pos_fname;
              byteno   = p.Lexing.pos_cnum;})

let keywords : (string, MapleAST.location -> token) Hashtbl.t = Hashtbl.create 53
let _ =
  List.iter (fun (key, builder) -> Hashtbl.add keywords key builder)
    [ ("type", fun loc -> TYPE loc);
      ("var", fun loc -> VAR loc);
      ("func", fun loc -> FUNC loc);
      ("reg", fun loc -> REG loc);
      ("javaclass", fun loc -> JAVACLASS loc);
      ("javainterface", fun loc -> JAVAINTERFACE loc);
      ("entryfunc", fun loc -> ENTRYFUNC loc);
      ("i8", fun loc -> I8 loc);
      ("i16", fun loc -> I16 loc);
      ("i32", fun loc -> I32 loc);
      ("i64", fun loc -> I64 loc);
      ("u8", fun loc -> U8 loc);
      ("u16", fun loc -> U16 loc);
      ("u32", fun loc -> U32 loc);
      ("u64", fun loc -> U64 loc);
      ("f32", fun loc -> F32 loc);
      ("f64", fun loc -> F64 loc);
      ("a32", fun loc -> A32 loc);
      ("a64", fun loc -> A64 loc);
      ("void", fun loc -> VOID loc);
      ("u1", fun loc -> BOOL loc);
      ("agg", fun loc -> AGG loc);
      ("ptr", fun loc -> PTR loc);
      ("ref", fun loc -> REF loc);
      ("struct", fun loc -> STRUCT loc);
      ("union", fun loc -> UNION loc);
      ("class", fun loc -> CLASS loc);
      ("interface", fun loc -> INTERFACE loc);
      ("public", fun loc -> PUBLIC loc);
      ("private", fun loc -> PRIVATE loc);
      ("protected", fun loc -> PROTECTED loc);
      ("align", fun loc -> ALIGN loc);
      ("abstract", fun loc -> ABSTRACT loc);
      ("final", fun loc -> FINAL loc);
      ("static", fun loc -> STATIC loc);
      ("virtual", fun loc -> VIRTUAL loc);
      ("constructor", fun loc -> CONSTRUCTOR loc);
      ("dread", fun loc -> DREAD loc);
      ("regread", fun loc -> REGREAD loc);
      ("iread", fun loc -> IREAD loc);
      ("addrof", fun loc -> ADDROF loc);
      ("addroffunc", fun loc -> ADDROFFUNC loc);
      ("constval", fun loc -> CONSTVAL loc);
      ("sizeoftype", fun loc -> SIZEOFTYPE loc);
      ("iaddrof", fun loc -> IADDROF loc);
      ("ceil", fun loc -> CEIL loc);
      ("cvt", fun loc -> CVT loc);
      ("floor", fun loc -> FLOOR loc);
      ("retype", fun loc -> RETYPE loc);
      ("trunc", fun loc -> TRUNC loc);
      ("cand", fun loc -> CAND loc);
      ("cior", fun loc -> CIOR loc);
      ("select", fun loc -> SELECT loc);
      ("array", fun loc -> ARRAY loc);
      ("abs", fun loc -> ABS loc);
      ("bnot", fun loc -> BNOT loc);
      ("lnot", fun loc -> LNOT loc);
      ("neg", fun loc -> NEG loc);
      ("recip", fun loc -> RECIP loc);
      ("sext", fun loc -> SEXT loc);
      ("zext", fun loc -> ZEXT loc);
      ("sqrt", fun loc -> SQRT loc);
      ("add", fun loc -> ADD loc);
      ("ashr", fun loc -> ASHR loc);
      ("band", fun loc -> BAND loc);
      ("bior", fun loc -> BIOR loc);
      ("bxor", fun loc -> BXOR loc);
      ("cmp", fun loc -> CMP loc);
      ("cmpg", fun loc -> CMPG loc);
      ("cmpl", fun loc -> CMPL loc);
      ("div", fun loc -> DIV loc);
      ("eq", fun loc -> EQ loc);
      ("ge", fun loc -> GE loc);
      ("gt", fun loc -> GT loc);
      ("land", fun loc -> LAND loc);
      ("lior", fun loc -> LIOR loc);
      ("le", fun loc -> LE loc);
      ("lshr", fun loc -> LSHR loc);
      ("lt", fun loc -> LT loc);
      ("max", fun loc -> MAX loc);
      ("min", fun loc -> MIN loc);
      ("mul", fun loc -> MUL loc);
      ("ne", fun loc -> NE loc);
      ("rem", fun loc -> REM loc);
      ("shl", fun loc -> SHL loc);
      ("sub", fun loc -> SUB loc);
      ("malloc", fun loc -> MALLOC loc);
      ("gcmalloc", fun loc -> GCMALLOC loc);
      ("gcmallocjarray", fun loc -> GCMALLOCJARRAY loc);
      ("gcpermalloc", fun loc -> GCPERMALLOC loc);
      ("dassign", fun loc -> DASSIGN loc);
      ("iassign", fun loc -> IASSIGN loc);
      ("regassign", fun loc -> REGASSIGN loc);
      ("if", fun loc -> IF loc);
      ("else", fun loc -> ELSE loc);
      ("while", fun loc -> WHILE loc);
      ("brtrue", fun loc -> BRTRUE loc);
      ("brfalse", fun loc -> BRFALSE loc);
      ("goto", fun loc -> GOTO loc);
      ("return", fun loc -> RETURN loc);
      ("switch", fun loc -> SWITCH loc);
      ("callassigned", fun loc -> CALLASSIGNED loc);
      ("icallassigned", fun loc -> ICALLASSIGNED loc);
      ("virtualcallassigned", fun loc -> VIRTUALCALLASSIGNED loc);
      ("interfacecallassigned", fun loc -> INTERFACECALLASSIGNED loc);
      ("javatry", fun loc -> JAVATRY loc);
      ("endtry", fun loc -> ENDTRY loc);
      ("javacatch", fun loc -> JAVACATCH loc);
      ("throw", fun loc -> THROW loc);
      ("eval", fun loc -> EVAL loc);
      ("free", fun loc -> FREE loc);
      ("incref", fun loc -> INCREF loc);
      ("decref", fun loc -> DECREF loc);
    ]
}

let digit = ['0'-'9']
let hexadecimal_digit = ['0'-'9' 'A'-'F' 'a'-'f']
let nondigit = ['_' 'a'-'z' 'A'-'Z']

let ident = nondigit (nondigit|digit)*

(* Whitespaces *)
let whitespace = [' ' '\t'  '\011' '\012' '\r']+

(* Integer constants *)
let sign = ['-'] as signpart
let decimal_constant = sign? (digit+ as intpart)

let hexadecimal_prefix = "0x" | "0X"
let hexadecimal_constant =
  sign? hexadecimal_prefix (hexadecimal_digit+ as intpart)

(*let unsigned_suffix = ['u' 'U']
let long_suffix = ['l' 'L']
let long_long_suffix = "ll" | "LL"
let integer_suffix =
    unsigned_suffix long_suffix?
  | unsigned_suffix long_long_suffix
  | long_suffix unsigned_suffix?
  | long_long_suffix unsigned_suffix?

let integer_constant =
    decimal_constant
  | hexadecimal_constant
let signed_integer_constant = sign? integer_constant*)

(* Floating constants *)
let digit_sequence = digit+
let floating_suffix = ['f' 'l' 'F' 'L'] as suffix

let fractional_constant =
    (digit_sequence as intpart)? '.' (digit_sequence as frac)
  | (digit_sequence as intpart) '.'
let exponent_part =
    'e' ((sign? digit_sequence) as expo)
  | 'E' ((sign? digit_sequence) as expo)
let decimal_floating_constant =
    fractional_constant exponent_part? floating_suffix?
  | (digit_sequence as intpart) exponent_part floating_suffix?
let signed_decimal_floating_constant = sign? decimal_floating_constant

let hexadecimal_digit_sequence = hexadecimal_digit+
let hexadecimal_fractional_constant =
    (hexadecimal_digit_sequence as intpart)? '.' (hexadecimal_digit_sequence as frac)
  | (hexadecimal_digit_sequence as intpart) '.'
let binary_exponent_part =
    'p' ((sign? digit_sequence) as expo)
  | 'P' ((sign? digit_sequence) as expo)
let hexadecimal_floating_constant =
    hexadecimal_prefix hexadecimal_fractional_constant
        binary_exponent_part floating_suffix?
  | hexadecimal_prefix (hexadecimal_digit_sequence as intpart)
        binary_exponent_part floating_suffix?
let signed_hexadecimal_floating_constant = sign? hexadecimal_floating_constant

let newline = '\n'
let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let gident = '$' (ident as id)
let lident = '%' (ident as id)
let mvident_or_label = '@' (ident as id)
let pident = '%' (digit+ as intpart)
let fident = '&' (ident as id)

(* part "4" *)
rule read =
  parse
  | whitespace    { read lexbuf }
  | newline  { new_line lexbuf; read lexbuf }
  | '*'   { POINTER (currentLoc lexbuf)}
  | '{'      { LBRACE }
  | '}'      { RBRACE }
  | '['      { LBRACK }
  | ']'      { RBRACK }
  | '('      { LPAREN }
  | ')'      { RPAREN }
  | '<'      { LANGLE }
  | '>'      { RANGLE }
  | ','      { COMMA }
  | ':'      { COLON }
  | '#'      { singleline_comment lexbuf; read lexbuf }
  | "%%thrownval" { THROWNVAL }
  | ident as id
    { try
        Hashtbl.find keywords id (currentLoc lexbuf)
      with Not_found ->
        raise (LexError ("Invalid keyword: " ^ id))
    }
  | gident { GIDENT (id) }
  | lident { LIDENT (id) }
  | mvident_or_label { MVIDENTORLABEL (id, currentLoc lexbuf) }
  | fident { FIDENT (id, currentLoc lexbuf) }
  | pident as c
      { PIDENT { MapleAST.coq_II_source = c;
                 MapleAST.coq_II_isNegative = false;
                 MapleAST.coq_II_isHex = false;
                 MapleAST.coq_II_integer = intpart;
      } }
  | decimal_constant as c
      { INT { MapleAST.coq_II_source = c;
              MapleAST.coq_II_isNegative =
                (match signpart with
                 | Some _ -> true
                 | None -> false);
              MapleAST.coq_II_isHex = false;
              MapleAST.coq_II_integer = intpart;
      } }
  | hexadecimal_constant as c
      { INT { MapleAST.coq_II_source = c;
              MapleAST.coq_II_isNegative =
                (match signpart with
                 | Some _ -> true
                 | None -> false);
              MapleAST.coq_II_isHex = true;
              MapleAST.coq_II_integer = intpart;
      } }
  | signed_decimal_floating_constant as c
      { FLOAT { MapleAST.coq_FI_source = c;
                MapleAST.coq_FI_isNegative =
                  (match signpart with
                   | Some _ -> true
                   | None -> false);
                MapleAST.coq_FI_isHex = false;
                MapleAST.coq_FI_integer = intpart;
                MapleAST.coq_FI_fraction = frac;
                MapleAST.coq_FI_exponent = expo;
                MapleAST.coq_FI_suffix =
                  (match suffix with
                   | None -> None
                   | Some c -> Some (String.make 1 c));
    } }
  | hexadecimal_floating_constant as c
      { FLOAT { MapleAST.coq_FI_source = c;
                MapleAST.coq_FI_isNegative =
                  (match signpart with
                   | Some _ -> true
                   | None -> false);
                MapleAST.coq_FI_isHex = true;
                MapleAST.coq_FI_integer = intpart;
                MapleAST.coq_FI_fraction = frac;
                MapleAST.coq_FI_exponent = Some expo;
                MapleAST.coq_FI_suffix =
                  (match suffix with
                   | None -> None
                   | Some c -> Some (String.make 1 c));
      } }
  | _ { raise (LexError ("Invalid symbol: " ^ lexeme lexbuf)) }
  | eof      { EOF }
(* Single-line comment terminated by a newline *)
and singleline_comment = parse
  | newline   { new_line lexbuf }
  | eof    { () }
  | _      { singleline_comment lexbuf }


(* part "5" *)
(*and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }*)
