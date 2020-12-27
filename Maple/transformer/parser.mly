%token <MapleAST.intInfo> INT
%token <MapleAST.floatInfo> FLOAT
%token <string> IDENT GIDENT LIDENT
%token <string * MapleAST.location> FIDENT MVIDENTORLABEL
%token <MapleAST.intInfo> PIDENT
%token <MapleAST.location> TYPE VAR FUNC REG JAVACLASS JAVAINTERFACE ENTRYFUNC
(*%token DOLLAR PERCENT AT AND*)
%token <MapleAST.location> I8 I16 I32 I64 U8 U16 U32 U64 A32 A64 F32 F64
%token <MapleAST.location> VOID BOOL AGG PTR REF POINTER STRUCT UNION CLASS INTERFACE
%token <MapleAST.location> PUBLIC PRIVATE PROTECTED ALIGN ABSTRACT FINAL STATIC VIRTUAL CONSTRUCTOR
%token <MapleAST.location> DREAD REGREAD IREAD ADDROF ADDROFFUNC CONSTVAL SIZEOFTYPE IADDROF CEIL CVT FLOOR RETYPE TRUNC CAND CIOR SELECT ARRAY
%token <MapleAST.location> ABS BNOT LNOT NEG RECIP SEXT ZEXT SQRT
%token <MapleAST.location> ADD ASHR BAND BIOR BXOR CMP CMPG CMPL DIV EQ GE GT LAND LIOR LE LSHR LT MAX MIN MUL NE REM SHL SUB
%token THROWNVAL
%token <MapleAST.location> MALLOC GCMALLOC GCMALLOCJARRAY GCPERMALLOC
%token <MapleAST.location> SKIP DASSIGN IASSIGN REGASSIGN IF ELSE WHILE BRTRUE BRFALSE GOTO RETURN SWITCH CALLASSIGNED ICALLASSIGNED VIRTUALCALLASSIGNED INTERFACECALLASSIGNED JAVATRY ENDTRY JAVACATCH THROW EVAL FREE INCREF DECREF
%token LBRACE RBRACE
%token LBRACK RBRACK
%token LPAREN RPAREN
%token LANGLE RANGLE
%token COMMA
%token COLON
%token EOF
(*%right SEQ*)

%start <MapleAST.program> program

%%

program:
  | gdl = list(global_declaration); EOF { gdl };;
(*| e = statement; EOF { e }*)

(*global_declaration_list:
  | gdl = list(global_declaration) { gdl };;*)

global_declaration:
  | loc = VAR; id = GIDENT; t = typespec; tal = list(type_attr); { MapleAST.GD_var (id, (t, tal), loc) }
  | loc = TYPE; id = GIDENT; t = coq_type; { MapleAST.GD_type (id, t, loc) }
  | loc = FUNC; id = FIDENT; fal = list(func_attr); LPAREN; p = params; RPAREN; t = typespec; { MapleAST.GD_func (fst id, ({ MapleAST.fun_attr = fal; fun_returns = t; fun_params = p; }, None), loc) }
  | loc = FUNC; id = FIDENT; fal = list(func_attr); LPAREN; p = params; RPAREN; t = typespec; LBRACE; ldl = list(local_declaration); s = statement; RBRACE { MapleAST.GD_func (fst id, ({ MapleAST.fun_attr = fal; MapleAST.fun_returns = t; MapleAST.fun_params = p; }, Some { MapleAST.fun_localdecl = ldl; MapleAST.fun_statement = s}), loc) }
  | loc = JAVACLASS; id1 = GIDENT; LANGLE; id2 = GIDENT; RANGLE; cal = list(class_attr) { MapleAST.GD_javaclass (id1, id2, cal, loc) }
  | loc = JAVAINTERFACE; id1 = GIDENT; LANGLE; id2 = GIDENT; RANGLE; cal = list(class_attr) { MapleAST.GD_javainterface (id1, id2, cal, loc) }
  | loc = ENTRYFUNC; id = FIDENT { MapleAST.GD_entryfunc (fst id, loc) };;

typespec:
  | pt = prim_type { MapleAST.TSprim pt }
  | LANGLE; pt = prim_type ; RANGLE { MapleAST.TSprim pt  }
  | LANGLE; POINTER; t = typespec ; RANGLE { MapleAST.TSpointer t }
  | LANGLE; LBRACK; z = INT; RBRACK; t = typespec ; RANGLE { MapleAST.TSarray (t, Some z) }
  | LANGLE; LBRACK; RBRACK; t = typespec ; RANGLE { MapleAST.TSarray (t, None) }
  | LANGLE; FUNC; LPAREN; tl = typespeclist ; RPAREN; t = typespec; RANGLE { MapleAST.TSfunction (tl, t) }
  | LANGLE; id = GIDENT; RANGLE { MapleAST.TSglobal id }
  | LANGLE; id = LIDENT; RANGLE { MapleAST.TSlocal id }

typespeclist:
  | { TSnil }
  | t = typespec { MapleAST.TScons (t, TSnil) }
  | t = typespec; COMMA; tl = typespeclist { MapleAST.TScons (t, tl) };;

coq_type:
  | pt = prim_type { MapleAST.Tprim pt }
  | LANGLE; pt = prim_type ; RANGLE { MapleAST.Tprim pt  }
  | LANGLE; POINTER; t = typespec ; RANGLE { MapleAST.Tpointer t }
  | LANGLE; LBRACK; z = INT; RBRACK; t = typespec ; RANGLE { MapleAST.Tarray (t, Some z) }
  | LANGLE; LBRACK; RBRACK; t = typespec ; RANGLE { MapleAST.Tarray (t, None) }
  | LANGLE; FUNC; LPAREN; tl = typespeclist ; RPAREN; t = typespec; RANGLE { MapleAST.Tfunction (tl, t) }
  | LANGLE; STRUCT; LBRACE; mv = membervars ; RBRACE; RANGLE { MapleAST.Tstruct mv }
  | LANGLE; UNION; LBRACE; mv = membervars ; RBRACE; RANGLE { MapleAST.Tunion mv }
  | LANGLE; CLASS; LBRACE; mv = membervars; mf = memberfuncs; idl = identlist ; RBRACE; RANGLE { MapleAST.Tclass (None, idl, mv, mf) }
  | LANGLE; CLASS; LANGLE; id = GIDENT; RANGLE; LBRACE; mv = membervars; mf = memberfuncs; idl = identlist ; RBRACE; RANGLE { MapleAST.Tclass (Some id, idl, mv, mf) }
  | LANGLE; INTERFACE; LBRACE; mv = membervars; mf = memberfuncs; idl = identlist ; RBRACE; RANGLE { MapleAST.Tinterface (idl, mv, mf) }
  | LANGLE; id = GIDENT; RANGLE { MapleAST.Tglobal id }
  | LANGLE; id = LIDENT; RANGLE { MapleAST.Tlocal id }

prim_type:
  | VOID { MapleLightTypes.PTvoid }
  | BOOL { MapleLightTypes.PTbool }
  | AGG { MapleLightTypes.PTagg }
  | PTR { MapleLightTypes.PTptr }
  | REF { MapleLightTypes.PTref }
  | I8 { MapleLightTypes.PTint (I8, Signed) }
  | I16 { MapleLightTypes.PTint (I16, Signed) }
  | I32 { MapleLightTypes.PTint (I32, Signed) }
  | I64 { MapleLightTypes.PTint (I64, Signed) }
  | U8 { MapleLightTypes.PTint (I8, Unsigned) }
  | U16 { MapleLightTypes.PTint (I16, Unsigned) }
  | U32 { MapleLightTypes.PTint (I32, Unsigned) }
  | U64 { MapleLightTypes.PTint (I64, Unsigned) }
  | F32 { MapleLightTypes.PTfloat F32 }
  | F64 { MapleLightTypes.PTfloat F64 }
  | A32 { MapleLightTypes.PTaddr A32 }
  | A64 { MapleLightTypes.PTaddr A64 };;

membervars:
  | { MVnil }
  | id = MVIDENTORLABEL; t = typespec; mval = membervar_attr_list { MapleAST.MVcons (fst id, t, mval, MVnil, snd id) }
  | id = MVIDENTORLABEL; t = typespec; mval = membervar_attr_list; COMMA; mv = membervars { MapleAST.MVcons (fst id, t, mval, mv, snd id) };;

membervar_attr_list:
  mval = list(membervar_attr) { mval };;

membervar_attr:
  | am = access_modifier { MapleAST.MVA_access am }
  | ALIGN; LPAREN; n = INT; RPAREN { MapleAST.MVA_align n };;

type_attr:
| ALIGN; LPAREN; n = INT; RPAREN { (*MapleAST.VA_align*) n };;

memberfuncs:
  | { MFnil }
  | id = FIDENT; mfal = list(func_attr); LPAREN; tl = typespeclist; RPAREN; t = typespec { MapleAST.MFcons (fst id, tl, t, mfal, MFnil, snd id) }
  | id = FIDENT; mfal = list(func_attr); LPAREN; tl = typespeclist; RPAREN; t = typespec; COMMA; mv = memberfuncs { MapleAST.MFcons (fst id, tl, t, mfal, mv, snd id) };;

(*func_attr_list:
  mfal = list(func_attr) { mfal };;*)

func_attr:
  | am = access_modifier { MapleAST.FA_access am }
  | ABSTRACT { MapleAST.FA_abstract }
  | FINAL { MapleAST.FA_final }
  | STATIC { MapleAST.FA_static }
  | VIRTUAL { MapleAST.FA_virtual }
  | CONSTRUCTOR { MapleAST.FA_constructor }

access_modifier:
  | PUBLIC { MapleLightTypes.AM_public }
  | PRIVATE { MapleLightTypes.AM_private }
  | PROTECTED { MapleLightTypes.AM_protected };;

(*identlist:
  | { [] }
  | id = GIDENT { [id] }
  | id = GIDENT; COMMA; idl = identlist { id :: idl };;*)

identlist:
  idl = separated_list(COMMA, GIDENT) { idl };;

class_attr:
  | am = access_modifier { MapleAST.CA_access am }
  | ABSTRACT { MapleAST.CA_abstract }
  | FINAL { MapleAST.CA_final };;

params:
  | { [] }
  | VAR; id = LIDENT; t = typespec { [(id, t)] }
  | VAR; id = LIDENT; t = typespec; COMMA; tl = params { (id, t) :: tl };;

local_declaration:
  | loc = VAR; id = LIDENT; t = typespec; tal = list(type_attr); { MapleAST.LD_var (id, (t, tal), loc) }
  | loc = TYPE; id = LIDENT; t = coq_type; { MapleAST.LD_type (id, t, loc) }
  | loc = REG; id = INT; pt = prim_type; { MapleAST.LD_preg (id, pt, loc) };;

expr:
  | DREAD; pt = prim_type; vid = var_id; fi = field_id? { MapleAST.E_dread (pt, vid, fi) }
  | REGREAD; pt = prim_type; rid = reg_id { MapleAST.E_regread (pt, rid) }
  | IREAD; pt = prim_type; t = typespec; fi = field_id?; LPAREN; e = expr; RPAREN { MapleAST.E_iread (pt, t, fi, e) }
  | ADDROF; pt =  prim_type; vid =  var_id; fi = field_id? { MapleAST.E_addrof (pt, vid, fi) }
  | ADDROFFUNC; pt = prim_type; fid = FIDENT { MapleAST.E_addroffunc (pt, fst fid) }
  | CONSTVAL; pt = prim_type; c = constant { MapleAST.E_constval (pt, c) }
  | SIZEOFTYPE; pt = prim_type; t = typespec { MapleAST.E_sizeoftype (pt, t) }
  | ABS; pt = prim_type; LPAREN; e = expr; RPAREN { MapleAST.E_unary (O_abs, pt, e) }
  | BNOT; pt = prim_type; LPAREN; e = expr; RPAREN { MapleAST.E_unary (O_bnot, pt, e) }
  | LNOT; pt = prim_type; LPAREN; e = expr; RPAREN { MapleAST.E_unary (O_lnot, pt, e) }
  | NEG; pt = prim_type; LPAREN; e = expr; RPAREN { MapleAST.E_unary (O_neg, pt, e) }
  | RECIP; pt = prim_type; LPAREN; e = expr; RPAREN { MapleAST.E_unary (O_recip, pt, e) }
  | SEXT; pt = prim_type; n = INT; LPAREN; e = expr; RPAREN { MapleAST.E_unary (O_sext n, pt, e) }
  | ZEXT; pt = prim_type; n = INT; LPAREN; e = expr; RPAREN { MapleAST.E_unary (O_zext n, pt, e) }
  | SQRT; pt = prim_type; LPAREN; e = expr; RPAREN { MapleAST.E_unary (O_sqrt, pt, e) }
  | IADDROF; pt = prim_type; t = typespec; fi = field_id?; LPAREN; e = expr; RPAREN { MapleAST.E_iaddrof (pt, t, fi, e) }
  | CEIL; pt1 = prim_type; pt2 = prim_type; LPAREN; e = expr; RPAREN { MapleAST.E_ceil (pt1, pt2, e) }
  | CVT; pt1 = prim_type; pt2 = prim_type; LPAREN; e = expr; RPAREN { MapleAST.E_cvt (pt1, pt2, e) }
  | FLOOR; pt1 = prim_type; pt2 = prim_type; LPAREN; e = expr; RPAREN { MapleAST.E_floor (pt1, pt2, e) }
  | RETYPE; pt = prim_type; t = typespec; LPAREN; e = expr; RPAREN { MapleAST.E_retype (pt, t, e) }
  | TRUNC; pt1 = prim_type; pt2 = prim_type; e = expr { MapleAST.E_trunc (pt1, pt2, e) }
  | ADD; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_add, pt, e1, e2) }
  | ASHR; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_ashr, pt, e1, e2) }
  | BAND; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_band, pt, e1, e2) }
  | BIOR; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_bior, pt, e1, e2) }
  | BXOR; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_bxor, pt, e1, e2) }
  | CMP; pt1 = prim_type; pt2 = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_cmp pt2, pt1, e1, e2) }
  | CMPG; pt1 = prim_type; pt2 = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_cmpg pt2, pt1, e1, e2) }
  | CMPL; pt1 = prim_type; pt2 = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_cmpl pt2, pt1, e1, e2) }
  | DIV; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_div, pt, e1, e2) }
  | EQ; pt1 = prim_type; pt2 = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_eq pt2, pt1, e1, e2) }
  | GE; pt1 = prim_type; pt2 = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_ge pt2, pt1, e1, e2) }
  | GT; pt1 = prim_type; pt2 = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_gt pt2, pt1, e1, e2) }
  | LAND; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_land, pt, e1, e2) }
  | LIOR; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_lior, pt, e1, e2) }
  | LE; pt1 = prim_type; pt2 = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_le pt2, pt1, e1, e2) }
  | LSHR; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_lshr, pt, e1, e2) }
  | LT; pt1 = prim_type; pt2 = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_lt pt2, pt1, e1, e2) }
  | MAX; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_max, pt, e1, e2) }
  | MIN; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_min, pt, e1, e2) }
  | MUL; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_mul, pt, e1, e2) }
  | NE; pt1 = prim_type; pt2 = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_ne pt2, pt1, e1, e2) }
  | REM; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_rem, pt, e1, e2) }
  | SHL; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_shl, pt, e1, e2) }
  | SUB; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_binary (O_sub, pt, e1, e2) }
  | CAND; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_cand (pt, e1, e2) }
  | CIOR; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN { MapleAST.E_cior (pt, e1, e2) }
  | SELECT; pt = prim_type; LPAREN; e1 = expr; COMMA; e2 = expr; COMMA; e3 = expr; RPAREN { MapleAST.E_select (pt, e1, e2, e3) }
  | ARRAY; n = INT; pt = prim_type; t = typespec; LPAREN; el = exprlist; RPAREN { MapleAST.E_array (n, pt, t, el) };;

exprlist:
  | { E_nil }
  | e = expr { MapleAST.E_cons (e, E_nil) }
  | e = expr; COMMA; el = exprlist { E_cons (e, el) };;

var_id:
  | id = GIDENT { MapleAST.VI_global id }
  | id = LIDENT { MapleAST.VI_local id };;

field_id:
  | n = INT { n };;

reg_id:
  | THROWNVAL { RI_thrownval }
  | id = PIDENT { RI_pseudo id };;

constant:
  | n = INT { C_int n }
  | f = FLOAT { C_float f };;

ext_expr:
  | e = expr { MapleAST.EE_pure e }
  | MALLOC; pt = prim_type; LPAREN; e = expr; RPAREN { MapleAST.EE_malloc (pt, e) }
  | GCMALLOC; pt = prim_type; t = typespec { MapleAST.EE_gcmalloc (pt, t) }
  | GCMALLOCJARRAY; pt = prim_type; t = typespec; LPAREN; e = expr; RPAREN { MapleAST.EE_gcmallocjarray (pt, t, e) }
  | GCPERMALLOC; pt = prim_type; t = typespec { MapleAST.EE_gcpermalloc (pt, t) };;

statement:
  | loc = SKIP { S_skip loc }
  | loc = DASSIGN; vid = var_id; fi = field_id?; LPAREN; ee = ext_expr; RPAREN { MapleAST.S_dassign (vid, fi, ee, loc) }
  | loc = IASSIGN; t = typespec; fi = field_id?; LPAREN; e = expr; COMMA; ee = ext_expr; RPAREN { MapleAST.S_iassign (t, fi, e, ee, loc) }
  | loc = REGASSIGN; pt = prim_type; rid = reg_id; LPAREN; ee = ext_expr; RPAREN { MapleAST.S_regassign (pt, rid, ee, loc) }
  | s1 = statement; s2 = statement { MapleAST.S_seq (s1, s2) }
  | lbl = MVIDENTORLABEL; s = statement { MapleAST.S_label (fst lbl, s, snd lbl) }
  | loc = IF; LPAREN; e = expr; RPAREN; LBRACE; s1 = statement; RBRACE { MapleAST.S_if (e, s1, S_skip loc, loc) }
  | loc = IF; LPAREN; e = expr; RPAREN; LBRACE; s1 = statement; RBRACE; ELSE; LBRACE; s2 = statement; RBRACE; { MapleAST.S_if (e, s1, s2, loc) }
  | loc = WHILE; LPAREN; e = expr; RPAREN; LBRACE; s = statement; RBRACE { MapleAST.S_while (e, s, loc) }
  | loc = BRTRUE; lbl = MVIDENTORLABEL; LPAREN; e = expr; RPAREN { MapleAST.S_brtrue (fst lbl, e, loc) }
  | loc = BRFALSE; lbl = MVIDENTORLABEL; LPAREN; e = expr; RPAREN { MapleAST.S_brfalse (fst lbl, e, loc) }
  | loc = GOTO; lbl = MVIDENTORLABEL { MapleAST.S_goto (fst lbl, loc) }
  | loc = RETURN LPAREN; el = exprlist; RPAREN { MapleAST.S_return (el, loc) }
  | loc = SWITCH; LPAREN; e = expr; RPAREN; lbl = MVIDENTORLABEL; LPAREN; cl = list(case); RPAREN { MapleAST.S_switch (e, fst lbl, cl, loc) }
  | loc = CALLASSIGNED; fid = FIDENT; LPAREN; el = exprlist; RPAREN; LBRACE; rl = list(return_assign); RBRACE { MapleAST.S_callassigned (fst fid, el, rl, loc) }
  | loc = ICALLASSIGNED; LPAREN; el = exprlist; RPAREN; LBRACE; rl = list(return_assign); RBRACE { MapleAST.S_icallassigned (el, rl, loc) }
  | loc = VIRTUALCALLASSIGNED; fid = FIDENT; LPAREN; el = exprlist; RPAREN; LBRACE; rl = list(return_assign); RBRACE { MapleAST.S_virtualcallassigned (fst fid, el, rl, loc) }
  | loc = INTERFACECALLASSIGNED; fid = FIDENT; LPAREN; el = exprlist; RPAREN; LBRACE; rl = list(return_assign); RBRACE { MapleAST.S_interfacecallassigned (fst fid, el, rl, loc) }
  | loc = JAVATRY; LBRACE; ll = list(MVIDENTORLABEL); RBRACE; s = statement; ENDTRY; { MapleAST.S_javatry (List.map fst ll, s, loc) }
  | loc = THROW; LPAREN; e = expr; RPAREN { MapleAST.S_throw (e, loc) }
  | lbl = MVIDENTORLABEL; loc = JAVACATCH; LBRACE; tl = list(typespec); RBRACE { MapleAST.S_javacatch (fst lbl, tl, loc) }
  | loc = DECREF; LPAREN; e = expr; RPAREN { MapleAST.S_decref (e, loc) }
  | loc = FREE; LPAREN; e = expr; RPAREN { MapleAST.S_free (e, loc) }
  | loc = INCREF; LPAREN; e = expr; RPAREN { MapleAST.S_incref (e, loc) }
  | loc = EVAL; LPAREN; e = expr; RPAREN { MapleAST.S_eval (e, loc) };;

case:
  | n = INT; COLON; GOTO; lbl = MVIDENTORLABEL { ((n, fst lbl), snd lbl) };;

return_assign:
  | loc = DASSIGN; vid = var_id; fi = field_id? { ((vid, fi), loc) };;
