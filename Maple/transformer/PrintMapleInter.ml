open Printf
open MapleLightTypes
open MapleLightOp
open MapleAST
open MapleInter

let print_id_option (oc: out_channel) (oid: ident option) =
  match oid with
  | Some id -> fprintf oc "%s" id
  | None -> ()

let print_var_id (oc: out_channel) (vid: var_id) =
  match vid with
  | VI_global id -> fprintf oc "$%s" id
  | VI_local id -> fprintf oc "%%%s" id

let print_intInfo (oc: out_channel) (i: intInfo) =
  let neg_sign = if i.coq_II_isNegative then "-" else "" in
  let hex_sign = if i.coq_II_isHex then "0x" else "" in
  fprintf oc "%s%s%s" neg_sign hex_sign i.coq_II_integer

let print_intInfo_option (oc: out_channel) (oi: intInfo option) =
  match oi with
  | Some i -> print_intInfo oc i
  | None -> ()

let print_type_attr (oc: out_channel) (ta: type_attr) = print_intInfo oc ta

let print_access_modifier (oc: out_channel) (am: access_modifier) =
  match am with
  | AM_friendly -> fprintf oc "friendly"
  | AM_public -> fprintf oc "public"
  | AM_private -> fprintf oc "private"
  | AM_protected -> fprintf oc "protected"

let print_membervar_attr (oc: out_channel) (mva: membervar_attr) =
  match mva with
  | MVA_access am -> print_access_modifier oc am
  | MVA_align i -> fprintf oc "align(%a)" print_intInfo i

let print_func_attr (oc: out_channel) (fa: func_attr) =
  match fa with
  | FA_access am -> print_access_modifier oc am
  | FA_abstract -> fprintf oc "abstract"
  | FA_final -> fprintf oc "final"
  | FA_static -> fprintf oc "static"
  | FA_virtual -> fprintf oc "virtual"
  | FA_constructor -> fprintf oc "constructor"

let rec print_prim_type (oc: out_channel) (pt: prim_type) =
  match pt with
  | PTvoid -> fprintf oc "void"
  | PTint (isz, Signed) -> fprintf oc "i%a" print_intsize isz
  | PTint (isz, Unsigned) -> fprintf oc "u%a" print_intsize isz
  | PTbool -> fprintf oc "bool"
  | PTagg -> fprintf oc "agg"
  | PTptr -> fprintf oc "ptr"
  | PTref -> fprintf oc "ref"
  | PTaddr asz -> fprintf oc "a%a" print_addrsize asz
  | PTfloat fsz -> fprintf oc "f%a" print_floatsize fsz
and print_intsize (oc: out_channel) (isz: intsize) =
  match isz with
  | I8 -> fprintf oc "8"
  | I16 -> fprintf oc "16"
  | I32 -> fprintf oc "32"
  | I64 -> fprintf oc "64"
and print_addrsize (oc: out_channel) (asz: addrsize) =
  match asz with
  | A32 -> fprintf oc "32"
  | A64 -> fprintf oc "64"
and print_floatsize (oc: out_channel) (fsz: floatsize) =
  match fsz with
  | F32 -> fprintf oc "32"
  | F64 -> fprintf oc "64"

let rec print_typespec (oc: out_channel) (ts: typespec) =
  match ts with
  | TSprim pt ->
     print_prim_type oc pt
  | TSpointer ts ->
     fprintf oc "<* %a>" print_typespec ts
  | TSarray (ts, oi) ->
     fprintf oc "<[%a] %a>" print_intInfo_option oi print_typespec ts
  | TSfunction (tsl, ts) ->
     fprintf oc "<func (%a) %a>" print_typespeclist tsl print_typespec ts
  | TSglobal id ->
     fprintf oc "<$%s>" id
  | TSlocal id ->
     fprintf oc "<%%%s>" id
and print_typespeclist (oc: out_channel) (tsl: typespeclist) =
  match tsl with
  | TSnil -> ()
  | TScons (ts, tsl) ->
     fprintf oc "%a, %a" print_typespec ts print_typespeclist tsl

let rec print_coq_type (oc: out_channel) (t: coq_type) =
  match t with
  | Tprim pt ->
     print_prim_type oc pt
  | Tpointer ts ->
     fprintf oc "<* %a>" print_typespec ts
  | Tarray (ts, oi) ->
     fprintf oc "<[%a] %a>" print_intInfo_option oi print_typespec ts
  | Tfunction (tsl, ts) ->
     fprintf oc "<func (%a) %a>" print_typespeclist tsl print_typespec ts
  | Tstruct mv ->
     fprintf oc "<struct {%a}>" print_membervars mv
  | Tunion mv ->
     fprintf oc "<union {%a}>" print_membervars mv
  | Tclass (oid, idl, mv, mf) ->
     fprintf oc "<class <%a> {%a%a%a}>" print_id_option oid print_membervars mv print_memberfuncs mf print_type_id_list idl
  | Tinterface (idl, mv, mf) ->
     fprintf oc "<interface {%a%a%a}>" print_membervars mv print_memberfuncs mf print_type_id_list idl
  | Tglobal id ->
     fprintf oc "<$%s>" id
  | Tlocal id ->
     fprintf oc "<%%%s>" id
and print_typespeclist (oc: out_channel) (tsl: typespeclist) =
  match tsl with
  | TSnil -> ()
  | TScons (ts, tsl) ->
     fprintf oc "%a, %a" print_typespec ts print_typespeclist tsl
and print_membervars (oc: out_channel) (mv: membervars) =
  match mv with
  | MVnil -> ()
  | MVcons (id, ts, mal, mv, loc) ->
     fprintf oc "\n\t@%s %a %a,%a" id print_typespec ts print_membervar_attr_list mal print_membervars mv
and print_membervar_attr_list (oc: out_channel) (mal: membervar_attr list) =
  match mal with
  | [] -> ()
  | ma :: mal ->
     fprintf oc "%a %a" print_membervar_attr ma print_membervar_attr_list mal
and print_memberfuncs (oc: out_channel) (mf: memberfuncs) =
  match mf with
  | MFnil -> ()
  | MFcons (id1, id2, tsl, ts, fal, mf, loc) ->
     fprintf oc "\n\t&%s &%s %a (%a) %a,%a" id1 id2 print_func_attr_list fal print_typespeclist tsl print_typespec ts print_memberfuncs mf
and print_func_attr_list (oc: out_channel) (fal: func_attr list) =
  match fal with
  | [] -> ()
  | fa :: fal ->
     fprintf oc "%a %a" print_func_attr fa print_func_attr_list fal
and print_type_id_list (oc: out_channel) (idl: ident list) =
  match idl with
  | [] -> ()
  | id :: idl ->
     fprintf oc "\n\t$%s,%a" id print_type_id_list idl

let print_reg_id (oc: out_channel) (rid: reg_id) =
  match rid with
  | RI_pseudo i -> fprintf oc "%%%a" print_intInfo i
  | RI_thrownval -> fprintf oc "%%%%thrownval"

let print_label (oc: out_channel) (lbl: label) =
  fprintf oc "@%s" lbl

let print_floatInfo (oc: out_channel) (f: floatInfo) =
  let neg_sign = if f.coq_FI_isNegative then "-" else "" in
  let hex_sign = if f.coq_FI_isHex then "0x" else "" in
  let intpart = match f.coq_FI_integer with Some s -> s | None -> "0" in
  let fraction = match f.coq_FI_fraction with Some s -> s | None -> "0" in
  let exp_sign = if f.coq_FI_isHex then "p" else "e" in
  let exponent = match f.coq_FI_exponent with Some s -> exp_sign ^ s | None -> "" in
  let suffix = match f.coq_FI_suffix with Some s -> s | None -> "" in
  fprintf oc "%s%s%s.%s%s%s" neg_sign hex_sign intpart fraction exponent suffix

let print_constant (oc: out_channel) (c: constant) =
  match c with
  | C_int i -> print_intInfo oc i
  | C_float f -> print_floatInfo oc f

let print_unary_operation (oc: out_channel) (uop: unary_operation) =
  match uop with
  | O_abs -> fprintf oc "abs"
  | O_bnot -> fprintf oc "bnot"
  | O_lnot -> fprintf oc "lnot"
  | O_neg -> fprintf oc "neg"
  | O_recip -> fprintf oc "recip"
  | O_sext b -> fprintf oc "sext %a" print_intInfo b
  | O_zext b -> fprintf oc "zext %a" print_intInfo b
  | O_sqrt -> fprintf oc "sqrt"

let print_binary_operation (oc: out_channel) (bop: binary_operation) =
  match bop with
  | O_add -> fprintf oc "add"
  | O_ashr -> fprintf oc "ashr"
  | O_band -> fprintf oc "band"
  | O_bior -> fprintf oc "bior"
  | O_bxor -> fprintf oc "bxor"
  | O_cmp pt -> fprintf oc "cmp %a" print_prim_type pt
  | O_cmpg pt -> fprintf oc "cmpg %a" print_prim_type pt
  | O_cmpl pt -> fprintf oc "cmpl %a" print_prim_type pt
  | O_div -> fprintf oc "div"
  | O_eq pt -> fprintf oc "eq %a" print_prim_type pt
  | O_ge pt -> fprintf oc "ge %a" print_prim_type pt
  | O_gt pt -> fprintf oc "gt %a" print_prim_type pt
  | O_land -> fprintf oc "land"
  | O_lior -> fprintf oc "lior"
  | O_le pt -> fprintf oc "le %a" print_prim_type pt
  | O_lshr -> fprintf oc "lshr"
  | O_lt pt -> fprintf oc "lt %a" print_prim_type pt
  | O_max -> fprintf oc "max"
  | O_min -> fprintf oc "min"
  | O_mul -> fprintf oc "mul"
  | O_ne pt -> fprintf oc "ne %a" print_prim_type pt
  | O_rem -> fprintf oc "rem"
  | O_shl -> fprintf oc "shl"
  | O_sub -> fprintf oc "sub"

let rec print_expr (oc: out_channel) (e: expr) =
  match e with
  | E_dread (pt, vid, ofi) ->
     fprintf oc "dread %a %a %a" print_prim_type pt print_var_id vid print_intInfo_option ofi
  | E_regread (pt, rid) ->
     fprintf oc "regread %a %a" print_prim_type pt print_reg_id rid
  | E_iread (pt, ts, ofi, e) ->
     fprintf oc "iread %a %a %a (%a)" print_prim_type pt print_typespec ts print_intInfo_option ofi print_expr e
  | E_addrof (pt, vid, ofi) ->
     fprintf oc "addrof %a %a %a" print_prim_type pt print_var_id vid print_intInfo_option ofi
  | E_addroffunc (pt, id) ->
     fprintf oc "addroffunc %a &%s" print_prim_type pt id
  | E_constval (pt, c) ->
     fprintf oc "constval %a %a" print_prim_type pt print_constant c
  | E_sizeoftype (pt, ts) ->
     fprintf oc "sizeoftype %a %a" print_prim_type pt print_typespec ts
  | E_unary (uop, pt, e) ->
     fprintf oc "%a %a (%a)" print_unary_operation uop print_prim_type pt print_expr e
  | E_iaddrof (pt, ts, ofi, e) ->
     fprintf oc "iaddrof %a %a %a (%a)" print_prim_type pt print_typespec ts print_intInfo_option ofi print_expr e
  | E_ceil (pt1, pt2, e) ->
     fprintf oc "ceil %a %a (%a)" print_prim_type pt1 print_prim_type pt2 print_expr e
  | E_cvt (pt1, pt2, e) ->
     fprintf oc "cvt %a %a (%a)" print_prim_type pt1 print_prim_type pt2 print_expr e
  | E_floor (pt1, pt2, e) ->
     fprintf oc "floor %a %a (%a)" print_prim_type pt1 print_prim_type pt2 print_expr e
  | E_retype (pt, ts, e) ->
     fprintf oc "retype %a %a (%a)" print_prim_type pt print_typespec ts print_expr e
  | E_trunc (pt1, pt2, e) ->
     fprintf oc "trunc %a %a (%a)" print_prim_type pt1 print_prim_type pt2 print_expr e
  | E_binary (bop, pt, e1, e2) ->
     fprintf oc "%a %a (%a, %a)" print_binary_operation bop print_prim_type pt print_expr e1 print_expr e2
  | E_cand (pt, e1, e2) ->
     fprintf oc "cand %a (%a, %a)" print_prim_type pt print_expr e1 print_expr e2
  | E_cior (pt, e1, e2) ->
     fprintf oc "cior %a (%a, %a)" print_prim_type pt print_expr e1 print_expr e2
  | E_select (pt, e1, e2, e3) ->
     fprintf oc "select %a (%a, %a, %a)" print_prim_type pt print_expr e1 print_expr e2 print_expr e3
  | E_array (i, pt, ts, el) ->
     fprintf oc "array %a %a %a (%a)" print_intInfo i print_prim_type pt print_typespec ts print_exprlist el
and print_exprlist (oc: out_channel) (el: exprlist) =
  match el with
  | E_nil -> ()
  | E_cons (e, el) ->
     fprintf oc "%a, %a" print_expr e print_exprlist el

let print_ext_expr (oc: out_channel) (ee: ext_expr) =
  match ee with
  | EE_pure e -> print_expr oc e
  | EE_malloc (pt, e) -> fprintf oc "malloc %a (%a)" print_prim_type pt print_expr e
  | EE_gcmalloc (pt, ts) -> fprintf oc "gcmalloc %a %a" print_prim_type pt print_typespec ts
  | EE_gcmallocjarray (pt, ts, e) -> fprintf oc "gcmallocjarray %a %a (%a)" print_prim_type pt print_typespec ts print_expr e
  | EE_gcpermalloc (pt, ts) -> fprintf oc "gcpermalloc %a %a" print_prim_type pt print_typespec ts

let rec print_statement (oc: out_channel) (s: statement) =
  match s with
  | S_skip loc ->
     fprintf oc "skip"
  | S_dassign (vid, ofi, ee, loc) ->
     fprintf oc "dassign %a %a (%a)" print_var_id vid print_intInfo_option ofi print_ext_expr ee
  | S_iassign (ts, ofi, e, ee, loc) ->
     fprintf oc "iassign %a %a (%a) (%a)" print_typespec ts print_intInfo_option ofi print_expr e print_ext_expr ee
  | S_regassign (pt, rid, ee, loc) ->
     fprintf oc "regassign %a %a (%a)" print_prim_type pt print_reg_id rid print_ext_expr ee
  | S_seq (s1, s2) ->
     fprintf oc "%a\n%a" print_statement s1 print_statement s2
  | S_label (lbl, s, loc) ->
     fprintf oc "%a:\t%a" print_label lbl print_statement s
  | S_if (e, s1, s2, loc) ->
     fprintf oc "if (%a) {\n%a\n} else {\n%a\n}" print_expr e print_statement s1 print_statement s2
  | S_while (e, s, loc) ->
     fprintf oc "while (%a) {\n%a\n}" print_expr e print_statement s
  | S_goto (lbl, loc) ->
     fprintf oc "goto %a" print_label lbl
  | S_return (el, loc) ->
     fprintf oc "return (%a)" print_exprlist el
  | S_switch (e, lbl, l, loc) ->
     fprintf oc "switch (%a) %a {\n%a}" print_expr e print_label lbl print_switch_table l
  | S_callassigned (id, el, l, loc) ->
     fprintf oc "callassigned &%s (%a) { %a }" id print_exprlist el print_assign_list l
  | S_icallassigned (el, l, loc) ->
     fprintf oc "icallassigned (%a) { %a }" print_exprlist el print_assign_list l
  | S_virtualcallassigned (id1, id2, el, l, loc) ->
     fprintf oc "virtualcallassigned $%s &%s (%a) { %a }" id1 id2 print_exprlist el print_assign_list l
  | S_interfacecallassigned (id1, id2, el, l, loc) ->
     fprintf oc "interfacecallassigned $%s &%s (%a) { %a }" id1 id2 print_exprlist el print_assign_list l
  | S_javatry (ll, s, loc) ->
     fprintf oc "javatry {%a} {\n%a\n}" print_label_list ll print_statement s
  | S_throw (e, loc) ->
     fprintf oc "throw (%a)" print_expr e
  | S_javacatch (lbl, tsl, loc) ->
     fprintf oc "%a:\tjavacatch (%a)" print_label lbl print_typespec_list tsl
  | S_decref (e, loc) ->
     fprintf oc "decref (%a)" print_expr e
  | S_free (e, loc) ->
     fprintf oc "free (%a)" print_expr e
  | S_incref (e, loc) ->
     fprintf oc "incref (%a)" print_expr e
  | S_eval (e, loc) ->
     fprintf oc "eval (%a)" print_expr e
and print_switch_table (oc: out_channel) (l: ((intInfo * label) * location) list) =
  match l with
  | [] -> ()
  | ((i, lbl), loc) :: l ->
     fprintf oc "%a: goto %a\n%a" print_intInfo i print_label lbl print_switch_table l
and print_assign_list (oc: out_channel) (l: ((var_id * field_id option) * location) list) =
  match l with
  | [] -> ()
  | ((vid, ofi), loc) :: l ->
     fprintf oc "dassign %a %a, %a" print_var_id vid print_intInfo_option ofi print_assign_list l
and print_label_list (oc: out_channel) (l: label list) =
  match l with
  | [] -> ()
  | lbl :: l ->
     fprintf oc "%a, %a" print_label lbl print_label_list l
and print_typespec_list (oc: out_channel) (tsl: typespec list) =
  match tsl with
  | [] -> ()
  | ts :: tsl ->
     fprintf oc "%a, %a" print_typespec ts print_typespec_list tsl

let rec print_var_def (oc: out_channel) (vd: var_def) =
  let (ts, tal) = vd in
  fprintf oc "%a %a" print_typespec ts print_type_attr_list tal
and print_type_attr_list (oc: out_channel) (tal: type_attr list) =
  match tal with
  | [] -> ()
  | ta :: tal ->
     fprintf oc "%a %a" print_type_attr ta print_type_attr_list tal

let rec print_function_prototype (oc: out_channel) (fp: function_prototype) =
  fprintf oc "%a (%a) %a" print_func_attr_list fp.fun_attr print_function_params fp.fun_params print_typespec fp.fun_returns
and print_function_params (oc: out_channel) (l: (ident * typespec) list) =
  match l with
  | [] -> ()
  | (id, ts) :: l ->
     fprintf oc "var %%%s %a, %a" id print_typespec ts print_function_params l

let rec print_localvar_declaration_list (oc: out_channel) (l: (ident * var_def) list) =
  match l with
  | [] -> ()
  | (id, vd) :: l ->
     fprintf oc "var %%%s %a\n%a" id print_var_def vd print_localvar_declaration_list l

let rec print_localtype_declaration_list (oc: out_channel) (l: (ident * coq_type) list) =
  match l with
  | [] -> ()
  | (id, t) :: l ->
     fprintf oc "var %%%s %a\n%a" id print_coq_type t print_localtype_declaration_list l

let rec print_preg_declaration_list (oc: out_channel) (l: (intInfo * prim_type) list) =
  match l with
  | [] -> ()
  | (i, pt) :: l ->
     fprintf oc "reg %%%a %a\n%a" print_intInfo i print_prim_type pt print_preg_declaration_list l

let print_function_body (oc: out_channel) (fb: function_body) =
  fprintf oc "{\n%a\n%a\n%a\n%a\n}"
    print_localvar_declaration_list (List.map fst fb.fun_vars)
    print_localtype_declaration_list (List.map fst fb.fun_types)
    print_preg_declaration_list (List.map fst fb.fun_pregs)
    print_statement (fb.fun_statement)

let print_coq_function (oc: out_channel) (f: coq_function) =
  match f with
  | fp, Some fb ->
     fprintf oc "%a %a" print_function_prototype fp print_function_body fb
  | fp, None ->
     print_function_prototype oc fp

let print_class_attr (oc: out_channel) (ca: class_attr) =
  match ca with
  | CA_access am -> print_access_modifier oc am
  | CA_abstract -> fprintf oc "abstract"
  | CA_final -> fprintf oc "final"

let rec print_class_attr_list (oc: out_channel) (cal: class_attr list) =
  match cal with
  | [] -> ()
  | ca :: cal ->
     fprintf oc "%a %a" print_class_attr ca print_class_attr_list cal

let rec print_globalvar_declaration_list (oc: out_channel) (l: (ident * var_def) list) =
  match l with
  | [] -> ()
  | (id, vd) :: l ->
     fprintf oc "var $%s %a\n%a" id print_var_def vd print_globalvar_declaration_list l

let rec print_type_declaration_list (oc: out_channel) (l: (ident * coq_type) list) =
  match l with
  | [] -> ()
  | (id, t) :: l ->
     fprintf oc "type $%s %a\n%a" id print_coq_type t print_type_declaration_list l

let rec print_function_declaration_list (oc: out_channel) (l: (ident * coq_function) list) =
  match l with
  | [] -> ()
  | (id, f) :: l ->
     fprintf oc "func &%s %a\n%a" id print_coq_function f print_function_declaration_list l

let rec print_javaclass_declaration_list (oc: out_channel) (l: ((ident * ident) * class_attr list) list) =
  match l with
  | [] -> ()
  | ((id1, id2), cal) :: l ->
     fprintf oc "javaclass $%s <$%s> %a\n%a" id1 id2 print_class_attr_list cal print_javaclass_declaration_list l

let rec print_javainterface_declaration_list (oc: out_channel) (l: ((ident * ident) * class_attr list) list) =
  match l with
  | [] -> ()
  | ((id1, id2), cal) :: l ->
     fprintf oc "javainterface $%s <$%s> %a\n%a" id1 id2 print_class_attr_list cal print_javainterface_declaration_list l

let print_entryfunc (oc: out_channel) (id: ident) =
  fprintf oc "entryfunc &%s" id

let rec print_program (oc: out_channel) (p: MapleInter.program) =
  fprintf oc "%a\n%a\n%a\n%a\n%a\n%a" print_entryfunc (fst p.prog_main) print_type_declaration_list (List.map fst p.prog_types) print_javaclass_declaration_list (List.map fst p.prog_javaclass) print_javainterface_declaration_list (List.map fst p.prog_javainterface) print_globalvar_declaration_list (List.map fst p.prog_vars) print_function_declaration_list (List.map fst p.prog_funcs)
