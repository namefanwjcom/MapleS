open Printf
open BinNums
open AST
open Floats
open Integers
open Values
open Camlcoq
open MapleLightTypes
open MapleLightOp
open MapleLight

let print_positive (oc: out_channel) (p: positive) =
  fprintf oc "%d" (P.to_int p)

let print_coq_N (oc: out_channel) (n: coq_N) =
  fprintf oc "%d" (N.to_int n)

let print_coq_Z (oc: out_channel) (z: coq_Z) =
  fprintf oc "%d" (Z.to_int z)

let print_ident (oc: out_channel) (id: ident) =
  print_positive oc id

let print_id_option (oc: out_channel) (oid: ident option) =
  match oid with
  | Some id -> fprintf oc "%a" print_ident id
  | None -> ()

let print_var_id (oc: out_channel) (vid: var_id) =
  match vid with
  | V_global id -> fprintf oc "$%a" print_ident id
  | V_local id -> fprintf oc "%%%a" print_ident id

let print_field_id (oc: out_channel) (fi: field_id) =
  print_coq_N oc fi

let print_coq_N_option (oc: out_channel) (oi: coq_N option) =
  match oi with
  | Some i -> print_coq_N oc i
  | None -> ()

let print_type_attr (oc: out_channel) (ta: type_attr) = print_coq_N_option oc ta

let print_access_modifier (oc: out_channel) (am: access_modifier) =
  match am with
  | AM_friendly -> fprintf oc "friendly"
  | AM_public -> fprintf oc "public"
  | AM_private -> fprintf oc "private"
  | AM_protected -> fprintf oc "protected"

let print_field_attr (oc: out_channel) (fa: field_attr) =
  print_access_modifier oc fa

let print_func_attr (oc: out_channel) (fa: func_attr) =
  let abstract_flag = if fa.fa_abstract then " abstract" else "" in
  let final_flag = if fa.fa_final then " final" else "" in
  let static_flag = if fa.fa_static then " static" else "" in
  let virtual_flag = if fa.fa_virtual then " virtual" else "" in
  let constructor_flag = if fa.fa_constructor then " constructor" else "" in
  fprintf oc "%a%s%s%s%s%s" print_access_modifier fa.fa_access abstract_flag final_flag static_flag virtual_flag constructor_flag

let print_class_attr (oc: out_channel) (ca: class_attr) =
  let abstract_flag = if ca.ca_abstract then " abstract" else "" in
  let final_flag = if ca.ca_final then " final" else "" in
  fprintf oc "%a%s%s" print_access_modifier ca.ca_access abstract_flag final_flag

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

let rec print_coq_type (oc: out_channel) (t: coq_type) =
  match t with
  | Tprim pt ->
     print_prim_type oc pt
  | Tpointer t ->
     fprintf oc "<* %a>" print_coq_type t
  | Tarray (t, z) ->
     fprintf oc "<[%a] %a>" print_coq_Z z print_coq_type t
  | Tfunction (tl1, tl2) ->
     fprintf oc "<func (%a) %a>" print_typelist tl1 print_typelist tl2
  | Tcomposite id ->
     fprintf oc "<$%a>" print_ident id
and print_typelist (oc: out_channel) (tl: typelist) =
  match tl with
  | Tnil -> ()
  | Tcons (t, tl) ->
     fprintf oc "%a %a" print_coq_type t print_typelist tl

let rec print_composite_definition (oc: out_channel) (cd: composite_definition) =
  match cd with
  | CDstruct mv ->
     fprintf oc "<struct {%a}>" print_membervars mv
  | CDunion mv ->
     fprintf oc "<union {%a}>" print_membervars mv
  | CDclass (oid, idl, mv, mf, ca) ->
     fprintf oc "<class <%a> {%a%a%a} %a>" print_id_option oid print_membervars mv print_memberfuncs mf print_ident_list idl print_class_attr ca
  | CDinterface (idl, mv, mf, ca) ->
     fprintf oc "<interface {%a%a%a} %a>" print_membervars mv print_memberfuncs mf print_ident_list idl print_class_attr ca
and print_membervars (oc: out_channel) (mv: membervars) =
  match mv with
  | MVnil -> ()
  | MVcons (id, t, ta, fa, mv) ->
     fprintf oc "\n\t@%a %a %a %a,%a" print_ident id print_coq_type t print_type_attr ta print_field_attr fa print_membervars mv
and print_memberfuncs (oc: out_channel) (mf: memberfuncs) =
  match mf with
  | MFnil -> ()
  | MFcons (id1, id2, t, fa, mf) ->
     fprintf oc "\n\t&%a &%a %a %a,%a" print_ident id1 print_ident id2 print_func_attr fa print_coq_type t print_memberfuncs mf
and print_ident_list (oc: out_channel) (idl: ident list) =
  match idl with
  | [] -> ()
  | id :: idl ->
     fprintf oc "\n\t$%a,%a" print_ident id print_ident_list idl

let print_reg_id (oc: out_channel) (rid: reg_id) =
  match rid with
  | Preg i -> fprintf oc "%%%a" print_ident i
  | Thrownval -> fprintf oc "%%%%thrownval"

let print_label (oc: out_channel) (lbl: label) =
  fprintf oc "@%a" print_ident lbl

let print_int (oc: out_channel) (i: Int.int) =
  fprintf oc "%ld" (camlint_of_coqint i)

let print_int64 (oc: out_channel) (i: Int64.int) =
  fprintf oc "%Ld" (camlint64_of_coqint i)

let print_float (oc: out_channel) (f: float) =
  fprintf oc "%f" (camlfloat_of_coqfloat f)

let print_float32 (oc: out_channel) (f: float32) =
  fprintf oc "%f" (camlfloat_of_coqfloat32 f)

let print_coq_val (oc: out_channel) (c: constant) =
  match c with
  | C_int i -> print_int oc i
  | C_long l -> print_int64 oc l
  | C_float f -> print_float oc f
  | C_single s -> print_float32 oc s

let print_unary_operation (oc: out_channel) (uop: unary_operation) =
  match uop with
  | O_abs -> fprintf oc "abs"
  | O_bnot -> fprintf oc "bnot"
  | O_lnot -> fprintf oc "lnot"
  | O_neg -> fprintf oc "neg"
  | O_recip -> fprintf oc "recip"
  | O_sext b -> fprintf oc "sext %a" print_coq_N b
  | O_zext b -> fprintf oc "zext %a" print_coq_N b
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

let print_bool (oc: out_channel) (b: bool) =
  fprintf oc (if b then "true" else "false")

let rec print_expr (oc: out_channel) (e: expr) =
  match e with
  | E_dread (pt, vid, fi) ->
     fprintf oc "dread %a %a %a" print_prim_type pt print_var_id vid print_field_id fi
  | E_regread (pt, rid) ->
     fprintf oc "regread %a %a" print_prim_type pt print_reg_id rid
  | E_iread (pt, t, fi, e) ->
     fprintf oc "iread %a %a %a (%a)" print_prim_type pt print_coq_type t print_field_id fi print_expr e
  | E_addrof (pt, vid, fi) ->
     fprintf oc "addrof %a %a %a" print_prim_type pt print_var_id vid print_field_id fi
  | E_addroffunc (pt, id) ->
     fprintf oc "addroffunc %a &%a" print_prim_type pt print_ident id
  | E_constval (pt, c) ->
     fprintf oc "constval %a %a" print_prim_type pt print_coq_val c
  | E_sizeoftype (pt, t) ->
     fprintf oc "sizeoftype %a %a" print_prim_type pt print_coq_type t
  | E_unary (uop, pt, e) ->
     fprintf oc "%a %a (%a)" print_unary_operation uop print_prim_type pt print_expr e
  | E_iaddrof (pt, t, fi, e) ->
     fprintf oc "iaddrof %a %a %a (%a)" print_prim_type pt print_coq_type t print_field_id fi print_expr e
  | E_ceil (pt1, pt2, e) ->
     fprintf oc "ceil %a %a (%a)" print_prim_type pt1 print_prim_type pt2 print_expr e
  | E_cvt (pt1, pt2, e) ->
     fprintf oc "cvt %a %a (%a)" print_prim_type pt1 print_prim_type pt2 print_expr e
  | E_floor (pt1, pt2, e) ->
     fprintf oc "floor %a %a (%a)" print_prim_type pt1 print_prim_type pt2 print_expr e
  | E_retype (pt, t, e) ->
     fprintf oc "retype %a %a (%a)" print_prim_type pt print_coq_type t print_expr e
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
  | E_array (i, pt, t, el) ->
     fprintf oc "array %a %a %a (%a)" print_bool i print_prim_type pt print_coq_type t print_exprlist el
and print_exprlist (oc: out_channel) (el: exprlist) =
  match el with
  | E_nil -> ()
  | E_cons (e, el) ->
     fprintf oc "%a, %a" print_expr e print_exprlist el

let print_ext_expr (oc: out_channel) (ee: ext_expr) =
  match ee with
  | EE_pure e -> print_expr oc e
  | EE_malloc (pt, e) -> fprintf oc "malloc %a (%a)" print_prim_type pt print_expr e
  | EE_gcmalloc (pt, t) -> fprintf oc "gcmalloc %a %a" print_prim_type pt print_coq_type t
  | EE_gcmallocjarray (pt, t, e) -> fprintf oc "gcmallocjarray %a %a (%a)" print_prim_type pt print_coq_type t print_expr e
  | EE_gcpermalloc (pt, t) -> fprintf oc "gcpermalloc %a %a" print_prim_type pt print_coq_type t

let rec print_statement (oc: out_channel) (s: statement) =
  match s with
  | S_skip ->
     fprintf oc "skip"
  | S_dassign (vid, fi, ee) ->
     fprintf oc "dassign %a %a (%a)" print_var_id vid print_field_id fi print_ext_expr ee
  | S_iassign (t, fi, e, ee) ->
     fprintf oc "iassign %a %a (%a) (%a)" print_coq_type t print_field_id fi print_expr e print_ext_expr ee
  | S_regassign (pt, rid, ee) ->
     fprintf oc "regassign %a %a (%a)" print_prim_type pt print_reg_id rid print_ext_expr ee
  | S_seq (s1, s2) ->
     fprintf oc "%a\n%a" print_statement s1 print_statement s2
  | S_label (lbl, s) ->
     fprintf oc "%a:\t%a" print_label lbl print_statement s
  | S_if (e, s1, s2) ->
     fprintf oc "if (%a) {\n%a\n} else {\n%a\n}" print_expr e print_statement s1 print_statement s2
  | S_while (e, s) ->
     fprintf oc "while (%a) {\n%a\n}" print_expr e print_statement s
  | S_goto lbl ->
     fprintf oc "goto %a" print_label lbl
  | S_return el ->
     fprintf oc "return (%a)" print_exprlist el
  | S_switch (e, lbl, l) ->
     fprintf oc "switch (%a) %a {\n%a}" print_expr e print_label lbl print_switch_table l
  | S_callassigned (id, el, l) ->
     fprintf oc "callassigned &%a (%a) { %a }" print_ident id print_exprlist el print_assign_list l
  | S_icallassigned (e, el, l) ->
     fprintf oc "icallassigned (%a, %a) { %a }" print_expr e print_exprlist el print_assign_list l
  | S_virtualcallassigned (id1, id2, e, el, l) ->
     fprintf oc "virtualcallassigned $%a &%a (%a, %a) { %a }" print_ident id1 print_ident id2 print_expr e print_exprlist el print_assign_list l
  | S_interfacecallassigned (id1, id2, e, el, l) ->
     fprintf oc "interfacecallassigned $%a &%a (%a, %a) { %a }" print_ident id1 print_ident id2 print_expr e print_exprlist el print_assign_list l
  | S_javatry (ll, s) ->
     fprintf oc "javatry {%a} {\n%a\n}" print_label_list ll print_statement s
  | S_throw e ->
     fprintf oc "throw (%a)" print_expr e
  | S_javacatch (lbl, tsl) ->
     fprintf oc "%a:\tjavacatch (%a)" print_label lbl print_coq_type_list tsl
  | S_decref e ->
     fprintf oc "decref (%a)" print_expr e
  | S_free e ->
     fprintf oc "free (%a)" print_expr e
  | S_incref e ->
     fprintf oc "incref (%a)" print_expr e
  | S_eval e ->
     fprintf oc "eval (%a)" print_expr e
and print_switch_table (oc: out_channel) (l: (coq_Z * label) list) =
  match l with
  | [] -> ()
  | (i, lbl) :: l ->
     fprintf oc "%a: goto %a\n%a" print_coq_Z i print_label lbl print_switch_table l
and print_assign_list (oc: out_channel) (l: (var_id * field_id) list) =
  match l with
  | [] -> ()
  | (vid, fi) :: l ->
     fprintf oc "dassign %a %a, %a" print_var_id vid print_field_id fi print_assign_list l
and print_label_list (oc: out_channel) (l: label list) =
  match l with
  | [] -> ()
  | lbl :: l ->
     fprintf oc "%a, %a" print_label lbl print_label_list l
and print_coq_type_list (oc: out_channel) (tsl: coq_type list) =
  match tsl with
  | [] -> ()
  | ts :: tsl ->
     fprintf oc "%a, %a" print_coq_type ts print_coq_type_list tsl

let rec print_var_def (oc: out_channel) (vd: var_def) =
  let (t, (sc, ta)) = vd in
  fprintf oc "%a %a" print_coq_type t print_type_attr ta
and print_type_attr_list (oc: out_channel) (tal: type_attr list) =
  match tal with
  | [] -> ()
  | ta :: tal ->
     fprintf oc "%a %a" print_type_attr ta print_type_attr_list tal

let rec print_function_prototype (oc: out_channel) (fp: function_prototype) =
  fprintf oc "%a (%a) %a" print_func_attr fp.fun_attr print_function_params fp.fun_params print_coq_type_list fp.fun_returns
and print_function_params (oc: out_channel) (l: (ident * coq_type) list) =
  match l with
  | [] -> ()
  | (id, t) :: l ->
     fprintf oc "var %%%a %a, %a" print_ident id print_coq_type t print_function_params l

let rec print_localvar_declaration_list (oc: out_channel) (l: (ident * var_def) list) =
  match l with
  | [] -> ()
  | (id, vd) :: l ->
     fprintf oc "var %%%a %a\n%a" print_ident id print_var_def vd print_localvar_declaration_list l

let rec print_preg_declaration_list (oc: out_channel) (l: (ident * prim_type) list) =
  match l with
  | [] -> ()
  | (id, pt) :: l ->
     fprintf oc "reg %%%a %a\n%a" print_ident id print_prim_type pt print_preg_declaration_list l

let print_function_body (oc: out_channel) (fb: function_body) =
  fprintf oc "{\n%a\n%a\n%a\n}" print_localvar_declaration_list fb.fun_vars print_preg_declaration_list fb.fun_pregs print_statement fb.fun_statement

let print_coq_function (oc: out_channel) (f: coq_function) =
  match f with
  | fp, Some fb ->
     fprintf oc "%a %a" print_function_prototype fp print_function_body fb
  | fp, None ->
     print_function_prototype oc fp

let rec print_globalvar_declaration_list (oc: out_channel) (l: (ident * var_def) list) =
  match l with
  | [] -> ()
  | (id, vd) :: l ->
     fprintf oc "var $%a %a\n%a" print_ident id print_var_def vd print_globalvar_declaration_list l

let rec print_composite_definition_list (oc: out_channel) (l: (ident * composite_definition) list) =
  match l with
  | [] -> ()
  | (id, cd) :: l ->
     fprintf oc "type $%a %a\n%a" print_ident id print_composite_definition cd print_composite_definition_list l

let rec print_function_declaration_list (oc: out_channel) (l: (ident * coq_function) list) =
  match l with
  | [] -> ()
  | (id, f) :: l ->
     fprintf oc "func &%a %a\n%a" print_ident id print_coq_function f print_function_declaration_list l

let print_entryfunc (oc: out_channel) (id: ident) =
  fprintf oc "entryfunc &%a" print_ident id

let rec print_program (oc: out_channel) (p: MapleLight.program) =
  fprintf oc "%a\n%a\n%a\n%a" print_entryfunc p.prog_main print_composite_definition_list p.prog_comps print_globalvar_declaration_list p.prog_vars print_function_declaration_list p.prog_funcs
