(*Require Import Coqlib.*)
Require Import Errors.
(*Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.*)
Require Import MapleLightOp.
Require Import MapleLightTypes.
Require Import MapleLight.

(*Set Implicit Arguments.*)
Local Open Scope error_monad_scope.

(* OCaml's string type. *)
Parameter string : Type.
(* OCaml's int type. *)
Parameter location: Type.

Definition ident := string.

(*Inductive global_id :=
  | Global: ident -> global_id.

Inductive local_id :=
  | Local: ident -> local_id.*)

Inductive var_id :=
  | VI_global : ident -> var_id
  | VI_local : ident -> var_id.

(*Inductive membervar_id :=
  | MV: ident -> membervar_id.

Inductive func_id :=
  | Func : ident -> func_id.*)

Record intInfo := {
  II_source: string;
  II_isNegative: bool;
  II_isHex: bool;
  II_integer: string;
}.

Inductive type_attr :=
  | VA_align: intInfo -> type_attr.

Inductive membervar_attr :=
  | MVA_access: access_modifier -> membervar_attr
  | MVA_align: intInfo -> membervar_attr.

Inductive func_attr :=
  | FA_access: access_modifier -> func_attr
  | FA_abstract
  | FA_final
  | FA_static
  | FA_virtual
  | FA_constructor.

Inductive typespec : Type :=
  | TSprim: prim_type -> typespec
  | TSpointer: typespec -> typespec
  | TSarray: typespec -> option intInfo -> typespec
  | TSfunction: typespeclist -> typespec -> typespec
  | TSglobal: ident -> typespec
  | TSlocal: ident -> typespec
with typespeclist : Type :=
  | TSnil: typespeclist
  | TScons: typespec -> typespeclist -> typespeclist.

Inductive type : Type :=
  | Tprim: prim_type -> type
  | Tpointer: typespec -> type
  | Tarray: typespec -> option intInfo -> type
  | Tfunction: typespeclist -> typespec -> type
  | Tstruct: membervars -> type
  | Tunion: membervars -> type
  | Tclass: option ident -> list ident -> membervars -> memberfuncs -> (*class_attr ->*) type
  | Tinterface: list ident -> membervars -> memberfuncs -> (*interface_attr ->*) type
  | Tglobal: ident -> type
  | Tlocal: ident -> type
with membervars : Type :=
  | MVnil: membervars
  | MVcons: ident -> typespec -> list membervar_attr -> membervars -> location -> membervars
with memberfuncs : Type :=
  | MFnil : memberfuncs
  | MFcons: ident -> typespeclist -> typespec -> list func_attr -> memberfuncs -> location -> memberfuncs.

Definition field_id := intInfo.

(*Inductive preg_id :=
  | Preg : ident -> preg_id.*)

Inductive reg_id :=
  | RI_pseudo : intInfo -> reg_id
  (*| SP*)
  (*| FP*)
  (*| GP*)
  (*| PC*)
  | RI_thrownval
  (*| Retval: ident -> reg_id*).

(*Theorem reg_id_dec : forall v1 v2: reg_id, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.*)

Definition label := ident.

(*Theorem label_dec : forall v1 v2: label, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.*)

Definition bsize := intInfo.

Record floatInfo := {
  FI_source: string;
  FI_isNegative: bool;
  FI_isHex: bool;
  FI_integer: option string;
  FI_fraction: option string;
  FI_exponent: option string;
  FI_suffix: option string;
}.

Inductive constant :=
  | C_int: intInfo -> constant
  | C_float: floatInfo -> constant
  (*| C_complex: complex -> constant*).

Inductive unary_operation :=
    O_abs : unary_operation
  | O_bnot : unary_operation
  | O_lnot : unary_operation
  | O_neg : unary_operation
  | O_recip : unary_operation
  | O_sext : bsize -> unary_operation
  | O_zext : bsize -> unary_operation
  | O_sqrt : unary_operation.

(* Pure expressions *)

Inductive expr :=
(* storage read expr *)
  | E_dread : prim_type -> var_id -> option field_id -> expr
  | E_regread : prim_type -> reg_id -> expr
  | E_iread : prim_type -> typespec -> option field_id -> expr -> expr
  (*| E_ireadoff : prim_type -> Boffset -> expr -> expr*)
  (*| E_ireadfpoff : prim_type -> Boffset -> expr -> expr*)
(* leaf expr *)
  | E_addrof : prim_type -> var_id -> option field_id -> expr
  (*| E_addroflable : prim_type -> label -> expr*)
  | E_addroffunc : prim_type -> ident -> expr
  (*| E_conststr : prim_type -> string_literal -> expr*)
  (*| E_conststr16 : prim_type -> string_literal -> expr*)
  | E_constval : prim_type -> constant -> expr
  | E_sizeoftype : prim_type -> typespec -> expr
(* unary expr *)
  | E_unary : unary_operation -> prim_type -> expr -> expr
  | E_iaddrof : prim_type -> typespec -> option field_id -> expr -> expr
(* type conversion expr *)
  | E_ceil : prim_type -> prim_type -> expr -> expr
  | E_cvt : prim_type -> prim_type -> expr -> expr
  | E_floor : prim_type -> prim_type -> expr -> expr
  | E_retype : prim_type -> typespec -> expr -> expr
  (*| E_round : prim_type -> prim_type -> expr -> expr*)
  | E_trunc : prim_type -> prim_type -> expr -> expr
(* binary expr *)
  | E_binary : binary_operation -> prim_type -> expr -> expr -> expr
  | E_cand : prim_type -> expr -> expr -> expr
  | E_cior : prim_type -> expr -> expr -> expr
(* ternary expr *)
  | E_select : prim_type -> expr -> expr -> expr -> expr
(* N-ary expr *)
  | E_array : intInfo -> prim_type -> typespec -> exprlist -> expr
  (*| E_intrinsicop : prim_type -> intrinsic_func_id -> list expr -> expr*)
  (*| E_intrinsicopwithtype : prim_type -> typespec -> intrinsic_func_id -> exprlist -> expr*)
with exprlist :=
  | E_nil : exprlist
  | E_cons : expr -> exprlist -> exprlist.

(* Exprs with side effects *)

Inductive ext_expr :=
(* pure expr *)
  | EE_pure : expr -> ext_expr
(* memory allocation expr *)
  (*| E_alloca : prim_type -> expr -> ext_expr*)
  | EE_malloc : prim_type -> expr -> ext_expr
  | EE_gcmalloc : prim_type -> typespec -> ext_expr
  | EE_gcmallocjarray : prim_type -> typespec -> expr -> ext_expr
  | EE_gcpermalloc : prim_type -> typespec -> ext_expr
  (*| E_stackmalloc : prim_type -> typespec -> ext_expr*)
  (*| E_stackmallocjarray : prim_type -> typespec -> expr -> ext_expr*).

Inductive statement :=
  | S_skip (loc: location)
(* storage assignment *)
  | S_dassign (v: var_id) (f: option field_id) (rhs_expr: ext_expr) (loc: location)
  | S_iassign (t: typespec) (f: option field_id) (addr_expr: expr) (rhs_expr: ext_expr) (loc: location)
  (*| S_iassignoff (t: prim_type) (Bofs: Boffset) (addr_expr: expr) (rhs_expr: ext_expr)*)
  (*| S_iassignfpoff (t: prim_type) (Bofs: Boffset) (rhs_expr: ext_expr)*)
  | S_regassign (t: prim_type) (r: reg_id) (rhs_expr: ext_expr) (loc: location)
  (* hierarchical control flow *)
  | S_seq (first_part second_part: statement)
  | S_label (lbl: label) (s: statement) (loc: location)
  (*| S_doloop (do_var: ident) (start_expr cont_expr incr_amt: expr) (body_stmts: statement)*)
  (*| S_dowhile (body_stmts: statement) (cond_expr: expr)*)
  (*| S_foreachelem (elem_var: ident) (collection_var: var_id) (body_stmts: statement)*)
  | S_if (cond_expr: expr) (then_part else_part: statement) (loc: location)
  | S_while (cond_expr: expr) (body_stmts: statement) (loc: location)
(* falt control flow statements *)
  | S_brfalse (l: label) (opnd: expr) (loc: location)
  | S_brtrue (l: label) (opnd: expr) (loc: location)
  | S_goto (l: label) (loc: location)
  (*| S_multiway (opnd: expr) (default_label: label) (label_table: list (expr * label))*)
  | S_return (retlist: exprlist) (loc: location)
  | S_switch (opnd: expr) (default_label: label) (label_table: list (intInfo * label * location)) (loc: location)
  (*| S_rangegoto (opnd: expr) (tag_offset: expr)(label_table: list (int * label))*)
  (*| S_indexgoto (opnd: expr) (jt: list label)*)
(* call statements *)
  (*| S_call (f: func_id) (opndlist: exprlist)*)
  (*| S_icall (f_ptr: expr) (opndlist: exprlist)*)
  (*| S_intrinsiccall (f: intrinsic_func_id) (opndlist: exprlist)*)
  (*| S_xintrinsiccall (user_intrinsiccall_index: expr) (opndlist: exprlist)*)
(* To do: callinstant *)
(* java call statements *)
  (*| S_virtualcall (c: ident) (f: ident) (obj_ptr: expr) (opndlist: exprlist)*)
  (*| S_superclasscall (c: ident) (f: ident) (obj_ptr: expr) (opndlist: exprlist)*)
  (*| S_interfacecall (c: ident) (f: ident) (obj_ptr: expr) (opndlist: exprlist)*)
(* To do: virtuallcallinstant *)
(* To do: superclasscallinstant *)
(* To do: interfacecallinstant *)
  | S_callassigned (f: ident) (opndlist: exprlist) (assignlist: list (var_id * option field_id * location)) (loc: location)
(* To do: callinstantassigned *)
  | S_icallassigned (opndlist: exprlist) (assignlist: list (var_id * option field_id * location)) (loc: location)
  (*| S_intrinsiccallassigned (f: intrinsic_func_id) (opndlist: exprlist) (assignlist: list (var_id * field_id))*)
(* To do: intrinsiccallwithtypeassigned *)
  (*| S_xintrinsiccallassigned (user_intrinsiccall_index: expr) (opndlist: exprlist) (assignlist: list (var_id * field_id))*)
  | S_virtualcallassigned (f: ident) (opndlist: exprlist) (assignlist: list (var_id * option field_id * location)) (loc: location)
(* To do: virtualcallinstantassigned *)
  (*| S_superclasscallassigned (c: ident) (f: ident) (obj_ptr: expr) (opndlist: exprlist) (assignlist: list (var_id * field_id))*)
(* To do: superclasscallinstantassigned *)
  | S_interfacecallassigned (f: ident) (opndlist: exprlist) (assignlist: list (var_id * option field_id * location)) (loc: location)
(* To do: interfacecallinstantassigned *)
(* exception handling *)
  (*| S_jstry (fl hl: label) (s: statement)*)
  | S_javatry (hl: list label) (s: statement) (loc: location)
  (*| S_cpptry (hl: list label) (s: statement)*)
  | S_throw (opnd: expr) (loc: location)
  (*| S_jscatch (s: statement)*)
  | S_javacatch (hl: label) (tl: list typespec) (loc: location)
  (*| S_cppcatch (hl: label) (tl: list typespec)*)
  (*| S_finally (fl: label) (s: statement)*)
  (*| S_cleanuptry*)
  (*| S_endtry (l: label)*)
  (*| S_gosub (fl: label)*)
  (*| S_retsub*)
(* memory deallocation *)
  | S_decref (opnd: expr) (loc: location)
  (*| S_decrefreset (opnd: expr)*)
  | S_free (opnd: expr) (loc: location)
  | S_incref (opnd: expr) (loc: location)
(* other statements *)
  (*| S_assertge (opnd0 opnd1: expr)*)
  (*| S_assertlt (opnd0 opnd1: expr)*)
  (*| S_assertnonnull (opnd: expr)*)
  | S_eval (opnd: expr) (loc: location)
  (*| S_membaracquire*)
  (*| S_membarrelease*)
  (*| S_membarfull*)
  (*| S_syncenter (opnd: expr)*)
  (*| S_syncexit (opnd: expr)*).

Definition var_def := (typespec * list type_attr) % type.

Record function_prototype : Type := {
  fun_attr: list func_attr;
  fun_returns: typespec;
  fun_params: list (ident * typespec);
}.

Inductive local_declaration :=
  | LD_var: ident -> var_def -> location -> local_declaration
  | LD_type: ident -> type -> location -> local_declaration
  | LD_preg: intInfo -> prim_type -> location -> local_declaration.

Record function_body : Type := {
  fun_localdecl: list local_declaration;
  fun_statement: statement;
}.

Definition function := (function_prototype * option function_body) % type.

Definition concrete_function := (function_prototype * function_body) % type.

Inductive class_attr :=
  | CA_access: access_modifier -> class_attr
  | CA_abstract
  | CA_final.

Inductive global_declaration :=
  | GD_var: ident -> var_def -> location -> global_declaration
  | GD_type: ident -> type -> location -> global_declaration
  | GD_func: ident -> function -> location -> global_declaration
  | GD_javaclass: ident -> ident -> list class_attr -> location -> global_declaration
  | GD_javainterface: ident -> ident -> list class_attr -> location -> global_declaration
  | GD_entryfunc: ident -> location -> global_declaration.

Definition program := list global_declaration.
