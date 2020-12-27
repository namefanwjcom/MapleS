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
Require Import MapleAST.

(*Set Implicit Arguments.*)
Local Open Scope error_monad_scope.

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
  | MFcons: ident -> ident -> typespeclist -> typespec -> list func_attr -> memberfuncs -> location -> memberfuncs.

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
  | S_label (l: label) (s: statement) (loc: location)
  (*| S_doloop (do_var: ident) (start_expr cont_expr incr_amt: expr) (body_stmts: statement)*)
  (*| S_dowhile (body_stmts: statement) (cond_expr: expr)*)
  (*| S_foreachelem (elem_var: ident) (collection_var: var_id) (body_stmts: statement)*)
  | S_if (cond_expr: expr) (then_part else_part: statement) (loc: location)
  | S_while (cond_expr: expr) (body_stmts: statement) (loc: location)
(* falt control flow statements *)
  (*| S_brfalse (l: label) (opnd: expr)*)
  (*| S_brtrue (l: label) (opnd: expr)*)
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
  | S_virtualcallassigned (c: ident) (f: ident) (opndlist: exprlist) (assignlist: list (var_id * option field_id * location)) (loc: location)
(* To do: virtualcallinstantassigned *)
  (*| S_superclasscallassigned (c: ident) (f: ident) (obj_ptr: expr) (opndlist: exprlist) (assignlist: list (var_id * field_id))*)
(* To do: superclasscallinstantassigned *)
  | S_interfacecallassigned (c: ident) (f: ident) (opndlist: exprlist) (assignlist: list (var_id * option field_id * location)) (loc: location)
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

Record function_body : Type := {
  fun_vars: list (ident * var_def * location);
  fun_types: list (ident * type * location);
  fun_pregs: list (intInfo * prim_type * location);
  fun_statement: statement;
}.

Definition function := (function_prototype * option function_body) % type.

Record program : Type := {
  prog_vars: list (ident * var_def * location);
  prog_types: list (ident * type * location);
  prog_funcs: list (ident * function * location);
  prog_javaclass: list (ident * ident * list class_attr * location);
  prog_javainterface: list (ident * ident * list class_attr * location);
  prog_main: ident * location;
}.
