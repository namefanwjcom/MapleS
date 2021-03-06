Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import MapleLightOp.
Require Import MapleLightTypes.

(*Set Implicit Arguments.*)
Local Open Scope error_monad_scope.

Inductive var_id :=
  | V_global : ident -> var_id
  | V_local : ident -> var_id.

Theorem var_id_dec : forall v1 v2: var_id, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.

Definition field_id := N.

Theorem field_id_dec : forall v1 v2: field_id, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.

Inductive func_id :=
  | Func : ident -> func_id.

Theorem func_id_dec : forall v1 v2: func_id, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.
(*
Inductive intrinsic_func_id :=
  | intrinsic_func_id_string : ident -> intrinsic_func_id.

Theorem intrinsic_func_id_dec : forall v1 v2: intrinsic_func_id, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.

Definition string_literal := ident.
*)
Inductive reg_id :=
  | Preg : ident -> reg_id
  (*| SP*)
  (*| FP*)
  (*| GP*)
  (*| PC*)
  | Thrownval
  (*| Retval: ident -> reg_id*).

Theorem reg_id_dec : forall v1 v2: reg_id, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.

Definition label := ident.

Theorem label_dec : forall v1 v2: label, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.
(*
Definition boffset := N.

Definition bsize := N.

Definition Boffset := N.
*)
Inductive constant :=
  | C_int: int -> constant
  | C_long: int64 -> constant
  | C_single: float32 -> constant
  | C_float: float -> constant
  (*| C_complex: complex -> constant*).

(* Pure exprs *)

Inductive expr :=
(* storage read expr *)
  | E_dread : prim_type -> var_id -> field_id -> expr
  | E_regread : prim_type -> reg_id -> expr
  | E_iread : prim_type -> type -> field_id -> expr -> expr
  (*| E_ireadoff : prim_type -> Boffset -> expr -> expr*)
  (*| E_ireadfpoff : prim_type -> Boffset -> expr -> expr*)
(* leaf expr *)
  | E_addrof : prim_type -> var_id -> field_id -> expr
  (*| E_addroflable : prim_type -> label -> expr*)
  | E_addroffunc : prim_type -> func_id -> expr
  (*| E_conststr : prim_type -> string_literal -> expr*)
  (*| E_conststr16 : prim_type -> string_literal -> expr*)
  | E_constval : prim_type -> constant -> expr
  | E_sizeoftype : prim_type -> type -> expr
(* unary expr *)
  | E_unary : unary_operation -> prim_type -> expr -> expr
  | E_iaddrof : prim_type -> type -> field_id -> expr -> expr
(* type conversion expr *)
  | E_ceil : prim_type -> prim_type -> expr -> expr
  | E_cvt : prim_type -> prim_type -> expr -> expr
  | E_floor : prim_type -> prim_type -> expr -> expr
  | E_retype : prim_type -> type -> expr -> expr
  (*| E_round : prim_type -> prim_type -> expr -> expr*)
  | E_trunc : prim_type -> prim_type -> expr -> expr
(* binary expr *)
  | E_binary : binary_operation -> prim_type -> expr -> expr -> expr
  | E_cand : prim_type -> expr -> expr -> expr
  | E_cior : prim_type -> expr -> expr -> expr
(* ternary expr *)
  | E_select : prim_type -> expr -> expr -> expr -> expr
(* N-ary expr *)
  | E_array : bool -> prim_type -> type -> exprlist -> expr
  (*| E_intrinsicop : prim_type -> intrinsic_func_id -> list expr -> expr*)
  (*| E_intrinsicopwithtype : prim_type -> type -> intrinsic_func_id -> exprlist -> expr*)
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
  | EE_gcmalloc : prim_type -> type -> ext_expr
  | EE_gcmallocjarray : prim_type -> type -> expr -> ext_expr
  | EE_gcpermalloc : prim_type -> type -> ext_expr
  (*| E_stackmalloc : prim_type -> type -> ext_expr*)
  (*| E_stackmallocjarray : prim_type -> type -> expr -> ext_expr*).

Inductive statement :=
  | S_skip
(* storage assignment *)
  | S_dassign (v: var_id) (f: field_id) (rhs_expr: ext_expr)
  | S_iassign (t: type) (f: field_id) (addr_expr: expr) (rhs_expr: ext_expr)
  (*| S_iassignoff (t: prim_type) (Bofs: Boffset) (addr_expr: expr) (rhs_expr: ext_expr)*)
  (*| S_iassignfpoff (t: prim_type) (Bofs: Boffset) (rhs_expr: ext_expr)*)
  | S_regassign (t: prim_type) (r: reg_id) (rhs_expr: ext_expr)
  (* hierarchical control flow *)
  | S_seq (first_part second_part: statement)
  | S_label (l: label) (s: statement)
  (*| S_doloop (do_var: ident) (start_expr cont_expr incr_amt: expr) (body_stmts: statement)*)
  (*| S_dowhile (body_stmts: statement) (cond_expr: expr)*)
  (*| S_foreachelem (elem_var: ident) (collection_var: var_id) (body_stmts: statement)*)
  | S_if (cond_expr: expr) (then_part else_part: statement)
  | S_while (cond_expr: expr) (body_stmts: statement)
(* falt control flow statements *)
  (*| S_brfalse (l: label) (opnd: expr)*)
  (*| S_brtrue (l: label) (opnd: expr)*)
  | S_goto (l: label)
  (*| S_multiway (opnd: expr) (default_label: label) (label_table: list (expr * label))*)
  | S_return (retlist: exprlist)
  | S_switch (opnd: expr) (default_label: label) (label_table: list (Z * label))
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
  | S_callassigned (f: func_id) (opndlist: exprlist) (assignlist: list (var_id * field_id))
(* To do: callinstantassigned *)
  | S_icallassigned (f_ptr: expr) (opndlist: exprlist) (assignlist: list (var_id * field_id))
  (*| S_intrinsiccallassigned (f: intrinsic_func_id) (opndlist: exprlist) (assignlist: list (var_id * field_id))*)
(* To do: intrinsiccallwithtypeassigned *)
  (*| S_xintrinsiccallassigned (user_intrinsiccall_index: expr) (opndlist: exprlist) (assignlist: list (var_id * field_id))*)
  | S_virtualcallassigned (c: ident) (f: ident) (obj_ptr: expr) (opndlist: exprlist) (assignlist: list (var_id * field_id))
(* To do: virtualcallinstantassigned *)
  (*| S_superclasscallassigned (c: ident) (f: ident) (obj_ptr: expr) (opndlist: exprlist) (assignlist: list (var_id * field_id))*)
(* To do: superclasscallinstantassigned *)
  | S_interfacecallassigned (c: ident) (f: ident) (obj_ptr: expr) (opndlist: exprlist) (assignlist: list (var_id * field_id))
(* To do: interfacecallinstantassigned *)
(* exception handling *)
  (*| S_jstry (fl hl: label) (s: statement)*)
  | S_javatry (hl: list label) (s: statement)
  (*| S_cpptry (hl: list label) (s: statement)*)
  | S_throw (opnd: expr)
  (*| S_jscatch (s: statement)*)
  | S_javacatch (hl: label) (tl: list type)
  (*| S_cppcatch (hl: label) (tl: list type)*)
  (*| S_finally (fl: label) (s: statement)*)
  (*| S_cleanuptry*)
  (*| S_endtry (l: label)*)
  (*| S_gosub (fl: label)*)
  (*| S_retsub*)
(* memory deallocation *)
  | S_decref (opnd: expr)
  (*| S_decrefreset (opnd: expr)*)
  | S_free (opnd: expr)
  | S_incref (opnd: expr)
(* other statements *)
  (*| S_assertge (opnd0 opnd1: expr)*)
  (*| S_assertlt (opnd0 opnd1: expr)*)
  (*| S_assertnonnull (opnd: expr)*)
  | S_eval (opnd: expr)
  (*| S_membaracquire*)
  (*| S_membarrelease*)
  (*| S_membarfull*)
  (*| S_syncenter (opnd: expr)*)
  (*| S_syncexit (opnd: expr)*).

Inductive storage_class : Set :=
  | SC_default
  (*| SC_extern
  | SC_fstatic
  | SC_pstatic*).

Definition var_attr := (storage_class * type_attr) % type.

Definition default_var_attr := (SC_default, default_type_attr).

Definition var_def := (type * var_attr) % type.

Record function_prototype : Type := {
  fun_attr: func_attr;
  fun_returns: list type;
  fun_params: list (ident * type);
}.

Lemma list_ident_type_eq:
  forall l1 l2: list (ident * type),
    {l1 = l2} + {l1 <> l2}.
Proof.
  intros. decide equality. decide equality.
  apply type_eq. apply ident_eq.
Qed.

Lemma function_prototype_eq:
  forall fp1 fp2: function_prototype,
    {fp1 = fp2} + {fp1 <> fp2}.
Proof.
  intros. decide equality.
  - apply list_ident_type_eq.
  - decide equality. apply type_eq.
  - repeat (decide equality).
Qed.

Opaque list_ident_type_eq function_prototype_eq.

Record function_body : Type := {
  fun_vars: list (ident * var_def);
  (*fun_types: list (ident * type);*)
  fun_pregs: list (ident * prim_type);
  fun_statement: statement;
}.

Definition function := (function_prototype * option function_body) % type.

Definition concrete_function := (function_prototype * function_body) % type.

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fun_params (fst f))) (type_of_returns (fun_returns (fst f))).

Record program : Type := {
  prog_vars: list (ident * var_def);
  prog_comps: list (ident * composite_definition);
  prog_funcs: list (ident * function);
  prog_main: ident;
}.

Record genv := mkgenv {
  genv_vars: PTree.t (block * var_def);
  genv_cenv: composite_env;
  genv_cenv_consistent: composite_env_consistent genv_cenv;
  genv_funcs: PTree.t block;
  genv_fundefs: PTree.t function;
}.

Section Build_genv_mem.

Variable p: program.

Section Add_globals.

Variable ce: composite_env.

Definition add_globalvar (gem: genv * mem) (x: ident * var_def) : res (genv * mem) :=
  let (ge, m) := gem in
  let (id, vd) := x in
  let (ty, va) := vd in
  let (sc, ta) := va in
  match (genv_vars ge) ! id with
  | Some _ => Error (MSG "multiple definitions of " :: CTX id:: nil)
  | None =>
    match complete_type ce ty with
    | true =>
      let (m', b) := Mem.alloc m 0 (sizeof ce ty ta) in
      OK ({| genv_vars := PTree.set id (b, (ty, va)) (genv_vars ge);
             genv_cenv := genv_cenv ge;
             genv_cenv_consistent := genv_cenv_consistent ge;
             genv_funcs := genv_funcs ge;
             genv_fundefs := genv_fundefs ge; |}, m')
    | false => Error (MSG "the type of " :: CTX id :: MSG " is incomplete" :: nil)
    end
  end.

Definition add_globalvars (gem: genv * mem) : res (genv * mem) :=
  mfold_left add_globalvar (prog_vars p) gem.

Definition find_function_by_name (ge: genv) (id: ident) : option (block * function) :=
  match (genv_funcs ge) ! id with
  | Some b =>
    match (genv_fundefs ge) ! b with
    | Some f => Some (b, f)
    | None => None
    end
  | None => None
  end.

Definition add_func (gem: genv * mem) (x: ident * function) : res (genv * mem) :=
  let (ge, m) := gem in
  let (id, f) := x in
  match find_function_by_name ge id with
  | Some (_, (_, Some _)) =>
    Error (MSG "multiple definitions of " :: CTX id :: nil)
  | Some (b, (fp, None)) =>
    if function_prototype_eq fp (fst f) then
      OK ({| genv_vars := genv_vars ge;
             genv_cenv := genv_cenv ge;
             genv_cenv_consistent := genv_cenv_consistent ge;
             genv_funcs := genv_funcs ge;
             genv_fundefs := PTree.set b f (genv_fundefs ge); |}, m)
    else Error (MSG "the definition of " :: CTX id :: MSG "conflicts with its prototype" :: nil)
  | None =>
      match complete_type ce (type_of_function f) with
      | false => Error ((MSG "the type of " :: CTX id :: MSG " is incomplete" :: nil))
      | true =>
        let (m', b) := Mem.alloc m 0 1 in
        OK ({| genv_vars := genv_vars ge;
               genv_cenv := genv_cenv ge;
               genv_cenv_consistent := genv_cenv_consistent ge;
               genv_funcs := PTree.set id b (genv_funcs ge);
               genv_fundefs := PTree.set b f (genv_fundefs ge); |}, m')
      end
  end.

Definition add_funcs (gem: genv * mem) : res (genv * mem) :=
  mfold_left add_func (prog_funcs p) gem.
(*
Definition add_javaclass_attr (ge: genv) (x: ident * class_attr) : res genv :=
  let (id, ca) := x in
  match (genv_javaclass_attrs ge) ! id with
  | Some _ => Error (MSG "multiple attributes of " :: CTX id :: nil)
  | None =>
    match ce ! id with
    | None => Error ((MSG "the type of " :: CTX id :: MSG " is incomplete" :: nil))
    | Some _ =>
      OK (mkgenv
            (ge.(genv_vars))
            (ge.(genv_mytypes))
            (ge.(genv_cenv))
            (ge.(genv_cenv_consistent))
            (ge.(genv_funcs))
            (PTree.set id ca ge.(genv_javaclass_attrs))
            (ge.(genv_javainterface_attrs))
            (ge.(genv_fundefs)))
    end
  end.

Definition add_javaclass_attrs (ge: genv) : res genv :=
  mfold_left add_javaclass_attr (prog_javaclass_attrs p) ge.

Definition add_javainterface_attr (ge: genv) (x: ident * interface_attr) : res genv :=
  let (id, ia) := x in
  match (genv_javaclass_attrs ge) ! id with
  | Some _ => Error (MSG "multiple attributes of " :: CTX id :: nil)
  | None =>
    match ce ! id with
    | None => Error ((MSG "the type of " :: CTX id :: MSG " is incomplete" :: nil))
    | Some _ =>
      OK (mkgenv
            (ge.(genv_vars))
            (ge.(genv_mytypes))
            (ge.(genv_cenv))
            (ge.(genv_cenv_consistent))
            (ge.(genv_funcs))
            (ge.(genv_javaclass_attrs))
            (PTree.set id ia ge.(genv_javainterface_attrs))
            (ge.(genv_fundefs)))
    end
  end.

Definition add_javainterface_attrs (ge: genv) : res genv :=
  mfold_left add_javainterface_attr (prog_javainterface_attrs p) ge.
*)
Definition init_genv (P: composite_env_consistent ce) : res genv :=
  OK {| genv_vars := PTree.empty (block * var_def);
        genv_cenv := ce;
        genv_cenv_consistent := P;
        genv_funcs := PTree.empty block;
        genv_fundefs := PTree.empty function; |}.

End Add_globals.

Program Definition build_genv_mem : res (genv * mem) :=
  match build_composite_env (prog_comps p) with
  | OK ce =>
    do ge1 <- init_genv ce _;
    do (ge2, m2) <- add_globalvars ce (ge1, Mem.empty);
    do (ge3, m3) <- add_funcs ce (ge2, m2);
    OK (ge3, m3)
  | Error msg => Error msg
  end.
Next Obligation.
  eapply build_composite_env_consistent; eauto.
Qed.

End Build_genv_mem.

(*
Inductive init_globals {A: Type} (f: (type * A) -> global_def) :
  list (ident * (type * A)) -> mem -> (PTree.t global_def) ->
  mem -> (PTree.t global_def) -> (PTree.t block) -> Prop :=
  | init_globals_nil:
      forall e m,
        init_globals f nil m e m e (PTree.empty block)
  | init_globals_cons:
      forall e e1 m id t d l m1 b1 m2 pb,
        init_globals f l m e m1 e1 pb ->
        Mem.alloc m1 0 (sizeof' t) = (m2, b1) ->
        init_globals f ((id, (t, d)) :: l) m e m2 (PTree.set b1 (f (t, d)) e1) (PTree.set id b1 pb).

Inductive init_functions :
  list (ident * func_def) -> mem -> (PTree.t global_def) ->
  mem -> (PTree.t global_def) -> (PTree.t block) -> Prop :=
  | init_functions_nil:
      forall e m,
        init_functions nil m e m e (PTree.empty block)
  | init_functions_cons:
      forall e e1 m id f d l m1 b1 m2 pb,
        init_functions l m e m1 e1 pb ->
        Mem.alloc m1 0 (sizeof' (type_of_function f)) = (m2, b1) ->
        init_functions ((id, (f, d)) :: l) m e m2 (PTree.set b1 (global_func_def (f, d)) e1) (PTree.set id b1 pb).

Inductive init_genv : program -> genv -> mem -> Prop :=
  | init_genv' P m1 e1 b1 m2 e2 b2:
      init_globals global_var_def P.(prog_vars) Mem.empty (PTree.empty global_def) m1 e1 b1 ->
      init_globals global_class_def P.(prog_vars) 
      init_functions P.(prog_funcs) m1 e1 m2 e2 b2 ->
      init_genv P (mkgenv b1 (PTree.empty type) b2 b1 b1 e1) m1.

Inductive object_id :=
  | Obj : ident -> object_id.

Inductive val : Type :=
  | Vundef : val
  | Vbyte : byte -> val
  | Vshort : short -> val
  | Vint : int -> val
  | Vlong : int64 -> val
  | Vfloat : float -> val
  | Vsingle : float32 -> val
  | Vptr : block -> ptrofs -> val.*)

Record lenv := mklenv {
  lenv_vars: PTree.t (block * var_def);
  lenv_pregs: PTree.t (val * prim_type);
}.

(** [deref_loc ty m b ofs v] computes the value of a datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  If the type [ty] indicates an access by value, the corresponding
  memory load is performed.  If the type [ty] indicates an access by
  reference or by copy, the pointer [Vptr b ofs] is returned. *)

Fixpoint deref_loc (mt: type) (m: mem) (b: block) (ofs: ptrofs) : option val :=
  match (access_mode mt) with
  | By_value chunk => Mem.loadv chunk m (Vptr b ofs)
  | By_reference => Some (Vptr b ofs)
  | By_copy => Some (Vptr b ofs)
  | By_nothing => None
  end.

(** Symmetrically, [assign_loc ty m b ofs v m'] returns the
  memory state after storing the value [v] in the datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  This is allowed only if [ty] indicates an access by value or by copy.
  [m'] is the updated memory state. *)

(*Inductive assign_loc (ce: composite_env) (mt: mytype) (ta: type_attr) (m: mem) (b: block) (ofs: ptrofs): val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode mt = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ce mt ta m b ofs v m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode mt = By_copy ->
      (sizeof ce mt > 0 -> (alignof ce mt ta | Ptrofs.unsigned ofs')) ->
      (sizeof ce mt > 0 -> (alignof ce mt ta | Ptrofs.unsigned ofs)) ->
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs' + sizeof ce mt <= Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs + sizeof ce mt <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce mt) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ce mt ta m b ofs (Vptr b' ofs') m'.*)

Definition assign_loc (ce: composite_env) (mt: type) (ta: type_attr) (m: mem) (b: block) (ofs: ptrofs) (v: val) : option mem :=
  match access_mode mt with
  | By_value chunk => Mem.storev chunk m (Vptr b ofs) v
  | By_copy =>
    match v with
    | Vptr b' ofs' =>
      if (Zdivide_dec (alignof ce mt ta) (Ptrofs.unsigned ofs')) then
        if (Zdivide_dec (alignof ce mt ta) (Ptrofs.unsigned ofs')) then
          if ((negb (b =? b')%positive)
              || (Ptrofs.unsigned ofs' =? Ptrofs.unsigned ofs)
              || (Ptrofs.unsigned ofs' + sizeof ce mt ta <=? Ptrofs.unsigned ofs)
              || (Ptrofs.unsigned ofs + sizeof ce mt ta <=? Ptrofs.unsigned ofs'))
          then
            match (Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce mt ta)) with
            | Some bytes =>
              Mem.storebytes m b (Ptrofs.unsigned ofs) bytes
            | None => None
            end
          else None
        else None
      else None
    | _ => None
    end
  | _ => None
  end.

Section Build_lenv_mem.

Variable ce: composite_env.

Section Add_locals.

Variable fp: function_prototype.

Variable fb: function_body.

(** Allocation of function-local variables.
  [alloc_variables e1 m1 vars e2 m2] allocates one memory block
  for each variable declared in [vars], and associates the variable
  name with this block.  [e1] and [m1] are the initial local environment
  and memory state.  [e2] and [m2] are the final local environment
  and memory state. *)

Definition add_localvar (lem: lenv * mem) (x: ident * var_def) : res (lenv * mem) :=
  let (le, m) := lem in
  let (id, vd) := x in
  let (mt, va) := vd in
  let (sc, ta) := va in
  match (lenv_vars le) ! id with
  | Some _ => Error (MSG "multiple definitions of " :: CTX id:: nil)
  | None =>
    match complete_type ce mt with
    | true =>
      let (m', b) := Mem.alloc m 0 (sizeof ce mt ta) in
      OK ({| lenv_vars := PTree.set id (b, (mt, va)) (lenv_vars le);
             lenv_pregs := lenv_pregs le |}, m')
    | false => Error (MSG "the type of " :: CTX id :: MSG " is incomplete" :: nil)
    end
  end.

Fixpoint params_to_vars (l: list (ident * type)) : list (ident * var_def) :=
  match l with
  | nil => nil
  | (id, ty) :: l' => (id, (ty, default_var_attr)) :: params_to_vars l'
  end.

(*Fixpoint change_type_of_vars (te: PTree.t type) (l: list (ident * var_def)) : res (list (ident * var_def)) :=
  match l with
  | nil => OK nil
  | (id, (ty, va)) :: l' =>
    do mt <- type_to_mytype te ty;
      do ml' <- change_type_of_vars te l';
      OK ((id, (mt, va)) :: ml')
  end.*)

(*Fixpoint change_type_of_params (te: PTree.t mytype) (l: list (ident * type)) : res (list (ident * mytype)) :=
  match l with
  | nil => OK nil
  | (id, ty) :: l' =>
    do mt <- type_to_mytype te ty;
      do ml' <- change_type_of_params te l';
      OK ((id, mt) :: ml')
  end.*)

Definition add_localvars (lem: lenv * mem) : res (lenv * mem) :=
  let (le, m) := lem in
  mfold_left add_localvar (params_to_vars (fun_params fp) ++ fun_vars fb) lem.

(** Initialization of local variables that are parameters to a function.
  [bind_parameters e m1 params args m2] stores the values [args]
  in the memory blocks corresponding to the variables [params].
  [m1] is the initial memory state and [m2] the final memory state. *)

(*Inductive bind_parameters (le: lenv):
                           mem -> list (ident * mytype) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters le m nil nil m
  | bind_parameters_cons:
      forall m id mt params v1 vl b m1 m2 ta sc,
      PTree.get id (lenv_vars le) = Some(b, (mt, (sc, ta))) ->
      assign_loc ce mt ta m b Ptrofs.zero v1 = Some m1 ->
      bind_parameters le m1 params vl m2 ->
      bind_parameters le m ((id, mt) :: params) (v1 :: vl) m2.*)

Fixpoint bind_parameters (le: lenv) (m: mem) (l: list (ident * type)) (vmtl: list (val * type)) : option mem :=
  match l, vmtl with
  | nil, nil => Some m
  | (id, _) :: l', (v, mt') :: vmtl' =>
    match (lenv_vars le) ! id with
    | Some (b, (mt, (_, ta))) =>
      match sem_cast v mt' mt m ce with
      | Some v' =>
        match (assign_loc ce mt ta m b Ptrofs.zero v') with
        | Some m1 => bind_parameters le m1 l' vmtl'
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | _, _ => None
  end.

(** Initialization of pseudo registers. *)

Definition add_preg (le: lenv) (x: ident * prim_type) : res (lenv) :=
  let (id, pt) := x in
  match (lenv_pregs le) ! id with
  | Some _ => Error (MSG "multiple definitions of " :: CTX id:: nil)
  | None =>
      match complete_type ce (Tprim pt) with
      | true =>
        OK {| lenv_vars := lenv_vars le;
              lenv_pregs := PTree.set id (Vundef, pt) (lenv_pregs le);
           |}
      | false => Error (MSG "the type of " :: CTX id :: MSG " is incomplete" :: nil)
      end
  end.

Definition add_pregs (lem: lenv) : res lenv :=
  mfold_left add_preg (fun_pregs fb) lem.

(** Return the list of blocks in the codomain of [e], with low and high bounds. *)
(*
Definition block_of_binding (id_b_ty: ident * (block * var_def)) :=
  match id_b_ty with (_, (b, (t, _))) => (b, 0, sizeof' t) end.

Definition blocks_of_env (e: lenv) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements e.(lenv_var)).
*)

End Add_locals.

Definition init_lenv : lenv :=
  {| lenv_vars := PTree.empty (block * var_def);
     lenv_pregs := PTree.empty (val * prim_type);
  |}.

Definition build_lenv_mem (f: concrete_function) (m: mem) (vmtl: list (val * type)) : option (lenv * mem) :=
  let (fp, fb) := f in
  match add_localvars fp fb (init_lenv, m) with
  | OK (le1, m1) =>
    match bind_parameters le1 m1 (fun_params fp) vmtl with
    | Some m2 =>
      match add_pregs fb le1 with
      | OK le2 => Some (le2, m2)
      | Error _ => None
      end
    | None => None
    end
  | Error _ => None
  end.

End Build_lenv_mem.

(** ** Transition semantics for statements and functions *)

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont
  (*| Kgoto: label -> cont -> cont
  | Kreturn: cont -> cont*)
  | Kjavatry: list label -> cont -> cont
  (*| Kexception: block -> cont -> cont*)
  | Kseq: statement -> cont -> cont       (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
  | Kwhile: expr -> statement -> cont -> cont (**r [Kloop1 s1 s2 k] = after [s1] in [Sloop s1 s2] *)
  | Kcall: list (var_id * field_id) ->                  (**r where to store result *)
           concrete_function ->                      (**r calling function *)
           lenv ->                          (**r local env of calling function *)
           cont -> cont.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kwhile e s k => call_cont k
  (*| Kgoto _ k => call_cont k
  | Kreturn k => call_cont k*)
  | Kjavatry _ k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : bool :=
  match k with
  | Kstop => true
  | Kcall _ _ _ _ => true
  (*| Kexception _ k => True*)
  | _ => false
  end.

Fixpoint catch_cont (k: cont) : cont :=
  match k with
  | Kseq s k => catch_cont k
  | Kwhile e s k => catch_cont k
  (*| Kgoto _ k => catch_cont k
  | Kreturn k => catch_cont k
  | Kexception _ k => catch_cont k*)
  | _ => k
  end.

(* the object environment maps each unique object_id to its block number in the heap, the class it belongs to and the count it is referred to. *)
Definition oenv := PTree.t (type * nat * bool).

(* the sreg environment contains special registers such as %%thrownval, etc. *)
Record senv: Type := {
  senv_thrownval: option (val * prim_type);
}.

(** States *)

Inductive state: Type :=
  | NormalState
      (f: concrete_function)
      (s: statement)
      (k: cont)
      (le: lenv)
      (oe: oenv)
      (se: senv)
      (m: mem) : state
  | CallState
      (f: function)
      (args: list (val * type))
      (k: cont)
      (oe: oenv)
      (se: senv)
      (m: mem) : state
  | ReturnState
      (res: list (val * type))
      (k: cont)
      (oe: oenv)
      (se: senv)
      (m: mem) : state
  | ExceptionState
      (f: concrete_function)
      (k: cont)
      (le: lenv)
      (oe: oenv)
      (se: senv)
      (m: mem) : state.

Definition init_oenv : oenv := PTree.empty (type * nat * bool).

Definition init_senv : senv :=
  {| senv_thrownval := None |}.

Inductive initial_state (p: program) (vmtl: list (val * type)) : genv -> state -> Prop :=
  | initial_state_intro: forall ge m b f,
      build_genv_mem p = OK (ge, m) ->
      find_function_by_name ge (prog_main p) = Some (b, f) ->
      initial_state p vmtl ge (CallState f vmtl Kstop init_oenv init_senv m).

Section Semantics.

Variable ge: genv.

Fixpoint sem_cast_list (vl: list val) (mtl1 mtl2: typelist) (m: mem) : option (list (val * type)) :=
  match vl, mtl1, mtl2 with
  | nil, Tnil, Tnil => Some nil
  | v :: vl', Tcons mt1  mtl1', Tcons mt2 mtl2' =>
    match sem_cast v mt1 mt2 m (genv_cenv ge) with
    | Some v' =>
      match sem_cast_list vl' mtl1' mtl2' m with
      | Some vmtl'' => Some ((v', mt2) :: vmtl'')
      | None => None
      end
    | None => None
    end
  | _, _, _ => None
  end.

Definition prim_type_of (e: expr) : prim_type :=
  match e with
  | E_dread pt _ _ => pt
  | E_regread pt _ => pt
  | E_iread pt _ _ _ => pt
  | E_addrof pt _ _ => pt
  | E_addroffunc pt _ => pt
  | E_constval pt _ => pt
  | E_sizeoftype pt _ => pt
  | E_unary op pt _ => pt
  | E_iaddrof pt _ _ _ => pt
  | E_ceil pt _ _ => pt
  | E_cvt pt _ _ => pt
  | E_floor pt _ _ => pt
  | E_retype pt _ _ => pt
  | E_trunc pt _ _ => pt
  | E_binary op pt _ _ => pt
  | E_cand pt _ _ => pt
  | E_cior pt _ _ => pt
  | E_select pt _ _ _ => pt
  | E_array b pt _ _ => pt
  end.

Definition typeof (e: expr) : type :=
  Tprim (prim_type_of e).

Fixpoint typelistof (el: exprlist) : typelist :=
  match el with
  | E_nil => Tnil
  | E_cons e el' => Tcons (typeof e) (typelistof el')
  end.

Definition prim_type_of_ext_expr (ee: ext_expr) : prim_type :=
  match ee with
  | EE_pure e => prim_type_of e
  | EE_malloc pt _ => pt
  | EE_gcmalloc pt _ => pt
  | EE_gcmallocjarray pt _ _ => pt
  | EE_gcpermalloc pt _ => pt
  end.

Definition typeof_ext_expr (ee: ext_expr) : type :=
  Tprim (prim_type_of_ext_expr ee).

Definition is_pointer_prim_type (pt: prim_type) : bool :=
  match pt with
  | PTptr | PTref => true
  | PTaddr A32 => negb Archi.ptr64
  | PTaddr A64 => negb Archi.ptr64
  | _ => false
  end.

Definition is_int_prim_type (pt: prim_type) : bool :=
  match pt with
  | PTint _ _ | PTbool => true
  | _ => false
  end.

Definition is_float_prim_type (pt: prim_type) : bool :=
  match pt with
  | PTfloat _ => true
  | _ => false
  end.

Definition type_prim_type_compatible (mt: type) (pt: prim_type) : bool :=
  match mt with
  | Tprim pt' => prim_type_eq pt' pt
  | Tpointer _ => is_pointer_prim_type pt
  | Tarray _ _ => is_pointer_prim_type pt (* Not sure *)
  | Tfunction _ _ => false
  | Tcomposite id =>
    match pt with
    | PTagg => true
    | _ => false
    end
  end.

Section Eval_ext_expr.

Variable se: senv.

Variable le: lenv.

(*
Variable java_throw_exception_sem : (expr * mem * oenv) -> (block * ptrofs * mem * oenv) -> Prop.

Inductive value :=
  | Normal_value: val -> value
  | Exception_value: block -> ptrofs -> value.

Inductive address :=
  | Normal_address: block -> ptrofs -> address
  | Exception_address: block -> ptrofs -> address.
*)

Definition find_var (vid: var_id) : option (block * var_def) :=
  match vid with
  | V_local id => (lenv_vars le) ! id
  | V_global id => (genv_vars ge) ! id
  end.

Definition find_preg (id: ident) : option (val * prim_type) :=
  (lenv_pregs le) ! id.

Definition find_thrownval : option (val * prim_type) :=
  senv_thrownval se.

Definition find_reg (rid: reg_id) : option (val * prim_type) :=
  match rid with
  | Thrownval => find_thrownval
  | Preg id => find_preg id
  end.

Section Eval_expr.

Variable m: mem.

Inductive eval_array: bool -> type -> list val -> ptrofs -> Prop :=
  | eval_Earray_one_dimension:
      forall mt mt' len i z b,
        mt = Tpointer (Tarray mt' len) ->
        (b = false \/ (b = true /\ Int.intval i < len)) ->
        Int.intval i * (sizeof (genv_cenv ge) mt' default_type_attr) = z ->
        eval_array b mt (Vint i :: nil) (Ptrofs.repr z)
  | eval_Earray_multi_dimension:
      forall mt ofs mt' len i z vl b,
        mt = Tpointer (Tarray mt' len) ->
        (b = false \/ (b = true /\ Int.intval i < len)) ->
        Int.intval i * (sizeof (genv_cenv ge) mt' default_type_attr) = z ->
        eval_array b mt' vl ofs ->
        eval_array b mt (Vint i :: vl) (Ptrofs.add ofs (Ptrofs.repr z)).

Inductive eval_expr : expr -> val -> Prop :=
  | eval_Econst_int:   forall i pt v',
      sem_cast (Vint i) (Tprim (PTint I32 Unsigned)) (Tprim pt) m (genv_cenv ge) = Some v' ->
      eval_expr (E_constval pt (C_int i)) v'
  | eval_Econst_long:   forall i pt v',
      sem_cast (Vlong i) (Tprim (PTint I64 Unsigned)) (Tprim pt) m (genv_cenv ge) = Some v' ->
      eval_expr (E_constval pt (C_long i)) v'
  | eval_Econst_single:   forall f pt v',
      sem_cast (Vsingle f) (Tprim (PTfloat F32)) (Tprim pt) m (genv_cenv ge) = Some v' ->
      eval_expr (E_constval pt (C_single f)) v'
  | eval_Econst_float:   forall f pt v',
      sem_cast (Vfloat f) (Tprim (PTfloat F64)) (Tprim pt) m (genv_cenv ge) = Some v' ->
      eval_expr (E_constval pt (C_float f)) v'
  | eval_Edread: forall vid b pt mt va fi ofs mt' v v',
      find_var vid = Some (b, (mt, va)) ->
      fieldoffset (genv_cenv ge) mt fi = OK (mt', ofs) ->
      deref_loc mt' m b (Ptrofs.repr ofs) = Some v ->
      sem_cast v mt' (Tprim pt) m (genv_cenv ge) = Some v' ->
      eval_expr (E_dread pt vid fi) v'
  | eval_Eiread: forall e b ofs pt t t' t'' fi delta v v',
      eval_expr e (Vptr b ofs) ->
      t = Tpointer t' ->
      fieldoffset (genv_cenv ge) t' fi = OK (t'', delta) ->
      deref_loc t'' m b (Ptrofs.add ofs (Ptrofs.repr delta)) = Some v ->
      sem_cast v t'' (Tprim pt) m (genv_cenv ge) = Some v' ->
      eval_expr (E_iread pt t fi e) v'
  | eval_Eregread:  forall pt' pt rid v v',
      find_reg rid = Some (v, pt) ->
      sem_cast v (Tprim pt) (Tprim pt') m (genv_cenv ge) = Some v' ->
      eval_expr (E_regread pt' rid) v'
  | eval_Eaddrof: forall vid b pt mt va fi ofs mt',
      is_pointer_prim_type pt = true ->
      find_var vid = Some(b, (mt, va)) ->
      fieldoffset (genv_cenv ge) mt fi = OK (mt', ofs) ->
      eval_expr (E_addrof pt vid fi)
                (Vptr b (Ptrofs.repr ofs))
  | eval_Eiaddrof: forall e b pt t t' t'' ofs delta fi,
      is_pointer_prim_type pt = true ->
      eval_expr e (Vptr b ofs) ->
      t = Tpointer t' ->
      fieldoffset (genv_cenv ge) t' fi = OK (t'', delta) ->
      eval_expr (E_iaddrof pt t fi e)
                (Vptr b (Ptrofs.add ofs (Ptrofs.repr delta)))
  | eval_Eaddroffunc: forall id b pt,
      (genv_funcs ge) ! id = Some b ->
      pt = (PTaddr A32) \/ pt = (PTaddr A64) ->
      eval_expr (E_addroffunc pt (Func id))
                (Vptr b (Ptrofs.repr 0))
  | eval_Esizeoftype: forall pt t v',
      sem_cast (Vptrofs (Ptrofs.repr (sizeof (genv_cenv ge) t default_type_attr))) (Tprim (if Archi.ptr64 then (PTint I64 Unsigned) else (PTint I32 Unsigned))) (Tprim pt) m (genv_cenv ge) = Some v' ->
      eval_expr (E_sizeoftype pt t) v'
  | eval_Eretype: forall pt t v v' e,
      eval_expr e v ->
      sem_cast v t (Tprim pt) m (genv_cenv ge) = Some v' ->
      eval_expr (E_retype pt t e) v'
  | eval_Ecvt: forall pt pt' v v' e,
      eval_expr e v ->
      sem_cast v (Tprim pt) (Tprim pt') m (genv_cenv ge) = Some v' ->
      eval_expr (E_cvt pt' pt e) v'
  | eval_Eceil: forall pt pt' v v' e,
      eval_expr e v ->
      sem_ceil v pt pt' = Some v' ->
      eval_expr (E_ceil pt' pt e) v'
  | eval_Efloor: forall pt pt' v v' e,
      eval_expr e v ->
      sem_floor v pt pt' = Some v' ->
      eval_expr (E_floor pt' pt e) v'
  | eval_Etrunc: forall pt pt' v v' e,
      eval_expr e v ->
      sem_trunc v pt pt' = Some v' ->
      eval_expr (E_trunc pt' pt e) v'
  | eval_Eunary: forall e uop pt v v',
      eval_expr e v ->
      sem_unary_operation uop v (typeof e) (Tprim pt) m (genv_cenv ge) = Some v' ->
      eval_expr (E_unary uop pt e) v'
  | eval_Ebinary: forall e1 e2 v1 v2 bop pt v,
      eval_expr e1 v1 ->
      eval_expr e2 v2 ->
      sem_binary_operation bop v1 (typeof e1) v2 (typeof e2) (Tprim pt) m (genv_cenv ge) = Some v ->
      eval_expr (E_binary bop pt e1 e2) v
  | eval_Ecand_true: forall e1 e2 v1 v2 b pt,
      is_int_prim_type pt = true ->
      eval_expr e1 v1 ->
      bool_val v1 (typeof e1) m = Some true ->
      eval_expr e2 v2 ->
      bool_val v2 (typeof e2) m = Some b ->
      eval_expr (E_cand pt e1 e2)
                (Val.of_bool b)
  | eval_Ecand_false: forall e1 e2 v1 pt,
      is_int_prim_type pt = true ->
      eval_expr e1 v1 ->
      bool_val v1 (typeof e1) m = Some false ->
      eval_expr (E_cand pt e1 e2)
                (Val.of_bool false)
  | eval_Ecior_false: forall e1 e2 v1 v2 b pt,
      is_int_prim_type pt = true ->
      eval_expr e1 v1 ->
      bool_val v1 (typeof e1) m = Some false ->
      eval_expr e2 v2 ->
      bool_val v2 (typeof e2) m = Some b ->
      eval_expr (E_cior pt e1 e2)
                (Val.of_bool b)
  | eval_Ecior_true: forall e1 e2 v1 pt,
      is_int_prim_type pt = true ->
      eval_expr e1 v1 ->
      bool_val v1 (typeof e1) m = Some true ->
      eval_expr (E_cior pt e1 e2)
                (Val.of_bool true)
  | eval_Eselect_left: forall e1 e2 e3 v1 v2 pt,
      (prim_type_of e2 = pt /\ prim_type_of e3 = pt) ->
      eval_expr e1 v1 ->
      bool_val v1 (typeof e1) m = Some true ->
      eval_expr e2 v2 ->
      eval_expr (E_select pt e1 e2 e3) v2
  | eval_Eselect_right: forall e1 e2 e3 v1 v3 pt,
      (prim_type_of e2 = pt /\ prim_type_of e3 = pt) ->
      eval_expr e1 v1 ->
      bool_val v1 (typeof e1) m = Some false ->
      eval_expr e3 v3  ->
      eval_expr (E_select pt e1 e2 e3) v3
  | eval_Earray: forall pt t e loc ofs el vl delta b,
      is_pointer_prim_type pt = true ->
      eval_expr e (Vptr loc ofs) ->
      eval_exprlist el vl ->
      eval_array b t vl delta ->
      eval_expr (E_array b pt t (E_cons e el))
                (Vptr loc (Ptrofs.add ofs delta))
with eval_exprlist: exprlist -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist E_nil nil
  | eval_Econs: forall e el v vl,
      eval_expr e v ->
      eval_exprlist el vl ->
      eval_exprlist (E_cons e el) (v :: vl).

(*Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
  with eval_exprlist_ind2 := Minimality for eval_exprlist Sort Prop.
Combined Scheme eval_expr_exprlist_ind from eval_expr_ind2, eval_exprlist_ind2.*)

End Eval_expr.

Definition val_to_ptrofs (v: val) : option ptrofs :=
  match v with
  | Vint i =>
    if Archi.ptr64 then None else Some (Ptrofs.of_int i)
  | Vlong i =>
    if Archi.ptr64 then Some (Ptrofs.of_int64 i) else None
  | _ => None
  end.

Inductive eval_ext_expr: (ext_expr * oenv * mem) -> (val * oenv * mem) -> Prop :=
  | eval_pure: forall e v oe m,
      eval_expr m e v ->
      eval_ext_expr (EE_pure e, oe, m)
                    (v, oe, m)
  | eval_malloc: forall pt e oe m m' b v ofs m'',
      eval_expr m e v ->
      val_to_ptrofs v = Some ofs ->
      Mem.alloc m (- size_chunk Mptr) (Ptrofs.unsigned ofs) = (m', b) ->
      Mem.store Mptr m' b (- size_chunk Mptr) v = Some m'' ->
      is_pointer_prim_type pt = true ->
      eval_ext_expr (EE_malloc pt e, oe, m)
                    (Vptr b Ptrofs.zero, oe, m'')
  | eval_gcmalloc: forall pt t oe m m' b,
      Mem.alloc m 0 (sizeof (genv_cenv ge) t default_type_attr) = (m', b) ->
      is_pointer_prim_type pt = true ->
      eval_ext_expr (EE_gcmalloc pt t, oe, m)
                    (Vptr b Ptrofs.zero, PTree.set b (t, O, true) oe, m')
  | eval_gcmallocjarray_int: forall pt t e oe m m' b v n z,
      eval_expr m e v ->
      (v = Vint n /\ Int.unsigned n = z) ->
      Mem.alloc m 0 (Z.mul z (sizeof (genv_cenv ge) t default_type_attr)) = (m', b) ->
      is_pointer_prim_type pt = true ->
      eval_ext_expr (EE_gcmallocjarray pt t e, oe, m)
                    (Vptr b Ptrofs.zero, PTree.set b (Tarray t z, O, true) oe, m')
  | eval_gcmallocjarray_long: forall pt t e oe m m' b v n z,
      eval_expr m e v ->
      (v = Vlong n /\ Int64.unsigned n = z) ->
      Mem.alloc m 0 (Z.mul z (sizeof (genv_cenv ge) t default_type_attr)) = (m', b) ->
      is_pointer_prim_type pt = true ->
      eval_ext_expr (EE_gcmallocjarray pt t e, oe, m)
                    (Vptr b Ptrofs.zero, PTree.set b (Tarray t z, O, true) oe, m')
  | eval_gcpermalloc: forall pt t oe m m' b,
      Mem.alloc m 0 (sizeof (genv_cenv ge) t default_type_attr) = (m', b) ->
      is_pointer_prim_type pt = true ->
      eval_ext_expr (EE_gcpermalloc pt t, oe, m)
                    (Vptr b Ptrofs.zero, PTree.set b (t, O, false) oe, m').

(*Inductive eval_expr_cast_normal : expr -> type -> type -> val -> Prop :=
  | eval_expr_nomal_cast: forall e mt1 mt2 v v',
      eval_expr_normal e v ->
      sem_cast v mt1 mt2 m = Some v' ->
      eval_expr_cast_normal e mt1 mt2 v'
with eval_exprlist_cast_normal: exprlist -> typelist -> list val -> Prop :=
  | eval_Enil_cast:
      eval_exprlist_cast_normal nil MTnil nil
  | eval_Econs_cast: forall e el v v' vl mt mtl,
      eval_expr_normal e v ->
      sem_cast v mt (typeof e) m = Some v' ->
      eval_exprlist_cast_normal el mtl vl  ->
      eval_exprlist_cast_normal (e :: el) (MTcons mt mtl) (v' :: vl).*)

End Eval_ext_expr.

Fixpoint find_label (lbl: label) (s: statement) (k: cont)
                    {struct s}: option (statement * cont) :=
  match s with
  | S_seq s1 s2 =>
    match find_label lbl s1 (Kseq s2 k) with
    | Some sk => Some sk
    | None => find_label lbl s2 k
    end
  | S_if e s1 s2 =>
    match find_label lbl s1 k with
    | Some sk => Some sk
    | None => find_label lbl s2 k
    end
  | S_while e s' =>
    find_label lbl s' (Kwhile e s' k)
  | S_label lbl' s' =>
    if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | S_javatry ll s' =>
    find_label lbl s' (Kjavatry ll k)
  | _ => None
  end.

Definition find_function_by_address (b: block) : option function :=
  (genv_fundefs ge) ! b.

Definition direct_superclass (id: ident) : option ident :=
  match (genv_cenv ge) ! id with
  | Some co =>
    match co_def co with
    | CDclass (Some pid) _ _ _ _ => Some pid
    | _ => None
    end
  | None => None
  end.

Lemma direct_superclass_decrease_depth:
  forall id id',
    direct_superclass id = Some id' ->
    (depthof_id (genv_cenv ge) id' < depthof_id (genv_cenv ge) id) % N.
Proof.
  intros. unfold direct_superclass, depthof_id in *.
  destruct (genv_cenv ge) ! id eqn: E;
    destruct (genv_cenv ge) ! id' eqn: E';
    try congruence.
  - destruct (genv_cenv_consistent ge id c) as [_ _ _ Hdepth].
    auto. rewrite Hdepth. unfold depthof_composite.
    destruct (co_def c); try congruence.
    destruct o; try congruence. unfold depthof_id.
    destruct (genv_cenv ge) ! i eqn: E''; try congruence.
    inversion H; subst. rewrite E'' in E'.
    inversion E'; subst. xomega.
  - destruct (genv_cenv_consistent ge id c) as [_ _ _ Hdepth].
    auto. rewrite Hdepth. unfold depthof_composite.
    destruct (co_def c); try congruence.
    destruct o; try congruence. xomega.
Qed.

(*Program Fixpoint subclass (id1 id2: ident) {measure (N.to_nat (depthof_id (genv_cenv ge) id1))} : bool :=
  if ident_eq id1 id2 then true else
    match direct_superclass id1 with
    | Some id3 => subclass id3 id2
    | None => false
    end.
Next Obligation.
  apply nat_compare_Lt_lt. rewrite <- Nnat.N2Nat.inj_compare.
  apply direct_superclass_decrease_depth; auto.
Qed.*)

(*Definition direct_superinterfaces (id: ident) : list ident :=
  match (genv_cenv ge) ! id with
  | Some co =>
    match co_def co with
    | MCDclass _ li _ _ => li
    | MCDinterface li _ _ => li
    | _ => nil
    end
  | None => nil
  end.*)

Fixpoint find_member_function (l: memberfuncs) (fid: ident) : option ident :=
  match l with
  | MFnil => None
  | MFcons id id' mt _ l' =>
    if (ident_eq fid id) then Some id'
    else find_member_function l' fid
  end.

Program Fixpoint dispatch_function (cid: ident) (fid: ident) {measure (N.to_nat (depthof_id (genv_cenv ge) cid))} : option ident :=
  match (genv_cenv ge) ! cid with
  | Some co =>
    match co_def co with
    | CDclass p _ _ l _ =>
      match p with
      | Some pid =>
        match find_member_function l fid with
        | Some fid' => Some fid'
        | None => dispatch_function pid fid
        end
      | None => find_member_function l fid
      end
    | _ => None
    end
  | _ => None
  end.
Next Obligation.
  apply nat_compare_Lt_lt. rewrite <- Nnat.N2Nat.inj_compare.
  apply direct_superclass_decrease_depth; auto.
  unfold direct_superclass.
  rewrite <- Heq_anonymous0, <- Heq_anonymous1. auto.
Qed.

Variable sub_prim_type : prim_type -> prim_type -> bool.

Fixpoint sub_type (ce: composite_env) (mt1 mt2: type) : bool :=
  match mt1, mt2 with
  | Tprim pt1, Tprim pt2 => prim_type_eq pt1 pt2
  | Tarray mt1' n1, Tarray mt2' n2 => Z.eq_dec n1 n2 && sub_type ce mt1' mt2'
  | Tpointer mt1', Tpointer mt2' => sub_type ce mt1' mt2'
  | Tcomposite id1, Tcomposite id2 =>
    ident_eq id1 id2
    || in_dec ident_eq id2 (superclasses_id ce id1)
    || in_dec ident_eq id2 (superinterfaces_id ce id1)
  | _, _ => false
  end.

Fixpoint find_catch (mt: type) (lbl: label) (s: statement) (k: cont) : option cont :=
  match s with
  | S_seq s1 s2 =>
    match find_catch mt lbl s1 (Kseq s2 k) with
    | Some k' => Some k'
    | None => find_catch mt lbl s2 k
    end
  | S_if e s1 s2 =>
    match find_catch mt lbl s1 k with
    | Some k' => Some k'
    | None => find_catch mt lbl s2 k
    end
  | S_while e s' =>
    find_catch mt lbl s' (Kwhile e s' k)
  | S_label lbl' s' =>
    find_catch mt lbl s' k
  | S_javatry ll s' =>
    find_catch mt lbl s' (Kjavatry ll k)
  | S_javacatch lbl' tyl =>
    if (ident_eq lbl lbl') then
      match find (sub_type (genv_cenv ge) mt) tyl with
      | Some mt' => Some k
      | None => None
      end
    else None
  | _ => None
  end.

Fixpoint find_handler (mt: type) (ll: list label) (s: statement) (k: cont) : option cont :=
  match ll with
  | nil => None
  | lbl :: ll' =>
    match find_catch mt lbl s k with
    | Some k' => Some k'
    | None => find_handler mt ll' s k
    end
  end.

Definition resolve_ref (oe: oenv) (v: val) : option type :=
  match v with
  | Vptr loc ofs =>
    if zeq (Ptrofs.unsigned ofs) 0 then
      match oe ! loc with
      | Some (mt, _, _) => Some mt
      | None => None
      end
    else None
  | _ => None
  end.

Definition resolve_type (oe: oenv) (v: val) (pt: prim_type) : type :=
  match pt with
  | PTref =>
    match resolve_ref oe v with
    | Some mt => (Tpointer mt)
    | None => (Tprim pt)
    end
  | _ => (Tprim pt)
  end.

Definition function_entry := build_lenv_mem (genv_cenv ge).

Definition set_preg (le: lenv) (id: ident) (v: val) (pt: prim_type) : lenv :=
  {| lenv_vars := lenv_vars le;
     lenv_pregs := PTree.set id (v, pt) (lenv_pregs le);
  |}.

Definition set_thrownval (se: senv) (v: val) (pt: prim_type) : senv :=
  {| senv_thrownval := Some (v, pt); |}.

Fixpoint select_switch (n: Z) (dl: label) (ll: list (Z * label)): label :=
  match ll with
  | nil => dl
  | (z, l) :: ll' => if zeq z n then l else select_switch n dl ll'
  end.

Definition dassign (le: lenv) (m: mem) (vid: var_id) (fi: field_id) (v: val) (mt0: type) : option mem :=
  match find_var le vid with
  | Some (loc, (mt, (sc, ta))) =>
      match fieldoffset (genv_cenv ge) mt fi with
      | OK (mt', ofs) =>
        match sem_cast v mt0 mt' m (genv_cenv ge) with
        | Some v' => assign_loc (genv_cenv ge) mt' ta m loc (Ptrofs.repr ofs) v'
        | None => None
        end
      | Error _ => None
      end
  | None => None
  end.

Fixpoint assign_returns (le: lenv) (m: mem) (l: list (var_id * field_id)) (vmtl: list (val * type)) : option mem :=
  match l, vmtl with
  | nil, nil => Some m
  | (vid, fi) :: l', (v, mt) :: vl' =>
    match dassign le m vid fi v mt with
    | Some m' => assign_returns le m' l' vl'
    | None => None
    end
  | _, _ => None
  end.

(** Return the list of blocks in the codomain of [e], with low and high bounds. *)

Definition block_of_binding (id_b_vd: ident * (block * var_def)) :=
  match id_b_vd with (id, (b, (mt, (sc, ta)))) => (b, 0, sizeof (genv_cenv ge) mt ta) end.

Definition blocks_of_lenv (le: lenv) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements (lenv_vars le)).

(** Transition relation *)

Inductive step: state -> trace -> state -> Prop :=
  | step_dassign: forall f vid fi k e le m loc ofs mt mt' sc ta v v' m' oe m'' oe' se,
      find_var le vid = Some (loc, (mt, (sc, ta))) ->
      fieldoffset (genv_cenv ge) mt fi = OK (mt', ofs) ->
      eval_ext_expr se le (e, oe, m) (v, oe', m') ->
      sem_cast v (typeof_ext_expr e) mt' m' (genv_cenv ge) = Some v' ->
      assign_loc (genv_cenv ge) mt' ta m' loc (Ptrofs.repr ofs) v' = Some m'' ->
      step (NormalState f (S_dassign vid fi e) k le oe se m)
        E0 (NormalState f S_skip k le oe' se m'')
  | step_iassign: forall f ty ty' ty'' k e1 e2 le m loc ofs delta v v' m' fi oe oe' m'' se,
      eval_expr se le m e1 (Vptr loc ofs) ->
      ty = Tpointer ty' ->
      fieldoffset (genv_cenv ge) ty' fi = OK (ty'', delta) ->
      eval_ext_expr se le (e2, oe, m) (v, oe', m') ->
      sem_cast v (typeof_ext_expr e2) ty'' m' (genv_cenv ge) = Some v' ->
      assign_loc (genv_cenv ge) ty'' default_type_attr m' loc (Ptrofs.add ofs (Ptrofs.repr delta)) v' = Some m'' ->
      step (NormalState f (S_iassign ty fi e1 e2) k le oe se m)
        E0 (NormalState f S_skip k le oe' se m'')
  | step_regassign_preg_exist: forall f id pt k e le m v0 v v' oe oe' m' se,
      find_preg le id = Some (v0, pt) ->
      eval_ext_expr se le (e, oe, m) (v, oe', m') ->
      sem_cast v (typeof_ext_expr e) (Tprim pt) m' (genv_cenv ge) = Some v' ->
      step (NormalState f (S_regassign pt (Preg id) e) k le oe se m)
        E0 (NormalState f S_skip k (set_preg le id v' pt) oe' se m')
  | step_regassign_preg_fresh: forall f id pt k e le m v v' oe oe' m' se,
      find_preg le id = None ->
      eval_ext_expr se le (e, oe, m) (v, oe', m') ->
      sem_cast v (typeof_ext_expr e) (Tprim pt) m' (genv_cenv ge) = Some v' ->
      step (NormalState f (S_regassign pt (Preg id) e) k le oe se m)
        E0 (NormalState f S_skip k (set_preg le id v' pt) oe' se m')
  | step_regassign_thrownval: forall f pt k e le m v v' oe oe' m' se,
      eval_ext_expr se le (e, oe, m) (v, oe', m') ->
      sem_cast v (typeof_ext_expr e) (Tprim pt) m' (genv_cenv ge) = Some v' ->
      step (NormalState f (S_regassign pt Thrownval e) k le oe se m)
        E0 (NormalState f S_skip k le oe' (set_thrownval se v' pt) m')
  | step_seq: forall f s1 s2 k le oe m se,
      step (NormalState f (S_seq s1 s2) k le oe se m)
        E0 (NormalState f s1 (Kseq s2 k) le oe se m)
  | step_skip_seq: forall f s k le oe m se,
      step (NormalState f S_skip (Kseq s k) le oe se m)
        E0 (NormalState f s k le oe se m)
  | step_if: forall f e s1 s2 k le oe m v b se,
      eval_expr se le m e v ->
      bool_val v (typeof e) m = Some b ->
      step (NormalState f (S_if e s1 s2) k le oe se m)
        E0 (NormalState f (if b then s1 else s2) k le oe se m)
  | step_while: forall f s k e le oe se m,
      step (NormalState f (S_while e s) k le oe se m)
        E0 (NormalState f (S_if e (S_seq s (S_while e s)) S_skip) k le oe se m)
  | step_skip_while:  forall f s k e le oe se m,
      step (NormalState f S_skip (Kwhile e s k) le oe se m)
        E0 (NormalState f (S_while e s) k le oe se m)
  | step_label: forall f lbl s k le oe se m,
      step (NormalState f (S_label lbl s) k le oe se m)
        E0 (NormalState f s k le oe se m)
  | step_goto: forall f lbl k le oe m s' k' se,
      find_label lbl (fun_statement (snd f)) (call_cont k) = Some (s', k') ->
      step (NormalState f (S_goto lbl) k le oe se m)
        E0 (NormalState f s' k' le oe se m)
  | step_switch: forall f dl ll k e le oe m v n se,
      eval_expr se le m e v ->
      sem_switch_arg v (typeof e) = Some n ->
      step (NormalState f (S_switch e dl ll) k le oe se m)
        E0 (NormalState f (S_goto (select_switch n dl ll)) k le oe se m)
  | step_return_nil: forall f k el le oe m m' se,
      eval_exprlist se le m el nil ->
      (type_of_returns (fun_returns (fst f)) = Tnil \/
       type_of_returns (fun_returns (fst f)) = Tcons (Tprim PTvoid) Tnil)->
      Mem.free_list m (blocks_of_lenv le) = Some m' ->
      step (NormalState f (S_return el) k le oe se m)
        E0 (ReturnState nil (call_cont k) oe se m')
  | step_return_cons: forall f k el le oe m m' vl vl' se,
      eval_exprlist se le m el vl ->
      vl <> nil ->
      sem_cast_list vl (typelistof el) (type_of_returns (fun_returns (fst f))) m = Some vl' ->
      Mem.free_list m (blocks_of_lenv le) = Some m' ->
      step (NormalState f (S_return el) k le oe se m)
        E0 (ReturnState vl' (call_cont k) oe se m')
  | step_skip_return: forall f k le oe m m' se,
      is_call_cont k = true ->
      (type_of_returns (fun_returns (fst f)) = Tnil \/
       type_of_returns (fun_returns (fst f)) = Tcons (Tprim PTvoid) Tnil)->
      Mem.free_list m (blocks_of_lenv le) = Some m' ->
      step (NormalState f S_skip k le oe se m)
        E0 (ReturnState nil k oe se m')
  | step_callassigned: forall f fid k el le oe m vl l loc f' vl' se,
      eval_exprlist se le m el vl ->
      find_function_by_name ge fid = Some (loc, f') ->
      sem_cast_list vl (typelistof el) (type_of_params (fun_params (fst f'))) m = Some vl' ->
      step (NormalState f (S_callassigned (Func fid) el l) k le oe se m)
        E0 (CallState f' vl' (Kcall l f le k) oe se m)
  | step_virtualcallassigned: forall cid f fid k el le oe m vl l loc f' vl' e v cid' fid' se,
      eval_expr se le m e v ->
      eval_exprlist se le m el vl ->
      resolve_ref oe v = Some (Tcomposite cid') ->
      (cid = cid' \/ In cid (superclasses_id (genv_cenv ge) cid')) ->
      dispatch_function cid' fid = Some fid' ->
      find_function_by_name ge fid' = Some (loc, f') ->
      sem_cast_list (v :: vl) (typelistof (E_cons e el)) (type_of_params (fun_params (fst f'))) m = Some vl' ->
      step (NormalState f (S_virtualcallassigned cid fid e el l) k le oe se m)
        E0 (CallState f' vl' (Kcall l f le k) oe se m)
  | step_interfaceclasscallassigned: forall cid f fid k el le oe m vl l loc f' vl' e v cid' fid' se,
      eval_expr se le m e v ->
      eval_exprlist se le m el vl ->
      resolve_ref oe v = Some (Tcomposite cid') ->
      In cid (superinterfaces_id (genv_cenv ge) cid') ->
      dispatch_function cid' fid = Some fid' ->
      find_function_by_name ge fid' = Some (loc, f') ->
      sem_cast_list (v :: vl) (typelistof (E_cons e el)) (type_of_params (fun_params (fst f'))) m = Some vl' ->
      step (NormalState f (S_interfacecallassigned cid fid e el l) k le oe se m)
        E0 (CallState f' vl' (Kcall l f le k) oe se m)
  | step_icallassigned: forall f k e el le oe m vl l loc f' vl' se,
      eval_expr se le m e (Vptr loc Ptrofs.zero) ->
      eval_exprlist se le m el vl ->
      find_function_by_address loc = Some f' ->
      sem_cast_list vl (typelistof el) (type_of_params (fun_params (fst f'))) m = Some vl' ->
      step (NormalState f (S_icallassigned e el l) k le oe se m)
        E0 (CallState f' vl' (Kcall l f le k) oe se m)
  | step_javatry: forall f ll s k le oe se m,
      step (NormalState f (S_javatry ll s) k le oe se m)
        E0 (NormalState f s (Kjavatry ll k) le oe se m)
  | step_skip_javatry: forall f ll k le oe se m,
      step (NormalState f S_skip (Kjavatry ll k) le oe se m)
        E0 (NormalState f S_skip k le oe se m)
  (*| step_javacatch: forall f lbl tl s k le oe m,
      step (NormalState f (S_javacatch lbl tl) k le oe m)
        E0 (NormalState f S_skip k le oe m)*)
  | step_javacatch1: forall f ll k k1 k3 le oe m v mt se,
      find_thrownval se = Some (v, mt) ->
      catch_cont k = Kjavatry ll k1 ->
      find_handler (resolve_type oe v mt) ll (fun_statement (snd f)) (call_cont k1) = Some k3 ->
      step (ExceptionState f k le oe se m)
        E0 (NormalState f S_skip k3 le oe se m)
  | step_javacatch2: forall f ll k k1 le oe m v mt se,
      find_thrownval se = Some (v, mt) ->
      catch_cont k = Kjavatry ll k1 ->
      find_handler (resolve_type oe v mt) ll (fun_statement (snd f)) (call_cont k1) = None ->
      step (ExceptionState f k le oe se m)
        E0 (ExceptionState f k1 le oe se m)
  | step_javacatch3: forall f k k1 le oe m f' le' m' l se,
      catch_cont k = Kcall l f' le' k1 ->
      Mem.free_list m (blocks_of_lenv le) = Some m' ->
      step (ExceptionState f k le oe se m)
        E0 (ExceptionState f' k1 le' oe se m')
  | step_throw: forall f k le oe m e v se,
      eval_expr se le m e v ->
      step (NormalState f (S_throw e) k le oe se m)
        E0 (ExceptionState f k le oe (set_thrownval se v (prim_type_of e)) m)
  | step_free: forall f k le oe m e b lo v sz m' se,
      eval_expr se le m e (Vptr b lo) ->
      Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) = Some v ->
      val_to_ptrofs v = Some sz ->
      Ptrofs.unsigned sz > 0 ->
      Mem.free m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) = Some m' ->
      step (NormalState f (S_free e) k le oe se m)
        E0 (NormalState f S_skip k le oe se m')
  | step_free_null: forall f k le oe m e se,
      eval_expr se le m e Vnullptr ->
      step (NormalState f (S_free e) k le oe se m)
        E0 (NormalState f S_skip k le oe se m)
  | step_incref: forall f k le oe m e loc mt n b se,
      prim_type_of e = PTref ->
      eval_expr se le m e (Vptr loc (Ptrofs.repr 0)) ->
      oe ! loc = Some (mt, n, b) ->
      step (NormalState f (S_incref e) k le oe se m)
        E0 (NormalState f S_skip k le (PTree.set loc (mt, S n, b) oe) se m)
  | step_decref: forall f k le oe m e loc mt n b se,
      prim_type_of e = PTref ->
      eval_expr se le m e (Vptr loc (Ptrofs.repr 0)) ->
      oe ! loc = Some (mt, n, b) ->
      step (NormalState f (S_decref e) k le oe se m)
        E0 (NormalState f S_skip k le (PTree.set loc (mt, pred n, b) oe) se m)
  | step_eval: forall f k le oe m e v se,
      eval_expr se le m e v ->
      step (NormalState f (S_eval e) k le oe se m)
        E0 (NormalState f S_skip k le oe se m)
  | step_internal_function: forall f fp fb vl k m le oe se m',
      f = (fp, Some fb) ->
      function_entry (fp, fb) m vl = Some (le, m') ->
      step (CallState f vl k oe se m)
        E0 (NormalState (fp, fb) (fun_statement fb) k le oe se m')
  | step_returnstate: forall f le oe k m m' l vl se,
      assign_returns le m l vl = Some m' ->
      step (ReturnState vl (Kcall l f le k) oe se m)
        E0 (NormalState f S_skip k le oe se m').

(** ** Whole-program semantics *)

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. *)

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state : state -> list (val * type) -> Prop :=
  | final_state_intro: forall vmtl oe se m,
      final_state (ReturnState vmtl Kstop oe se m) vmtl.

End Semantics.

(** The two semantics for function parameters.  First, parameters as local variables. *)

(*Definition MapleSmallstep (p: program) (args: list (val * type)) : res semantics :=
  do (ge, m) <- build_genv_mem p;
  OK (Semantics_gen step (initial_state p args ge) final_state ge ge).*)
