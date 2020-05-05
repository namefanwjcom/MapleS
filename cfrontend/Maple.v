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
Require Import Cop.
Require Import Mapletypes.

Set Implicit Arguments.
Local Open Scope error_monad_scope.

Inductive var_id :=
  | Global : ident -> var_id
  | Local : ident -> var_id.

Theorem var_id_dec : forall v1 v2: var_id, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.

(* Not used?
Inductive identifier :=
  | var_identifier : var_id -> identifier
  | func_identifier : function_name -> identifier.
*)

Definition field_id := ident.

Theorem field_id_dec : forall v1 v2: field_id, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.

Inductive func_id :=
  | Func : ident -> func_id.

Theorem func_id_dec : forall v1 v2: func_id, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.

Inductive intrinsic_func_id :=
  | intrinsic_func_id_string : ident -> intrinsic_func_id.

Theorem intrinsic_func_id_dec : forall v1 v2: intrinsic_func_id, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.

Definition string_literal := ident.

Inductive reg_id :=
  | Preg : ident -> reg_id
  | SP
  | FP
  | GP
  | PC
  | Thrownval
  | Retval: ident -> reg_id.

Theorem reg_id_dec : forall v1 v2: reg_id, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.

Inductive label :=
  | Label : ident -> label.

Theorem label_dec : forall v1 v2: label, {v1 = v2} + {v1 <> v2}.
Proof. repeat (decide equality). Qed.

(*
Inductive leaf :=
  | dread : prim_type -> var_id -> field_id -> leaf
  | regread : prim_type -> reg_id -> leaf
  | addrof : prim_type -> var_id -> field_id -> leaf
  | addroflable : prim_type -> label -> leaf
  | addroffunc : prim_type -> func_id -> leaf
  | conststr : prim_type -> string_literal -> leaf
  | conststr16 : prim_type -> string_literal -> leaf
  | constval : prim_type -> const_value -> leaf
  | sizeoftype : prim_type -> type -> leaf.
Locate "+".
Check (list nat + nat)%type.
*)
Definition boffset := N.

Definition bsize := N.

Definition Boffset := N.

Inductive const_value :=
  | const_int_val: int -> const_value
  | const_float_val: float -> const_value
  (*| const_complex_val: complex -> const_val*).

Inductive expression :=
(* storage read expression *)
  | dread : prim_type -> var_id -> field_id -> expression
  | regread : prim_type -> reg_id -> expression
  | iread : prim_type -> type -> field_id -> expression -> expression
  | ireadoff : prim_type -> Boffset -> expression -> expression
  | ireadfpoff : prim_type -> Boffset -> expression -> expression
(* leaf expression *)
  | addrof : prim_type -> var_id -> field_id -> expression
  | addroflable : prim_type -> label -> expression
  | addroffunc : prim_type -> func_id -> expression
  | conststr : prim_type -> string_literal -> expression
  | conststr16 : prim_type -> string_literal -> expression
  | constval : prim_type -> const_value -> expression
  | sizeoftype : prim_type -> type -> expression
(* unary expression *)
  | abs : prim_type -> expression -> expression
  | bnot : prim_type -> expression -> expression
  | extractbits : prim_type -> boffset -> bsize -> expression
  | iaddrof : prim_type -> type -> field_id -> expression -> expression
  | lnot : prim_type -> expression -> expression
  | neg : prim_type -> expression -> expression
  | recip : prim_type -> expression -> expression
  | sext : prim_type -> bsize -> expression -> expression
  | sqrt : prim_type -> expression -> expression
  | zext : prim_type -> bsize -> expression -> expression
(* type conversion expression *)
  | ceil : prim_type -> prim_type -> expression -> expression
  | cvt : prim_type -> prim_type -> expression -> expression
  | floor : prim_type -> prim_type -> expression -> expression
  | retype : prim_type -> type -> expression -> expression
  | round : prim_type -> prim_type -> expression -> expression
  | trunc : prim_type -> prim_type -> expression -> expression
(* binary expression *)
  | add : prim_type -> expression -> expression -> expression
  | ashr : prim_type -> expression -> expression -> expression
  | band : prim_type -> expression -> expression -> expression
  | bior : prim_type -> expression -> expression -> expression
  | bxor : prim_type -> expression -> expression -> expression
  | cand : prim_type -> expression -> expression -> expression
  | cior : prim_type -> expression -> expression -> expression
  | cmp : prim_type -> prim_type -> expression -> expression -> expression
  | cmpg : prim_type -> prim_type -> expression -> expression -> expression
  | cmpl : prim_type -> prim_type -> expression -> expression -> expression
  | depositbits : prim_type -> boffset -> bsize -> expression -> expression -> expression
  | div : prim_type -> expression -> expression -> expression
  | eq : prim_type -> prim_type -> expression -> expression -> expression
  | ge : prim_type -> prim_type -> expression -> expression -> expression
  | gt : prim_type -> prim_type -> expression -> expression -> expression
  | land : prim_type -> expression -> expression -> expression
  | lior : prim_type -> expression -> expression -> expression
  | le : prim_type -> prim_type -> expression -> expression -> expression
  | lshr : prim_type -> expression -> expression -> expression
  | lt : prim_type -> prim_type -> expression -> expression -> expression
  | max : prim_type -> expression -> expression -> expression
  | min : prim_type -> expression -> expression -> expression
  | mul : prim_type -> expression -> expression -> expression
  | ne : prim_type -> prim_type -> expression -> expression -> expression
  | rem : prim_type -> expression -> expression -> expression
  | shl : prim_type -> expression -> expression -> expression
  | sub : prim_type -> expression -> expression -> expression
(* ternary expression *)
  | select : prim_type -> expression -> expression -> expression -> expression
(* N-ary expression *)
  | array : bool -> type -> type -> list expression -> expression
  | intrinsicop : prim_type -> intrinsic_func_id -> list expression -> expression
  | intrinsicopwithtype : prim_type -> type -> intrinsic_func_id -> list expression -> expression.

(* To do *)
Definition jump_table := list label.

Inductive statement :=
(* storage assignment *)
  | dassign (v: var_id) (f: field_id) (rhs_expr: expression)
  | iassign (t: type) (f: field_id) (addr_expr rhs_expr: expression)
  | iassignoff (t: prim_type) (Bofs: Boffset) (addr_expr rhs_expr: expression)
  | iassignfpoff (t: prim_type) (Bofs: Boffset) (rhs_expr: expression)
  | regassign (t: prim_type) (r: reg_id) (rhs_expr: expression)
(* sequence *)
  | seq (first_part second_part: statement)
(* hierarchical control flow *)
  | doloop (do_var: ident) (start_expr cont_expr incr_amt: expression) (body_stmts: statement)
  | dowhile (body_stmts: statement) (cond_expr: expression)
  | foreachelem (elem_var: ident) (collection_var: var_id) (body_stmts: statement)
  | If (cond_expr: expression) (then_part else_part: statement)
  | while (cond_expr: expression) (body_stmts: statement)
(* falt control flow statements *)
  | brfalse (l: label) (opnd: expression)
  | brtrue (l: label) (opnd: expression)
  | goto (l: label)
  | multiway (opnd: expression) (default_label: label) (label_table: list (expression * label))
  | Return (retlist: list expression)
  | switch (opnd: expression) (default_label: label) (label_table: list (int * label))
  | rangegoto (opnd: expression) (tag_offset: expression)(label_table: list (int * label))
  | indexgoto (opnd: expression) (jt: jump_table)
(* call statements *)
  | call (f: func_id) (opndlist: list expression)
  | icall (f_ptr: expression) (opndlist: list expression)
  | intrinsiccall (f: intrinsic_func_id) (opndlist: list expression)
  | xintrinsiccall (user_intrinsiccall_index: expression) (opndlist: list expression)
(* To do: callinstant *)
  (*| callinstant *)
(* java call statements *)
  | virtualcall (f: func_id) (obj_ptr: expression) (opndlist: list expression)
  | superclasscall (f: func_id) (obj_ptr: expression) (opndlist: list expression)
  | interfacecall (f: func_id) (obj_ptr: expression) (opndlist: list expression)
  (*| virtuallcallinstant *)
  (*| superclasscallinstant *)
  (*| interfacecallinstant *)
  | callassigned (f: func_id) (opndlist: list expression) (assignlist: list (var_id * field_id))
  (*| callinstantassigned *)
  | icallassigned (f_ptr: expression) (opndlist: list expression) (assignlist: list (var_id * field_id))
  | intrinsiccallassigned (f: intrinsic_func_id) (opndlist: list expression) (assignlist: list (var_id * field_id))
  (*| intrinsiccallwithtypeassigned *)
  | xintrinsiccallassigned (user_intrinsiccall_index: expression) (opndlist: list expression) (assignlist: list (var_id * field_id))
  | virtualcallassigned (f: func_id) (obj_ptr: expression) (opndlist: list expression) (assignlist: list (var_id * field_id))
  (*| virtualcallinstantassigned *)
  | superclasscallassigned (f: func_id) (obj_ptr: expression) (opndlist: list expression) (assignlist: list (var_id * field_id))
  (*| superclasscallinstantassigned *)
  | interfacecallassigned (f: func_id) (obj_ptr: expression) (opndlist: list expression) (assignlist: list (var_id * field_id))
  (*| interfacecallinstantassigned *)
(* exception handling *)
  | javatrycatchfinally (hl: list label) (fl: label) (s: statement)
  | javatrycatch (hl: list label) (s: statement)
  | javatryfinally (fl: label) (s: statement)
  | throw (opnd: expression)
  | catch (hl: label) (t: type) (s: statement)
  | finally (fl: label) (s: statement)
  | cleanuptry
  | endtry (l: label)
  | gosub (fl: label)
  | retsub
(* memory allocation and deallocation *)
  | alloca (pt: prim_type) (opnd: expression)
  | decref (opnd: expression)
  | decrefwithcheck (opnd: expression)
  | free (opnd: expression)
  | gcmalloc (ppt: type) (t: type)
  | gcmallocjarray (ppt: type) (t: type) (opnd: expression)
  | incref (opnd: expression)
  | malloc (ppt: type) (opnd: expression)
(* other statements *)
  | assertge (opnd0 opnd1: expression)
  | assertlt (opnd0 opnd1: expression)
  | assertnonnull (opnd: expression)
  | eval (opnd: expression)
  | membaracquire
  | membarrelease
  | membarfull
  | syncenter (opnd: expression)
  | syncexit (opnd: expression).

Inductive class_attr :=
.

Inductive interface_attr :=
.

Definition var_def := (type * var_attr) % type.

Record function : Type := mkfunction {
  fun_returns: typelist;
  fun_params: list (ident * type);
  fun_vars: list (ident * var_def);
  fun_types: list (ident * type);
  fun_pregs: list (ident * prim_type);
  fun_body: statement
}.

Definition func_def := (function * func_attr) % type.

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fun_params f)) (fun_returns f).

Record program : Type := {
  prog_vars: list (ident * var_def);
  prog_types: list (ident * type);
  prog_comps: list (ident * composite_definition);
  prog_funcs: list (ident * func_def);
  prog_main: ident;
  prog_javaclass_attrs: list (ident * class_attr);
  prog_javainterface_attrs: list (ident * interface_attr);
}.

Definition myvar_def := (mytype * var_attr) % type.

Inductive global_def :=
  | global_var_def : myvar_def -> global_def
  | global_func_def : func_def -> global_def.

Record genv := mkgenv {
  genv_vars: PTree.t block;
  genv_mytypes: PTree.t mytype;
  genv_comps: composite_env;
  genv_funcs: PTree.t block;
  genv_javaclass_attrs: PTree.t class_attr;
  genv_javainterface_attrs: PTree.t interface_attr;
  genv_defs: PTree.t global_def;
}.

Section Build_genv_mem.

Variable p: program.

Section Add_globals.

Variable ce: composite_env.

Definition add_globalvar (gem: genv * mem) (x: ident * var_def) : res (genv * mem) :=
  let (ge, m) := gem in
  let (id, vd) := x in
  let (ty, va) := vd in
  match (genv_vars ge) ! id with
  | Some _ => Error (MSG "multiple definitions of " :: CTX id:: nil)
  | None =>
    do mt <- type_to_mytype (genv_mytypes ge) ty;
      match complete_mytype ce mt with
      | true =>
        let (m', b) := Mem.alloc m 0 (sizeof ce mt) in
        OK (mkgenv
              (PTree.set id b ge.(genv_vars))
              (ge.(genv_mytypes))
              (ge.(genv_comps))
              (ge.(genv_funcs))
              (ge.(genv_javaclass_attrs))
              (ge.(genv_javainterface_attrs))
              (PTree.set b (global_var_def (mt, va)) ge.(genv_defs)), m')
      | false => Error (MSG "the type of " :: CTX id :: MSG " is incomplete" :: nil)
      end
  end.

Definition add_globalvars (gem: genv * mem) : res (genv * mem) :=
  mfold_left add_globalvar (prog_vars p) gem.

Definition add_func (gem: genv * mem) (x: ident * func_def) : res (genv * mem) :=
  let (ge, m) := gem in
  let (id, fd) := x in
  let (f, fa) := fd in
  match (genv_funcs ge) ! id with
  | Some _ =>
    Error (MSG "multiple definitions of " :: CTX id :: nil)
  | None =>
    do mt <- type_to_mytype (genv_mytypes ge) (type_of_function f);
      match complete_mytype ce mt with
      | false => Error ((MSG "the type of " :: CTX id :: MSG " is incomplete" :: nil))
      | true =>
        let (m', b) := Mem.alloc m 0 (sizeof ce mt) in
        OK (mkgenv
              (ge.(genv_vars))
              (ge.(genv_mytypes))
              (ge.(genv_comps))
              (PTree.set id b ge.(genv_funcs))
              (ge.(genv_javaclass_attrs))
              (ge.(genv_javainterface_attrs))
              (PTree.set b (global_func_def (snd x)) ge.(genv_defs)), m')
      end
  end.

Definition add_funcs (gem: genv * mem) : res (genv * mem) :=
  mfold_left add_func (prog_funcs p) gem.

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
            (ge.(genv_comps))
            (ge.(genv_funcs))
            (PTree.set id ca ge.(genv_javaclass_attrs))
            (ge.(genv_javainterface_attrs))
            (ge.(genv_defs)))
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
            (ge.(genv_comps))
            (ge.(genv_funcs))
            (ge.(genv_javaclass_attrs))
            (PTree.set id ia ge.(genv_javainterface_attrs))
            (ge.(genv_defs)))
    end
  end.

Definition add_javainterface_attrs (ge: genv) : res genv :=
  mfold_left add_javainterface_attr (prog_javainterface_attrs p) ge.

Definition init_genv (te: PTree.t mytype) : res genv :=
  do te' <- check_complete ce te;
  OK (mkgenv
        (PTree.empty block)
        (te')
        (PTree.empty composite)
        (PTree.empty block)
        (PTree.empty class_attr)
        (PTree.empty interface_attr)
        (PTree.empty global_def)).

End Add_globals.

Definition build_genv_mem : res (genv * mem) :=
  do te <- add_types (prog_types p);
    do ce <- build_composite_env te (prog_comps p);
    do ge1 <- init_genv ce te;
    do (ge2, m2) <- add_globalvars ce (ge1, Mem.empty);
    do (ge3, m3) <- add_funcs ce (ge2, m2);
    do ge4 <- add_javaclass_attrs ce ge3;
    do ge5 <- add_javainterface_attrs ce ge4;
    OK (ge5, m3).

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

(* Inductive value : Type :=
  | Vundef : value
  | Vint : int -> value
  | Vlong : int64 -> value
  | Vfloat : float -> value
  | Vsingle : float32 -> value
  | Vptr : block -> ptrofs -> value. *)
*)
Record lenv := mklenv {
  lenv_vars: PTree.t (block * myvar_def);
  lenv_mytypes: PTree.t mytype;
  lenv_pregs: PTree.t (prim_type * val);
  (*lenv_def: PTree.t var_def;*)
}.

(* the object environment maps each unique object_id to its block number in the heap, the class it belongs to and the count it is referred to. *)
Definition oenv := PTree.t (block * ptrofs * ident * positive).

(** [deref_loc ty m b ofs v] computes the value of a datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  If the type [ty] indicates an access by value, the corresponding
  memory load is performed.  If the type [ty] indicates an access by
  reference or by copy, the pointer [Vptr b ofs] is returned. *)

Fixpoint deref_loc (mt: mytype) (m: mem) (b: block) (ofs: ptrofs) : option val :=
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

Fixpoint assign_loc (ce: composite_env) (mt: mytype) (ta: type_attr) (m: mem) (b: block) (ofs: ptrofs) (v: val) : option mem :=
  match access_mode mt with
  | By_value chunk => Mem.storev chunk m (Vptr b ofs) v
  | By_copy =>
    match v with
    | Vptr b' ofs' =>
      if (Zdivide_dec (alignof ce mt ta) (Ptrofs.unsigned ofs')) then
        if (Zdivide_dec (alignof ce mt ta) (Ptrofs.unsigned ofs')) then
          if ((negb (b =? b')%positive)
              || (Ptrofs.unsigned ofs' =? Ptrofs.unsigned ofs)
              || (Ptrofs.unsigned ofs' + sizeof ce mt <=? Ptrofs.unsigned ofs)
              || (Ptrofs.unsigned ofs + sizeof ce mt <=? Ptrofs.unsigned ofs'))
          then
            match (Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce mt)) with
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

Variable f: function.

Section Add_locals.

(** Allocation of function-local variables.
  [alloc_variables e1 m1 vars e2 m2] allocates one memory block
  for each variable declared in [vars], and associates the variable
  name with this block.  [e1] and [m1] are the initial local environment
  and memory state.  [e2] and [m2] are the final local environment
  and memory state. *)

Definition add_localvar (lem: lenv * mem) (x: ident * myvar_def) : res (lenv * mem) :=
  let (le, m) := lem in
  let (id, vd) := x in
  let (mt, va) := vd in
  match (lenv_vars le) ! id with
  | Some _ => Error (MSG "multiple definitions of " :: CTX id:: nil)
  | None =>
    match complete_mytype ce mt with
    | true =>
      let (m', b) := Mem.alloc m 0 (sizeof ce mt) in
      OK (mklenv
            (PTree.set id (b, (mt, va)) (lenv_vars le))
            (lenv_mytypes le)
            (lenv_pregs le), m')
    | false => Error (MSG "the type of " :: CTX id :: MSG " is incomplete" :: nil)
    end
  end.

Fixpoint params_to_vars (l: list (ident * type)) : list (ident * var_def) :=
  match l with
  | nil => nil
  | (id, ty) :: l' =>(id, (ty, default_var_attr)) :: params_to_vars l'
  end.

Fixpoint change_type_of_vars (te: PTree.t mytype) (l: list (ident * var_def)) : res (list (ident * myvar_def)) :=
  match l with
  | nil => OK nil
  | (id, (ty, va)) :: l' =>
    do mt <- type_to_mytype te ty;
      do ml' <- change_type_of_vars te l';
      OK ((id, (mt, va)) :: ml')
  end.

Fixpoint change_type_of_params (te: PTree.t mytype) (l: list (ident * type)) : res (list (ident * mytype)) :=
  match l with
  | nil => OK nil
  | (id, ty) :: l' =>
    do mt <- type_to_mytype te ty;
      do ml' <- change_type_of_params te l';
      OK ((id, mt) :: ml')
  end.

Definition add_localvars (lem: lenv * mem) : res (lenv * mem) :=
  let (le, m) := lem in
  do l <- change_type_of_vars (lenv_mytypes le) (params_to_vars (fun_params f) ++ fun_vars f);
  mfold_left add_localvar l lem.

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

Fixpoint bind_parameters (le: lenv) (m: mem) (l: list (ident * mytype)) (vl: list val) : option mem :=
  match l, vl with
  | nil, nil => Some m
  | (id, mt) :: l', v :: vl' =>
    match PTree.get id (lenv_vars le) with
    | Some (b, (mt, (_, ta))) =>
      match (assign_loc ce mt ta m b Ptrofs.zero v) with
      | Some m1 => bind_parameters le m1 l' vl'
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
      match complete_mytype ce (MTprim pt) with
      | true =>
        OK (mklenv
              (lenv_vars le)
              (lenv_mytypes le)
              (PTree.set id (pt, Vundef) (lenv_pregs le)))
      | false => Error (MSG "the type of " :: CTX id :: MSG " is incomplete" :: nil)
      end
  end.

Definition add_pregs (lem: lenv) : res lenv :=
  mfold_left add_preg (fun_pregs f) lem.

(** Return the list of blocks in the codomain of [e], with low and high bounds. *)
(*
Definition block_of_binding (id_b_ty: ident * (block * var_def)) :=
  match id_b_ty with (_, (b, (t, _))) => (b, 0, sizeof' t) end.

Definition blocks_of_env (e: lenv) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements e.(lenv_var)).
*)

End Add_locals.

Definition init_lenv (te: PTree.t mytype) : lenv :=
  mklenv
    (PTree.empty (block * myvar_def))
    (te)
    (PTree.empty (prim_type * val)).

Definition build_lenv_mem (m: mem) (vl: list val) : option (lenv * mem) :=
  match add_types (fun_types f) with
  | OK te =>
    match check_complete ce te with
    | OK te' =>
      match add_localvars ((init_lenv te'), m) with
      | OK (le1, m1) =>
        match change_type_of_params (lenv_mytypes le1) (fun_params f) with
        | OK l =>
          match bind_parameters le1 m1 l vl with
          | Some m2 =>
            match add_pregs le1 with
            | OK le2 => Some (le2, m2)
            | Error _ => None
            end
          | None => None
          end
        | Error _ => None
        end
      | Error _ => None
      end
    | Error _ => None
    end
  | Error _ => None
  end.

End Build_lenv_mem.

Section SEMANTICS.

Variable ge: genv.

(** ** Transition semantics for statements and functions *)

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont
  | Kgoto: label -> cont -> cont
  | Kreturn: cont -> cont
  | Kcatch: list label -> cont -> cont
  | Kfinally: label -> cont -> cont
  | Kcatchfinally: list label -> label -> cont -> cont
  | Kexception: block -> ptrofs -> cont -> cont
  (*| Kseq: statement -> cont -> cont       (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
  | Kloop1: statement -> statement -> cont -> cont (**r [Kloop1 s1 s2 k] = after [s1] in [Sloop s1 s2] *)
  | Kloop2: statement -> statement -> cont -> cont (**r [Kloop1 s1 s2 k] = after [s2] in [Sloop s1 s2] *)
  | Kswitch: cont -> cont       (**r catches [break] statements arising out of [switch] *)*)
  | Kcall: option ident ->                  (**r where to store result *)
           function ->                      (**r calling function *)
           lenv ->                          (**r local env of calling function *)
           cont -> cont.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  (*| Kseq s k => call_cont k
  | Kloop1 s1 s2 k => call_cont k
  | Kloop2 s1 s2 k => call_cont k
  | Kswitch k => call_cont k*)
  | Kgoto _ k => call_cont k
  | Kreturn k => call_cont k
  | Kcatch _ k => call_cont k
  | Kexception _ _ k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ => True
  | Kfinally _ _ => True
  | Kcatchfinally _ _ _ => True
  | _ => False
  end.

Fixpoint catch_cont (k: cont) : cont :=
  match k with
  (*| Kseq s k => call_cont k
  | Kloop1 s1 s2 k => call_cont k
  | Kloop2 s1 s2 k => call_cont k
  | Kswitch k => call_cont k*)
  | Kgoto _ k => call_cont k
  | Kreturn k => call_cont k
  | Kfinally _ k => call_cont k
  | Kexception _ _ k => call_cont k
  | _ => k
  end.

(** States *)

Inductive state: Type :=
  | State
      (f: function)
      (s: statement)
      (k: cont)
      (le: lenv)
      (oe: oenv)
      (m: mem) : state
  | CallState
      (f: function)
      (args: list val)
      (k: cont)
      (oe: oenv)
      (m: mem) : state
  | ReturnState
      (res: val)
      (k: cont)
      (oe: oenv)
      (m: mem) : state
  | ExceptionState
      (f: function)
      (obj: block * ptrofs)
      (k: cont)
      (le: lenv)
      (oe: oenv)
      (m: mem) : state.

End SEMANTICS.

Definition empty_oenv := PTree.empty (block * ptrofs * ident * positive).

Definition initial_state (p: program) (vl: list val) : res state :=
  do (ge, m) <- build_genv_mem p;
    match (genv_funcs ge) ! (prog_main p) with
    | Some b =>
      match (genv_defs ge) ! b with
      | Some (global_func_def (f, fa)) =>
        OK (CallState f vl Kstop empty_oenv m)
      | _ =>
        Error (MSG "cannot find the entry function " :: CTX (prog_main p) :: nil)
      end
    | None =>
      Error (MSG "cannot load the entry function " :: CTX (prog_main p) :: nil)
    end.

