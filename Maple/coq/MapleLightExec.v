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
Require Import MapleLight.

Local Open Scope error_monad_scope.

Section Semantics.

Variable ge: genv.

Section Eval_ext_expr.

Variable se: senv.

Variable le: lenv.

Section Eval_expr.

Variable m: mem.

Fixpoint eval_array (b: bool) (t: type) (vl: list val) {struct vl} : option ptrofs :=
  match vl with
  | nil => None
  | Vint i :: nil =>
    match t with
    | Tpointer (Tarray mt' len) =>
      if b then
        match (Int.intval i) ?= len with
        | Lt =>
          Some (Ptrofs.repr (Int.intval i * (sizeof (genv_cenv ge) mt' default_type_attr)))
        | _ => None
        end
      else
        Some (Ptrofs.repr (Int.intval i * (sizeof (genv_cenv ge) mt' default_type_attr)))
    | _ => None
    end
  | Vint i :: vl =>
    match t with
    | Tpointer (Tarray mt' len) =>
      if b then
        match (Int.intval i) ?= len with
        | Lt =>
          match eval_array b mt' vl with
          | Some ofs => Some (Ptrofs.add ofs (Ptrofs.repr (Int.intval i * (sizeof (genv_cenv ge) mt' default_type_attr))))
          | None => None
          end
        | _ => None
        end
      else
        match eval_array b mt' vl with
        | Some ofs => Some (Ptrofs.add ofs (Ptrofs.repr (Int.intval i * (sizeof (genv_cenv ge) mt' default_type_attr))))
        | None => None
        end
    | _ => None
    end
  | _ => None
  end.

Function eval_expr (e: expr) {struct e} : option val :=
  match e with
  | E_constval pt (C_int i) =>
    sem_cast (Vint i) (Tprim (PTint I32 Unsigned)) (Tprim pt) m (genv_cenv ge)
  | E_constval pt (C_long i) =>
    sem_cast (Vlong i) (Tprim (PTint I64 Unsigned)) (Tprim pt) m (genv_cenv ge)
  | E_constval pt (C_single f) =>
    sem_cast (Vsingle f) (Tprim (PTfloat F32)) (Tprim pt) m (genv_cenv ge)
  | E_constval pt (C_float f) =>
    sem_cast (Vfloat f) (Tprim (PTfloat F64)) (Tprim pt) m (genv_cenv ge)
  | E_dread pt vid fi =>
    match find_var ge le vid with
    | Some (b, (mt, va)) =>
      match fieldoffset (genv_cenv ge) mt fi with
      | OK (mt', ofs) =>
        match deref_loc mt' m b (Ptrofs.repr ofs) with
        | Some v =>
          sem_cast v mt' (Tprim pt) m (genv_cenv ge)
        | None => None
        end
      | Error _ => None
      end
    | None => None
    end
  | E_iread pt ty fi e =>
    match eval_expr e with
    | Some (Vptr b ofs) =>
      match ty with
      | Tpointer mt' =>
        match fieldoffset (genv_cenv ge) mt' fi with
        | OK (mt'', delta) =>
          match  deref_loc mt'' m b (Ptrofs.add ofs (Ptrofs.repr delta)) with
          | Some v =>
            sem_cast v mt'' (Tprim pt) m (genv_cenv ge)
          | None => None
          end
        | Error _ => None
        end
      | _ => None
      end
    | _ => None
    end
  | E_regread pt' rid =>
    match find_reg se le rid with
    | Some (v, pt) =>
      sem_cast v (Tprim pt) (Tprim pt') m (genv_cenv ge)
    | None => None
    end
  | E_addrof pt vid fi =>
    if is_pointer_prim_type pt then
      match find_var ge le vid with
      | Some (b, (mt, va)) =>
        match fieldoffset (genv_cenv ge) mt fi with
        | OK (mt', ofs) =>
          Some (Vptr b (Ptrofs.repr ofs))
        | Error _ => None
        end
      | None => None
      end
    else None
  | E_iaddrof pt ty fi e =>
    if is_pointer_prim_type pt then
      match eval_expr e with
      | Some (Vptr b ofs) =>
        match ty with
        | Tpointer mt' =>
          match fieldoffset (genv_cenv ge) mt' fi with
          | OK (mt'', delta) =>
            Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr delta)))
          | Error _ => None
          end
        | _ => None
        end
      | _ => None
      end
    else None
  | E_addroffunc pt (Func id) =>
    match (genv_funcs ge) ! id with
    | Some b =>
      match pt with
      | PTaddr A32 | PTaddr A64 => Some (Vptr b (Ptrofs.repr 0))
      | _ => None
      end
    | None => None
    end
  | E_sizeoftype pt ty =>
    sem_cast (Vptrofs (Ptrofs.repr (sizeof (genv_cenv ge) ty default_type_attr))) (Tprim (if Archi.ptr64 then (PTint I64 Unsigned) else (PTint I32 Unsigned))) (Tprim pt) m (genv_cenv ge)
  | E_retype pt ty e =>
    match eval_expr e with
    | Some v =>
      sem_cast v ty (Tprim pt) m (genv_cenv ge)
    | None => None
    end
  | E_cvt pt' pt e =>
    match eval_expr e with
    | Some v =>
      sem_cast v (Tprim pt) (Tprim pt') m (genv_cenv ge)
    | None => None
    end
  | E_ceil pt' pt e =>
    match eval_expr e with
    | Some v =>
      sem_ceil v pt pt'
    | None => None
    end
  | E_floor pt' pt e =>
    match eval_expr e with
    | Some v =>
      sem_floor v pt pt'
    | None => None
    end
  | E_trunc pt' pt e =>
    match eval_expr e with
    | Some v =>
      sem_trunc v pt pt'
    | None => None
    end
  | E_unary op pt e =>
    match eval_expr e with
    | Some v =>
      sem_unary_operation op v (typeof e) (Tprim pt) m (genv_cenv ge)
    | None => None
    end
  | E_binary op pt e1 e2 =>
    match eval_expr e1 with
    | Some v1 =>
      match eval_expr e2 with
      | Some v2 =>
        sem_binary_operation op v1 (typeof e1) v2 (typeof e2) (Tprim pt) m (genv_cenv ge)
      | None => None
      end
    | None => None
    end
  | E_cand pt e1 e2 =>
    if is_int_prim_type pt then
      match eval_expr e1 with
      | Some v1 =>
        match bool_val v1 (typeof e1) m with
        | Some true =>
          match eval_expr e2 with
          | Some v2 =>
            match bool_val v2 (typeof e2) m with
            | Some b => Some (Val.of_bool b)
            | None => None
            end
          | None => None
          end
        | Some false => Some (Val.of_bool false)
        | None => None
        end
      | None => None
      end
    else None
  | E_cior pt e1 e2 =>
    if is_int_prim_type pt then
      match eval_expr e1 with
      | Some v1 =>
        match bool_val v1 (typeof e1) m with
        | Some false =>
          match eval_expr e2 with
          | Some v2 =>
            match bool_val v2 (typeof e2) m with
            | Some b => Some (Val.of_bool b)
            | None => None
            end
          | None => None
          end
        | Some true => Some (Val.of_bool true)
        | None => None
        end
      | None => None
      end
    else None
  | E_select pt e1 e2 e3 =>
    if prim_type_eq (prim_type_of e2) pt
       && prim_type_eq (prim_type_of e3) pt
    then
      match eval_expr e1 with
      | Some v1 =>
        match bool_val v1 (typeof e1) m with
        | Some true => eval_expr e2
        | Some false => eval_expr e3
        | None => None
        end
      | None => None
      end
    else None
  | E_array _ _ _ E_nil => None
  | E_array b pt ty (E_cons e el) =>
    if is_pointer_prim_type pt then
      match eval_expr e with
      | Some (Vptr loc ofs) =>
        match eval_exprlist el with
        | Some vl =>
          match eval_array b ty vl with
          | Some delta => Some (Vptr loc (Ptrofs.add ofs delta))
          | None => None
          end
        | None => None
        end
      | _ => None
      end
    else None
  end
with eval_exprlist (el: exprlist) {struct el} : option (list val) :=
       match el with
       | E_nil => Some nil
       | E_cons e el' =>
         match eval_expr e with
         | Some v =>
           match eval_exprlist el' with
           | Some vl => Some (v :: vl)
           | None => None
           end
         | None => None
         end
       end.

Lemma eval_array_sound: forall b vl mt ofs,
    eval_array b mt vl = Some ofs ->
    MapleLight.eval_array ge b mt vl ofs.
Proof.
  intros b vl. induction vl; intros; simpl in *.
  - inversion H.
  - destruct a; try congruence. destruct vl; try congruence.
    + destruct mt; try congruence. destruct mt; try congruence. destruct b.
      { destruct (Int.intval i ?= z) eqn: E1; try congruence.
        inversion H; subst. econstructor; eauto. }
      { inversion H; subst. econstructor; eauto. }
    + destruct mt; try congruence. destruct mt; try congruence. destruct b.
      { destruct (Int.intval i ?= z) eqn: E1; try congruence.
        destruct (eval_array true mt (v :: vl)) eqn: E2; try congruence.
        inversion H; subst. econstructor; eauto. }
      { destruct (eval_array false mt (v :: vl)) eqn: E2; try congruence.
        inversion H; subst. econstructor; eauto. }
Qed.

Lemma eval_expr_sound: forall e v,
    eval_expr e = Some v ->
    MapleLight.eval_expr ge se le m e v
with eval_exprlist_sound: forall el vl,
    eval_exprlist el = Some vl ->
    MapleLight.eval_exprlist ge se le m el vl.
Proof.
  intros e. (*clear eval_expr_sound.*)
  induction e; simpl in *; intros; try congruence.
  - (* E_dread *)
    destruct (find_var ge le v) eqn: E1; try congruence.
    destruct p0 eqn: E2. destruct v1 eqn: E3.
    destruct (fieldoffset (genv_cenv ge) t f) eqn: E4; try congruence.
    destruct p1 eqn: E6.
    destruct (deref_loc t0 m b (Ptrofs.repr z)) eqn: E7; try congruence.
    econstructor; eauto.
  - (* E_regread *)
    destruct (find_reg se le r) eqn: E1; try congruence.
    destruct p0 eqn: E2. eapply eval_Eregread; eauto.
  - (* E_iread *)
    destruct (eval_expr e) eqn: E1; try congruence.
    destruct v0 eqn: E2; try congruence.
    destruct t eqn: E4; try congruence.
    destruct (fieldoffset (genv_cenv ge) t0 f) eqn: E5; try congruence.
    destruct p0 eqn: E6.
    destruct (deref_loc t1 m b (Ptrofs.add i (Ptrofs.repr z))) eqn: E7; try congruence.
    econstructor; eauto.
  - (* E_addrof *)
    destruct (is_pointer_prim_type p) eqn: E1.
    destruct (find_var ge le v) eqn: E2. destruct p0 eqn: E3.
    destruct v1 eqn: E4.
    destruct (fieldoffset (genv_cenv ge) t f) eqn: E5.
    destruct p1 eqn: E6. inversion H; subst.
    econstructor; eauto. inversion H.
    inversion H. inversion H.
  - (*E_addroffunc *)
    destruct f eqn: E1. destruct ((genv_funcs ge) ! i) eqn: E2.
    destruct p eqn: E3. inversion H. inversion H.
    inversion H. inversion H. inversion H. inversion H.
    destruct a eqn: E4.
    inversion H; subst. econstructor; eauto.
    inversion H; subst. econstructor; eauto.
    inversion H. inversion H.
  - (* E_constval *)
    destruct c eqn: E1; try congruence; econstructor; eauto.
  - (* E_sizeoftype *)
    econstructor; eauto.
  - (* E_unary *)
    destruct (eval_expr e) eqn: E1; try congruence.
    econstructor; eauto.
  - (* E_iaddrof *)
    destruct (is_pointer_prim_type p) eqn: E1; try congruence.
    destruct (eval_expr e) eqn: E2; try congruence.
    destruct v0 eqn: E3; try congruence.
    destruct t eqn: E5; try congruence.
    destruct (fieldoffset (genv_cenv ge) t0 f) eqn: E6; try congruence.
    destruct p0 eqn: E7. inversion H; subst.
    econstructor; eauto.
  - (* E_ceil *)
    destruct (eval_expr e) eqn: E1; try congruence.
    econstructor; eauto.
  - (* E_cvt *)
    destruct (eval_expr e) eqn: E1; try congruence.
    econstructor; eauto.
  - (* E_floor *)
    destruct (eval_expr e) eqn: E1; try congruence.
    econstructor; eauto.
  - (* E_retype *)
    destruct (eval_expr e) eqn: E1; try congruence.
    econstructor; eauto.
  - (* E_trunc *)
    destruct (eval_expr e) eqn: E1; try congruence.
    econstructor; eauto.
  - (* E_binary *)
    destruct (eval_expr e1) eqn: E1; try congruence.
    destruct (eval_expr e2) eqn: E2; try congruence.
    econstructor; eauto.
  - (* E_cand *)
    destruct (is_int_prim_type p) eqn: E1; try congruence.
    destruct (eval_expr e1) eqn: E2; try congruence.
    destruct (bool_val v0 (typeof e1) m) eqn: E3; try congruence.
    destruct b eqn: E4; try congruence.
    + destruct (eval_expr e2) eqn: E5; try congruence.
      destruct (bool_val v1 (typeof e2) m) eqn: E6; try congruence.
      inversion H; subst. econstructor; eauto.
    + inversion H; subst. econstructor; eauto.
  - (* E_cior *)
    destruct (is_int_prim_type p) eqn: E1; try congruence.
    destruct (eval_expr e1) eqn: E2; try congruence.
    destruct (bool_val v0 (typeof e1) m) eqn: E3; try congruence.
    destruct b eqn: E4; try congruence.
    + inversion H; subst. econstructor; eauto.
    + destruct (eval_expr e2) eqn: E5; try congruence.
      destruct (bool_val v1 (typeof e2) m) eqn: E6; try congruence.
      inversion H; subst. econstructor; eauto.
  - (* E_select *)
    destruct (prim_type_eq (prim_type_of e2) p) eqn: E1; simpl in H; try congruence.
    destruct (prim_type_eq (prim_type_of e3) p) eqn: E2; simpl in H; try congruence.
    destruct (eval_expr e1) eqn: E3; try congruence.
    destruct (bool_val v0 (typeof e1) m) eqn: E4; try congruence.
    destruct b eqn: E5.
    + eapply eval_Eselect_left; eauto.
    + eapply eval_Eselect_right; eauto.
  (*- (* E_array *)
    destruct (eval_exprlist e) eqn: E; try congruence.
    inversion H; subst. econstructor; eauto.*)
  - destruct e eqn: E1; try congruence.
    destruct (is_pointer_prim_type p) eqn: E2; try congruence.
    destruct (eval_expr e0) eqn: E4; try congruence.
    destruct v0 eqn: E5; try congruence.
    destruct (eval_exprlist e1) eqn: E6; try congruence.
    destruct (eval_array b t l) eqn: E7; try congruence.
    inversion H; subst. econstructor; eauto.
    apply eval_array_sound; auto.
  - (* exprlist *)
    clear eval_exprlist_sound. intros el.
    induction el; intros; simpl in *.
    + inversion H; subst. econstructor; eauto.
    + destruct (eval_expr e) eqn: E1; try congruence.
      destruct (eval_exprlist el) eqn: E2; try congruence.
      inversion H; subst. econstructor; eauto.
Qed.

Lemma eval_array_complete: forall b vl mt ofs,
    MapleLight.eval_array ge b mt vl ofs ->
    eval_array b mt vl = Some ofs.
Proof.
  intros b vl. induction vl; intros.
  - inversion H.
  - inversion H; subst; clear H.
    + destruct b; simpl; try congruence. destruct H5; try congruence.
      destruct H. destruct (Int.intval i ?= len) eqn: E; auto.
      * unfold Z.lt in H0. rewrite E in H0. inversion H0.
      * unfold Z.lt in H0. rewrite E in H0. inversion H0.
    + destruct vl; try congruence.
      * inversion H8.
      * remember (v :: vl) as vl'. destruct b; simpl; subst.
        { destruct H3; try congruence. destruct H.
          destruct (Int.intval i ?= len) eqn: E.
          { unfold Z.lt in H0. rewrite E in H0. inversion H0. }
          { erewrite IHvl; eauto. }
          { unfold Z.lt in H0. rewrite E in H0. inversion H0. } }
        { erewrite IHvl; eauto. }
Qed.

Lemma eval_expr_complete: forall e v,
    MapleLight.eval_expr ge se le m e v ->
    eval_expr e = Some v
with eval_exprlist_complete: forall el vl,
    MapleLight.eval_exprlist ge se le m el vl ->
    eval_exprlist el = Some vl.
Proof.
  intros. induction H; simpl in *; auto.
  - rewrite H, H0, H1, H2; auto.
  - rewrite IHeval_expr, H0, H1, H2, H3; auto.
  - rewrite H; auto.
  - rewrite H, H0, H1; auto.
  - rewrite IHeval_expr, H, H1, H2; auto.
  - destruct H0; rewrite H, H0; auto.
  - rewrite IHeval_expr, H0; auto.
  - rewrite IHeval_expr, H0; auto.
  - rewrite IHeval_expr, H0; auto.
  - rewrite IHeval_expr, H0; auto.
  - rewrite IHeval_expr, H0; auto.
  - rewrite IHeval_expr, H0; auto.
  - rewrite IHeval_expr1, IHeval_expr2, H1; auto.
  - rewrite IHeval_expr1, IHeval_expr2, H, H1, H3; auto.
  - rewrite IHeval_expr, H, H1; auto.
  - rewrite IHeval_expr1, IHeval_expr2, H, H1, H3; auto.
  - rewrite IHeval_expr, H, H1; auto.
  - rewrite IHeval_expr1. destruct H. rewrite <- H3 in H.
    destruct (prim_type_eq (prim_type_of e2) pt); try congruence.
    destruct (prim_type_eq (prim_type_of e3) pt); try congruence.
    simpl. rewrite H1, IHeval_expr2; auto.
  - rewrite IHeval_expr1. destruct H. rewrite <- H3 in H.
    destruct (prim_type_eq (prim_type_of e2) pt); try congruence.
    destruct (prim_type_eq (prim_type_of e3) pt); try congruence.
    simpl. rewrite H1, IHeval_expr2; auto.
  - rewrite H, IHeval_expr.
    erewrite eval_exprlist_complete; eauto.
    erewrite eval_array_complete; eauto.
  - clear eval_exprlist_complete. intros. induction H; auto.
    unfold eval_expr, eval_exprlist in *.
    erewrite eval_expr_complete; eauto.
    erewrite IHeval_exprlist; eauto.
Qed.

End Eval_expr.

Definition eval_ext_expr (ee_oe_m: ext_expr * oenv * mem) : option (val * oenv * mem) :=
  let (ee_oe, m) := ee_oe_m in
  let (ee, oe) := ee_oe in
  match ee with
  | EE_pure e =>
    match eval_expr m e with
    | Some v => Some (v, oe, m)
    | None => None
    end
  | EE_malloc pt e =>
    if is_pointer_prim_type pt then
      match eval_expr m e with
      | Some v =>
        match val_to_ptrofs v with
        | Some sz =>
          let (m', b) := Mem.alloc m (- size_chunk Mptr) (Ptrofs.unsigned sz) in
          match Mem.store Mptr m' b (- size_chunk Mptr) v with
          | Some m'' => Some (Vptr b Ptrofs.zero, oe, m'')
          | None => None
          end
        | None => None
        end
      | None => None
      end
    else None
  | EE_gcmalloc pt ty =>
    if is_pointer_prim_type pt then
      let (m', b) := Mem.alloc m 0 (sizeof (genv_cenv ge) ty default_type_attr) in
      Some (Vptr b Ptrofs.zero, PTree.set b (ty, O, true) oe, m')
    else None
  | EE_gcmallocjarray pt ty e =>
    if is_pointer_prim_type pt then
      match eval_expr m e with
      | Some (Vint n) =>
        let z := (Int.unsigned n) in
        let (m', b) := Mem.alloc m 0 (Z.mul z (sizeof (genv_cenv ge) ty default_type_attr)) in
        Some (Vptr b Ptrofs.zero, PTree.set b (Tarray ty z, O, true) oe, m')
      | Some (Vlong n) =>
        let z := (Int64.unsigned n) in
        let (m', b) := Mem.alloc m 0 (Z.mul z (sizeof (genv_cenv ge) ty default_type_attr)) in
        Some (Vptr b Ptrofs.zero, PTree.set b (Tarray ty z, O, true) oe, m')
      | _ => None
      end
    else None
  | EE_gcpermalloc pt ty =>
    if is_pointer_prim_type pt then
      let (m', b) := Mem.alloc m 0 (sizeof (genv_cenv ge) ty default_type_attr) in
      Some (Vptr b Ptrofs.zero, PTree.set b (ty, O, false) oe, m')
    else None
  end.

Lemma eval_ext_expr_sound: forall ee oe m v oe' m',
    eval_ext_expr (ee, oe, m) = Some (v, oe', m') ->
    MapleLight.eval_ext_expr ge se le (ee, oe, m) (v, oe', m').
Proof.
  Hint Resolve eval_expr_sound: core.
  intros. destruct ee; simpl in *; auto.
  - (* EE_pure *)
    destruct (eval_expr m e) eqn: E1; try congruence.
    inversion H; subst; econstructor; eauto.
  - (* EE_malloc *)
    destruct (is_pointer_prim_type p) eqn: E1; try congruence.
    destruct (eval_expr m e) eqn: E2; try congruence.
    destruct (val_to_ptrofs v0) eqn: E3; try congruence.
    destruct (Mem.alloc m (- size_chunk Mptr) (Ptrofs.unsigned i)) eqn: E4; try congruence.
    destruct (Mem.store Mptr m0 b (- size_chunk Mptr) v0) eqn: E5; try congruence.
    inversion H; subst; econstructor; eauto.
  - (* EE_gcmalloc *)
    destruct (is_pointer_prim_type p) eqn: E1; try congruence.
    destruct (Mem.alloc m 0 (sizeof (genv_cenv ge) t default_type_attr)) eqn: E3; try congruence.
    inversion H; subst; econstructor; eauto.
  - (* EE_gcmallocjarray *)
    destruct (is_pointer_prim_type p) eqn: E1; try congruence.
    destruct (eval_expr m e) eqn: E3; try congruence.
    destruct v0 eqn: E4; try congruence.
    + destruct (Mem.alloc m 0 (Int.unsigned i * sizeof (genv_cenv ge) t default_type_attr)) eqn: E5; try congruence.
      inversion H; subst; eapply eval_gcmallocjarray_int; eauto.
    + destruct (Mem.alloc m 0 (Int64.unsigned i * sizeof (genv_cenv ge) t default_type_attr)) eqn: E5; try congruence.
      inversion H; subst; eapply eval_gcmallocjarray_long; eauto.
  - (* EE_gcpermalloc *)
    destruct (is_pointer_prim_type p) eqn: E1; try congruence.
    destruct (Mem.alloc m 0 (sizeof (genv_cenv ge) t default_type_attr)) eqn: E3; try congruence.
    inversion H; subst; econstructor; eauto.
Qed.

Lemma eval_ext_expr_complete: forall ee oe m v oe' m',
    MapleLight.eval_ext_expr ge se le (ee, oe, m) (v, oe', m') ->
    eval_ext_expr (ee, oe, m) = Some (v, oe', m').
Proof.
  intros. induction H; simpl in *; subst; auto.
  - erewrite eval_expr_complete; eauto.
  - erewrite H3, eval_expr_complete; eauto.
    rewrite H0, H1, H2; auto.
  - rewrite H, H0; auto.
  - erewrite H2, eval_expr_complete; eauto.
    destruct H0; subst; rewrite H1; auto.
  - erewrite H2, eval_expr_complete; eauto.
    destruct H0; subst; rewrite H1; auto.
  - rewrite H, H0; auto.
Qed.

End Eval_ext_expr.

Definition step (st: state) : option state :=
  match st with
  | NormalState f S_skip (Kjavatry ll k) le oe se m =>
    Some (NormalState f S_skip k le oe se m)
  | NormalState f (S_dassign vid fi e) k le oe se m =>
    match find_var ge le vid with
    | Some (loc, (mt, (sc, ta))) =>
      match fieldoffset (genv_cenv ge) mt fi with
      | OK (mt', ofs) =>
        match eval_ext_expr se le (e, oe, m) with
        | Some (v, oe', m') =>
          match sem_cast v (typeof_ext_expr e) mt' m' (genv_cenv ge) with
          | Some v' =>
            match assign_loc (genv_cenv ge) mt' ta m' loc (Ptrofs.repr ofs) v' with
            | Some m'' =>
              Some (NormalState f S_skip k le oe' se m'')
            | None => None
            end
          | None => None
          end
        | None => None
        end
      | Error _ => None
      end
    | None => None
    end
  | NormalState f (S_iassign ty fi e1 e2) k le oe se m =>
    match eval_expr se le m e1 with
    | Some (Vptr loc ofs) =>
      match ty with
      | Tpointer mt' =>
        match fieldoffset (genv_cenv ge) mt' fi with
        | OK (mt'', delta) =>
          match eval_ext_expr se le (e2, oe, m) with
          | Some (v, oe', m') =>
            match sem_cast v (typeof_ext_expr e2) mt'' m' (genv_cenv ge) with
            | Some v' =>
              match assign_loc (genv_cenv ge) mt'' default_type_attr m' loc (Ptrofs.add ofs (Ptrofs.repr delta)) v' with
              | Some m'' =>
                Some (NormalState f S_skip k le oe' se m'')
              | None => None
              end
            | None => None
            end
          | None => None
          end
        | Error _ => None
        end
      | _ => None
      end
    | _ => None
    end
  | NormalState f (S_regassign pt (Preg id) e) k le oe se m =>
    match find_preg le id with
    | Some (v0, pt') =>
      if prim_type_eq pt pt' then
        match eval_ext_expr se le (e, oe, m) with
        | Some (v, oe', m') =>
          match sem_cast v (typeof_ext_expr e) (Tprim pt) m' (genv_cenv ge) with
          | Some v' =>
            Some (NormalState f S_skip k (set_preg le id v' pt) oe' se m')
          | None => None
          end
        | None => None
        end
      else None
    | None =>
      match eval_ext_expr se le (e, oe, m) with
      | Some (v, oe', m') =>
        match sem_cast v (typeof_ext_expr e) (Tprim pt) m' (genv_cenv ge) with
        | Some v' =>
          Some (NormalState f S_skip k (set_preg le id v' pt) oe' se m')
        | None => None
        end
      | None => None
      end
    end
  | NormalState f (S_regassign pt Thrownval e) k le oe se m =>
    match eval_ext_expr se le (e, oe, m) with
    | Some (v, oe', m') =>
      match sem_cast v (typeof_ext_expr e) (Tprim pt) m' (genv_cenv ge) with
      | Some v' =>
        Some (NormalState f S_skip k le oe' (set_thrownval se v' pt) m')
      | None => None
      end
    | None => None
    end
  | NormalState f (S_seq s1 s2) k le oe se m =>
    Some (NormalState f s1 (Kseq s2 k) le oe se m)
  | NormalState f S_skip (Kseq s k) le oe se m =>
    Some (NormalState f s k le oe se m)
  | NormalState f (S_if e s1 s2) k le oe se m =>
    match eval_expr se le m e with
    | Some v =>
      match bool_val v (typeof e) m with
      | Some b =>
        Some (NormalState f (if b then s1 else s2) k le oe se m)
      | None => None
      end
    | None => None
    end
  | NormalState f (S_while e s) k le oe se m =>
    Some (NormalState f (S_if e (S_seq s (S_while e s)) S_skip) k le oe se m)
  | NormalState f S_skip (Kwhile e s k) le oe se m =>
    Some (NormalState f (S_while e s) k le oe se m)
  | NormalState f (S_label lbl s) k le oe se m =>
    Some (NormalState f s k le oe se m)
  | NormalState f (S_goto lbl) k le oe se m =>
    match find_label lbl (fun_statement (snd f)) (call_cont k) with
    | Some (s', k') =>
      Some (NormalState f s' k' le oe se m)
    | None => None
    end
  | NormalState f (S_switch e dl ll) k le oe se m =>
    match eval_expr se le m e with
    | Some v =>
      match sem_switch_arg v (typeof e) with
      | Some n =>
        Some (NormalState f (S_goto (select_switch n dl ll)) k le oe se m)
      | None => None
      end
    | None => None
    end
  | NormalState f (S_return el) k le oe se m =>
    match eval_exprlist se le m el with
    | Some nil =>
      match (type_of_returns (fun_returns (fst f))) with
      | Tnil | Tcons (Tprim PTvoid) Tnil =>
        match Mem.free_list m (blocks_of_lenv ge le) with
        | Some m' =>
          Some (ReturnState nil (call_cont k) oe se m')
        | None => None
        end
      | _ => None
      end
    | Some vl =>
      match sem_cast_list ge vl (typelistof el) (type_of_returns (fun_returns (fst f))) m with
      | Some vl' =>
        match Mem.free_list m (blocks_of_lenv ge le) with
        | Some m' =>
          Some (ReturnState vl' (call_cont k) oe se m')
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | NormalState f S_skip k le oe se m =>
    if is_call_cont k then
      match type_of_returns (fun_returns (fst f)) with
      | Tnil | Tcons (Tprim PTvoid) Tnil =>
        match Mem.free_list m (blocks_of_lenv ge le) with
        | Some m' =>
          Some (ReturnState nil k oe se m')
        | None => None
        end
      | _ => None
      end
    else None
  | NormalState f (S_callassigned (Func fid) el l) k le oe se m =>
    match eval_exprlist se le m el with
    | Some vl =>
      match find_function_by_name ge fid with
      | Some (loc, f') =>
        match sem_cast_list ge vl (typelistof el) (type_of_params (fun_params (fst f'))) m with
        | Some vl' =>
          Some (CallState f' vl' (Kcall l f le k) oe se m)
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | NormalState f (S_virtualcallassigned cid fid e el l) k le oe se m =>
    match eval_expr se le m e with
    | Some v =>
      match eval_exprlist se le m el with
      | Some vl =>
        match resolve_ref oe v with
        | Some (Tcomposite cid') =>
          if ident_eq cid cid'
             || in_dec ident_eq cid (superclasses_id (genv_cenv ge) cid')
          then
            match dispatch_function ge cid' fid with
            | Some fid' =>
              match find_function_by_name ge fid' with
              | Some (loc, f') =>
                match sem_cast_list ge (v :: vl) (typelistof (E_cons e el)) (type_of_params (fun_params (fst f'))) m with
                | Some vl' =>
                  Some (CallState f' vl' (Kcall l f le k) oe se m)
                | None => None
                end
              | None => None
              end
            | None => None
            end
          else None
        | _ => None
        end
      | None => None
      end
    | None => None
    end
  | NormalState f (S_interfacecallassigned cid fid e el l) k le oe se m =>
    match eval_expr se le m e with
    | Some v =>
      match eval_exprlist se le m el with
      | Some vl =>
        match resolve_ref oe v with
        | Some (Tcomposite cid') =>
          if in_dec ident_eq cid (superinterfaces_id (genv_cenv ge) cid') then
            match dispatch_function ge cid' fid with
            | Some fid' =>
              match find_function_by_name ge fid' with
              | Some (loc, f') =>
                match sem_cast_list ge (v :: vl) (typelistof (E_cons e el)) (type_of_params (fun_params (fst f'))) m with
                | Some vl' =>
                  Some (CallState f' vl' (Kcall l f le k) oe se m)
                | None => None
                end
              | None => None
              end
            | None => None
            end
          else None
        | _ => None
        end
      | None => None
      end
    | None => None
    end
  | NormalState f (S_icallassigned e el l) k le oe se m =>
    match eval_expr se le m e with
    | Some (Vptr loc ofs) =>
      if Ptrofs.eq_dec ofs Ptrofs.zero then
        match eval_exprlist se le m el with
        | Some vl =>
          match find_function_by_address ge loc with
          | Some f' =>
            match sem_cast_list ge vl (typelistof el) (type_of_params (fun_params (fst f'))) m with
            | Some vl' =>
              Some (CallState f' vl' (Kcall l f le k) oe se m)
            | None => None
            end
          | None => None
          end
        | None => None
        end
      else None
    | _ => None
    end
  | NormalState f (S_javatry ll s) k le oe se m =>
    Some (NormalState f s (Kjavatry ll k) le oe se m)
  | ExceptionState f k le oe se m =>
    match catch_cont k with
    | Kjavatry ll k1 =>
      match find_thrownval se with
      | Some (v, mt) =>
        match find_handler ge (resolve_type oe v mt) ll (fun_statement (snd f)) (call_cont k1) with
        | Some k3 =>
          Some (NormalState f S_skip k3 le oe se m)
        | None =>
          (*Some (NormalState f (S_while (E_constval (PTint I32 Signed) (Vlong (Int64.repr 1))) S_skip) k le oe m)*)
          Some (ExceptionState f k1 le oe se m)
        end
      | None => None
      end
    | Kcall l f' le' k1 =>
      match Mem.free_list m (blocks_of_lenv ge le) with
      | Some m' =>
        Some (ExceptionState f' k1 le' oe se m')
      | None => None
      end
    | _ => None
    end
  | NormalState f (S_throw e) k le oe se m =>
    match eval_expr se le m e with
    | Some v =>
      Some (ExceptionState f k le oe (set_thrownval se v (prim_type_of e)) m)
    | None => None
    end
  | NormalState f (S_free e) k le oe se m =>
    match eval_expr se le m e as v with
    | Some (Vptr b lo) =>
      match Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) with
      | Some v =>
        match val_to_ptrofs v with
        | Some sz =>
          match Z.compare (Ptrofs.unsigned sz) 0 with
          | Gt =>
            match Mem.free m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) with
            | Some m' =>
              Some (NormalState f S_skip k le oe se m')
            | None => None
            end
          | _ => None
          end
        | None => None
        end
      | None => None
      end
    | Some (Vint i) =>
      if negb Archi.ptr64 && Int.eq_dec i Int.zero then
        Some (NormalState f S_skip k le oe se m)
      else None
    | Some (Vlong i) =>
      if Archi.ptr64 && Int64.eq_dec i Int64.zero then
        Some (NormalState f S_skip k le oe se m)
      else None
    | _ => None
    end
  | NormalState f (S_incref e) k le oe se m =>
    match prim_type_of e with
    | PTref =>
      match eval_expr se le m e with
      | Some (Vptr loc ofs) =>
        if Ptrofs.eq_dec ofs (Ptrofs.repr 0) then
          match oe ! loc with
          | Some (mt, n, b) =>
            Some (NormalState f S_skip k le (PTree.set loc (mt, S n, b) oe) se m)
          | None => None
          end
        else None
      | _ => None
      end
    | _ => None
    end
  | NormalState f (S_decref e) k le oe se m =>
    match prim_type_of e with
    | PTref =>
      match eval_expr se le m e with
      | Some (Vptr loc ofs) =>
        if Ptrofs.eq_dec ofs (Ptrofs.repr 0) then
          match oe ! loc with
          | Some (mt, n, b) =>
            Some (NormalState f S_skip k le (PTree.set loc (mt, pred n, b) oe) se m)
          | None => None
          end
        else None
      | _ => None
      end
    | _ => None
    end
  | NormalState f (S_eval e) k le oe se m =>
    match eval_expr se le m e with
    | Some v =>
      Some (NormalState f S_skip k le oe se m)
    | None => None
    end
  | CallState f vl k oe se m =>
    match f with
    | (fp, Some fb) =>
      match function_entry ge (fp, fb) m vl with
      | Some (le, m') =>
        Some (NormalState (fp, fb) (fun_statement fb) k le oe se m')
      | None => None
      end
    | (_, None) => None
    end
  | ReturnState vl (Kcall l f le k) oe se m =>
    match assign_returns ge le m l vl with
    | Some m' =>
      Some (NormalState f S_skip k le oe se m')
    | None => None
    end
  | NormalState _ (S_javacatch _ _) _ _ _ _ _ => None
  | ReturnState _ _ _ _ _ => None
  (*| _ => None*)
  end.

Lemma step_sound: forall st st',
    step st = Some st' -> MapleLight.step ge st E0 st'.
Proof.
  Hint Constructors MapleLight.step: core.
  Hint Resolve eval_expr_sound: core.
  Hint Resolve eval_exprlist_sound: core.
  Hint Resolve eval_ext_expr_sound: core.
  intros. destruct st; unfold step in H.
  - (* NormalState *)
    destruct s; eauto.
    + (* S_skip *)
      destruct k; simpl in *; try congruence.
      * destruct (type_of_returns (fun_returns (fst f))) eqn: E1; try congruence.
        destruct (Mem.free_list m (blocks_of_lenv ge le)) eqn: E2; try congruence.
        inversion H; subst; eauto.
        destruct t; try congruence. destruct p; try congruence.
        destruct t0; try congruence.
        destruct (Mem.free_list m (blocks_of_lenv ge le)) eqn: E2; try congruence.
        inversion H; subst; eauto.
      * inversion H; subst; eauto.
      * inversion H; subst; eauto.
      * inversion H; subst; eauto.
      * destruct (type_of_returns (fun_returns (fst f))) eqn: E1; try congruence.
        destruct (Mem.free_list m (blocks_of_lenv ge le)) eqn: E2; try congruence.
        inversion H; subst; eauto.
        destruct t; try congruence. destruct p; try congruence.
        destruct t0; try congruence.
        destruct (Mem.free_list m (blocks_of_lenv ge le)) eqn: E2; try congruence.
        inversion H; subst; eauto.
    + (* S_dassign *)
      destruct (find_var ge le v) eqn: E1; try congruence.
      destruct p as [loc [mt [sc ta]]]; try congruence.
      destruct (fieldoffset (genv_cenv ge) mt f0) eqn: E2; try congruence.
      destruct p; try congruence.
      destruct (eval_ext_expr se le (rhs_expr, oe, m)) eqn: E3; try congruence.
      destruct p as [[v' oe'] m']; try congruence.
      destruct (sem_cast v' (typeof_ext_expr rhs_expr) t m' (genv_cenv ge)) eqn: E4; try congruence.
      destruct (assign_loc (genv_cenv ge) t ta m' loc (Ptrofs.repr z) v0) eqn: E5; try congruence.
      inversion H; subst; eauto.
    + (* S_iassign *)
      destruct (eval_expr se le m addr_expr) eqn: E2; try congruence.
      destruct v; try congruence.
      destruct t; try congruence.
      destruct (fieldoffset (genv_cenv ge) t f0) eqn: E3; try congruence.
      destruct p; try congruence.
      destruct (eval_ext_expr se le (rhs_expr, oe, m)) eqn: E4; try congruence.
      destruct p as [[v' oe'] m']; try congruence.
      destruct (sem_cast v' (typeof_ext_expr rhs_expr) t0 m' (genv_cenv ge)) eqn: E5; try congruence.
      destruct (assign_loc (genv_cenv ge) t0 default_type_attr m' b  (Ptrofs.add i (Ptrofs.repr z)) v) eqn: E6; try congruence.
      inversion H; subst; eauto.
    + (* S_regassign *)
      destruct r; try congruence.
      destruct (find_preg le i) eqn: E1; try congruence.
      * (* existing preg *)
        destruct p; try congruence.
        destruct (prim_type_eq t p); try congruence.
        destruct (eval_ext_expr se le (rhs_expr, oe, m)) eqn: E2; try congruence.
        destruct p0 as [[v' oe'] m']; try congruence.
        destruct (sem_cast v' (typeof_ext_expr rhs_expr) (Tprim t) m' (genv_cenv ge)) eqn: E3; try congruence.
        inversion H; subst; eauto.
      * (* fresh preg *)
        destruct (eval_ext_expr se le (rhs_expr, oe, m)) eqn: E2; try congruence.
        destruct p as [[v' oe'] m']; try congruence.
        destruct (sem_cast v' (typeof_ext_expr rhs_expr) (Tprim t) m' (genv_cenv ge)) eqn: E3; try congruence.
        inversion H; subst; eauto.
      * (* thrownval *)
        destruct (eval_ext_expr se le (rhs_expr, oe, m)) eqn: E2; try congruence.
        destruct p as [[v' oe'] m']; try congruence.
        destruct (sem_cast v' (typeof_ext_expr rhs_expr) (Tprim t) m' (genv_cenv ge)) eqn: E3; try congruence.
        inversion H; subst; eauto.
    + (* S_seq *)
      inversion H; subst; eauto.
    + (* S_label *)
      inversion H; subst; eauto.
    + (* S_if *)
      destruct (eval_expr se le m cond_expr) eqn: E1; try congruence.
      destruct (bool_val v (typeof cond_expr) m) eqn: E2; try congruence.
      inversion H; subst; eauto.
    + (* S_while *)
      inversion H; subst; eauto.
    + (* S_goto *)
      destruct (find_label l (fun_statement (snd f)) (call_cont k)) eqn: E1; try congruence.
      destruct p.
      inversion H; subst; eauto.
    + (* S_return *)
      destruct (eval_exprlist se le m retlist) eqn: E1; try congruence.
      destruct l.
      * destruct (type_of_returns (fun_returns (fst f))) eqn: E2; try congruence.
        destruct (Mem.free_list m (blocks_of_lenv ge le)) eqn: E4; try congruence.
        inversion H; subst; eauto.
        destruct t; try congruence. destruct p; try congruence.
        destruct t0; try congruence.
        destruct (Mem.free_list m (blocks_of_lenv ge le)) eqn: E4; try congruence.
        inversion H; subst; eauto.
      * destruct (sem_cast_list ge (v :: l) (typelistof retlist) (type_of_returns (fun_returns (fst f))) m) eqn: E3; try congruence.
        destruct (Mem.free_list m (blocks_of_lenv ge le)) eqn: E4; try congruence.
        inversion H; subst. econstructor; eauto.
        intro. congruence.
    + (* S_switch *)
      destruct (eval_expr se le m opnd) eqn: E1; try congruence.
      destruct (sem_switch_arg v (typeof opnd)) eqn: E2; try congruence.
      inversion H; subst; eauto.
    + (* S_callassigned *)
      destruct f0.
      destruct (eval_exprlist se le m opndlist) eqn: E1; try congruence.
      destruct (find_function_by_name ge i) eqn: E2; try congruence.
      destruct p.
      destruct (sem_cast_list ge l (typelistof opndlist) (type_of_params (fun_params (fst f0))) m) eqn: E4; try congruence.
      inversion H; subst; eauto.
    + (* S_icallassigned *)
      destruct (eval_expr se le m f_ptr) eqn: E1; try congruence.
      destruct v; try congruence.
      destruct (Ptrofs.eq_dec i Ptrofs.zero); try congruence.
      destruct (eval_exprlist se le m opndlist) eqn: E2; try congruence.
      destruct (find_function_by_address ge b) eqn: E3; try congruence.
      destruct (sem_cast_list ge l (typelistof opndlist) (type_of_params (fun_params (fst f0))) m)  eqn: E5; try congruence.
      inversion H; subst; eauto.
    + (* S_virtualcallassigned *)
      destruct (eval_expr se le m obj_ptr) eqn: E1; try congruence.
      destruct (eval_exprlist se le m opndlist) eqn: E2; try congruence.
      destruct (resolve_ref oe v) eqn: E3; try congruence.
      destruct t; try congruence.
      destruct (ident_eq c i || in_dec ident_eq c (superclasses_id (genv_cenv ge) i)) eqn: E4; try congruence.
      destruct (dispatch_function ge i f0) eqn: E5; try congruence.
      destruct (find_function_by_name ge i0) eqn: E6; try congruence.
      destruct p.
      destruct (sem_cast_list ge (v :: l) (typelistof (E_cons obj_ptr opndlist)) (type_of_params (fun_params (fst f1))) m) eqn: E7; try congruence.
      inversion H; subst; econstructor; eauto. apply orb_prop in E4.
      destruct E4 as [E4 | E4]; apply proj_sumbool_true in E4; eauto.
    + (* S_interfacecallassigned *)
      destruct (eval_expr se le m obj_ptr) eqn: E1; try congruence.
      destruct (eval_exprlist se le m opndlist) eqn: E2; try congruence.
      destruct (resolve_ref oe v) eqn: E3; try congruence.
      destruct t; try congruence.
      destruct (in_dec ident_eq c (superinterfaces_id (genv_cenv ge) i)); try congruence.
      destruct (dispatch_function ge i f0) eqn: E4; try congruence.
      destruct (find_function_by_name ge i1) eqn: E5; try congruence.
      destruct p.
      destruct (sem_cast_list ge (v :: l) (typelistof (E_cons obj_ptr opndlist)) (type_of_params (fun_params (fst f1))) m) eqn: E7; try congruence.
      inversion H; subst; eauto.
    + (* S_javatry *)
      inversion H; subst; eauto.
    + (* s_throw *)
      destruct (eval_expr se le m opnd) eqn: E1; try congruence.
      inversion H; subst; eauto.
    + (* S_javacatch *)
      congruence.
    + (* S_decref *)
      destruct (prim_type_of opnd) eqn: E1; try congruence.
      destruct (eval_expr se le m opnd) eqn: E2; try congruence.
      destruct v; try congruence.
      destruct (Ptrofs.eq_dec i (Ptrofs.repr 0)); try congruence.
      destruct (oe ! b) eqn: E3; try congruence.
      destruct p as [[mt n] b0].
      inversion H; subst; eauto.
    + (* S_free *)
      destruct (eval_expr se le m opnd) eqn: E1; try congruence.
      destruct v; try congruence.
      * destruct (negb Archi.ptr64) eqn: E2; simpl in *; try congruence.
        destruct (Int.eq_dec i Int.zero); simpl in *; try congruence.
        apply negb_true_iff in E2.
        inversion H; subst. eapply step_free_null; eauto.
        unfold Vnullptr. rewrite E2. auto.
      * destruct Archi.ptr64 eqn: E2; simpl in *; try congruence.
        destruct (Int64.eq_dec i Int64.zero); simpl in *; try congruence.
        inversion H; subst; eauto.
      * destruct (Mem.load Mptr m b (Ptrofs.unsigned i - size_chunk Mptr)) eqn: E2; try congruence.
        destruct (val_to_ptrofs v) eqn: E3; try congruence.
        destruct (Ptrofs.unsigned i0 ?= 0) eqn: E4; try congruence.
        destruct (Mem.free m b (Ptrofs.unsigned i - size_chunk Mptr) (Ptrofs.unsigned i + Ptrofs.unsigned i0)) eqn: E5; try congruence.
        inversion H; subst; eauto.
    + (* S_incref *)
      destruct (prim_type_of opnd) eqn: E1; try congruence.
      destruct (eval_expr se le m opnd) eqn: E2; try congruence.
      destruct v; try congruence.
      destruct (Ptrofs.eq_dec i (Ptrofs.repr 0)); try congruence.
      destruct (oe ! b) eqn: E3; try congruence.
      destruct p as [[mt n] b0].
      inversion H; subst; eauto.
    + (* S_eval *)
      destruct (eval_expr se le m opnd) eqn: E1; try congruence.
      inversion H; subst; eauto.
  - (* CallState *)
    destruct f. destruct o; try congruence.
    destruct (function_entry ge (f, f0) m args) eqn: E1; try congruence.
    destruct p.
    inversion H; subst; eauto.
  - (* ReturnState *)
    destruct k; try congruence.
    destruct (assign_returns ge l0 m l res) eqn: E1; try congruence.
    inversion H; subst; eauto.
  - (* ExceptionState *)
    destruct (catch_cont k) eqn: E2; try congruence.
    destruct (find_thrownval se) eqn: E1; try congruence. destruct p.
    destruct (find_handler ge (resolve_type oe v p) l (fun_statement (snd f)) (call_cont c)) eqn: E3; try congruence.
    + (* case 1 *)
      inversion H; subst; eauto.
    + (* case 2 *)
      inversion H; subst; eauto.
    + (* case 3 *)
      destruct (Mem.free_list m (blocks_of_lenv ge le)) eqn: E3; try congruence.
      inversion H; subst; eauto.
Qed.

Lemma step_complete: forall st st',
    MapleLight.step ge st E0 st' -> step st = Some st'.
Proof.
  intros. inversion H; subst; unfold step; auto.
  - (* S_dassign *)
    erewrite H0, H1, eval_ext_expr_complete, H3, H4; eauto.
  - (* S_iassign *)
    erewrite eval_ext_expr_complete, H2, eval_expr_complete; eauto. simpl.
    rewrite H4, H5; eauto.
  - (* S_regassign existing preg *)
    erewrite H0, eval_ext_expr_complete, H2; eauto.
    destruct (prim_type_eq); auto. congruence.
  - (* S_regassign fresh preg *)
    erewrite H0, eval_ext_expr_complete, H2; eauto.
  - (* S_regassign thrownval *)
    erewrite eval_ext_expr_complete, H1; eauto.
  - (* S_if *)
    erewrite eval_expr_complete, H1; eauto.
  - (* S_goto *)
    erewrite H0; eauto.
  - (* S_switch *)
    erewrite eval_expr_complete, H1; eauto.
  - (* S_return nil *)
    erewrite eval_exprlist_complete; eauto; simpl.
    destruct H1; rewrite H1, H2; eauto.
  - (* S_return cons *)
    erewrite eval_exprlist_complete; eauto; simpl.
    destruct vl; try congruence. rewrite H2, H3; eauto.
  - (* S_skip return *)
    destruct k; simpl in *; try congruence; destruct H1; rewrite H1, H2; auto.
  - (* S_callassigned *)
    erewrite eval_exprlist_complete, H1, H2; eauto.
  - (* S_virtualcallassigned *)
    erewrite eval_expr_complete, eval_exprlist_complete, H2; eauto.
    destruct (ident_eq cid cid' || in_dec ident_eq cid (superclasses_id (genv_cenv ge) cid')) eqn: E1.
    rewrite H4, H5, H6; auto. exfalso. apply orb_false_elim in E1. destruct E1.
    destruct H3.
    + destruct (ident_eq cid cid'); auto. inversion H7.
    + destruct (in_dec ident_eq cid (superclasses_id (genv_cenv ge) cid')); auto.
      inversion H8.
  - (* S_interfacecallassigned *)
    erewrite eval_expr_complete, eval_exprlist_complete, H2; eauto.
    destruct (in_dec ident_eq cid (superinterfaces_id (genv_cenv ge) cid')).
    rewrite H4, H5, H6; auto. exfalso. auto.
  - (* S_icallassigned *)
    erewrite eval_expr_complete; eauto. simpl.
    erewrite eval_exprlist_complete, H2, H3; eauto.
  - (* ExceptionState case 1 *)
    erewrite H0, H1, H2; eauto.
  - (* ExceptionState case 2 *)
    erewrite H0, H1, H2; eauto.
  - (* ExceptionState case 3 *)
    erewrite H0, H1; eauto.
  - (* S_throw *)
    erewrite eval_expr_complete; eauto.
  - (* S_free *)
    erewrite eval_expr_complete; eauto. simpl.
    rewrite H1, H2, H3, H4; auto.
  - (* S_free nullptr *)
    erewrite eval_expr_complete; eauto. unfold Vnullptr.
    destruct Archi.ptr64; simpl; auto.
  - (* S_incref *)
    erewrite H0, eval_expr_complete; eauto. simpl.
    rewrite H2; auto.
  - (* S_decref *)
    erewrite H0, eval_expr_complete; eauto. simpl.
    rewrite H2; auto.
  - (* S_eval *)
    erewrite eval_expr_complete; eauto.
  - (* CallState *)
    rewrite H1; auto.
  - (* ReturnState *)
    inversion H; subst. rewrite H0; auto.
Qed.

End Semantics.

Definition initial_state (p: program) (vmtl: list (val * type)) : res (genv * state) :=
  do (ge, m) <- build_genv_mem p;
    match find_function_by_name ge (prog_main p) with
    | Some (b, f) =>
      OK (ge, CallState f vmtl Kstop init_oenv init_senv m)
    | None =>
      Error (MSG "cannot load the entry function " :: CTX (prog_main p) :: nil)
    end.

Lemma initial_state_sound: forall p vmtl ge st,
    initial_state p vmtl = OK (ge, st) -> MapleLight.initial_state p vmtl ge st.
Proof.
  unfold initial_state; intros.
  destruct (build_genv_mem p) eqn: E1; simpl in H; try congruence. destruct p0.
  destruct (find_function_by_name g (prog_main p)) eqn:E2; try congruence.
  destruct p0. inversion H; subst. econstructor; eauto.
Qed.

Lemma initial_state_complete: forall p vmtl ge st,
    MapleLight.initial_state p vmtl ge st -> initial_state p vmtl = OK (ge, st).
Proof.
  unfold initial_state; intros. inversion H; subst.
  rewrite H0; simpl. rewrite H1. auto.
Qed.

Definition final_state (s: state) : option (list (val * type)) :=
  match s with
  | ReturnState vmtl Kstop oe se m => Some vmtl
  | _ => None
  end.

Lemma final_state_sound: forall s vmtl,
    final_state s = Some vmtl -> MapleLight.final_state s vmtl.
Proof.
  unfold final_state; intros. destruct s; try congruence.
  destruct k; try congruence. inversion H; subst. econstructor; eauto.
Qed.

Lemma final_state_complete: forall s vmtl,
    final_state s = Some vmtl -> MapleLight.final_state s vmtl.
Proof.
  unfold final_state; intros. destruct s; try congruence.
  destruct k; try congruence. inversion H; subst. econstructor; eauto.
Qed.
