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
Require Import MapleOp.
Require Import Mapletypes.
Require Import Maple.

Section Bigstep.

Variable ge: genv.

Inductive outcome: Type :=
  | Out_normal: outcome
  | Out_throw: outcome
  | Out_return: list val * mytypelist -> outcome.

Definition outcome_result (out: outcome) (mtl: mytypelist) (m: mem) : option (list (val * mytype)) :=
  match out, mtl with
  | Out_normal, (MTnil | MTcons (MTprim PTvoid) MTnil) =>
    Some nil
  | Out_return (nil, MTnil), (MTnil | MTcons (MTprim PTvoid) MTnil) =>
    Some nil
  | Out_return (vl, mtl'), mtl =>
    sem_cast_list ge vl mtl' mtl m
  | _, _ => None
  end.

Fixpoint find_label (lbl: label) (s: statement)
         {struct s}: option statement :=
  match s with
  | S_seq s1 s2 =>
    match find_label lbl s1 with
    | Some sr => Some (S_seq sr s2)
    | None => find_label lbl s2
    end
  | S_if e s1 s2 =>
    match find_label lbl s1 with
    | Some sr => Some sr
    | None => find_label lbl s2
    end
  | S_while e s' =>
    match find_label lbl s' with
    | Some sr => Some (S_seq sr (S_while e s'))
    | None => None
    end
  | S_label lbl' s' =>
    if ident_eq lbl lbl'
    then Some s'
    else find_label lbl s'
  | S_javatry ll s' =>
    match find_label lbl s' with
    | Some sr => Some (S_javatry ll sr)
    | None => None
    end
  | _ => None
  end.

Fixpoint find_catch (mt: mytype) (lbl: label) (s: statement) : option statement :=
  match s with
  | S_seq s1 s2 =>
    match find_catch mt lbl s1 with
    | Some sr => Some (S_seq sr s2)
    | None => find_catch mt lbl s2
    end
  | S_if e s1 s2 =>
    match find_catch mt lbl s1 with
    | Some sr => Some sr
    | None => find_catch mt lbl s2
    end
  | S_while e s' =>
    match find_catch mt lbl s' with
    | Some sr => Some (S_seq sr (S_while e s'))
    | None => None
    end
  | S_label lbl' s' =>
    find_catch mt lbl s'
  | S_javatry ll s' =>
    match find_catch mt lbl s' with
    | Some sr => Some (S_javatry ll sr)
    | None => None
    end
  | S_javacatch lbl' tyl =>
    if (ident_eq lbl lbl') then
      match listtype_to_listmytype (genv_mytypes ge) tyl with
      | OK mtl =>
        match find (sub_mytype (genv_cenv ge) mt) mtl with
        | Some mt' => Some s
        | None => None
        end
      | Error _ => None
      end
    else None
  | _ => None
  end.

Fixpoint find_handler (mt: mytype) (ll: list label) (s: statement) : option statement :=
  match ll with
  | nil => None
  | lbl :: ll' =>
    match find_catch mt lbl s with
    | Some sr => Some sr
    | None => find_handler mt ll' s
    end
  end.

(*Section Exec_stmt.*)

(*Variable f: concrete_function.*)

Inductive exec_stmt: concrete_function -> lenv -> oenv -> mem -> statement -> trace -> lenv -> oenv -> mem -> outcome -> Prop :=
  | exec_dassign: forall f vid fi e le m loc ofs mt mt' sc ta v v' m' oe m'' oe',
      find_var ge le vid = Some (loc, (mt, (sc, ta))) ->
      fieldoffset (genv_cenv ge) mt fi = OK (mt', ofs) ->
      eval_ext_expr ge le (e, oe, m) (v, oe', m') ->
      sem_cast v (mytypeof_ext_expr e) mt' m' (genv_cenv ge) = Some v' ->
      assign_loc (genv_cenv ge) mt' ta m' loc (Ptrofs.repr ofs) v' = Some m'' ->
      exec_stmt f le oe m (S_dassign vid fi e)
                E0 le oe' m'' Out_normal
  | exec_iassign: forall f ty e1 e2 le m loc ofs delta v v' m' mt mt' mt'' fi oe oe' m'',
      type_to_mytype (genv_mytypes ge) ty = OK mt ->
      eval_expr ge le m e1 (Vptr loc ofs) ->
      mt = MTpointer mt' ->
      fieldoffset (genv_cenv ge) mt' fi = OK (mt'', delta) ->
      eval_ext_expr ge le (e2, oe, m) (v, oe', m') ->
      sem_cast v (mytypeof_ext_expr e2) mt'' m' (genv_cenv ge) = Some v' ->
      assign_loc (genv_cenv ge) mt'' default_type_attr m' loc (Ptrofs.add ofs (Ptrofs.repr delta)) v' = Some m'' ->
      exec_stmt f le oe m (S_iassign ty fi e1 e2)
                E0 le oe' m'' Out_normal
  | exec_regassign_preg_exist: forall f id pt e le m v0 v v' oe oe' m',
      find_preg le id = Some (v0, pt) ->
      eval_ext_expr ge le (e, oe, m) (v, oe', m') ->
      sem_cast v (mytypeof_ext_expr e) (MTprim pt) m' (genv_cenv ge) = Some v' ->
      exec_stmt f le oe m (S_regassign pt (Preg id) e)
                E0 (set_preg le id v' pt) oe' m' Out_normal
  | exec_regassign_preg_fresh: forall f id pt e le m v v' oe oe' m',
      find_preg le id = None ->
      eval_ext_expr ge le (e, oe, m) (v, oe', m') ->
      sem_cast v (mytypeof_ext_expr e) (MTprim pt) m' (genv_cenv ge) = Some v' ->
      exec_stmt f le oe m (S_regassign pt (Preg id) e)
                E0 (set_preg le id v' pt) oe' m' Out_normal
  | exec_regassign_thrownval: forall f pt e le m v v' oe oe' m',
      eval_ext_expr ge le (e, oe, m) (v, oe', m') ->
      sem_cast v (mytypeof_ext_expr e) (MTprim pt) m' (genv_cenv ge) = Some v' ->
      exec_stmt f le oe m (S_regassign pt Thrownval e)
                E0 (set_thrownval le v' pt) oe' m' Out_normal
  | exec_seq1: forall f s1 s2 le oe m le' oe' m' le'' oe'' m'' t1 t2 out,
      exec_stmt f le oe m s1 t1 le' oe' m' Out_normal ->
      exec_stmt f le' oe' m' s2 t2 le'' oe'' m'' out ->
      exec_stmt f le oe m (S_seq s1 s2)
                (t1 ** t2) le'' oe'' m'' out
  | exec_seq2: forall f s1 s2 le oe m le' oe' m' t1 out,
      exec_stmt f le oe m s1 t1 le' oe' m' out ->
      out <> Out_normal ->
      exec_stmt f le oe m (S_seq s1 s2)
                t1 le' oe' m' out
  | exec_skip: forall f le oe m,
      exec_stmt f le oe m S_skip
                E0 le oe m Out_normal
  | exec_if: forall f e s1 s2 le oe m v b le' oe' m' t out,
      eval_expr ge le m e v ->
      bool_val v (mytypeof e) m = Some b ->
      exec_stmt f le oe m (if b then s1 else s2) t le' oe' m' out ->
      exec_stmt f le oe m (S_if e s1 s2)
                t le' oe' m' out
  | exec_while_false: forall f s e v le oe m,
      eval_expr ge le m e v ->
      bool_val v (mytypeof e) m = Some false ->
      exec_stmt f le oe m (S_while e s)
                E0 le oe m Out_normal
  | exec_while_true1: forall f s e v le oe m le' oe' m' le'' oe'' m'' t1 t2 out,
      eval_expr ge le m e v ->
      bool_val v (mytypeof e) m = Some true ->
      exec_stmt f le oe m s t1 le' oe' m' Out_normal ->
      exec_stmt f le' oe' m' (S_while e s) t2 le'' oe'' m'' out ->
      exec_stmt f le oe m (S_while e s)
                (t1 ** t2) le'' oe'' m'' out
  | exec_while_true2: forall f s e v le oe m le' oe' m' t out,
      eval_expr ge le m e v ->
      bool_val v (mytypeof e) m = Some true ->
      exec_stmt f le oe m s t le' oe' m' out ->
      out <> Out_normal ->
      exec_stmt f le oe m (S_while e s)
                t le' oe' m' out
  | exec_label: forall f lbl s le oe m le' oe' m' t out,
      exec_stmt f le oe m s t le' oe' m' out ->
      exec_stmt f le oe m (S_label lbl s)
                t le' oe' m' out
  | exec_goto1: forall f lbl le oe m s' le' oe' m' t,
      find_label lbl (fun_statement (snd f)) = Some s' ->
      exec_stmt f le oe m s' t le' oe' m' Out_normal ->
      exec_stmt f le oe m (S_goto lbl)
                t le' oe' m' (Out_return (nil, MTnil))
  | exec_goto2: forall f lbl le oe m s' le' oe' m' t out,
      find_label lbl (fun_statement (snd f)) = Some s' ->
      exec_stmt f le oe m s' t le' oe' m' out ->
      out <> Out_normal ->
      exec_stmt f le oe m (S_goto lbl)
                t le' oe' m' out
  | exec_switch: forall f dl ll e le oe m v n s' le' oe' m' t out,
      eval_expr ge le m e v ->
      sem_switch_arg v (mytypeof e) = Some n ->
      find_label (select_switch n dl ll) (fun_statement (snd f)) = Some s' ->
      exec_stmt f le oe m s' t le' oe' m' out ->
      exec_stmt f le oe m (S_switch e dl ll)
                t le' oe' m' out
  | exec_return: forall f el le oe m vl,
      eval_exprlist ge le m el vl ->
      exec_stmt f le oe m (S_return el)
                E0 le oe m (Out_return (vl, mytypelistof el))
  | exec_callassigned_normal: forall f fid el le oe oe' m m' m'' vl l loc f' mtl' args res t,
      eval_exprlist ge le m el vl ->
      find_function_by_name ge fid = Some (loc, f') ->
      typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) = OK mtl' ->
      sem_cast_list ge vl (mytypelistof el) mtl' m = Some args ->
      eval_funcall_normal oe m f' args t oe' m' res ->
      assign_returns ge le l res m' = Some m'' ->
      exec_stmt f le oe m (S_callassigned (Func fid) el l)
                t le oe' m'' Out_normal
  | exec_callassigned_exception: forall f fid el le oe oe' m m' m'' vl l loc f' mtl' args t,
      eval_exprlist ge le m el vl ->
      find_function_by_name ge fid = Some (loc, f') ->
      typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) = OK mtl' ->
      sem_cast_list ge vl (mytypelistof el) mtl' m = Some args ->
      eval_funcall_exception oe m f' args t oe' m' ->
      exec_stmt f le oe m (S_callassigned (Func fid) el l)
                t le oe' m'' Out_throw
  | exec_virtualcallassigned_normal: forall f cid fid el le oe oe' m m' m'' vl l loc f' mtl' args e v cid' fid' res t,
      eval_expr ge le m e v ->
      eval_exprlist ge le m el vl ->
      resolve_ref oe v = Some (MTcomposite cid') ->
      In cid (superclasses_id (genv_cenv ge) cid') ->
      dispatch_function ge cid' fid = Some fid' ->
      find_function_by_name ge fid' = Some (loc, f') ->
      typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) = OK mtl' ->
      sem_cast_list ge (v :: vl) (mytypelistof (E_cons e el)) mtl' m = Some args ->
      eval_funcall_normal oe m f' args t oe' m' res ->
      assign_returns ge le l res m' = Some m'' ->
      exec_stmt f le oe m (S_virtualcallassigned cid fid e el l)
                t le oe' m'' Out_normal
  | exec_virtualcallassigned_exception: forall f cid fid el le oe oe' m m' m'' vl l loc f' mtl' args e v cid' fid' t,
      eval_expr ge le m e v ->
      eval_exprlist ge le m el vl ->
      resolve_ref oe v = Some (MTcomposite cid') ->
      In cid (superclasses_id (genv_cenv ge) cid') ->
      dispatch_function ge cid' fid = Some fid' ->
      find_function_by_name ge fid' = Some (loc, f') ->
      typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) = OK mtl' ->
      sem_cast_list ge (v :: vl) (mytypelistof (E_cons e el)) mtl' m = Some args ->
      eval_funcall_exception oe m f' args t oe' m' ->
      exec_stmt f le oe m (S_virtualcallassigned cid fid e el l)
                t le oe' m'' Out_throw
  | exec_interfaceclasscallassigned_normal: forall f cid fid el le oe oe' m m' m'' vl l loc f' mtl' args e v cid' fid' res t,
      eval_expr ge le m e v ->
      eval_exprlist ge le m el vl ->
      resolve_ref oe v = Some (MTcomposite cid') ->
      In cid (superinterfaces_id (genv_cenv ge) cid') ->
      dispatch_function ge cid' fid = Some fid' ->
      find_function_by_name ge fid' = Some (loc, f') ->
      typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) = OK mtl' ->
      sem_cast_list ge (v :: vl) (mytypelistof (E_cons e el)) mtl' m = Some args ->
      eval_funcall_normal oe m f' args t oe' m' res ->
      assign_returns ge le l res m' = Some m'' ->
      exec_stmt f le oe m (S_interfacecallassigned cid fid e el l)
                t le oe' m'' Out_normal
  | exec_interfaceclasscallassigned_exception: forall f cid fid el le oe oe' m m' m'' vl l loc f' mtl' args e v cid' fid' t,
      eval_expr ge le m e v ->
      eval_exprlist ge le m el vl ->
      resolve_ref oe v = Some (MTcomposite cid') ->
      In cid (superinterfaces_id (genv_cenv ge) cid') ->
      dispatch_function ge cid' fid = Some fid' ->
      find_function_by_name ge fid' = Some (loc, f') ->
      typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) = OK mtl' ->
      sem_cast_list ge (v :: vl) (mytypelistof (E_cons e el)) mtl' m = Some args ->
      eval_funcall_exception oe m f' args t oe' m' ->
      exec_stmt f le oe m (S_interfacecallassigned cid fid e el l)
                t le oe' m'' Out_throw
  | exec_icallassigned_normal: forall f e el le oe oe' m m' m'' vl l loc f' mtl' args res t,
      eval_expr ge le m e (Vptr loc Ptrofs.zero) ->
      eval_exprlist ge le m el vl ->
      find_function_by_address ge loc = Some f' ->
      typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) = OK mtl' ->
      sem_cast_list ge vl (mytypelistof el) mtl' m = Some args ->
      eval_funcall_normal oe m f' args t oe' m' res ->
      assign_returns ge le l res m' = Some m'' ->
      exec_stmt f le oe m (S_icallassigned e el l)
                t le oe' m'' Out_normal
  | exec_icallassigned_exception: forall f e el le oe oe' m m' m'' vl l loc f' mtl' args t,
      eval_expr ge le m e (Vptr loc Ptrofs.zero) ->
      eval_exprlist ge le m el vl ->
      find_function_by_address ge loc = Some f' ->
      typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) = OK mtl' ->
      sem_cast_list ge vl (mytypelistof el) mtl' m = Some args ->
      eval_funcall_exception oe m f' args t oe' m' ->
      exec_stmt f le oe m (S_icallassigned e el l)
                t le oe' m'' Out_throw
  | exec_javatry: forall f ll s le oe m le' oe' m' t,
      exec_stmt f le oe m s t le' oe' m' Out_normal ->
      exec_stmt f le oe m (S_javatry ll s)
                t le' oe' m' Out_normal
  | exec_javacatch1: forall f ll s le oe m le' oe' m' s' v pt t1 t2 out,
      exec_stmt f le oe m s t1 le' oe' m' Out_throw ->
      lenv_thrownval le = Some (v, pt) ->
      find_handler (resolve_type oe v pt) ll (fun_statement (snd f)) = Some s' ->
      exec_stmt f le oe m s' t2 le' oe' m' out ->
      exec_stmt f le oe m (S_javatry ll s)
                (t1 ** t2) le' oe' m' out
  | exec_javacatch2: forall f ll le oe m le' oe' m' v pt s t,
      exec_stmt f le oe m s t le' oe' m' Out_throw ->
      lenv_thrownval le = Some (v, pt) ->
      find_handler (resolve_type oe v pt) ll (fun_statement (snd f)) = None ->
      exec_stmt f le oe m (S_javatry ll s)
                t le' oe' m' Out_throw
  | exec_throw: forall f le oe m e v,
      eval_expr ge le m e v ->
      exec_stmt f le oe m (S_throw e)
                E0 (set_thrownval le v (prim_type_of e)) oe m Out_throw
  | exec_free: forall f le oe m e b lo v sz m',
      eval_expr ge le m e (Vptr b lo) ->
      Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) = Some v ->
      val_to_ptrofs v = Some sz ->
      Ptrofs.unsigned sz > 0 ->
      Mem.free m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) = Some m' ->
      exec_stmt f le oe m (S_free e)
                E0 le oe m' Out_normal
  | exec_free_null: forall f le oe m e,
      eval_expr ge le m e Vnullptr ->
      exec_stmt f le oe m (S_free e)
                E0 le oe m Out_normal
  | exec_incref: forall f le oe m e loc mt n b,
      prim_type_of e = PTref ->
      eval_expr ge le m e (Vptr loc (Ptrofs.repr 0)) ->
      oe ! loc = Some (mt, n, b) ->
      exec_stmt f le oe m (S_incref e)
                E0 le (PTree.set loc (mt, S n, b) oe) m Out_normal
  | exec_decref: forall f le oe m e loc mt n b,
      prim_type_of e = PTref ->
      eval_expr ge le m e (Vptr loc (Ptrofs.repr 0)) ->
      oe ! loc = Some (mt, n, b) ->
      exec_stmt f le oe m (S_decref e)
                E0 le (PTree.set loc (mt, pred n, b) oe) m Out_normal
  | exec_eval: forall f le oe m e v,
      eval_expr ge le m e v ->
      exec_stmt f le oe m (S_eval e)
                E0 le oe m Out_normal
with eval_funcall_normal : oenv -> mem -> function -> list (val * mytype) -> trace -> oenv -> mem -> list (val * mytype) -> Prop :=
| eval_funcall_normal_intro: forall f fp fb args le le' oe oe' m m' m'' m''' mtl res out t,
    f = (fp, Some fb) ->
    function_entry ge (fp, fb) m args = Some (le, m') ->
    exec_stmt (fp, fb) le oe m' (fun_statement fb) t le' oe' m'' out ->
    out <> Out_throw ->
    typelist_to_mytypelist (genv_mytypes ge) (type_of_returns (fun_returns fp)) = OK mtl ->
    outcome_result out mtl m'' = Some res ->
    Mem.free_list m'' (blocks_of_lenv ge le) = Some m''' ->
    eval_funcall_normal oe m f args t oe' m''' res
with eval_funcall_exception : oenv -> mem -> function -> list (val * mytype) -> trace -> oenv -> mem -> Prop :=
| eval_funcall_throw_intro: forall f fp fb args le le' oe oe' m m' m'' m''' t,
    f = (fp, Some fb) ->
    function_entry ge (fp, fb) m args = Some (le, m') ->
    exec_stmt (fp, fb) le oe m' (fun_statement fb) t le' oe' m'' Out_throw ->
    Mem.free_list m'' (blocks_of_lenv ge le) = Some m''' ->
    eval_funcall_exception oe m f args t oe' m'''.

Inductive execinf_stmt : concrete_function -> lenv -> oenv -> mem -> statement -> traceinf -> Prop :=
  | execinf_seq1: forall f s1 s2 le oe m t,
      execinf_stmt f le oe m s1 t ->
      execinf_stmt f le oe m (S_seq s1 s2) t
  | execinf_seq2: forall f s1 s2 le oe m le' oe' m' t1 t2,
      exec_stmt f le oe m s1 t1 le' oe' m' Out_normal ->
      execinf_stmt f le' oe' m' s2 t2 ->
      execinf_stmt f le oe m (S_seq s1 s2) (t1 *** t2)
  | execinf_if: forall f e s1 s2 le oe m v b t,
      eval_expr ge le m e v ->
      bool_val v (mytypeof e) m = Some b ->
      execinf_stmt f le oe m (if b then s1 else s2) t ->
      execinf_stmt f le oe m (S_if e s1 s2) t
  | execinf_while_true1: forall f s e v le oe m le' oe' m' t1 t2,
      eval_expr ge le m e v ->
      bool_val v (mytypeof e) m = Some true ->
      exec_stmt f le oe m s t1 le' oe' m' Out_normal ->
      execinf_stmt f le' oe' m' (S_while e s) t2 ->
      execinf_stmt f le oe m (S_while e s) (t1 *** t2)
  | execinf_while_true2: forall f s e v le oe m t,
      eval_expr ge le m e v ->
      bool_val v (mytypeof e) m = Some true ->
      execinf_stmt f le oe m s t ->
      execinf_stmt f le oe m (S_while e s) t
  | execinf_label: forall f lbl s le oe m t,
      execinf_stmt f le oe m s t ->
      execinf_stmt f le oe m (S_label lbl s) t
  | execinf_goto: forall f lbl le oe m s' t,
      find_label lbl (fun_statement (snd f)) = Some s' ->
      execinf_stmt f le oe m s' t ->
      execinf_stmt f le oe m (S_goto lbl) t
  | execinf_switch: forall f dl ll e le oe m v n s' t,
      eval_expr ge le m e v ->
      sem_switch_arg v (mytypeof e) = Some n ->
      find_label (select_switch n dl ll) (fun_statement (snd f)) = Some s' ->
      execinf_stmt f le oe m s' t ->
      execinf_stmt f le oe m (S_switch e dl ll) t
  | execinf_callassigned: forall f fid el le oe m vl l loc f' mtl' args t,
      eval_exprlist ge le m el vl ->
      find_function_by_name ge fid = Some (loc, f') ->
      typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) = OK mtl' ->
      sem_cast_list ge vl (mytypelistof el) mtl' m = Some args ->
      evalinf_funcall oe m f' args t ->
      execinf_stmt f le oe m (S_callassigned (Func fid) el l) t
  | execinf_virtualcallassigned: forall f cid fid el le oe m vl l loc f' mtl' args e v cid' fid' t,
      eval_expr ge le m e v ->
      eval_exprlist ge le m el vl ->
      resolve_ref oe v = Some (MTcomposite cid') ->
      In cid (superclasses_id (genv_cenv ge) cid') ->
      dispatch_function ge cid' fid = Some fid' ->
      find_function_by_name ge fid' = Some (loc, f') ->
      typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) = OK mtl' ->
      sem_cast_list ge (v :: vl) (mytypelistof (E_cons e el)) mtl' m = Some args ->
      evalinf_funcall oe m f' args t ->
      execinf_stmt f le oe m (S_virtualcallassigned cid fid e el l) t
  | execinf_interfaceclasscallassigned: forall f cid fid el le oe m vl l loc f' mtl' args e v cid' fid' t,
      eval_expr ge le m e v ->
      eval_exprlist ge le m el vl ->
      resolve_ref oe v = Some (MTcomposite cid') ->
      In cid (superinterfaces_id (genv_cenv ge) cid') ->
      dispatch_function ge cid' fid = Some fid' ->
      find_function_by_name ge fid' = Some (loc, f') ->
      typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) = OK mtl' ->
      sem_cast_list ge (v :: vl) (mytypelistof (E_cons e el)) mtl' m = Some args ->
      evalinf_funcall oe m f' args t ->
      execinf_stmt f le oe m (S_interfacecallassigned cid fid e el l) t
  | execinf_icallassigned_normal: forall f e el le oe m vl l loc f' mtl' args t,
      eval_expr ge le m e (Vptr loc Ptrofs.zero) ->
      eval_exprlist ge le m el vl ->
      find_function_by_address ge loc = Some f' ->
      typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) = OK mtl' ->
      sem_cast_list ge vl (mytypelistof el) mtl' m = Some args ->
      evalinf_funcall oe m f' args t ->
      execinf_stmt f le oe m (S_icallassigned e el l) t
  | execinf_javatry: forall f ll s le oe m t,
      execinf_stmt f le oe m s t ->
      execinf_stmt f le oe m (S_javatry ll s) t
  | execinf_javacatch: forall f ll s le oe m le' oe' m' s' v pt t1 t2,
      exec_stmt f le oe m s t1 le' oe' m' Out_throw ->
      lenv_thrownval le = Some (v, pt) ->
      find_handler (resolve_type oe v pt) ll (fun_statement (snd f)) = Some s' ->
      execinf_stmt f le oe m s' t2 ->
      execinf_stmt f le oe m (S_javatry ll s) (t1 *** t2)
with evalinf_funcall : oenv -> mem -> function -> list (val * mytype) -> traceinf -> Prop :=
| evalinf_funcall_intro: forall f fp fb args le oe m m' t,
    f = (fp, Some fb) ->
    function_entry ge (fp, fb) m args = Some (le, m') ->
    execinf_stmt (fp, fb) le oe m' (fun_statement fb) t->
    evalinf_funcall oe m f args t.

End Bigstep.

(** Big-step execution of a whole program.  *)

Inductive bigstep_program_terminates (p: program) (args: list (val * mytype)) : trace -> list (val * mytype) -> Prop :=
  | bigstep_program_terminates_intro: forall b f m m' ge oe t res,
      build_genv_mem p = OK (ge, m) ->
      find_function_by_name ge (prog_main p) = Some (b, f) ->
      eval_funcall_normal ge empty_oenv m f args t oe m' res ->
      bigstep_program_terminates p args t res.

Inductive bigstep_program_diverges (p: program) (args: list (val * mytype)) : traceinf -> Prop :=
  | bigstep_program_diverges_intro: forall b f m ge t,
      build_genv_mem p = OK (ge, m) ->
      find_function_by_name ge (prog_main p) = Some (b, f) ->
      evalinf_funcall ge empty_oenv m f args t ->
      bigstep_program_diverges p args t.
