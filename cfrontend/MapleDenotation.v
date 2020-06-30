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
Require Import MapleExec.
Require Import ITree.

Section Denotation.

Inductive emptyE: Type -> Type := .

Definition exec_program_aux (ge: genv) (st: state) : itree emptyE (state + option (list (val * mytype))) :=
  match step ge st with
  | Some st' =>
    match final_state st' with
    | Some res => Ret (inr (Some res))
    | None => Ret (inl st')
    end
  | None => Ret (inr None)
  end.

Definition exec_program (p: program) (args: list (val * mytype)) : itree emptyE (option (list (val * mytype))) :=
  match initial_state p args with
  | OK (ge, st) =>
    ITree.iter (exec_program_aux ge) st
  | Error _ => Ret None
  end.

End Denotation.
(*
Section Denotation.

Variable ge: genv.

Inductive outcome: Type :=
  | Out_normal: outcome
  | Out_throw: outcome
  | Out_return: list (val * mytype) -> outcome.

Inductive emptyE: Type -> Type := .

Definition tree : Type := itree emptyE (option (lenv * oenv * mem * outcome)).

Definition bind_tree (t: tree) (k: outcome -> lenv -> oenv -> mem -> tree) : tree :=
  ITree.bind t (fun ost =>
                  match ost with
                  | Some (le, oe, m, out) => k out le oe m
                  | None => Ret None
                  end).

Definition out_tree (out: outcome) : lenv -> oenv -> mem -> tree :=
  fun le oe m => Ret (Some (le, oe, m, out)).

Variable k: (option (lenv * oenv * mem * outcome)) -> itree emptyE (option (lenv * oenv * mem * outcome) + option (lenv * oenv * mem * outcome)).

Fixpoint exec_stmt (f: concrete_function) (s: statement) (le: lenv) (oe: oenv) (m: mem) : tree :=
  match s with
  | S_skip => Ret (Some (le, oe, m, Out_normal))
  | S_dassign vid fi e =>
    match find_var ge le vid with
    | Some (loc, (mt, (sc, ta))) =>
      match fieldoffset (genv_cenv ge) mt fi with
      | OK (mt', ofs) =>
        match eval_ext_expr ge le (e, oe, m) with
        | Some (v, oe', m') =>
          match sem_cast v (mytypeof_ext_expr e) mt' m' (genv_cenv ge) with
          | Some v' =>
            match assign_loc (genv_cenv ge) mt' ta m' loc (Ptrofs.repr ofs) v' with
            | Some m'' =>
              Ret (Some (le, oe', m'', Out_normal))
            | None => Ret None
            end
          | None => Ret None
          end
        | None => Ret None
        end
      | Error _ => Ret None
      end
    | None => Ret None
    end
  (*| NormalState f (S_iassign ty fi e1 e2) k le oe m =>
    match type_to_mytype (genv_mytypes ge) ty with
    | OK mt =>
      match eval_expr le m e1 with
      | Some (Vptr loc ofs) =>
        match mt with
        | MTpointer mt' =>
          match fieldoffset (genv_cenv ge) mt' fi with
          | OK (mt'', delta) =>
            match eval_ext_expr le (e2, oe, m) with
            | Some (v, oe', m') =>
              match sem_cast v (mytypeof_ext_expr e2) mt'' m' (genv_cenv ge) with
              | Some v' =>
                match assign_loc (genv_cenv ge) mt'' default_type_attr m' loc (Ptrofs.add ofs (Ptrofs.repr delta)) v' with
                | Some m'' =>
                  Some (NormalState f S_skip k le oe' m'')
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
    | Error _ => None
    end
  | NormalState f (S_regassign pt (Preg id) e) k le oe m =>
    match find_preg le id with
    | Some (v0, pt') =>
      if prim_type_eq pt pt' then
        match eval_ext_expr le (e, oe, m) with
        | Some (v, oe', m') =>
          match sem_cast v (mytypeof_ext_expr e) (MTprim pt) m' (genv_cenv ge) with
          | Some v' =>
            Some (NormalState f S_skip k (set_preg le id v' pt) oe' m')
          | None => None
          end
        | None => None
        end
      else None
    | None =>
      match eval_ext_expr le (e, oe, m) with
      | Some (v, oe', m') =>
        match sem_cast v (mytypeof_ext_expr e) (MTprim pt) m' (genv_cenv ge) with
        | Some v' =>
          Some (NormalState f S_skip k (set_preg le id v' pt) oe' m')
        | None => None
        end
      | None => None
      end
    end
  | NormalState f (S_regassign pt Thrownval e) k le oe m =>
    match eval_ext_expr le (e, oe, m) with
    | Some (v, oe', m') =>
      match sem_cast v (mytypeof_ext_expr e) (MTprim pt) m' (genv_cenv ge) with
      | Some v' =>
        Some (NormalState f S_skip k (set_thrownval le v' pt) oe' m')
      | None => None
      end
    | None => None
    end*)
  | S_seq s1 s2 =>
    bind_tree
      (exec_stmt f s1 le oe m)
      (fun out =>
         match out with
         | Out_normal => exec_stmt f s2
         | _ => out_tree out
         end)
  | S_if e s1 s2 =>
    match eval_expr ge le m e with
    | Some v =>
      match bool_val v (mytypeof e) m with
      | Some b =>
        exec_stmt f (if b then s1 else s2) le oe m
      | None => Ret None
      end
    | None => Ret None
    end
  | S_while e s =>
    ITree.iter
      (fun st =>
         match st with
         | Some (le, oe, m, Out_normal) =>
           match eval_expr ge le m e with
           | Some v =>
             match bool_val v (mytypeof e) m with
             | Some true =>
               ITree.bind
                 (exec_stmt f s le oe m)
                 (fun st => Ret (inl st))
             | Some false =>
               Ret (inr (Some (le, oe, m, Out_normal)))
             | None => Ret (inr None)
             end
           | None => Ret (inr None)
           end
         | Some (le, oe, m, out) =>
           Ret (inr (Some (le, oe, m, out)))
         | None => Ret (inr None)
         end)
      (Some (le, oe, m, Out_normal))
  | S_label lbl s =>
    exec_stmt f s le oe m
  | S_goto lbl =>
    match find_label lbl (fun_statement (snd f)) (call_cont k) with
    | Some (s', k') =>
      Some (NormalState f s' k' le oe m)
    | None => None
    end
  | _ => Ret None
  end.
  | NormalState f (S_switch e dl ll) k le oe m =>
    match eval_expr le m e with
    | Some v =>
      match sem_switch_arg v (mytypeof e) with
      | Some n =>
        Some (NormalState f (S_goto (select_switch n dl ll)) k le oe m)
      | None => None
      end
    | None => None
    end
  | NormalState f (S_return el) k le oe m =>
    match eval_exprlist le m el with
    | Some nil =>
      match (type_of_returns (fun_returns (fst f))) with
      | Tnil | Tcons (Tprim PTvoid) Tnil =>
        match Mem.free_list m (blocks_of_lenv ge le) with
        | Some m' =>
          Some (ReturnState nil (call_cont k) oe m')
        | None => None
        end
      | _ => None
      end
    | Some vl =>
      match typelist_to_mytypelist (genv_mytypes ge) (type_of_returns (fun_returns (fst f))) with
      | OK mtl' =>
        match sem_cast_list ge vl (mytypelistof el) mtl' m with
        | Some vl' =>
          match Mem.free_list m (blocks_of_lenv ge le) with
          | Some m' =>
            Some (ReturnState vl' (call_cont k) oe m')
          | None => None
          end
        | None => None
        end
      | Error _ => None
      end
    | None => None
    end
  | NormalState f S_skip k le oe m =>
    if is_call_cont k then
      match type_of_returns (fun_returns (fst f)) with
      | Tnil =>
        match Mem.free_list m (blocks_of_lenv ge le) with
        | Some m' =>
          Some (ReturnState nil k oe m')
        | None => None
        end
      | _ => None
      end
    else None
  | NormalState f (S_callassigned (Func fid) el l) k le oe m =>
    match eval_exprlist le m el with
    | Some vl =>
      match find_function_by_name ge fid with
      | Some (loc, f') =>
        match typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) with
        | OK mtl' =>
          match sem_cast_list ge vl (mytypelistof el) mtl' m with
          | Some vl' =>
            Some (CallState f' vl' (Kcall l f le k) oe m)
          | None => None
          end
        | Error _ => None
        end
      | None => None
      end
    | None => None
    end
  | NormalState f (S_virtualcallassigned cid fid e el l) k le oe m =>
    match eval_expr le m e with
    | Some v =>
      match eval_exprlist le m el with
      | Some vl =>
        match resolve_ref oe v with
        | Some (MTcomposite cid') =>
          if in_dec ident_eq cid (superclasses_id (genv_cenv ge) cid') then
            match dispatch_function ge cid' fid with
            | Some fid' =>
              match find_function_by_name ge fid' with
              | Some (loc, f') =>
                match typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) with
                | OK mtl' =>
                  match sem_cast_list ge (v :: vl) (mytypelistof (E_cons e el)) mtl' m with
                  | Some vl' =>
                    Some (CallState f' vl' (Kcall l f le k) oe m)
                  | None => None
                  end
                | Error _ => None
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
  | NormalState f (S_interfacecallassigned cid fid e el l) k le oe m =>
    match eval_expr le m e with
    | Some v =>
      match eval_exprlist le m el with
      | Some vl =>
        match resolve_ref oe v with
        | Some (MTcomposite cid') =>
          if in_dec ident_eq cid (superinterfaces_id (genv_cenv ge) cid') then
            match dispatch_function ge cid' fid with
            | Some fid' =>
              match find_function_by_name ge fid' with
              | Some (loc, f') =>
                match typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) with
                | OK mtl' =>
                  match sem_cast_list ge (v :: vl) (mytypelistof (E_cons e el)) mtl' m with
                  | Some vl' =>
                    Some (CallState f' vl' (Kcall l f le k) oe m)
                  | None => None
                  end
                | Error _ => None
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
  | NormalState f (S_icallassigned e el l) k le oe m =>
    match eval_expr le m e with
    | Some (Vptr loc ofs) =>
      if Ptrofs.eq_dec ofs Ptrofs.zero then
        match eval_exprlist le m el with
        | Some vl =>
          match find_function_by_address ge loc with
          | Some f' =>
            match typelist_to_mytypelist (genv_mytypes ge) (type_of_params (fun_params (fst f'))) with
            | OK mtl' =>
              match sem_cast_list ge vl (mytypelistof el) mtl' m with
              | Some vl' =>
                Some (CallState f' vl' (Kcall l f le k) oe m)
              | None => None
              end
            | Error _ => None
            end
          | None => None
          end
        | None => None
        end
      else None
    | _ => None
    end
  | NormalState f (S_javatry ll s) k le oe m =>
    Some (NormalState f s (Kjavatry ll k) le oe m)
  | ExceptionState f k le oe m =>
    match find_thrownval le with
    | Some (v, mt) =>
      match catch_cont k with
      | Kjavatry ll k1 =>
        match find_handler ge (resolve_type oe v mt) ll (fun_statement (snd f)) (call_cont k1) with
        | Some k3 =>
          Some (NormalState f S_skip k3 le oe m)
        | None => Some (ExceptionState f k1 le oe m)
        end
      | Kcall l f' le' k1 =>
        match Mem.free_list m (blocks_of_lenv ge le) with
        | Some m' =>
          Some (ExceptionState f' k1 le' oe m')
        | None => None
        end
      | _ => None
      end
    | None => None
    end
  | NormalState f (S_throw e) k le oe m =>
    match eval_expr le m e with
    | Some v =>
      Some (ExceptionState f k (set_thrownval le v (prim_type_of e)) oe m)
    | None => None
    end
  | NormalState f (S_free e) k le oe m =>
    match eval_expr le m e as v with
    | Some (Vptr b lo) =>
      match Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) with
      | Some v =>
        match val_to_ptrofs v with
        | Some sz =>
          match Z.compare (Ptrofs.unsigned sz) 0 with
          | Gt =>
            match Mem.free m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) with
            | Some m' =>
              Some (NormalState f S_skip k le oe m')
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
        Some (NormalState f S_skip k le oe m)
      else None
    | Some (Vlong i) =>
      if Archi.ptr64 && Int64.eq_dec i Int64.zero then
        Some (NormalState f S_skip k le oe m)
      else None
    | _ => None
    end
  | NormalState f (S_incref e) k le oe m =>
    match prim_type_of e with
    | PTref =>
      match eval_expr le m e with
      | Some (Vptr loc ofs) =>
        if Ptrofs.eq_dec ofs (Ptrofs.repr 0) then
          match oe ! loc with
          | Some (mt, n, b) =>
            Some (NormalState f S_skip k le (PTree.set loc (mt, S n, b) oe) m)
          | None => None
          end
        else None
      | _ => None
      end
    | _ => None
    end
  | NormalState f (S_decref e) k le oe m =>
    match prim_type_of e with
    | PTref =>
      match eval_expr le m e with
      | Some (Vptr loc ofs) =>
        if Ptrofs.eq_dec ofs (Ptrofs.repr 0) then
          match oe ! loc with
          | Some (mt, n, b) =>
            Some (NormalState f S_skip k le (PTree.set loc (mt, pred n, b) oe) m)
          | None => None
          end
        else None
      | _ => None
      end
    | _ => None
    end
  | NormalState f (S_eval e) k le oe m =>
    match eval_expr le m e with
    | Some v =>
      Some (NormalState f S_skip k le oe m)
    | None => None
    end
  | CallState f vl k oe m =>
    match f with
    | (fp, Some fb) =>
      match function_entry ge (fp, fb) m vl with
      | Some (le, m') =>
        Some (NormalState (fp, fb) (fun_statement fb) k le oe m')
      | None => None
      end
    | (_, None) => None
    end
  | ReturnState vl (Kcall l f le k) oe m =>
    match assign_returns ge le l vl m with
    | Some m' =>
      Some (NormalState f S_skip k le oe m')
    | None => None
    end
  | NormalState _ (S_javacatch _ _) _ _ _ _ => None
  | ReturnState _ _ _ _ => None
  (*| _ => None*)
  end.

End Semantics.
*)
