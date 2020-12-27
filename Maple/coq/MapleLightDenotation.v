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
Require Import MapleLightExec.
From ITree Require Import ITree.

Section Denotation.

Inductive emptyE: Type -> Type := .

Definition exec_program_aux (ge: genv) (st: state) : itree emptyE (state + option (list (val * type))) :=
  match step ge st with
  | Some st' =>
    match final_state st' with
    | Some res => Ret (inr (Some res))
    | None => Ret (inl st')
    end
  | None => Ret (inr None)
  end.

Definition exec_program (p: program) (args: list (val * type)) : itree emptyE (option (list (val * type))) :=
  match initial_state p args with
  | OK (ge, st) =>
    ITree.iter (exec_program_aux ge) st
  | Error _ => Ret None
  end.

End Denotation.
