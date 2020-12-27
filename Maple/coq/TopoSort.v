(*Require Import Coqlib Maps.

Definition node := positive.
Definition nodelist := list positive.
Definition graph := PTree.t nodelist.

Lemma fold_left_snd_property:
  forall (A B: Type) (a: A) (l1: list (A * B)) (l2: list A),
    In a (fold_left (fun (al: list A) (p: A * B) => fst p :: al) l1 l2) ->
    In a l2 \/ exists b, In (a, b) l1.
Proof.
  intros. generalize dependent l2.
  induction l1; intros; unfold fold_left; simpl; auto.
  - destruct a0. simpl in H. apply IHl1 in H. destruct H.
    + inversion H; subst; auto. right. eexists; eauto.
    + right. destruct H. eexists; eauto.
Qed.

Section Graph.

Variable G: graph.

Definition V: nodelist :=
  PTree.fold (fun l v _ => v :: l) G nil.

Lemma V_in_G: forall v,
    In v V -> exists l, PTree.get v G = Some l.
Proof.
  intros. unfold V in H. rewrite PTree.fold_spec in H.
  apply fold_left_snd_property in H. destruct H. inversion H.
  destruct H. apply PTree.elements_complete in H. eauto.
Qed.

Definition adj_list (v: node) : nodelist :=
  match G ! v with Some l => l | None => nil end.

Definition adj (u v: node) : bool :=
  in_dec peq u (adj_list v).

Definition in_degree (v: node) : Z :=
  fold_left (fun n u => if adj v u then Z.succ n else n) V 0.

Definition zero_in_degree (v: node) : bool :=
  match Z.compare (in_degree v) 0 with
  | Eq => true
  | _ => false
  end.

Definition zero_in_degree_nodes : nodelist :=
  filter (fun v => zero_in_degree v) V.

Definition in_degrees : PTree.t Z :=
  PTree.map (fun v _ => in_degree v) G.

End Graph.

Definition init_graph (l: nodelist) : graph :=
  PTree.empty nodelist.

Program Fixpoint naive_topological_sort_rec (g: graph) (l: nodelist) {measure (PTree_Properties.cardinal g)} : nodelist :=
  match zero_in_degree_nodes g with
  | nil => l
  | v :: _ =>
    v :: naive_topological_sort_rec (PTree.remove v g) l
  end.
Next Obligation.
  unfold zero_in_degree_nodes in *.
  assert (In v (filter (fun v : node => zero_in_degree g v) (V g))).
  rewrite <- Heq_anonymous; simpl; auto. apply filter_In in H.
  destruct H as [H _]. apply V_in_G in H. destruct H.
  eapply PTree_Properties.cardinal_remove; eauto.
Qed.

Definition naive_topological_sort (g: graph) : nodelist :=
  naive_topological_sort_rec g nil.
*)
Require Import Coqlib Maps.

Definition node := positive.
Definition nodeset := PTree.t unit.
Definition empty_nodeset := PTree.empty unit.
Definition graph := PTree.t nodeset.
Definition empty_graph := PTree.empty nodeset.

Lemma fold_left_list_property:
  forall (A B: Type) (a: A) (l1: list (A * B)) (l2: list A),
    In a (fold_left (fun (al: list A) (p: A * B) => fst p :: al) l1 l2) ->
    In a l2 \/ exists b, In (a, b) l1.
Proof.
  intros. generalize dependent l2.
  induction l1; intros; unfold fold_left; simpl; auto.
  - destruct a0. simpl in H. apply IHl1 in H. destruct H.
    + inversion H; subst; auto. right. eexists; eauto.
    + right. destruct H. eexists; eauto.
Qed.

Lemma fold_left_set_property:
  forall (i: positive) (l: list (positive * nodeset)) (s: nodeset),
    (fold_left (fun (s0: nodeset) (x: positive * nodeset) => PTree.set (fst x) tt s0) l s) ! i = Some tt ->
    s ! i = Some tt \/ exists s1, In (i, s1) l.
Proof.
  intros. generalize dependent s.
  induction l; intros; unfold fold_left; simpl; auto.
  destruct a. simpl in H. apply IHl in H. destruct H.
  - destruct (peq i p); subst; eauto.
    rewrite PTree.gso in H; auto.
  - right. destruct H. eexists; eauto.
Qed.

Section Graph.

Variable G: graph.

Definition V: nodeset :=
  PTree.fold (fun s v _ => PTree.set v tt s) G empty_nodeset.

Lemma V_in_G: forall v,
    V ! v = Some tt -> exists l, G ! v = Some l.
Proof.
  intros. unfold V in H. rewrite PTree.fold_spec in H.
  apply fold_left_set_property in H. destruct H.
  - rewrite PTree.gempty in H. congruence.
  - destruct H. apply PTree.elements_complete in H. eauto.
Qed.

Definition add_node (v: node) : graph :=
  match G ! v with
  | Some s => G
  | None => PTree.set v empty_nodeset G
  end.

Definition add_edge (u v: node) : graph :=
  match G ! u with
  | Some s =>
    match s ! v with
    | Some tt => G
    | None => PTree.set u (PTree.set v tt s) G
    end
  | None => PTree.set u (PTree.set v tt empty_nodeset) G
  end.

Definition adj (u v: node) : bool :=
  match G ! u with
  | Some s =>
    match s ! v with
    | Some tt => true
    | None => false
    end
  | None => false
  end.

Definition in_degree (v: node) : Z :=
  PTree.fold (fun n u _ => if adj u v then Z.succ n else n) V 0.

Definition in_degrees : PTree.t Z :=
  PTree.map (fun v _ => in_degree v) G.

(* Two ways to calculate nodes with zero in_degree, I don't know which one is more efficient. *)

Definition zero_in_degree (v: node) : bool :=
  match Z.compare (in_degree v) 0 with
  | Eq => true
  | _ => false
  end.

Definition zero_in_degree' (v: node) : bool :=
  match in_degrees ! v with
  | Some n =>
    match Z.compare n 0 with
    | Eq => true
    | _ => false
    end
  | None => false
  end.

Definition zero_in_degree_nodes : nodeset :=
  PTree.fold (fun s v _ => if zero_in_degree v then (PTree.set v tt s) else s) V empty_nodeset.

Definition find_zero_in_degree_node : option node :=
  find (fun v => zero_in_degree v) (map fst (PTree.elements V)).

End Graph.

Program Fixpoint naive_topological_sort_rec (g: graph) (l: list node) {measure (PTree_Properties.cardinal g)} : list node :=
  match find_zero_in_degree_node g with
  | None => l
  | Some v =>
    v :: naive_topological_sort_rec (PTree.remove v g) l
  end.
Next Obligation.
  unfold find_zero_in_degree_node in *.
  symmetry in Heq_anonymous. apply find_some in Heq_anonymous.
  destruct Heq_anonymous. apply list_in_map_inv in H.
  destruct H as [x [H H1]]. destruct x. simpl in H. subst.
  destruct u. apply PTree.elements_complete in H1.
  apply V_in_G in H1. destruct H1.
  eapply PTree_Properties.cardinal_remove; eauto.
Qed.

Definition naive_topological_sort (g: graph) : list node :=
  naive_topological_sort_rec g nil.

(*
Definition remove_node (g: graph) (in_degs: PTree.t Z) (v: node) : graph * PTree.t Z :=
  (PTree.remove v g, PTree.map (fun u n => if adj g u v then (Z.pred n) else n) in_degs).

Fixpoint topological_sort_rec (g: graph) (zl: nodelist) (in_deg: PTree.t Z) (ol: nodelist) : nodelist :=
  match zl with
  | nil => ol
  | v :: zl' =>
    let (g', in_degs') := remove_node g in_degs v in
    v :: topological_sort g' in_degs' ol
*)
