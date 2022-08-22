From refinedc.typing Require Import typing.
(* Notation "'[∗' 'map]' k ↦ x ∈ m , P" := (big_opM bi_sep (λ k x, P%I) m) : bi_scope. *)
Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : A -> tree A -> tree A -> tree A.

Inductive path (A : Type) : Type :=
| top : path A
| down : bool -> A -> tree A -> path A -> path A.

Arguments leaf {A}.
Arguments node {A} v l r.
Arguments top {A}.
Arguments down {A} b a t p.

(* TODO: rename state, add d to it and into struct *)
Definition zipper (A : Type) : Type := bool * tree A * path A.

Definition mirror_root {A} (t : tree A) : tree A :=
  match t with
  | leaf => leaf
  | node a l r => node a r l
  end.

Fixpoint mirror_rec {A} (t : tree A) : tree A :=
  match t with
  | leaf => leaf
  | node a l r => node a (mirror_rec r) (mirror_rec l)
  end.

Global Instance maybe_node {A} : Maybe3 (@node A) := λ t,
  match t with
  | leaf       => None
  | node a l r => Some (a, l, r)
  end.

Global Instance inhabited_tree A : Inhabited (tree A) := populate leaf.
Global Instance inhabited_path A : Inhabited (path A) := populate top.

Global Instance simpl_both_rel_leaf A (t : tree A) : SimplBothRel (=) (maybe3 node t) None (t = leaf).
Proof. split; destruct t; naive_solver. Qed.
Global Instance simpl_both_rel_node A (t : tree A) x : SimplBothRel (=) (maybe3 node t) (Some x) (t = node x.1.1 x.1.2 x.2).
Proof. split; destruct t, x as [[b l] r]; naive_solver. Qed.

Definition duplicate {A} (a : A) : A * A := (a, a).

Definition up_to_left {A} (z : zipper A) : zipper A :=
  let '(b, t, p) := z in
  match b with
    | true => z
    | _ =>
      match t with
        | node a l r => (false, l, down false a r p)
        | _ => z
      end
  end.

Definition left_to_right {A} (z : zipper A) : zipper A :=
  let '(b, l, p) := z in
  match b with
  | false => z
  | _ =>
    match p with
      | down false a r f => (false, r, down true a l f)
      | _ => z
    end
  end.

Definition right_to_up {A} (z : zipper A) : zipper A :=
  let '(b, r, p) := z in
  match b with
  | false => z
  | _ =>
    match p with
      | down true a l f => (true, node a l r, f)
      | _ => z
    end
  end.

Fixpoint map_tree {A B} (f : A -> B) (t : tree A) : (tree B) :=
  match t with
    | leaf => leaf
    | node a l r => node (f a) (map_tree f l) (map_tree f r)
  end.

Fixpoint size_tree {A} (t : tree A) : nat :=
match t with
  | leaf => 0
  | node _ l r => 1 + size_tree l + size_tree r
end.

Fixpoint size_path {A} (p: path A) : nat :=
  match p with
    | top => 0
    | down b _ t f => size_path f + match b with
      | false => 0
      | true => size_tree t
    end
  end.

Definition size_zipper {A} (z: zipper A) : nat :=
  let '(b, t, p) := z in
  size_path p + match b with
    | false => 0
    | true => size_tree t
  end.

Fixpoint size_path_all {A} (p: path A) : nat :=
  match p with
    | top => 0
    | down b _ t f => 1 + size_path_all f + size_tree t
  end.

Definition size_zipper_all {A} (z: zipper A) : nat :=
  let '(b, t, p) := z in
  size_path_all p + size_tree t
.

Lemma size_path_le_all {A} (p: path A) :
  size_path p ≤ size_path_all p.
Proof.
  induction p; try destruct b; simpl; lia.
Qed.

Lemma size_up_to_left {A} (z : zipper A) :
  size_zipper (up_to_left z) = size_zipper z.
Proof.
  destruct z as [[[] []] t]; simpl; lia.
Qed.

Lemma size_left_to_right {A} (z : zipper A) :
   size_zipper (left_to_right z) = size_zipper z.
Proof.
  destruct z as [[[] u] []]; simpl; eauto.
  - case b; simpl; lia.
Qed.

Lemma size_right_to_up {A} (a : A) l r p :
  size_zipper (right_to_up (true, r, down true a l p)) =
  (size_path p + size_tree l + size_tree r + 1)%nat.
Proof.
  simpl. lia.
Qed.

Lemma size_all_up_to_left {A} (z : zipper A) : size_zipper_all (up_to_left z) = size_zipper_all z.
  destruct z as [[[] []] t]; simpl; lia.
Qed.

Lemma size_all_left_to_right {A} (z : zipper A) : size_zipper_all (left_to_right z) = size_zipper_all z.
Proof.
  destruct z as [[[] u] []]; simpl; eauto.
  - case b; simpl; lia.
Qed.

Lemma size_all_right_to_up {A} (z : zipper A) :
  size_zipper_all (right_to_up z) = size_zipper_all z
.
  destruct z as [[[] u] []]; simpl; eauto.
  - case b; simpl; lia.
Qed.

Lemma size_map_tree {A B} (f : A -> B) (t : tree A) :
  size_tree (map_tree f t) = size_tree t
.
Proof.
  induction t; simpl; congruence.
Qed.


Inductive Forall_tree {A} (P : A -> Prop) : tree A -> Prop :=
| Forall_tree_leaf : Forall_tree P leaf
| Forall_tree_node : forall a l r, P a -> Forall_tree P l -> Forall_tree P r -> Forall_tree P (node a l r).

Inductive Forall_path {A} (P : A -> Prop) : path A -> Prop :=
| Forall_path_top : Forall_path P top
| Forall_path_dowb : forall b a t p, P a -> Forall_tree P t -> Forall_path P p -> Forall_path P (down b a t p).

Definition Forall_zipper {A} (P : A -> Prop) (z : zipper A) : Prop :=
  Forall_tree P z.1.2 /\ Forall_path P z.2.

Lemma forall_up_to_left {A} (P : A -> Prop) (z : zipper A) :
  Forall_zipper P z -> Forall_zipper P (up_to_left z).
Proof.
  destruct z as [[[] []] p]; simpl; eauto.
  - intros [Ht Hp]; simpl in *.
    split; simpl.
    all: try constructor; by inversion Ht.
Qed.

Lemma forall_left_to_right {A} (P : A -> Prop) (z : zipper A) :
  Forall_zipper P z -> Forall_zipper P (left_to_right z).
Proof.
  destruct z as [[[] t] []]; simpl; eauto.
  - intros [Ht Hp]; simpl in *.
    split; simpl; case b.
    all: try constructor; by inversion Hp.
Qed.

(* Lemma forall_right_to_up {A} (P : A -> Prop) (z : zipper A) :
  Forall_zipper P z -> Forall_zipper P (right_to_up z).
Proof.
  destruct z as [[[] t] []]; simpl; eauto.
  - intros [Ht Hp]; simpl in *.
    split; simpl; case b.
    all: try constructor; by inversion Hp.
Qed. *)

Lemma forall_equal_duplicate {A} {t : tree A} {b} :
  Forall_zipper (λ p, p.1 = p.2) (b, map_tree duplicate t, top).
Proof.
  split; simpl.
  - induction t; by constructor.
  - constructor.
Qed.

(* #[export] Hint Rewrite @size_up_to_left : lithium_rewrite.
#[export] Hint Rewrite @size_left_to_right : lithium_rewrite.
#[export] Hint Rewrite @size_right_to_up : lithium_rewrite.
#[export] Hint Rewrite @size_all_up_to_left : lithium_rewrite.
#[export] Hint Rewrite @size_all_left_to_right : lithium_rewrite.
#[export] Hint Rewrite @size_all_right_to_up : lithium_rewrite. *)

(* Lemma size_zipper_le_all {A} (z: zipper A) : size_zipper z ≤ size_zipper_all z.
Proof.
  destruct z as [[b t] p]; destruct b.
  all: simpl; pose proof (size_path_le_all p); lia.
Qed. *)

Fixpoint insert_leftmost {A} (t : tree A) (u: tree A) : tree A :=
match t with
  | leaf => u
  | node a l r => node a (insert_leftmost l u) r
end.

Inductive zip_tree_agree {A} : tree A -> tree A -> Prop :=
| leaf_zta : zip_tree_agree leaf leaf
| node_zta : forall ta tl tr ua ul ur,
              zip_tree_agree tl ul ->
              zip_tree_agree tr ur ->
              zip_tree_agree (node ta tl tr) (node ua ul ur).

Fixpoint zip_tree {A B} (t : tree A) (u : tree B) : tree (A * B) :=
match t with
  | leaf => leaf
  | node ta tl tr =>
    match u with
      | leaf => leaf
      | node ua ul ur => node (ta, ua) (zip_tree tl ul) (zip_tree tr ur)
    end
end.

Lemma forall_equal_zip {A} {t u: tree A} (Htu: zip_tree_agree t u) (Hzip: Forall_tree (λ p, p.1 = p.2) (zip_tree t u)) :
  u = t.
Proof.
  induction Htu; f_equal; inversion Hzip; eauto.
Qed.

Lemma size_zip_tree {A} (t u : tree A) (Htu : zip_tree_agree t u) :
  size_tree (zip_tree t u) = size_tree t
.
Proof.
  induction Htu; simpl; congruence.
Qed.

Section spec.
Context `{!typeG Σ} {A : Type}.

Global Instance simpl_size_path_inst (p : path A) : SimplAndUnsafe true ((0 @ int(size_t))%I = ((size_path p) @ int(size_t))%I) (λ T, (p = top) ∧ T).
Proof. intros P [Hp HP]. subst. done. Qed.
Section pi.
Context (PI : (type * zipper A) -> iProp Σ).

Global Instance mapsto_related_to z : RelatedTo (PI z) := {|
    rt_fic := FindDirect PI;
  |}.

Lemma subsume_up_to_left :
  `{⌜∀ z, PI (d, z) -∗ PI (d, (up_to_left z))⌝ ∗ ⌜p' = down false a r p⌝ ∗ T -∗
    subsume (PI (d, (false, node a l r, p))) (PI (d, (false, l, p'))) T}.
Proof.
  iIntros "* (%Hul & -> & $) HPI".
  iPoseProof (Hul with "HPI") as "HPI".
  done.
Qed.
Global Instance subsume_up_to_left_inst d a l r p p' :
  Subsume (PI (d, (false, node a l r, p))) (PI (d, (false, l, p')))
   :=
  λ T, i2p (subsume_up_to_left).

Lemma subsume_left_to_right :
  `{⌜∀ z, PI (d, z) -∗ PI (d, (left_to_right z))⌝ ∗ ⌜p' = down true a l p⌝ ∗ T -∗
    subsume (PI (d, (true, l, down false a r p))) (PI (d, (false, r, p'))) T}.
Proof.
  iIntros "* (%Hul & -> & $) HPI".
  iPoseProof (Hul with "HPI") as "HPI".
  done.
Qed.
Global Instance subsume_left_to_right_inst d a l r p p' :
  Subsume (PI (d, (true, l, down false a r p))) (PI (d, (false, r, p'))) :=
  λ T, i2p (subsume_left_to_right).

Lemma subsume_right :
  `{⌜l = l'⌝ ∗⌜r = r'⌝ ∗ ⌜p = p'⌝ ∗ T -∗
    subsume (PI (d, (true, r, down true a l p))) (PI (d, (true, r', down true a l' p'))) T}.
Proof.
  iIntros "* (-> & -> & -> & $) HPI //".
Qed.
Global Instance subsume_right_inst d a l l' r r' p p' :
  Subsume (PI (d, (true, r, down true a l p))) (PI (d, (true, r', down true a l' p'))):=
  λ T, i2p (subsume_right).

Lemma subsume_leaf :
  `{⌜∀ p, PI (d, (false, leaf, p)) -∗ PI (d, (true, leaf, p))⌝ ∗ T -∗
    subsume (PI (d, (false, leaf, p))) (PI (d, (true, leaf, p))) T}.
Proof.
  iIntros "* [%Hl $] HPI".
  iApply Hl.
  done.
Qed.
Global Instance subsume_leaf_inst d p  :
  Subsume (PI (d, (false, leaf, p))) (PI (d, (true, leaf, p))) :=
  λ T, i2p (subsume_leaf).

End pi.

Definition PI_size_tree_pure (p : type) (z : zipper (type * type)) : Prop :=
  p = with_refinement (int (size_t)) (size_zipper z) /\
  size_zipper_all z ≤ max_int size_t /\
  Forall_zipper (fun pa => pa.1 = pa.2) z.

Definition PI_size_tree (pz : type * zipper (type * type)) : iPropI Σ :=
  ⌜PI_size_tree_pure pz.1 pz.2⌝.

Lemma simplify_hyp_PI_size_tree d z T:
  (⌜PI_size_tree_pure d z⌝ -∗ T) -∗ simplify_hyp (PI_size_tree (d, z)) T.
Proof. done. Qed.
Global Instance simplify_hyp_PI_size_tree_inst d z:
  SimplifyHyp (PI_size_tree (d, z)) (Some 0%N) :=
  λ T, i2p (simplify_hyp_PI_size_tree d z T).

Lemma simplify_goal_PI_size_tree d z T :
  T (⌜PI_size_tree_pure d z⌝ ) -∗ simplify_goal (PI_size_tree (d, z)) T.
Proof.
  iIntros "HT". iExists _. iFrame. by iIntros "?".
Qed.
Global Instance simplify_goal_PI_size_tree_inst d z :
  SimplifyGoal (PI_size_tree (d, z)) (Some 0%N) :=
  λ T, i2p (simplify_goal_PI_size_tree d z T).

Lemma PI_size_tree_ul : `{PI_size_tree (d, z) -∗ PI_size_tree (d, up_to_left z)}.
Proof.
  iPureIntro.
  intros d z (Hd & Hsize & Hz). simpl in *.
  split; try split.
  - by rewrite size_up_to_left.
  - by rewrite size_all_up_to_left.
  - by apply forall_up_to_left.
Qed.

Lemma PI_size_tree_lr : `{PI_size_tree (d, z) -∗ PI_size_tree (d, left_to_right z)}.
Proof.
  iPureIntro.
  intros d z (Hd & Hsize & Hz). simpl in *.
  split; try split.
  - by rewrite size_left_to_right.
  - by rewrite size_all_left_to_right.
  - by apply forall_left_to_right.
Qed.

(* Global Instance subsume_place1 {f_coq : type -> type -> (type * type)} {a d l r}:
  (SimpleSubsumePlace
	  (f_coq (map_tree_coq f_coq (map_tree_coq f_coq d l).1 r).1 a).1
    (let (d, l) := map_tree_coq f_coq d l in
      let (d, r) := map_tree_coq f_coq d r in
      let (d, a) := f_coq d a in (d, node a l r)).1
    True).
Proof.
  iIntros (??) "_ H".
  destruct (map_tree_coq f_coq d l) as [d0 l1].
  destruct (map_tree_coq f_coq d0 r) as [d1 r1] eqn:H1.
  iEval (rewrite H1) in "H".
  destruct (f_coq d1 a) as [d2 a0] eqn:H2.
  iEval (rewrite H2) in "H".
  eauto.
Qed.

Global Instance subsume_place2 {f_coq : type -> type -> (type * type)} {d a l r na nl nr}:
  (SimpleSubsumePlace
	  (f_coq (map_tree_coq f_coq (map_tree_coq f_coq d l).1 r).1 a).2
    na
    ⌜(let (d, l) := map_tree_coq f_coq d l in
    let (d, r) := map_tree_coq f_coq d r in
    let (d, a) := f_coq d a in (d, node a l r)).2 =
      node na nl nr⌝).
Proof.
  iIntros (??) "%H0 H".
  destruct (map_tree_coq f_coq d l) as [d0 l1] eqn:HH.
  destruct (map_tree_coq f_coq d0 r) as [d1 r1] eqn:H1.
  iEval (rewrite H1) in "H".
  destruct (f_coq d1 a) as [d2 a0] eqn:H2.
  iEval (rewrite H2) in "H".
  simpl in H0.
  inversion H0; subst.
  eauto.
Qed. *)
End spec.


(* (* Lemma simplify_persistent_pure_goal T A (PI : zipper A -> iProp Σ) a l r p (H: ∀ z, PI z -∗ PI (up_to_left z)):
  T (PI (false, l, down false a r p)) -∗ simplify_goal (PI (false, node a l r, p)) T.
Proof. iIntros "HT". iExists _. iFrame. iIntros "HPI". iPoseProof (H with "HPI") as "HPI /=". done. Qed.
Global Instance simplify_persistent_pure_goal_id {Σ} (Φ : Prop):
  SimplifyGoal (Σ:=Σ) (□ ⌜Φ⌝) (Some 0%N) :=
  λ T, i2p (simplify_persistent_pure_goal Φ T). *)

  Global Instance mapsto_related_to A (PI : zipper A -> iProp Σ) z : RelatedTo (PI z) := {|
    rt_fic := FindDirect PI;
  |}.

  Class TCAssumption (P: Prop) := tc_assumption : P.
  Hint Extern 0 (TCAssumption _) => unfold TCAssumption; eassumption: typeclass_instances.

Lemma simplify_up_to_left T A (PI : zipper A -> iProp Σ) a l r p { H: TCFastDone (∀ z, PI z -∗ PI (up_to_left z)) } :
  (PI (false, l, down false a r p) -∗ T) -∗ simplify_hyp (PI (false, node a l r, p)) T.
Proof. iIntros "HT HPI". iApply "HT". iPoseProof (H with "HPI") as "HPI /=". done. Qed.

Global Instance simplify_up_to_left_inst A (PI : zipper A -> iProp Σ) a l r p { H: TCAssumption (∀ z, PI z -∗ PI (up_to_left z)) } :
  SimplifyHyp (PI (false, node a l r, p)) (Some 0%N) :=
  λ T, i2p (simplify_up_to_left T A PI a l r p). *)

(* WORKING *)

(* Lemma subsume_up_to_left {T A} {PI : zipper A -> iProp Σ} {a l r p p'} :
⌜∀ z, PI z -∗ PI (up_to_left z)⌝ ∗ ⌜p' = down false a r p⌝ ∗ T -∗
  subsume (PI (false, node a l r, p)) (PI (false, l, p')) T.
Proof.
  iIntros "(%Hul & -> & $) HPI".
  iPoseProof (Hul with "HPI") as "HPI /=".
  done.
Qed.
Global Instance subsume_up_to_left_inst {A} {PI : zipper A -> iProp Σ} {a l r p p'}  :
  Subsume (PI (false, node a l r, p)) (PI (false, l, p')) :=
  λ T, i2p (subsume_up_to_left).

Global Instance mapsto_related_to A (PI : zipper A -> iProp Σ) z : RelatedTo (PI z) := {|
    rt_fic := FindDirect PI;
  |}. *)
