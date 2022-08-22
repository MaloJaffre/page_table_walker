From iris.heap_lang Require Import proofmode notation.

(*
  heap_tree A := option ref (A * (tree A * tree A)))
*)
Inductive tree A : Type :=
| leaf : tree A
| node : A -> tree A -> tree A -> tree A.

Inductive path A : Type :=
| top : path A
| down : bool -> A -> tree A -> path A -> path A.

Arguments leaf {A}.
Arguments node {A} v l r.
Arguments top {A}.
Arguments down {A} b a p t.

Definition zipper A : Type := bool * tree A * path A.

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

(** A function that maps a function over all elements of a tree: *)
Fixpoint map_tree_coq {A B} (f : A -> B) (t : tree A) : tree B :=
  match t with
    | leaf => leaf
    | node a l r => node (f a) (map_tree_coq f l) (map_tree_coq f r)
  end.

(** A function that maps a function over all elements of a heap_tree: *)
Definition map_tree : val :=
  rec: "map_tree" "f" "tr" :=
    match: "tr" with
      NONE => #()
    | SOME "n" =>
      let: "a" := Fst !"n" in
      let: "p" := Snd !"n" in
      "map_tree" "f" (Fst "p") ;;
      "map_tree" "f" (Snd "p") ;;
      "n" <- ("f" "a", "p")
    end.

Definition size_tree_with_map : val :=
  λ: "tr",
    let: "c" := ref #0 in
    map_tree (λ: "v", "c" <- !"c" + #1 ;; "v") "tr";;
    !"c"
.

Fixpoint size_tree_coq {A} (t : tree A) : nat :=
  match t with
    | leaf => 0
    | node _ l r => 1 + size_tree_coq l + size_tree_coq r
  end.

Fixpoint size_path {A} (p: path A) : nat :=
  match p with
    | top => 0
    | down b _ t f => size_path f + match b with
      | false => 0
      | true => size_tree_coq t
    end
  end.

Definition size_zipper {A} (z: zipper A) : nat :=
  let '(b, t, p) := z in
  size_path p + match b with
    | false => 0
    | true => size_tree_coq t
  end.

Lemma size_up_to_left {A} (z : zipper A) : size_zipper (up_to_left z) = size_zipper z.
  destruct z as [z t]. destruct z as [b u].
  case b.
  - eauto.
  - case u.
    + eauto.
    + intros a l r. simpl. lia.
Qed.

Lemma size_left_to_right {A} (z : zipper A) : size_zipper (left_to_right z) = size_zipper z.
  destruct z as [z t]. destruct z as [b u].
  case b.
  - case t.
    + eauto.
    + intros d a c p. simpl. case d.
      * eauto.
      * simpl. lia.
  - eauto.
Qed.

Lemma size_right_to_up {A} (a : A) l r p :
  size_zipper (right_to_up (true, r, down true a l p)) =
  size_path p + size_tree_coq l + size_tree_coq r + 1
.
  simpl. lia.
Qed.

Lemma map_tree_coq_id {A} (t : tree A) : map_tree_coq id t = t.
  induction t; simpl; congruence.
Qed.

Section proof.
Context `{!heapGS Σ}.

(** Representation predicate in separation logic for a tree *)
Fixpoint is_tree (v : val) (t : tree val) : iProp Σ :=
  match t with
  | leaf => ⌜v = NONEV⌝
  | node a l r => ∃ ln : loc,
    ⌜v = SOMEV #ln⌝ ∗
    ∃ vl vr : val,
      ln ↦ (a, (vl, vr)) ∗
      is_tree vl l ∗
      is_tree vr r
  end%I.

(** Spec for map_tree using an induction predicate supporting local mutable
    state for the callback *)
Lemma map_tree_spec PI (f_coq: val -> val) (p: path val) (f: val) (v: val) (t: tree val):
  (∀ p, PI (false, leaf, p) -∗ PI (true, leaf, p)) ->
  (∀ z, PI z -∗ PI (up_to_left z)) ->
  (∀ z, PI z -∗ PI (left_to_right z)) ->
  (∀ a l r p,
    {{{ PI (true, r, down true a l p) }}}
    f a
    {{{ RET (f_coq a); PI (right_to_up (true, r, down true a l p)) }}}) -∗
  {{{ is_tree v t ∗ PI (false, t, p) }}}
  map_tree f v
  {{{RET #(); is_tree v (map_tree_coq f_coq t) ∗ PI (true, t, p) }}}
.
  iIntros "%Hll %Hul %Hlr #Hf %Φ !> Ht Post".
  iLöb as "IH" forall (v t p Φ). destruct t as [|a l r]; simpl; wp_rec; wp_let.
  - iDestruct "Ht" as "[-> HPI]". wp_match. iApply "Post". iSplitR.
    + eauto.
    + iApply Hll. iExact "HPI".
  - iDestruct "Ht" as "[Ht HPI]".
    iDestruct "Ht" as (ln) "[-> Ht]".
    iDestruct "Ht" as (vl vr) "(Hln & Hvl & Hvr)".
    do 2 (wp_load; wp_proj).
    wp_smart_apply ("IH" with "[$Hvl HPI]").
    iPoseProof (Hul with "HPI") as "HPI /="; eauto.
    iIntros "[Hvl HPI]".
    iPoseProof (Hlr with "HPI") as "HPI /=".
    wp_smart_apply ("IH" with "[$Hvr HPI //]").
    iIntros "[Hvr HPI]".
    wp_smart_apply ("Hf" with "[HPI //]").
    iIntros "HPI".
    wp_store.
    iApply "Post".
    iSplitR "HPI"; eauto 6 with iFrame.
Qed.

(** Induction predicate for the callback in size_tree *)
Definition PI_size_tree (c: loc) (z: zipper val) : iPropI Σ :=
  c ↦ #(size_zipper z).

Lemma size_tree_with_map_spec (v: val) (t: tree val) :
  {{{ is_tree v t }}} size_tree_with_map v {{{RET #(size_tree_coq t); is_tree v t }}}
.
  iIntros "%Φ Ht Post".
  wp_lam.
  wp_alloc c as "Hc".
  wp_let.
  set (PI := PI_size_tree c ).
  wp_smart_apply (map_tree_spec PI id top with "[] [Ht Hc] [Post]");
  unfold PI; unfold PI_size_tree.
  - eauto.
  - iIntros "%z HPI".
    iEval (rewrite size_up_to_left).
    eauto.
  - iIntros "%z HPI".
    iEval (rewrite size_left_to_right).
    eauto.
  - iIntros "%a %l %r %p %Φf !> HPI Postf".
    wp_lam.
    wp_load.
    wp_binop.
    wp_store.
    iApply "Postf".
    iEval (rewrite size_right_to_up).
    iEval (rewrite Nat2Z.inj_add).
    eauto.
  - iSplitL "Ht"; eauto.
  - iIntros "!> [Ht HPI]".
    wp_load.
    iApply "Post".
    iEval (rewrite map_tree_coq_id) in "Ht".
    iExact "Ht".
Qed.

End proof.
