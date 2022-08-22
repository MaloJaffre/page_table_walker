From refinedc.typing Require Import typing.


(* Definition sum_proj_inl {A B} (p : A + B) (H : is_inl p) : A :=
  match p with
    | inl a => Some a
    | _ => None
  end. *)
(* bit-index of the start of a physical adress chunk (a, b, c, d, e) *)
Definition granule_shift (l : Z) : Z :=
  match l with
    | 0 => 39
    | 1 => 30
    | 2 => 21
    | 3 => 12
    | _ => 0
  end.

Lemma granule_shift_def (l : Z) {H1 : 0 ≤ l} {H2 : l < 4} :
  (12 - 3) * (4 - l) + 3 = granule_shift l.
Proof.
  case l as [| p |]; try done.
  repeat (case p as [p | p |]; try done).
Qed.

Inductive tree (A : Type) : Type :=
  | node : A -> list (tree A) -> tree A.

Inductive path (A : Type) : Type :=
  | top : path A
  | down : A -> list (tree A) -> list (tree A) -> path A -> path A.

Arguments node {A} a cs.
Arguments top {A}.
Arguments down {A} a ls rs p.

Definition zipper (A : Type) : Type := bool * tree A * path A.

Definition tree_head {A} (t : tree A) : A :=
  match t with
    | node a _ => a
  end.

Definition tree_children {A} (t : tree A) : list (tree A):=
  match t with
    | node _ cs => cs
  end.

Fixpoint map_tree {A B} (f: A -> B) (t : tree A) : tree B :=
  match t with
    | node a ts => node (f a) (map_tree f <$> ts)
  end.

Definition up_to_first {A} (z : zipper A) : zipper A :=
  let: (d, t, p) := z in
  match d with
    | true => z
    | _ =>
      match t with
        | node a ls =>
          match ls with
            | l::ls => (false, l, down a [] ls p)
            | _ => z
          end
      end
  end.

Definition next_sibling {A} (z : zipper A) : zipper A :=
  let: (d, t, p) := z in
  match d with
    | false => z
    | _ =>
    match p with
      | down a ls rs f =>
        match rs with
          | r::rs => (false, r, down a (ls ++ [r]) rs f)
          | _ => z
        end
      | _ => z
    end
  end.

Definition last_to_up {A} (z : zipper A) : zipper A :=
  let: (d, r, p) := z in
  match d with
  | false => z
  | _ =>
    match p with
      | down a ls rs f =>
        match ls with
          | [] => (true, node a rs, f)
          | _ => z
        end
      | _ => z
    end
  end.

Record Pte := mk_pte {
  pte_valid : bool;
  pte_type : bool;
  pte_leaf_attr_lo : Z;
  pte_addr : Z;
  pte_undef : Z;
  pte_leaf_attr_hi : Z;
}.

Global Instance Pte_settable : Settable _ := settable! mk_pte
  <pte_valid; pte_type; pte_leaf_attr_lo; pte_addr; pte_undef; pte_leaf_attr_hi>.

Definition null_pte := {|
  pte_valid := false;
  pte_type := false;
  pte_leaf_attr_lo := 0;
  pte_addr := 0;
  pte_undef := 0;
  pte_leaf_attr_hi := 0;
|}.

Definition mk_pte_addr (a : addr) : Pte := null_pte <| pte_addr := a |>.

Definition pte_repr (p : Pte) : Z :=
  bf_cons 0 1 (bool_to_Z $ pte_valid p) $
  bf_cons 1 1 (bool_to_Z $ pte_type p) $
  bf_cons 2 10 (pte_leaf_attr_lo p) $
  bf_cons 12 36 (pte_addr p) $
  bf_cons 48 3 (pte_undef p) $
  bf_cons 51 13 (pte_leaf_attr_hi p) $
  bf_nil.

Arguments pte_repr _/.

Definition pte_wf (p : Pte) : Prop :=
  0 ≤ bool_to_Z $ pte_valid p < 2^1 ∧
  0 ≤ bool_to_Z $ pte_type p < 2^1 ∧
  0 ≤ pte_leaf_attr_lo p < 2^10 ∧
  0 ≤ pte_addr p < 2^36 ∧
  0 ≤ pte_undef p < 2^3 ∧
  0 ≤ pte_leaf_attr_hi p < 2^13.

Global Instance Pte_BitfieldDesc : BitfieldDesc Pte := {|
  bitfield_it := u64;
  bitfield_repr := pte_repr;
  bitfield_wf := pte_wf;
|}.

Global Instance simpl_exist_Pte P : SimplExist Pte P
  (∃ valid type leaf_attr_lo addr undef leaf_attr_hi,
    P {|
      pte_valid := valid;
      pte_type := type;
      pte_leaf_attr_lo := leaf_attr_lo;
      pte_addr := addr;
      pte_undef := undef;
      pte_leaf_attr_hi := leaf_attr_hi;
    |}).
Proof. unfold SimplExist. naive_solver. Qed.
Global Instance simpl_forall_Pte P : SimplForall Pte 6 P
  (∀ valid type leaf_attr_lo addr undef leaf_attr_hi,
    P {|
      pte_valid := valid;
      pte_type := type;
      pte_leaf_attr_lo := leaf_attr_lo;
      pte_addr := addr;
      pte_undef := undef;
      pte_leaf_attr_hi := leaf_attr_hi;
    |}).
Proof. unfold SimplForall => ? []. naive_solver. Qed.



Definition max_level : Z := 4.

(* Get a complete adress from a page address and an offset into that page *)
Definition page_addr_and_offset_to_addr (page_addr : Z) (offset : Z) : Z :=
  bf_cons 0 12 offset $
  bf_cons 12 48 page_addr $
  bf_nil.

(* For a pte that is a block or page entry, get the physical adress of the block or page (OA) *)
Definition pte_block_or_page_to_page_addr (l: Z) (p: Pte) : Z :=
  let: s := (granule_shift l) in
  bf_slice (s - 12) (48 - s) (pte_addr p).
  (* or bf_slice s (48 - s) (pte_repr p) *)

(* From an addr, get the offset into a block or page at level l *)
Definition addr_to_offset (l: Z) (paddr : Z) : Z :=
  bf_slice 0 (granule_shift l) paddr.

(* For a physical adress to translate, get the index for the table at level l *)
Definition vaddr_to_table_idx (l : Z) : Z -> Z := bf_slice (granule_shift l) 9.

Inductive Pte_Type :=
  | Invalid
  | Block_or_Page
  | Table.

(* Get the type of a pte p at level l *)
Definition pte_discriminate (l : Z) (p : Pte) : Pte_Type :=
  if pte_valid p then
    if orb (l =? 3) (negb $ pte_type p) then
      Block_or_Page
    else
      Table
  else
    Invalid.

(* From the current focused view ps of the page table at level (4 - inverted_level), recursively translate vaddr to a physical page adress *)
Fixpoint translate_vaddr_to_paddr_inner
  (inverted_level : nat) (table: list (tree Pte)) (vaddr : Z) : option Z
:=
  match inverted_level with
    | O => None
    | S inverted_next_level =>
      let: level := 4 - inverted_level in
      let: idx_in_table := Z.to_nat (vaddr_to_table_idx level vaddr) in
      table_tree ← table !! idx_in_table;
      match table_tree with
        node pte next_table =>
          match pte_discriminate level pte with
            | Invalid => None
            | Block_or_Page => Some $ page_addr_and_offset_to_addr
              (pte_block_or_page_to_page_addr level pte)
              (addr_to_offset level vaddr)
            | Table =>
              translate_vaddr_to_paddr_inner inverted_next_level next_table vaddr
          end
      end
  end.

(* Translate a virtual adress to a physical adress using a page table *)
Definition translate_vaddr_to_paddr : list (tree Pte) -> Z -> option Z
:= translate_vaddr_to_paddr_inner 4.

(* Get the physical address of the next-level translation table for a pte that is a table entry *)
(* "Pte to ptr" *)
(* Only useful to refine kvm_pte_t with (list (tree Pte)) *)
Definition pte_table_to_next_table_paddr (l: Z) (p: Pte) : option Z :=
  match pte_discriminate l p with
    | Table => Some $ page_addr_and_offset_to_addr (pte_addr p) 0
    | _ => None
  end.

Global Instance pte_discriminate_Table l pte : Decision (pte_discriminate l pte = Table).
Proof. solve_decision. Defined.

Lemma pte_discriminate_3_not_table pte : pte_discriminate 3 pte ≠ Table.
Proof. unfold pte_discriminate. by case (pte_valid pte). Qed.
(*
(* Examples: *)

Definition chunks_to_vaddr (a b c d e : Z) : Z :=
  bf_cons 0 12 e $
  bf_cons 12 9 d $
  bf_cons 21 9 c $
  bf_cons 30 9 b $
  bf_cons 39 9 a $
  bf_nil.

Definition invalid_pte : Pte :=
  empty_pte.

Definition mk_block_pte (block_addr : Z) : Pte :=
  mk_pte true false 0 block_addr 0 0.

Definition mk_page_pte (page_addr : Z) : Pte :=
  mk_pte true true 0 page_addr 0 0.

Definition dummy_table_pte : Pte :=
  mk_pte true true 0 0 0 0.

Definition mk_leaf_pgtree (p : Pte) : tree Pte :=
  node p [].

Definition mk_dummy_pgtree_from_pgtable (table : list (tree Pte)) : tree Pte :=
  node dummy_table_pte table.

Definition empty_pgtree : tree Pte := mk_leaf_pgtree invalid_pte.

Definition empty_pgtable : list (tree Pte) := repeat empty_pgtree 512.

Definition mk_one_pgtree_pgtable (idx : nat) (pgtree : tree Pte) : list (tree Pte) :=
  repeat empty_pgtree idx ++ (pgtree :: repeat empty_pgtree (idx - 1)).

Definition one_block_pgtable : list (tree Pte) :=
  mk_one_pgtree_pgtable 1 $
  mk_dummy_pgtree_from_pgtable $ mk_one_pgtree_pgtable 2 $
  (mk_leaf_pgtree $ mk_block_pte 16).

Definition one_page_pgtable : list (tree Pte) :=
  mk_one_pgtree_pgtable 1 $
  mk_dummy_pgtree_from_pgtable $ mk_one_pgtree_pgtable 2 $
  mk_dummy_pgtree_from_pgtable $ mk_one_pgtree_pgtable 3 $
  mk_dummy_pgtree_from_pgtable $ mk_one_pgtree_pgtable 4 $
  (mk_leaf_pgtree $ mk_page_pte 16).

Compute translate_vaddr_to_paddr empty_pgtable 0.
Compute translate_vaddr_to_paddr one_block_pgtable (chunks_to_vaddr 2 2 3 7 5).
Compute translate_vaddr_to_paddr one_page_pgtable (chunks_to_vaddr 1 2 3 7 5).

Compute vaddr_to_table_idx 3 (chunks_to_vaddr 1 2 3 4 5).

Compute pte_discriminate 3 $ mk_page_pte 4. *)

Definition pte_loc_agree (level : Z) (pte : option Pte) (l : loc) : Prop :=
  match pte with
    | Some pte => pte_table_to_next_table_paddr level pte = Some l.2
    | None => True
  end.

Definition pgtable_refinement : Type := (Z * option Pte * list (tree Pte)).

Definition pgtree_to_next_pgtable_refinement (level : Z) (pgtree : tree Pte) : option pgtable_refinement :=
  match pgtree with
    | node pte next_pgtable =>
      match pte_discriminate level pte with
        | Table => Some (level + 1, Some pte, next_pgtable)
        | _ => None
      end
  end.

Section spec.
Context `{!typeG Σ}.

Global Instance subsume_invalid_pte :
  SimpleSubsumePlace
    (0 @ int(u64))
    (bf_cons 0 1 0
    (bf_cons 1 1 0
      (bf_cons 2 10 0
          (bf_cons 12 36 0 (bf_cons 48 3 0 (bf_cons 51 13 0 bf_nil))))) @
            bitfield_raw(u64))
    True.
Proof.
  iIntros (??) "_ ?". eauto.
Qed.
End spec.
