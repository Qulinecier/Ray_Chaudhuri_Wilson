import Mathlib.Data.Nat.Choose.Multinomial

open Finset

variable {α : Type} [DecidableEq α] {X: Finset α} (s: ℕ) (r: ℕ) (A B : Finset α)

/--Projection map from S to (A∩S, (B\A)∩ S)-/
def intersect_i: (a : Finset α) → a ∈ {S ∈ powersetCard s X | #(A ∩ S) = r ∧ S ⊆ B}
    → Finset α × Finset α :=
  fun S ↦ fun ?_ ↦ ((A: Finset α) ∩ S, ((B: Finset α) \ (A: Finset α)) ∩ S)

/--Reverse map from (S.1, S.2) to S.1 ∪ S.2-/
def intersect_j: (a : Finset α × Finset α) →
    a ∈ powersetCard r (A ∩ B) ×ˢ powersetCard (s - r) (B \ A) → Finset α :=
  fun S ↦ fun ?_ ↦ S.1 ∪ S.2

/--
The cardinality of {S∈𝓟ₛ(X)| |A∩S|=r and S⊆B} is equal to the number of ways choosing r elements
in A∩B and s-r elements in B\A.
#{S∈𝓟ₛ(X)| |A∩S|=r and S⊆B} = #𝓟ᵣ(A∩B) × #𝓟ₛ₋ᵣ(B\A)
-/
lemma card_powerset_card_product (hrs : r ≤ s) (hA: A ⊆ X) (hB: B ⊆ X) :
    #{S ∈ powersetCard s X | #(A ∩ S) = r
    ∧ (S: Finset α) ⊆ (B: Finset α)} = #((powersetCard r ((A: Finset α) ∩ (B: Finset α))) ×ˢ
    (powersetCard (s-r) ((B: Finset α) \ (A: Finset α)))) :=by
  apply Finset.card_bij' (intersect_i s r A B) (intersect_j s r A B)
  · intro S hS
    unfold intersect_i; unfold intersect_j
    simp only [mem_filter, mem_powersetCard] at hS
    simp_rw [← union_inter_distrib_right, union_sdiff_self_eq_union, inter_eq_right]
    exact subset_trans hS.2.2 subset_union_right
  · intro S hS
    unfold intersect_i; unfold intersect_j
    simp only [mem_product, mem_powersetCard] at hS
    obtain ⟨⟨hS1, _⟩ , ⟨hS3, _⟩ ⟩:= hS
    simp_rw [inter_union_distrib_left,
      disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_right hS3 disjoint_sdiff),
      union_empty]
    rw[inter_comm, inter_eq_left.mpr (subset_inter_iff.mp hS1).left]
    have hBAS: ((B: Finset α) \ (A:Finset α)) ∩ S.1 ⊆
        ((B: Finset α) \ (A:Finset α)) ∩ (A: Finset α) := by
      exact inter_subset_inter_left (subset_inter_iff.mp hS1).left
    rw [disjoint_iff_inter_eq_empty.mp sdiff_disjoint] at hBAS
    rw [subset_empty.mp hBAS, empty_union, inter_eq_right.mpr hS3]
  · intro S hS
    unfold intersect_i
    simp only [mem_product, mem_powersetCard, inter_subset_left, true_and]
    simp only [mem_filter, mem_powersetCard] at hS
    refine' ⟨⟨inter_subset_inter_left hS.2.2, hS.2.1⟩, ?_⟩
    have hBAS: ((B: Finset α) \ (A: Finset α)) ∩ S = ((B: Finset α) ∩ S) \ ((A: Finset α) ∩ S) := by
      ext x
      simp only [mem_inter, mem_sdiff, not_and];
      exact ⟨fun hx =>⟨⟨hx.left.left, hx.right⟩,
          fun hxA =>by exfalso; exact hx.left.right hxA⟩,
          fun hx =>⟨⟨hx.left.left, by by_contra hA; exact hx.right hA hx.left.right⟩,
          hx.left.right⟩⟩
    rw [hBAS, inter_eq_right.mpr hS.2.2, card_sdiff, hS.1.2, hS.2.1]
    exact inter_subset_right
  · intro S hS
    unfold intersect_j
    simp only [mem_filter, mem_powersetCard]
    simp only [mem_product, mem_powersetCard] at hS
    obtain ⟨⟨h1, h2⟩ , ⟨h3, h4⟩ ⟩:= hS
    refine' ⟨⟨fun x hx => by_cases (fun (hxS: x ∈ S.1) => hA (mem_of_mem_filter x (h1 hxS)))
      (fun (hxS: ¬ x ∈ S.1) => hB (mem_sdiff.mp (h3
      ((propext (or_iff_right hxS)).mp (mem_union.mp hx)))).left),
      by rw [card_union_eq_card_add_card.mpr (disjoint_of_subset_left h1
      (disjoint_of_subset_right h3 (disjoint_of_subset_left (inter_subset_left) disjoint_sdiff))),
      h2, h4, Nat.add_sub_cancel' hrs]⟩ ,
      ⟨by rw [inter_union_distrib_left, inter_comm, inter_eq_left.mpr (subset_inter_iff.mp h1).left,
      disjoint_iff_inter_eq_empty.mp (disjoint_of_subset_right h3 disjoint_sdiff),
      union_empty]; exact h2, union_subset (subset_inter_iff.mp h1).right
      (Subset.trans h3 sdiff_subset)⟩⟩


lemma card_set_subset_set_nat_choose (hrs : r ≤ s) (hA: A ⊆ X) (hB: B ⊆ X)  :
    #{S ∈ powersetCard s X | #(A ∩ S) = r ∧ (S: Finset α) ⊆ (B: Finset α)}
    = (Nat.choose (#(A∩B)) r) * (Nat.choose (#(B\A) ) (s-r)) :=by
  simp_rw [card_powerset_card_product s r A B hrs hA hB, card_product, card_powersetCard]

lemma powersetCard_eq_filter_of_subset (X : Finset α) (hA : A ⊆ X):  powersetCard s A = {S ∈ powersetCard s X | S ⊆ A} := by
  rw [@Subset.antisymm_iff]
  constructor
  · intro S hS
    simp only [mem_powersetCard] at hS
    simp only [mem_filter, mem_powersetCard]
    refine' ⟨⟨fun ⦃a⦄ a_1 ↦ hA (hS.1 a_1), hS.2⟩, hS.1⟩
  · intro S hS
    simp only [mem_powersetCard]
    simp only [mem_filter, mem_powersetCard] at hS
    refine' ⟨hS.2, hS.1.2⟩

/--
Given a finite set `X` and a subset `A ⊆ X`, the number of elements of the
attached `s`‑element subsets of `X`which are contained in `A` is `(#A).choose s`.
-/
lemma card_attach_powersetCard_filter_of_subset
    (hA : A ⊆ X): #({S ∈ (powersetCard s X).attach | S.val ⊆ A}) = (#A).choose s :=by
  rw [← card_powersetCard s A]
  rw [powersetCard_eq_filter_of_subset s A X hA]
  let hequiv:{S ∈ (powersetCard s X).attach | S.val ⊆ A}
  ≃ {S ∈ powersetCard s X | S ⊆ A} := {
    toFun := fun S =>⟨S.1.1, mem_filter.mpr ⟨by simp only [coe_mem], (mem_filter.mp S.2).2⟩⟩
    invFun := fun S => ⟨⟨S.1, (mem_filter.mp S.2).1⟩,
        mem_filter.mpr ⟨by simp only [mem_attach], (mem_filter.mp S.2).2⟩⟩
    left_inv S:=by simp only [Subtype.coe_eta]
    right_inv S:=by simp only [Subtype.coe_eta]
  }
  rw [Finset.card_eq_of_equiv hequiv]
