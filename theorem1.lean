import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse



open Finset
variable {α : Type} (n : ℕ) [DecidableEq α]
variable {X: Finset α} (F: Finset X.powerset)

def uniform {X: Finset α} (F: Finset X.powerset) (k : ℕ) : Prop := ∀ (A : F), #A.val.val = k

--PETER : Intersecting does not contain A ∩ A, so we should state that
def intersecting {X: Finset α} (F: Finset X.powerset) (L : Set ℕ) :=
  ∀ (A B: F), A ≠ B → #(A.val.val ∩ B.val.val) ∈ L



variable (k s: ℕ) (L : Finset ℕ)


instance: Module ℝ (F → ℝ) := by infer_instance

/--The indicator vector of subset S: S = ∑(A: A ∈ F, S ⊆ A).-/
def subset_indicator (S : Finset α): F → ℝ  :=
    fun A => if S ⊆ A then 1 else 0

/--The intersection indicator vector of subset S: H = ∑(B:B ∈ F,|B∩S|=μ)-/
def intersection_indicator (S: Finset α) (μ : ℕ): F → ℝ :=
    fun B => if #(B ∩ S) = μ then 1 else 0

/--The indicator combine both subset and intersection, i.e. G = ∑(S_bar: S∈ 𝓟ₛ(X), |S∩A| = μ)-/
def subset_intersection_indicator (A: Finset α) (μ : ℕ): F → ℝ :=
    fun B => ∑ (S: powersetCard s X), if #(A ∩ S)  = μ then (subset_indicator F S B) else 0

variable (r: ℕ) (A: Finset α)

--TODO
lemma indicator_eq: subset_intersection_indicator F s A r =
    ∑ (l: L), (Nat.choose l r) * (Nat.choose (#A - l) (s - r))
    * (intersection_indicator F A l) := by
  unfold subset_intersection_indicator
  funext B
  simp only [Finset.sum_apply]
  unfold subset_indicator
  simp only [Pi.natCast_def, Pi.mul_apply, mul_ite, mul_one, mul_zero]

  have h1: (∑ (S: powersetCard s X), if #(A ∩ S) = r then (if (S: Finset α) ⊆ (B: Finset α) then (1: ℝ) else 0) else 0)
    = ∑ (x : L), ∑ (S: powersetCard s X),
    if ((#(A ∩ S) = r) ∧ ((S: Finset α) ⊆ (B: Finset α)))
    then (intersection_indicator F A x B) else 0 := by sorry

  rw [h1]

  have h2: ∀ (x : L), (∑ (S: powersetCard s X),
    if ((#(A ∩ S) = r) ∧ ((S: Finset α) ⊆ (B: Finset α))) then (intersection_indicator F A x B) else 0) =
    (Nat.choose x r) * (Nat.choose (#A - x) (s - r))
    * (intersection_indicator F A x) B := by

    intro x
    sorry

  congr! with x hx

  rw [h2 x]

variable (S: X.powerset)


/--The set of indicator vectors {S_bar : S ∈ 𝓟ₛ(X)}-/
noncomputable def subset_indicator_set :=
  Finset.image (fun (S : Finset α) => (subset_indicator F S: F → ℝ)) (powersetCard s X)


theorem my_finrank_pi (ι : Type) [Fintype ι]:
    Module.finrank ℝ (ι → ℝ) = Fintype.card ι := by
  simp [Module.finrank]


lemma F_rank {α : Type} {X : Finset α} (F : Finset { x // x ∈ X.powerset }):
    Module.finrank ℝ (⊤: Submodule ℝ (F → ℝ)) = #F := by
  simp only [finrank_top]
  rw [← Fintype.card_coe F]
  exact my_finrank_pi F


lemma subset_indicator_rank (hX : #X = n): #(subset_indicator_set F s)
    ≤ Nat.choose n s := by
  have h1 : #(subset_indicator_set F s) ≤ #(powersetCard s X) := by
    exact Finset.card_image_le
  have h2 : #(powersetCard s X) = n.choose s := by
    have h := (Finset.card_powersetCard s X).symm
    rw [hX] at h
    exact h.symm
  rw [h2.symm]
  exact h1

#check rank_span_finset_le


lemma subset_vector_span_dim_le (h: Submodule.span ℝ (toSet (subset_indicator_set F s)) = (⊤: Submodule ℝ (F → ℝ)))
  (hX : #X = n) : #F ≤ Nat.choose n s := by
  have h1 : Module.finrank ℝ (Submodule.span ℝ (toSet (subset_indicator_set F s)))
      = Module.finrank ℝ (⊤: Submodule ℝ (F → ℝ)) := by
    rw [h]
  rw [F_rank] at h1
  have h2 := subset_indicator_rank n F s hX
  have h3 : Module.finrank ℝ (Submodule.span ℝ (toSet (subset_indicator_set F s)))
      ≤ #(subset_indicator_set F s) := by
    have h : Module.rank ℝ (Submodule.span ℝ (toSet (subset_indicator_set F s)))
      ≤ #(subset_indicator_set F s) := by
        exact rank_span_finset_le (subset_indicator_set F s)
    exact Module.finrank_le_of_rank_le h
  rw [h1] at h3
  exact Nat.le_trans h3 h2

--PETER: a < b is not antisymm but a ≤ b is
def sort_fun: ℕ → ℕ → Prop := fun a => fun b => a ≤ b
instance: DecidableRel sort_fun := by exact Aesop.Iteration.instDecidableRelLe
instance: IsTrans ℕ sort_fun where
  trans := by
    intro x b c hxb hbc
    exact Nat.le_trans hxb hbc

instance: IsAntisymm ℕ sort_fun where
  antisymm := by
    intro a b hab hba
    exact Nat.le_antisymm hab hba

instance: IsTotal ℕ sort_fun where
  total := by
    intro a b
    exact Nat.le_total a b

variable (hL: (Finset.sort sort_fun L).length = s)


namespace Frankl_Wilson

-- card_le F A B means that the cardinality of A is no greater than that of B.
def card_le (A B : { x // x ∈ X.powerset }) : Bool := #A.val ≤ #B.val

-- Show that the length of the sorted list is the same as the original finset.
omit [DecidableEq α] in
lemma F_sorted_length : #F = (F.toList.mergeSort card_le).length := by
  simp only [List.length_mergeSort, length_toList]

-- Show that the sorted list is a pairwise relation with respect to card_le.
omit [DecidableEq α] in
lemma pairwise_F_sorted_list :
    List.Pairwise (fun a b ↦ card_le a b) (F.toList.mergeSort card_le) := by
  refine @List.sorted_mergeSort _ card_le ?_ ?_ F.toList
  · unfold card_le
    simp only [decide_eq_true_eq, Subtype.forall, mem_powerset]
    intro _ _ _ _ _ _ hab hbc
    exact Nat.le_trans hab hbc
  · unfold card_le
    simp only [Bool.or_eq_true, decide_eq_true_eq, Subtype.forall, mem_powerset]
    intro a ha b hb
    exact Nat.le_total (#a) #b

-- The sorted version of the finset F, which is a function from Fin #F to the powerset of X.
noncomputable def F_sorted : Fin #F → { x // x ∈ X.powerset } :=
  fun i ↦ (F.toList.mergeSort card_le).get (Fin.cast (F_sorted_length F) i)

-- Show that the sorted version of F is a function from Fin #F to F.
omit [DecidableEq α] in
lemma F_sorted_mem (i : Fin #F) : F_sorted F i ∈ F := by
  unfold F_sorted
  simp only [List.get_eq_getElem, Fin.coe_cast]
  have h : (F.toList.mergeSort card_le)[i] ∈ (F.toList.mergeSort card_le) := List.mem_of_getElem rfl
  rw [List.mem_mergeSort] at h
  exact mem_toList.mp h

-- Show that the sorted version of F is a function from Fin #F to X.powerset.
omit [DecidableEq α] in
lemma sorted_F_sorted (i j : Fin #F) (h : i < j): card_le (F_sorted F i) (F_sorted F j):= by
  unfold F_sorted
  have h2 := pairwise_F_sorted_list F
  rw [@List.pairwise_iff_get] at h2
  exact h2 (Fin.cast (F_sorted_length F) i) (Fin.cast (F_sorted_length F) j) h

/- The characteristic vector of a set A is a function from
  X to {0, 1} that indicates membership in A.-/
def char_vec (A : F) : X → ℝ :=
    fun a => if a.val ∈ A.val.val then 1 else 0

-- Show that the inner product of characteristic vectors gives the card of the set intersection.
lemma char_vec_spec (A B : F) : (char_vec F A) ⬝ᵥ (char_vec F B) = #(A.val.val ∩ B.val.val) := by
  have h : char_vec F A ⬝ᵥ char_vec F B =
      ∑ a : X, if a.val ∈ A.val.val ∩ B.val.val then 1 else 0 := by
    simp only [(· ⬝ᵥ ·)]
    refine congrArg univ.sum ?_
    unfold char_vec
    aesop
  rw [h]
  simp only [sum_boole, Nat.cast_inj]
  suffices {x | x ∈ A.val.val ∩ B.val.val} = A.val.val ∩ B.val.val by
    refine card_nbij (·.val) (fun a ↦ ?_) ?_ ?_
    · intro ha
      simp only [univ_eq_attach, mem_filter, mem_attach, true_and] at ha ⊢
      exact ha
    · intro x1 hx1 x2 hx2 hf
      aesop
    · intro y hy
      have hmem : y ∈ X := by
        simp only [coe_inter, Set.mem_inter_iff, mem_coe] at hy
        have hA := A.val.property
        rw [@mem_powerset] at hA
        exact hA hy.left
      use ⟨y, hmem⟩
      simp only [univ_eq_attach, coe_filter, mem_attach, true_and, Set.mem_setOf_eq, and_true]
      exact hy
  ext a
  simp

-- The characteristic polynomial of a set A
noncomputable def char_pol (A : F) (x : X → ℝ): ℝ :=
  ∏ l ∈ L with l < #A.val.val, ((char_vec F A) ⬝ᵥ x - l)

-- Show that the characteristic polynomial is non-zero for the characteristic vector of A.
lemma char_pol_spec_1 (A : F) : char_pol F L A (char_vec F A) ≠ 0 := by
  unfold char_pol
  refine prod_ne_zero_iff.mpr ?_
  intro a ha
  rw [char_vec_spec]
  norm_cast
  rw [inter_self, Int.subNat_eq_zero_iff]
  rw [@mem_filter] at ha
  exact Nat.ne_of_lt' ha.2

/- Show that the characteristic polynomial is zero for
the characteristic vector of B with lower cardinality.-/
lemma char_pol_spec_2 (A B: F) (hneq : A ≠ B) (hAB : #B.val.val ≤ #A.val.val)
    (hintersect : intersecting F L): char_pol F L A (char_vec F B) = 0 := by
  unfold char_pol
  unfold intersecting at hintersect
  refine prod_eq_zero_iff.mpr ?_
  use #(A.val.val ∩ B.val.val)
  rw [char_vec_spec, sub_self, propext (and_iff_left rfl), mem_filter]
  constructor
  · exact hintersect A B hneq
  · refine card_lt_card ?_
    rw [@Finset.ssubset_iff_subset_ne]
    constructor
    · exact inter_subset_left
    · rw [ne_eq, inter_eq_left]
      by_contra hcon
      have h := eq_of_subset_of_card_le hcon hAB
      simp only [@SetCoe.ext_iff] at h
      exact hneq h

instance: Module ℝ ( (X → ({0, 1} : Set ℝ)) → ℝ) := by infer_instance

theorem Frankl_Wilson (hintersect : intersecting F L):
    #F ≤ ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by sorry

end Frankl_Wilson


def v_r (t: ℕ) (ht : t < s) := (Nat.choose (Finset.sort sort_fun L)[t] r)
    * (Nat.choose (k - (Finset.sort sort_fun L)[t])) (s - r)


def composed_mat : Matrix (Fin (s)) (Fin (s)) ℝ := fun i j => v_r k s L j hL i i.isLt

lemma invertible_composed_mat: IsUnit (composed_mat k s L hL) := by
  rw [isUnit_iff_exists]
  sorry


theorem span_bar: Submodule.span ℝ (subset_indicator_set F s)
    = (⊤: Submodule ℝ (F → ℝ)) := sorry


theorem Ray_Chaudhuri_Wilson (huniform: uniform F k) (hintersect : intersecting F L)
    (hL : #L = s): #F ≤ Nat.choose n s := by
  apply subset_vector_span_dim_le
  sorry
