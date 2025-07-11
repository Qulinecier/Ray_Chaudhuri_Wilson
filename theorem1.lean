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

-- The private sorted version of the finset F, which is a function from Fin #F to the powerset of X.
noncomputable def _F_sorted : Fin #F → { x // x ∈ X.powerset } :=
  fun i ↦ (F.toList.mergeSort card_le).get (Fin.cast (F_sorted_length F) i)

-- Show that the sorted version of F is a function from Fin #F to F.
omit [DecidableEq α] in
lemma F_sorted_mem (i : Fin #F) : _F_sorted F i ∈ F := by
  unfold _F_sorted
  simp only [List.get_eq_getElem, Fin.coe_cast]
  have h : (F.toList.mergeSort card_le)[i] ∈ (F.toList.mergeSort card_le) := List.mem_of_getElem rfl
  rw [List.mem_mergeSort] at h
  exact mem_toList.mp h

-- The sorted version of the finset F, which is a function from Fin #F to F.
noncomputable def F_sorted : Fin #F → F :=
  fun i ↦ ⟨_F_sorted F i, F_sorted_mem F i⟩

-- Show that the sorted version of F is a function from Fin #F to X.powerset.
omit [DecidableEq α] in
lemma sorted_F_sorted (i j : Fin #F) (h : i < j): card_le (F_sorted F i).val (F_sorted F j).val:= by
  unfold F_sorted
  have h2 := pairwise_F_sorted_list F
  rw [@List.pairwise_iff_get] at h2
  exact h2 (Fin.cast (F_sorted_length F) i) (Fin.cast (F_sorted_length F) j) h

-- Show that the sorted version of F is Nodup.
omit [DecidableEq α] in
lemma neq_F_sorted (i j : Fin #F) (h : i ≠ j) :
    (F_sorted F i) ≠ (F_sorted F j) := by
  suffices (F_sorted F i).val.val ≠ (F_sorted F j).val.val by
    simp [@Subtype.coe_ne_coe] at this
    exact this
  unfold F_sorted _F_sorted
  simp only [List.get_eq_getElem, Fin.coe_cast]
  rw [Subtype.coe_ne_coe]
  have hnodup : (F.toList.mergeSort card_le).Nodup := List.nodup_mergeSort.mpr (nodup_toList F)
  intro hcon
  apply (List.Nodup.get_inj_iff hnodup).mp at hcon
  rw [@Fin.mk_eq_mk, @Fin.val_eq_val] at hcon
  exact h hcon

--Ω is defined as X → {0, 1} in paper, and in this code it is defined as a subset of X → R.
def Ω : Set (X → ℝ) := { f : X → ℝ | ∀ a, f a = 0 ∨ f a = 1 }

instance: Module ℝ (@Ω α X → ℝ) := by infer_instance

/- The characteristic vector of a set A_i is a function from
  X to {0, 1} that indicates membership in A.-/
noncomputable def char_vec (i : Fin #F): X → ℝ :=
    fun a => if a.val ∈ (F_sorted F i).val.val then 1 else 0

-- Show that the char_vec can be restricted to {0, 1}.
lemma char_vec_mem_Ω (i : Fin #F) : char_vec F i ∈ Ω := by
  unfold char_vec Ω
  simp only [Subtype.forall, Set.mem_setOf_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    ite_eq_left_iff, zero_ne_one, Decidable.not_not]
  intro a b
  exact Decidable.not_or_of_imp fun a ↦ a

-- The char_vec with restricted codomain to {0, 1}.
noncomputable def Ω_char_vec (i : Fin #F): @Ω α X := ⟨char_vec F i, char_vec_mem_Ω F i⟩

-- Show that the inner product of characteristic vectors gives the card of the set intersection.
lemma char_vec_spec (i j : Fin #F) :
    (char_vec F i) ⬝ᵥ (char_vec F j) = #((F_sorted F i).val.val ∩ (F_sorted F j).val.val) := by
  have h : (char_vec F i) ⬝ᵥ (char_vec F j) =
      ∑ a : X, if a.val ∈ (F_sorted F i).val.val ∩ (F_sorted F j).val.val then 1 else 0 := by
    simp only [(· ⬝ᵥ ·)]
    refine congrArg univ.sum ?_
    unfold char_vec
    aesop
  rw [h]
  simp only [sum_boole, Nat.cast_inj]
  suffices {x | x ∈ (F_sorted F i).val.val ∩ (F_sorted F j).val.val} =
      (F_sorted F i).val.val ∩ (F_sorted F j).val.val by
    refine card_nbij (·.val) (fun a ↦ ?_) ?_ ?_
    · intro ha
      simp only [univ_eq_attach, mem_filter, mem_attach, true_and] at ha ⊢
      exact ha
    · intro x1 hx1 x2 hx2 hf
      aesop
    · intro y hy
      have hmem : y ∈ X := by
        simp only [coe_inter, Set.mem_inter_iff, mem_coe] at hy
        have hA := (F_sorted F i).val.property
        rw [@mem_powerset] at hA
        exact hA hy.left
      use ⟨y, hmem⟩
      simp only [univ_eq_attach, coe_filter, mem_attach, true_and, Set.mem_setOf_eq, and_true]
      exact hy
  ext a
  simp

-- The characteristic polynomial of a set A
noncomputable def char_pol (i : Fin #F) (x : X → ℝ): ℝ :=
  ∏ l ∈ L with l < #(F_sorted F i).val.val, ((char_vec F i) ⬝ᵥ x - l)

noncomputable def Ω_char_pol (i : Fin #F) (x : @Ω α X): ℝ := char_pol F L i (x : X → ℝ)

def Ω_char_pol_span : Submodule ℝ (@Ω α X → ℝ) :=
  Submodule.span ℝ (Set.range (Ω_char_pol F L))

lemma Ω_char_pol_mem_span : (Set.range (Ω_char_pol F L)) ⊆ (Ω_char_pol_span F L) := by
  exact Submodule.span_le.mp fun ⦃x⦄ a ↦ a

/-def Ω_unit_vec (i : X): @Ω α X := ⟨fun x => if i = x then 1 else 0, by
  unfold Ω
  simp only [Subtype.forall, Set.mem_setOf_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    ite_eq_left_iff, zero_ne_one, Decidable.not_not]
  intro a b
  exact ne_or_eq i ⟨a, b⟩ ⟩

def Ω_multilinear_set_deg_s : Set (@Ω α X → ℝ) := {f | ∃ S : Finset X, #S = s ∧
  f = fun (x : @Ω α X) => ∏ l ∈ S, (x : X → ℝ) ⬝ᵥ (Ω_unit_vec l)}-/


-- The set of all monic multilinear polynomials with degree less than L
def Ω_multilinear_set : Set (@Ω α X → ℝ) := {f | ∃ S : Finset X, #S ≤ #L ∧
  f = fun (x : @Ω α X) => ∏ l ∈ S, x.1 l}

-- The span of Ω_multilinear_set
def Ω_multilinear_span : Submodule ℝ (@Ω α X → ℝ) := Submodule.span ℝ (Ω_multilinear_set L)

-- This lemma shows that x_i ^ p = x_i for any x ∈ Ω.
omit [DecidableEq α] in
lemma Ω_spec (l : X) (p : ℕ) (hp : p ≠ 0):
    (fun (x : @Ω α X ) => (x.1 l) ^ p ) = (fun (x : @Ω α X ) => x.1 l) := by
  ext x
  have h := x.2
  simp only [Ω, Subtype.forall, Set.mem_setOf_eq] at h
  have h : x.1 l = 0 ∨ x.1 l = 1 := by exact h l l.2
  cases h
  next h =>
    rw [h]
    exact zero_pow hp
  next h =>
    rw [h]
    exact one_pow p

lemma Ω_char_pol_spec (i : Fin #F):
    Ω_char_pol F L i ∈ Ω_multilinear_span L := by
  refine Submodule.mem_span.mpr ?_
  sorry

lemma span_to_R_le_span_ml : (Ω_char_pol_span F L) ≤
    Ω_multilinear_span L := by
  unfold Ω_char_pol_span
  suffices Set.range (Ω_char_pol F L) ⊆ (Ω_multilinear_span (X := X) L) by
    exact Submodule.span_le.mpr this
  intro x hx
  rw [@Set.mem_range] at hx
  obtain ⟨y, hy⟩ := hx
  subst hy
  exact Ω_char_pol_spec F L y

instance : Fintype (Ω_multilinear_set (X := X) L) := by sorry

lemma card_Ω_multilinear_set :
    #(Ω_multilinear_set (X := X) L).toFinset = ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  sorry

lemma dim_Ω_multilinear_span : Module.rank ℝ (Ω_multilinear_span (X := X) L) ≤
    ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  rw [(card_Ω_multilinear_set L).symm]
  have h := rank_span_finset_le (R := ℝ) (Ω_multilinear_set (X := X) L).toFinset
  rw [Set.coe_toFinset] at h
  exact h

lemma dim_span_to_R_le : Module.rank ℝ (Ω_char_pol_span F L) ≤
    ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m:= by
  exact Preorder.le_trans (Module.rank ℝ (Ω_char_pol_span F L))
    (Module.rank ℝ (Ω_multilinear_span (X := X) L))
    (↑(∑ m ∈ range (#L + 1), (#X).choose m))
    (Submodule.rank_mono (span_to_R_le_span_ml F L)) (dim_Ω_multilinear_span L)

-- Show that the characteristic polynomial is non-zero for the characteristic vector of A.
lemma char_pol_spec_1 (i : Fin #F) : char_pol F L i (char_vec F i) ≠ 0 := by
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
lemma char_pol_spec_2 (i j: Fin #F) (hneq : i ≠ j) (hji : j < i)
    (hintersect : intersecting F L): char_pol F L i (char_vec F j) = 0 := by
  unfold char_pol
  unfold intersecting at hintersect
  refine prod_eq_zero_iff.mpr ?_
  use #((F_sorted F i).val.val ∩ (F_sorted F j).val.val)
  rw [char_vec_spec, sub_self, propext (and_iff_left rfl), mem_filter]
  constructor
  · refine hintersect (F_sorted F i) (F_sorted F j) ?_
    exact neq_F_sorted F i j hneq
  · refine card_lt_card ?_
    rw [@Finset.ssubset_iff_subset_ne]
    constructor
    · exact inter_subset_left
    · rw [ne_eq, inter_eq_left]
      by_contra hcon
      have hle := sorted_F_sorted F j i hji
      unfold card_le at hle
      rw [Bool.decide_iff] at hle
      have h := eq_of_subset_of_card_le hcon hle
      simp only [@SetCoe.ext_iff] at h
      exact (neq_F_sorted F i j hneq) h

lemma Fin_sum_seperated (n : ℕ) (f : Fin n → ℝ) (i : Fin n) :
    ∑ x, f x = f i + ∑ x with x < i, f x + ∑ x with i < x, f x := by
  rw [Fintype.sum_eq_add_sum_compl i (fun x ↦ f x)]
  have h : ({i}ᶜ : Finset (Fin n)) =
      ({x | x < i}: Finset (Fin n)) ∪ ({x | i < x} : Finset (Fin n)) := by
    ext x
    simp
  rw [Mathlib.Tactic.Ring.add_pf_add_lt, h]
  rw [eq_comm]
  refine sum_union (f := f) ?_
  rw [@disjoint_iff_inter_eq_empty, @eq_empty_iff_forall_not_mem]
  intro x hx
  simp only [gt_iff_lt, mem_inter, mem_filter, mem_univ, true_and] at hx
  obtain ⟨hx1, hx2⟩ := hx
  exact lt_asymm hx1 hx2

lemma Ω_char_pol_lin_indep (hintersect : intersecting F L) :
    LinearIndependent ℝ (Ω_char_pol F L) := by
  by_contra hcon
  rw [@Fintype.not_linearIndependent_iff] at hcon
  obtain ⟨g, hg, hi⟩ := hcon
  have h := Fin.find (fun i ↦ g i ≠ 0)
  have hexist := Fin.isSome_find_iff.mpr hi
  rw [@Option.isSome_iff_exists] at hexist
  obtain ⟨i, hi⟩ := hexist
  rw [@Fin.find_eq_some_iff] at hi
  obtain ⟨hi, hmin⟩ := hi
  have hsubst := congrFun hg (Ω_char_vec F i)
  simp only [Ω_char_vec, sum_apply, Pi.smul_apply, Ω_char_pol, smul_eq_mul,
    Pi.zero_apply] at hsubst
  rw [Fin_sum_seperated #F _ i] at hsubst
  --Show that all the x before i gives zero since g x = 0 by hmin.
  have hless : ∑ x ∈ {x | x < i}, g x * char_pol F L x (char_vec F i) = 0 := by
    rw [Finset.sum_eq_zero]
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    suffices g x = 0 by exact mul_eq_zero_of_left this (char_pol F L x (char_vec F i))
    by_contra hcon2
    exact (not_le.mpr hx) (hmin x hcon2)
  --Show that all the x after i gives zero since char_pol = 0 by char_pol_spec_2.
  have hmore : ∑ x ∈ {x | i < x}, g x * char_pol F L x (char_vec F i) = 0 := by
    rw [Finset.sum_eq_zero]
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [char_pol_spec_2 F L x i (ne_of_lt hx).symm hx hintersect]
    exact mul_zero (g x)
  --Thus Show that g i * char_pol F L i (char_vec F i) = 0, which contradicts char_pol_spec_1.
  simp only [hless, hmore, add_zero, mul_eq_zero] at hsubst
  cases hsubst with
  | inl h1 => exact hi h1
  | inr hi => exact char_pol_spec_1 F L i hi

theorem Frankl_Wilson (hintersect : intersecting F L):
    #F ≤ ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  have h := linearIndependent_span (Ω_char_pol_lin_indep F L hintersect)
  apply LinearIndependent.cardinal_le_rank at h
  rw [Cardinal.mk_fintype, Fintype.card_fin] at h
  exact Nat.cast_le.mp (le_trans h (dim_span_to_R_le F L))

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
