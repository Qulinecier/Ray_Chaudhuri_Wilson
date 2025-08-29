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
import Mathlib.RingTheory.MvPolynomial.Homogeneous


open Finset
variable {α : Type} (n : ℕ) [DecidableEq α] {X: Finset α} {F: Finset (Finset α)} (L : Finset ℕ)
variable (hF : ∀ A ∈ F, A ⊆ X)

def uniform (k : ℕ): Prop := ∀ A ∈ F, #A = k

def intersecting (F: Finset (Finset α)) (L : Set ℕ) := ∀ A ∈ F, ∀ B ∈ F, A ≠ B → #(A ∩ B) ∈ L

-- card_le F A B means that the cardinality of A is no greater than that of B.
def card_le (A B : Finset α) : Bool := #A ≤ #B

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
    intro _ _ _ hab hbc
    exact Nat.le_trans hab hbc
  · unfold card_le
    simp only [Bool.or_eq_true, decide_eq_true_eq, Subtype.forall, mem_powerset]
    intro a b
    exact Nat.le_total (#a) #b

-- The private sorted version of the finset F, which is a function from Fin #F to the powerset of X.
noncomputable def _F_sorted : Fin #F → Finset α :=
  fun i ↦ (F.toList.mergeSort card_le).get (Fin.cast (F_sorted_length) i)

-- Show that the sorted version of F is a function from Fin #F to F.
omit [DecidableEq α] in
lemma F_sorted_mem (i : Fin #F) : _F_sorted i ∈ F := by
  unfold _F_sorted
  simp only [List.get_eq_getElem, Fin.coe_cast]
  have h : (F.toList.mergeSort card_le)[i] ∈ (F.toList.mergeSort card_le) := List.mem_of_getElem rfl
  rw [List.mem_mergeSort] at h
  exact mem_toList.mp h

-- The sorted version of the finset F, which is a function from Fin #F to F.
noncomputable def F_sorted : Fin #F → F :=
  fun i ↦ ⟨_F_sorted i, F_sorted_mem i⟩

-- Show that the sorted version of F is a function from Fin #F to X.powerset.
omit [DecidableEq α] in
lemma sorted_F_sorted (i j : Fin #F) (h : i < j): card_le (F_sorted i).val (F_sorted j).val:= by
  unfold F_sorted
  have h2 := pairwise_F_sorted_list (F := F)
  rw [@List.pairwise_iff_get] at h2
  exact h2 (Fin.cast (F_sorted_length) i) (Fin.cast (F_sorted_length) j) h

-- Show that the sorted version of F is Nodup.
omit [DecidableEq α] in
lemma neq_F_sorted (i j : Fin #F) (h : i ≠ j) :
    (F_sorted i) ≠ (F_sorted j) := by
  suffices (F_sorted i).val.val ≠ (F_sorted j).val.val by
    simp [@Subtype.coe_ne_coe] at this
    exact this
  unfold F_sorted _F_sorted
  simp only [List.get_eq_getElem, Fin.coe_cast]
  --rw [Subtype.coe_ne_coe]
  have hnodup : (F.toList.mergeSort card_le).Nodup := List.nodup_mergeSort.mpr (nodup_toList F)
  intro hcon
  rw [val_inj] at hcon
  apply (List.Nodup.get_inj_iff hnodup).mp at hcon
  rw [@Fin.mk_eq_mk, @Fin.val_eq_val] at hcon
  exact h hcon

--Ω is defined as X → {0, 1} in paper, and in this code it is defined as a subset of X → R.
def Ω : Set (X → ℝ) := { f : X → ℝ | ∀ a, f a = 0 ∨ f a = 1 }

instance: Module ℝ (@Ω α X → ℝ) := by infer_instance

noncomputable instance : DecidableEq (@Ω α X → ℝ) := by apply Classical.typeDecidableEq


/- The characteristic vector of a set A_i is a function from
  X to {0, 1} that indicates membership in A.-/
noncomputable def char_vec (hF : ∀ A ∈ F, A ⊆ X) (i : Fin #F): X → ℝ :=
    fun a => if a.val ∈ (F_sorted i).val then 1 else 0

-- Show that the char_vec can be restricted to {0, 1}.
lemma char_vec_mem_Ω (i : Fin #F) : (char_vec hF i) ∈ Ω := by
  unfold char_vec Ω
  simp only [Subtype.forall, Set.mem_setOf_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    ite_eq_left_iff, zero_ne_one, Decidable.not_not]
  intro a b
  exact Decidable.not_or_of_imp fun a ↦ a

-- The char_vec with restricted codomain to {0, 1}.
noncomputable def Ω_char_vec (i : Fin #F): @Ω α X := ⟨char_vec hF i, char_vec_mem_Ω hF i⟩

-- Show that the inner product of characteristic vectors gives the card of the set intersection.
theorem char_vec_spec (i j : Fin #F) :
    (char_vec hF i) ⬝ᵥ (char_vec hF j) = #((F_sorted i).val ∩ (F_sorted j).val) := by
  have h : (char_vec hF i) ⬝ᵥ (char_vec hF j) =
      ∑ a : X, if a.val ∈ (F_sorted i).val ∩ (F_sorted j).val then 1 else 0 := by
    simp only [(· ⬝ᵥ ·)]
    refine congrArg univ.sum ?_
    unfold char_vec
    aesop
  rw [h]
  simp only [sum_boole, Nat.cast_inj]
  suffices {x | x ∈ (F_sorted i).val ∩ (F_sorted j).val} =
      (F_sorted i).val ∩ (F_sorted j).val by
    refine card_nbij (·.val) (fun a ↦ ?_) (fun x1 hx1 x2 hx2 hf =>by aesop) ?_
    · intro ha
      simp only [univ_eq_attach, mem_filter, mem_attach, true_and] at ha ⊢
      exact ha
    · intro y hy
      have hmem : y ∈ X := by
        simp only [coe_inter, Set.mem_inter_iff, mem_coe] at hy
        exact (hF (F_sorted i) (F_sorted i).property) hy.left
      use ⟨y, hmem⟩
      simp only [univ_eq_attach, coe_filter, mem_attach, true_and, Set.mem_setOf_eq, and_true]
      exact hy
  ext a
  simp

-- pol_to_eval sends a MvPolynomial to its evaluation as a function from Ω to ℝ
def pol_to_eval : (MvPolynomial X ℝ) →ₗ[ℝ] (@Ω α X → ℝ) where
  toFun fp := fun x => fp.eval (σ := X) x
  map_add' := by aesop
  map_smul' := by aesop

noncomputable instance (x : @Ω α X) (S : X →₀ ℕ): Decidable (S.support.toSet ⊆ x.1.support) :=
  Classical.propDecidable (S.support.toSet ⊆ x.1.support)

omit [DecidableEq α] in
lemma pol_to_eval_monomial_eq : ∀ S, pol_to_eval (MvPolynomial.monomial S 1) =
    (fun (x : @Ω α X) => if S.support.toSet ⊆ x.1.support then 1 else 0) := by
  intro S
  ext x
  unfold pol_to_eval
  simp only [LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.eval_monomial, Finsupp.prod_pow, one_mul]
  have hx : ∀ a : X, x.1 a = 0 ∨ x.1 a = 1 := x.2
  by_cases h : S.support.toSet ⊆ x.1.support
  · simp only [h, ↓reduceIte]
    suffices ∀ a : X, x.1 a ^ S a = 1 by simp [this]
    intro a
    by_cases hSa : S a = 0
    · simp [hSa]
    · have ha : a ∈ x.1.support := h (Finsupp.mem_support_iff.mpr hSa)
      rw [Function.mem_support] at ha
      have hx : x.1 a = 0 ∨ x.1 a = 1 := x.2 a
      simp only [ha, false_or] at hx
      simp [hx]
  · simp only [h, ↓reduceIte]
    rw [Finset.prod_eq_zero_iff]
    rw [@Set.not_subset_iff_exists_mem_not_mem] at h
    obtain ⟨a, ha, hax⟩ := h
    use a
    simp only [Function.mem_support, ne_eq, Decidable.not_not, mem_coe, Finsupp.mem_support_iff,
      univ_eq_attach, mem_attach, pow_eq_zero_iff', true_and] at hax ha ⊢
    exact ⟨hax, ha⟩

/- Ω_multilinear_set is the set of all monic multilinear polynomials with totaldegree less than L,
  in the context of function from Ω to ℝ.-/
def Ω_multilinear_set : Set (@Ω α X → ℝ) := pol_to_eval ''
  {f | f.totalDegree ≤ n ∧ ∃ S : X →₀ ℕ, f = MvPolynomial.monomial S 1}

/- pol_power_shrink send a Finsupp S to a "shrinked" Finsupp, keeping S.support the same while
decreasing any non-zero terms to 1. It is used to decrease the degree of MvPolynomials to 1,
since they are equivalent in the perspective of functions from Ω to ℝ.
S is usually the degree of a MvPolynomial. -/
noncomputable def pol_power_shrink (S : X →₀ ℕ) : X →₀ ℕ :=
  Finsupp.ofSupportFinite (fun x => if S x = 0 then 0 else 1) (by
    exact Set.toFinite (Function.support fun x ↦ if S x = 0 then 0 else 1))

-- A more handy definition of pol_power_shrink as a function
omit [DecidableEq α] in
lemma pol_power_shrink_spec (S : X →₀ ℕ) (x : X):
  (pol_power_shrink S) x = (fun x ↦ if S x = 0 then 0 else 1) x := rfl

-- pol_power_shrink keeps the support unchanged
omit [DecidableEq α] in
lemma pol_power_shrink_support_linear (S : X →₀ ℕ) : (pol_power_shrink S).support = S.support := by
  ext x
  simp [pol_power_shrink_spec]

-- pol_power_shrink are equal iff the support of the original Finsupp is the same
omit [DecidableEq α] in
lemma pol_power_shrink_support_eq_iff (S1 S2: X →₀ ℕ):
    S1.support = S2.support ↔ pol_power_shrink S1 = pol_power_shrink S2:= by
  apply Iff.intro
  · intro hs
    ext x
    simp only [pol_power_shrink_spec]
    rw [@Finset.ext_iff] at hs
    simp only [Finsupp.mem_support_iff, ne_eq, Subtype.forall, not_iff_not] at hs
    simp [hs x]
  · intro hp
    rw [← pol_power_shrink_support_linear, hp, pol_power_shrink_support_linear]

-- the card of the support of pol_power_shrink is equal to the sum of all its terms
omit [DecidableEq α] in
lemma card_pol_power_shrink_support (S : X →₀ ℕ) :
    #(pol_power_shrink S).support = (pol_power_shrink S).sum fun x e ↦ e := by
  unfold Finsupp.sum
  simp only [pol_power_shrink_support_linear, pol_power_shrink_spec]
  calc
  _ = ∑ x ∈ S.support, 1 := card_eq_sum_ones S.support
  _ = _ := by
    apply sum_congr rfl
    intro x hx
    rw [@Finsupp.mem_support_iff] at hx
    simp [hx]

-- MvPolynomials is unchanged under pol_power_shrink in the perspective of functions from Ω to ℝ.
omit [DecidableEq α] in
lemma Ω_pol_spec_1 (S : X →₀ ℕ) : pol_to_eval (MvPolynomial.monomial S 1) =
    pol_to_eval (MvPolynomial.monomial (pol_power_shrink S) 1) := by
  ext x
  unfold pol_to_eval
  simp only [LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.eval_monomial, Finsupp.prod_pow, one_mul]
  congr
  ext y
  rw [pol_power_shrink_spec S y]
  by_cases hSy : S y = 0
  · simp [hSy]
  have h := x.2
  simp only [Ω, Subtype.forall, Set.mem_setOf_eq] at h
  have h : x.1 y = 0 ∨ x.1 y = 1 := by exact h y y.2
  cases h
  next h =>
    simp [hSy, h]
  next h =>
    simp [hSy, h]

-- MvPolynomials's degree after pol_power_shrink is no greater than before
omit [DecidableEq α] in
lemma Ω_pol_spec_2 (S : X →₀ ℕ) :
    (MvPolynomial.monomial (pol_power_shrink S) (R := ℝ) 1).totalDegree ≤
    (MvPolynomial.monomial (R := ℝ) S 1).totalDegree := by
  simp [MvPolynomial.totalDegree_monomial]
  unfold Finsupp.sum
  have h : (pol_power_shrink S).support = S.support := by
    ext x
    simp [pol_power_shrink_spec]
  rw [h]
  apply sum_le_sum
  intro i hi
  simp [pol_power_shrink_spec]
  by_cases hSi : S i = 0
  · simp [hSi]
  · simp [hSi]
    exact Nat.one_le_iff_ne_zero.mpr hSi

-- ml_pol_deg_n_set is the set of all multilinear polynomials of degree equal to n
def ml_pol_deg_n_set : Set (MvPolynomial X ℝ) :=
  {f | f.totalDegree = n ∧ ∃ S : X →₀ ℕ, f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1}

-- state the definition of a MvPolynomial being in ml_pol_deg_n_set
omit [DecidableEq α] in
lemma ml_pol_deg_n_set_mem_def (f : MvPolynomial X ℝ) (hd : f.totalDegree = n)
    (hf : ∃ S : X →₀ ℕ, f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1) :
    f ∈ ml_pol_deg_n_set (X := X) n := by
  simp [ml_pol_deg_n_set, hf, hd]

-- Any MvPolynomial in (ml_pol_deg_n_set n) has degree equal to n.
def deg_n_to_deg_eq_n (f : ml_pol_deg_n_set (X := X) n) : f.1.totalDegree = n := f.2.1

-- Choose a Finsupp as the degree (after shrink) of the MvPolynomial in (ml_pol_deg_n_set n).
noncomputable def deg_n_to_finsupp (f : ml_pol_deg_n_set (X := X) n) : X →₀ ℕ := f.2.2.choose

-- Show that the pol_power_shrink of the chosen Finsupp is indeed the degree of that MvPolynomial
noncomputable def deg_n_to_finsupp_spec (f : ml_pol_deg_n_set (X := X) n) :
    f.1 = MvPolynomial.monomial (R := ℝ) (pol_power_shrink (deg_n_to_finsupp n f)) 1 :=
  f.2.2.choose_spec

-- Show that support of deg_n_to_finsupp is a subset of X
lemma deg_n_to_choose_n_sub_X (f : ml_pol_deg_n_set (X := X) n) :
    (deg_n_to_finsupp n f).support.image (Subtype.val) ⊆ X := by
  intro x hx
  simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hx
  obtain ⟨hx, _⟩ := hx
  exact hx

-- Show that support of deg_n_to_finsupp has the size of n
lemma deg_n_to_choose_n_card_n (f : ml_pol_deg_n_set (X := X) n) :
    #((deg_n_to_finsupp n f).support.image (Subtype.val)) = n := by
  rw [card_image_iff.mpr Set.injOn_subtype_val,
    ← pol_power_shrink_support_linear (deg_n_to_finsupp n f)]
  simp only [← deg_n_to_deg_eq_n n f, deg_n_to_finsupp_spec n f, ne_eq,
    one_ne_zero, not_false_eq_true, MvPolynomial.totalDegree_monomial]
  exact card_pol_power_shrink_support (deg_n_to_finsupp n f)

/-deg_n_to_choose_n send a polynomial to its degree finsupp, which is in powersetCard n X.-/
noncomputable def deg_n_to_choose_n (f : ml_pol_deg_n_set (X := X) n) :
    powersetCard n X := ⟨(deg_n_to_finsupp n f).support.image (Subtype.val), by
  simp [Finset.mem_powersetCard, deg_n_to_choose_n_sub_X, deg_n_to_choose_n_card_n]⟩

-- Show that deg_n_to_choose_n is injective
lemma deg_n_to_choose_n_inj : Function.Injective (deg_n_to_choose_n (X := X) n) := by
  intro a b hab
  simp only [deg_n_to_choose_n, Subtype.mk.injEq] at hab
  suffices a.1 = b.1 by exact SetCoe.ext this
  simp only [Set.mem_setOf_eq, deg_n_to_finsupp_spec, ne_eq, one_ne_zero, not_false_eq_true,
    MvPolynomial.monomial_left_inj, ← pol_power_shrink_support_eq_iff]
  rw [@Finset.ext_iff] at hab
  ext x
  simp only [mem_image, Finsupp.mem_support_iff, ne_eq, Subtype.exists, exists_and_right,
    exists_eq_right] at hab ⊢
  have h := (hab x.1)
  simp only [Subtype.coe_eta, coe_mem, exists_const] at h
  exact h

noncomputable instance : Fintype (ml_pol_deg_n_set (X := X) n) := by
  refine Set.Finite.fintype ?_
  exact Finite.of_injective (deg_n_to_choose_n (X := X) n) (deg_n_to_choose_n_inj (X := X) n)

-- Show that deg_n_to_choose_n is surjective
lemma deg_n_to_choose_n_suj : Function.Surjective (deg_n_to_choose_n (X := X) n) := by
  intro y
  let S : X →₀ ℕ := Finsupp.ofSupportFinite (fun x => if x.1 ∈ y.1 then 1 else 0) (
    Set.toFinite (Function.support fun (x : X) => if x.1 ∈ y.1 then 1 else 0))
  have hSdef (x : X) : S x = (fun x => if x.1 ∈ y.1 then 1 else 0) x := rfl
  have hS : (pol_power_shrink S) = S := by
    ext x
    simp [pol_power_shrink_spec, hSdef]
  have hyx := (Finset.mem_powersetCard.mp y.2).left
  have hSy : S.support.image Subtype.val = y := by aesop
  let f1 := MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1
  let f : (ml_pol_deg_n_set n) := ⟨f1, ml_pol_deg_n_set_mem_def n f1 (by
    rw [MvPolynomial.totalDegree_monomial (hc := one_ne_zero), ← card_pol_power_shrink_support]
    rw [← (Finset.mem_powersetCard.mp y.2).right, ← hSy, hS]
    refine card_nbij Subtype.val (fun a ↦ by simp) Set.injOn_subtype_val ?_
    intro x hx
    simp_all
    exact hyx hx) (by use S)⟩
  use f
  ext x
  simp only [deg_n_to_choose_n, mem_image, ← hSy]
  suffices (deg_n_to_finsupp n f).support = S.support by rw [this]
  have hf := (deg_n_to_finsupp_spec n f).symm
  have hf1 : f = f1 := rfl
  simp only [hf1, ne_eq, one_ne_zero, not_false_eq_true, MvPolynomial.monomial_left_inj, f1] at hf
  rw [pol_power_shrink_support_eq_iff, hf]

-- Show that deg_n_to_choose_n is bijective
lemma deg_n_to_choose_n_bij : Function.Bijective (deg_n_to_choose_n (X := X) n) :=
  ⟨deg_n_to_choose_n_inj n, deg_n_to_choose_n_suj n⟩

-- Using the bijection to show that the card of (ml_pol_deg_n_set n) is (#X).choose n
lemma card_ml_pol_deg_n_set : #(ml_pol_deg_n_set (X := X) n).toFinset
    = Nat.choose #X n := calc
  _ = Fintype.card (ml_pol_deg_n_set (X := X) n) := by apply Set.toFinset_card
  _ = Fintype.card (powersetCard n X) := Fintype.card_of_bijective (deg_n_to_choose_n_bij n)
  _ = #(powersetCard n X) := Fintype.card_coe (powersetCard n X)
  _ = _ := card_powersetCard n X

-- ml_pol_deg_le_n_set is the set of all multilinear polynomials of degree less than or equal to n
def ml_pol_deg_le_n_set : Set (MvPolynomial X ℝ) :=
  {f | f.totalDegree ≤ n ∧ ∃ S : X →₀ ℕ, f = MvPolynomial.monomial (pol_power_shrink S) 1}

omit [DecidableEq α] in
lemma ml_pol_deg_le_n_set_zero (hn0 : n = 0): ml_pol_deg_le_n_set (X := X) n = {1} := by
  unfold ml_pol_deg_le_n_set
  subst hn0
  ext f
  simp only [nonpos_iff_eq_zero, Set.mem_setOf_eq, Set.mem_singleton_iff]
  have h1 : (MvPolynomial.monomial 0) 1 = (1 : MvPolynomial X ℝ) := by simp
  constructor
  · intro ⟨hfd, ⟨S, hS⟩⟩
    subst hS
    rw [← h1, MvPolynomial.monomial_eq_monomial_iff]
    simp only [and_true, one_ne_zero, and_self, or_false]
    simp only [ne_eq, one_ne_zero, not_false_eq_true, MvPolynomial.totalDegree_monomial] at hfd
    rwa [← card_pol_power_shrink_support, @Finsupp.card_support_eq_zero] at hfd
  · intro hf
    subst hf
    simp only [MvPolynomial.totalDegree_one, true_and]
    use 0
    rw [← h1, MvPolynomial.monomial_eq_monomial_iff]
    simp only [and_true, one_ne_zero, and_self, or_false]
    ext x
    simp [pol_power_shrink_spec]

-- show that (ml_pol_deg_n_set n)'s are parwise disjoint for different degree n
lemma disjoint_ml_pol_deg_n_set :
    (Finset.range (n + 1)).toSet.PairwiseDisjoint
    (fun m => (ml_pol_deg_n_set (X := X) m).toFinset) := by
  intro x hx y hy hxy
  refine Set.disjoint_toFinset.mpr ?_
  refine Set.disjoint_iff_forall_ne.mpr ?_
  simp only [ml_pol_deg_n_set, Set.mem_setOf_eq, and_imp, forall_exists_index]
  intro a ha _ _ b hb _ _
  by_contra hcon
  subst hcon
  rw [ha] at hb
  exact hxy hb

-- Show that ml_pol_deg_le_n_set n is the disjoint union of polynomials of degree equal to m ≤ n
lemma multilinear_set_union_by_deg : ml_pol_deg_le_n_set n =
    ((Finset.range (n + 1)).disjiUnion (fun m => (ml_pol_deg_n_set (X := X) m).toFinset)
      (disjoint_ml_pol_deg_n_set n)).toSet := by
    ext f
    simp only [ml_pol_deg_le_n_set, Set.mem_setOf_eq, ml_pol_deg_n_set, disjiUnion_eq_biUnion,
      coe_biUnion, coe_range, Set.mem_Iio, Set.coe_toFinset, Set.mem_iUnion, exists_and_left,
      exists_prop, exists_eq_left', and_congr_left_iff, forall_exists_index]
    intro _ _
    exact Iff.symm Nat.lt_add_one_iff

noncomputable instance : Fintype (ml_pol_deg_le_n_set (X := X) n) := by
  rw [multilinear_set_union_by_deg]
  apply FinsetCoe.fintype

/- Show that Ω_multilinear_set is indeed the multilinear polynomial with degree ≤ n in the
perspective of function from Ω to ℝ by pol_to_eval (the function of evaluation).-/
omit [DecidableEq α] in
lemma Ω_multilinear_set_eq : Ω_multilinear_set (X := X) n = pol_to_eval ''
    ml_pol_deg_le_n_set n := by
  unfold Ω_multilinear_set ml_pol_deg_le_n_set
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  apply Iff.intro
  · intro a
    obtain ⟨w, ⟨h, S, hwS⟩, hw⟩ := a
    subst hwS
    rw [Ω_pol_spec_1] at hw
    use ((MvPolynomial.monomial (pol_power_shrink S)) 1)
    constructor
    · simp only [ne_eq, one_ne_zero, not_false_eq_true, MvPolynomial.monomial_left_inj, true_and]
      constructor
      · exact le_trans (Ω_pol_spec_2 S) h
      · use S
    · exact hw
  · intro a
    obtain ⟨w, ⟨h, S, hwS⟩, hw⟩ := a
    subst hw
    use w
    constructor
    · constructor
      · exact h
      · use pol_power_shrink S
    · rfl

noncomputable instance : Fintype (Ω_multilinear_set (X := X) n) := by
  rw [Ω_multilinear_set_eq]
  apply Fintype.ofFinite

-- Show that this "function of evaluation" is in fact bijective.
lemma pol_to_eval_bij : Set.BijOn (β := @Ω α X → ℝ) pol_to_eval
    (ml_pol_deg_le_n_set n) (Ω_multilinear_set (X := X) n) := by
  simp only [LinearMap.coe_mk, AddHom.coe_mk, pol_to_eval]
  constructor
  · intro f hf
    simp only [Ω_multilinear_set_eq, Set.mem_image]
    use f
    exact ⟨hf, rfl⟩
  constructor
  · intro f hf g hg hfg
    rw [funext_iff] at hfg
    simp only [Subtype.forall] at hfg
    rw [hf.2.choose_spec, hg.2.choose_spec] at hfg ⊢
    refine (MvPolynomial.monomial_eq_monomial_iff (pol_power_shrink hf.right.choose)
      (pol_power_shrink hg.right.choose) 1 1).mpr ?_
    simp only [and_true, one_ne_zero, and_self, or_false]
    rw [← pol_power_shrink_support_eq_iff]
    ext x
    rw [← pol_power_shrink_support_linear]
    conv => rhs; rw [← pol_power_shrink_support_linear]
    simp only [Finsupp.mem_support_iff, ne_eq, not_iff_not]
    let a : X → ℝ := fun w => if w = x then 0 else 1
    have hfg := hfg a (by
      simp only [Ω, Subtype.forall, Set.mem_setOf_eq, ite_eq_right_iff, one_ne_zero, imp_false,
        ite_eq_left_iff, zero_ne_one, Decidable.not_not, a]
      intro _ _
      apply eq_or_ne
      )
    simp only [MvPolynomial.eval_monomial, Finsupp.prod, ite_pow, one_pow, prod_ite_eq',
      Finsupp.mem_support_iff, ne_eq, ite_not, mul_ite, mul_one, one_mul, a] at hfg
    apply Iff.intro
    · intro h
      by_contra hcon
      simp [h, hcon] at hfg
    · intro h
      by_contra hcon
      simp [h, hcon] at hfg
  · simp only [Ω_multilinear_set_eq]
    exact fun ⦃a⦄ a ↦ a

-- This shows the equiv relation between the multilinear polynomial and its evaluation at Ω → ℝ.
noncomputable instance ml_equiv_Ω_ml :
    ml_pol_deg_le_n_set (X := X) n ≃ Ω_multilinear_set (X := X) n :=
  Set.BijOn.equiv pol_to_eval (pol_to_eval_bij (X := X) n)

/- This theorem shows that the number of all multilinear monic monomials wtih degree n is
∑ m ∈ Finset.range (n + 1), Nat.choose #X m.-/
theorem card_Ω_multilinear_set :
    #(Ω_multilinear_set (X := X) n).toFinset = ∑ m ∈ Finset.range (n + 1), Nat.choose #X m := calc
  #(Ω_multilinear_set (X := X) n).toFinset = #(ml_pol_deg_le_n_set (X := X) n).toFinset := by
    have h := pol_to_eval_bij (X := X) n
    simp only [Set.toFinset_card]
    apply Fintype.card_congr
    exact (ml_equiv_Ω_ml n).symm
  _ = #((Finset.range (n + 1)).disjiUnion (fun m => (ml_pol_deg_n_set (X := X) m).toFinset)
      (disjoint_ml_pol_deg_n_set n)) := by
    congr
    simp only [multilinear_set_union_by_deg, disjiUnion_eq_biUnion, coe_biUnion, coe_range,
      Set.mem_Iio, Set.coe_toFinset]
    ext f
    simp only [ml_pol_deg_le_n_set, Set.mem_toFinset, Set.mem_setOf_eq, ml_pol_deg_n_set,
      mem_biUnion, mem_range, existsAndEq, true_and, and_congr_left_iff, forall_exists_index]
    intro _ _
    exact Iff.symm Nat.lt_add_one_iff
  _ = ∑ m ∈ Finset.range (n + 1), Nat.choose #X m := by
    rw [Finset.card_disjiUnion]
    congr
    ext m
    exact card_ml_pol_deg_n_set m

-- A Fin sum can be seperated in three parts : sum less than, equal to, and greater than a number
lemma Fin_sum_seperated (n : ℕ) (f : Fin n → ℝ) (i : Fin n) :
    ∑ x, f x = f i + ∑ x with x < i, f x + ∑ x with i < x, f x:= by
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

/-This lemma split the multilinear set of degree ≤ n to multilinear set of degree equals to n and
multilinear set of degree ≤ n - 1. It is preparation for the induction step below.-/
omit [DecidableEq α] in
lemma Ω_multilinear_set_union_eq (hn : n ≠ 0): Ω_multilinear_set (X := X) n
    = (pol_to_eval '' (ml_pol_deg_n_set (X := X) n)) ∪  Ω_multilinear_set (X := X) (n - 1) := by
  rw [@Nat.ne_zero_iff_zero_lt] at hn
  simp only [Ω_multilinear_set_eq]
  suffices ml_pol_deg_n_set (X := X) n ∪ ml_pol_deg_le_n_set (n - 1) = ml_pol_deg_le_n_set n by
    rw [← Set.image_union]
    refine congrArg (Set.image pol_to_eval) ?_
    ext x
    unfold ml_pol_deg_le_n_set ml_pol_deg_n_set
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hx
      by_cases h : x.totalDegree = n
      · left
        exact ⟨h, hx.right⟩
      · right
        simp_all only
        simp only [and_true]
        rw [← Nat.lt_iff_le_pred hn]
        exact Nat.lt_of_le_of_ne hx.left h
    · intro hx
      cases hx with
      | inl he => simp_all
      | inr hi =>
        simp_all only [ne_eq, and_true]
        exact le_trans hi.left (Nat.sub_le n 1)
  unfold ml_pol_deg_n_set ml_pol_deg_le_n_set
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq]
  apply Iff.intro
  · intro a
    cases a with
    | inl he => simp_all only [le_refl, and_self]
    | inr hi =>
      simp_all only [and_true]
      exact le_trans hi.left (Nat.sub_le n 1)
  · intro a
    simp_all only [ne_eq, and_true]
    rw [← Nat.lt_iff_le_pred hn, ← le_iff_eq_or_lt]
    exact a.left

-- a lemma used to decompose the condition of being a member of sets, no need to worry about it
omit [DecidableEq α] in
lemma Ω_f_support_mem {f : (@Ω α X → ℝ) →₀ ℝ} {S : Set (@Ω α X → ℝ)}
    (hf : f ∈ Finsupp.supported ℝ ℝ S) : ∀ x ∈ f.support, x ∈ S := by
  intro x hx
  have hx := hf hx
  simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hx
  exact hx

-- a lemma used to decompose the condition of being a member of sets, no need to worry about it
omit [DecidableEq α] in
lemma Ω_deg_n_condition (P : ℕ → Prop) : ∀ x ∈ (pol_to_eval '' {f |
    P f.totalDegree ∧ ∃ S : X →₀ ℕ, f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1}), ∃
    (g : X →₀ ℕ), x = (fun x ↦ if g.support.toSet ⊆ x.1.support then 1 else 0) ∧ P #g.support := by
  intro x hx
  obtain ⟨w, ⟨hwdeg, S, hS⟩, hwx⟩ := hx
  use pol_power_shrink S
  rw [hS, pol_to_eval_monomial_eq] at hwx
  refine ⟨hwx.symm, ?_⟩
  rw [card_pol_power_shrink_support]
  rw [hS] at hwdeg
  simp only [ne_eq, one_ne_zero, not_false_eq_true, MvPolynomial.totalDegree_monomial] at hwdeg
  exact hwdeg

lemma Ω_deg_n_lin_indep : LinearIndepOn ℝ id (pol_to_eval '' (ml_pol_deg_n_set (X := X) n)) := by
  by_contra hcon
  rw [@linearDepOn_iff] at hcon
  obtain ⟨f, hf, h, hcon⟩ := hcon
  simp only [id_eq] at h
  rw [← @Finsupp.support_nonempty_iff] at hcon
  obtain ⟨a, ha⟩ := hcon
  rw [Finset.sum_eq_sum_diff_singleton_add ha (fun x ↦ f x • x), @add_eq_zero_iff_neg_eq'] at h
  have hx := (Ω_deg_n_condition (X := X) (fun pn => pn = n))
  obtain ⟨g, hg, hgs⟩ := hx a ((Ω_f_support_mem hf) a ha)
  let gx : @Ω α X := ⟨fun x => if x ∈ g.support.toSet then (1 : ℝ) else 0, by
    simp [Ω]
    intro a b
    exact Or.symm (ne_or_eq (g ⟨a, b⟩) 0)⟩
  have hcg := congrFun h gx
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, sum_apply] at hcg
  have hgsup : (Function.support fun x ↦ if g x = 0 then 0 else (1 : ℝ)) = g.support.toSet := by
    ext x
    simp
  have hx0 : ∀ x ∈ f.support \ {a}, x gx = 0 := by
    intro w hw
    obtain ⟨gw, hgw, hgsw⟩ := hx w ((Ω_f_support_mem hf) w (sdiff_subset hw))
    simp only [hgw, mem_coe, Finsupp.mem_support_iff, ne_eq, ite_not, hgsup, coe_subset,
      ite_eq_right_iff, one_ne_zero, imp_false, gx]
    by_contra hneg
    have hc : #g.support ≤ #gw.support := by rw [hgs, hgsw]
    have hseq := (Finset.subset_iff_eq_of_card_le hc).mp hneg
    simp only [hseq, ← hg] at hgw
    simp [hgw] at hw
  have hcg : -(f a * a gx) = 0 := calc
    _ = ∑ x ∈ f.support \ {a}, f x * x gx := hcg
    _ = ∑ x ∈ f.support \ {a}, f x * 0 := by
      exact sum_congr rfl fun x a ↦ congrArg (HMul.hMul (f x)) (hx0 x a)
    _ = 0 := by simp
  simp only [Finsupp.mem_support_iff, ne_eq] at ha
  simp only [neg_eq_zero, mul_eq_zero, ha, false_or] at hcg
  simp [hg, gx, hgsup] at hcg

lemma Ω_multilinear_set_lin_indep : LinearIndepOn ℝ id (Ω_multilinear_set (X := X) n) := by
  induction' n with n ih
  · suffices #(Ω_multilinear_set (X := X) 0).toFinset = 1 by
      rw [Finset.card_eq_one] at this
      obtain ⟨a, ha⟩ := this
      rw [← Finset.coe_eq_singleton, Set.coe_toFinset] at ha
      rw [ha]
      refine LinearIndepOn.id_singleton ℝ ?_
      rw [Ω_multilinear_set_eq, ml_pol_deg_le_n_set_zero] at ha
      simp only [pol_to_eval, LinearMap.coe_mk, AddHom.coe_mk, Set.image_singleton, map_one,
        Set.singleton_eq_singleton_iff] at ha
      rw [← ha]
      by_contra hcon
      have hneg := congrFun hcon (⟨fun x => 0, by simp [Ω]⟩ : @Ω α X)
      simp at hneg
      exact rfl
    rw [card_Ω_multilinear_set]
    simp
  rw [Ω_multilinear_set_union_eq (n + 1) (Nat.zero_ne_add_one n).symm, add_tsub_cancel_right]
  apply LinearIndepOn.id_union (Ω_deg_n_lin_indep (n + 1)) ih
  /-Where I get stuck-/
  sorry

-- Give an index to Ω_multilinear_set
noncomputable def Ω_multilinear_set_indexed (i : Fin #(Ω_multilinear_set (X := X) #L).toFinset):
  @Ω α X → ℝ := (Ω_multilinear_set (X := X) #L).toFinset.toList[i]

-- Show that the image of Ω_multilinear_set_indexed is in Ω_multilinear_set
lemma Ω_multilinear_set_indexed_mem (i : Fin #(Ω_multilinear_set (X := X) #L).toFinset):
    (Ω_multilinear_set_indexed L i) ∈ (Ω_multilinear_set (X := X) #L) := by
  suffices (Ω_multilinear_set #L).toFinset.toList[i] ∈ (Ω_multilinear_set #L).toFinset by
    rwa [@Set.mem_toFinset] at this
  rw [← Finset.mem_toList]
  exact List.mem_of_getElem rfl

-- Show that there exist a multilinear polynomial's evaluation equals the indexed result
lemma Ω_multilinear_set_indexed_spec (i : Fin #(Ω_multilinear_set (X := X) #L).toFinset):
    ∃ f ∈ {f | f.totalDegree ≤ #L ∧ ∃ S : X →₀ ℕ, f = MvPolynomial.monomial S 1},
    pol_to_eval f = (Ω_multilinear_set_indexed L i) := by
  have h := Ω_multilinear_set_indexed_mem L i
  unfold Ω_multilinear_set at h
  rwa [Set.mem_image] at h

-- The span of Ω_multilinear_set
def Ω_multilinear_span : Submodule ℝ (@Ω α X → ℝ) := Submodule.span ℝ (Ω_multilinear_set #L)

noncomputable def ml_pol_span (X : Finset α) : Submodule ℝ (MvPolynomial X ℝ) :=
  Submodule.span ℝ (ml_pol_deg_le_n_set (X := X) #L)

-- Show that the rank of the span of Ω_multilinear_set is equal to its cardinality
/-lemma dim_Ω_multilinear_span : Module.rank ℝ (Ω_multilinear_span (X := X) L) =
    ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  rw [← card_Ω_multilinear_set, Set.toFinset_card]
  have h := (rank_span (Ω_multilinear_set_lin_indep (X := X) L))
  rw [Ω_multilinear_set_indexed_range] at h
  rw [Ω_multilinear_span, h, Cardinal.mk_fintype]-/

-- Show that any monomials of degree no greater than #L is in the span of Ω_multilinear_set.
omit [DecidableEq α] in
theorem monomial_in_Ω_span (v : X →₀ ℕ) (hv : (v.sum fun x e ↦ e) ≤ #L):
    pol_to_eval (MvPolynomial.monomial (R := ℝ) v 1) ∈ Ω_multilinear_span L := by
  unfold Ω_multilinear_span
  suffices pol_to_eval ((MvPolynomial.monomial v) 1) ∈ (Ω_multilinear_set (X := X) #L) by
    exact Submodule.mem_span.mpr fun p a ↦ a this
  simp only [Ω_multilinear_set, Set.mem_image]
  use (MvPolynomial.monomial v) 1
  constructor
  · simp only [Set.mem_setOf_eq, ne_eq, one_ne_zero, not_false_eq_true,
      MvPolynomial.totalDegree_monomial, MvPolynomial.monomial_left_inj, exists_eq', and_true]
    exact hv
  · rfl

omit [DecidableEq α] in
lemma Ω_multilinear_span_deg_le_mem (f : MvPolynomial X ℝ) (hdeg : f.totalDegree ≤ #L) :
    pol_to_eval f ∈ Ω_multilinear_span (X := X) L := by
  rw [MvPolynomial.as_sum f, map_sum]
  apply Submodule.sum_mem
  intro v hv
  have hsmul (a : ℝ): (MvPolynomial.monomial v a) =
    a • (MvPolynomial.monomial v 1) := by
    rw [@MvPolynomial.smul_monomial]
    simp
  suffices pol_to_eval ((MvPolynomial.monomial v) 1) ∈ Ω_multilinear_span L by
    rw [hsmul, map_smul]
    exact Submodule.smul_mem (Ω_multilinear_span L) (MvPolynomial.coeff v f) this
  apply monomial_in_Ω_span
  refine le_trans ?_ hdeg
  apply MvPolynomial.le_totalDegree
  exact hv

/-lemma Ω_multilinear_span_pol_to_eval_mem:
    Set.MapsTo pol_to_eval (ml_pol_span (X := X) L).carrier (Ω_multilinear_span (X := X) L) := by

  apply Ω_multilinear_span_deg_le_mem
  have hmem : f.1 ∈ Submodule.span ℝ ((ml_pol_deg_le_n_set #L).toFinset).toSet := by
    rw [Set.coe_toFinset]
    exact f.2
  apply mem_span_finset.mp at hmem
  obtain ⟨g, hg⟩ := hmem
  rw [← hg]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  simp only [ml_pol_deg_le_n_set, Set.mem_toFinset, Set.mem_setOf_eq] at hi
  refine le_trans ?_ hi.left
  apply MvPolynomial.totalDegree_smul_le-/

/- not useful anymore, but this proves the linear independence of multilinear polynomials
  with degree less or equal to n (NOT AS EVALUATION FUNCTION)-/
lemma ml_lin_indep : LinearIndepOn ℝ id (ml_pol_deg_le_n_set (X := X) #L) := by
  by_contra hcon
  rw [@linearDepOn_iff] at hcon
  obtain ⟨f, hf, h, hcon⟩ := hcon
  simp only [id_eq] at h
  rw [← @Finsupp.support_nonempty_iff] at hcon
  obtain ⟨a, ha⟩ := hcon
  rw [Finset.sum_eq_sum_diff_singleton_add ha (fun x ↦ f x • x)] at h
  have hf : f.support ⊆ (ml_pol_deg_le_n_set (X := X) #L).toFinset := Set.subset_toFinset.mpr hf
  have hx : ∀ x ∈ f.support, ∃ g, x = MvPolynomial.monomial g 1 := by
    intro x hx
    have hx := hf hx
    simp only [ml_pol_deg_le_n_set, Set.mem_toFinset, Set.mem_setOf_eq] at hx
    obtain ⟨_, S, hS⟩ := hx
    use pol_power_shrink S
  obtain ⟨g, hg⟩ := hx a ha
  have h : MvPolynomial.coeff g (∑ x ∈ f.support \ {a}, f x • x + f a • a)
    = MvPolynomial.coeff g 0 := congrArg (MvPolynomial.coeff g) h
  conv at h => lhs; congr; rfl; congr; rfl; congr; rfl; rw [hg]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial,
    ↓reduceIte, smul_eq_mul, mul_one, MvPolynomial.coeff_zero] at h
  suffices MvPolynomial.coeff g (∑ x ∈ f.support \ {a}, f x • x) = 0 by
    rw [this, zero_add] at h
    rw [@Finsupp.mem_support_iff] at ha
    exact ha h
  rw [MvPolynomial.coeff_sum]
  suffices ∑ x ∈ f.support \ {a}, MvPolynomial.coeff g (f x • x) = ∑ x ∈ f.support \ {a}, 0 by
    rw [this]
    simp
  apply Finset.sum_congr rfl
  intro x hxa
  obtain ⟨j, hj⟩ := hx x (sdiff_subset hxa)
  conv => lhs; congr; rfl; congr; rfl; rw [hj]
  simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero, ite_eq_right_iff]
  intro hjg
  subst hjg hj
  rw [← hg] at hxa
  simp at hxa

-- Show that the rank of the span of Ω_multilinear_set is ≤ its cardinality
lemma dim_Ω_multilinear_span : Module.rank ℝ (Ω_multilinear_span (X := X) L) ≤
    ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  have h := rank_span_finset_le (R := ℝ) (Ω_multilinear_set (X := X) #L).toFinset
  rw [Set.coe_toFinset] at h
  rw [← card_Ω_multilinear_set]
  exact h




namespace Frankl_Wilson

-- The characteristic polynomial of a set A
noncomputable def char_pol (i : Fin #F) : MvPolynomial X ℝ :=
  ∏ l ∈ L with l < #(F_sorted i).val,
    (∑ m : X, ((char_vec hF i m) • (MvPolynomial.X m)) - (MvPolynomial.C l : MvPolynomial X ℝ) )

-- Show that the total degree of the characteristic polynomial is no greater than #L
lemma char_pol_degree (i : Fin #F): (char_pol L hF i).totalDegree ≤ #L := by
  unfold char_pol
  have h : (∑ m, char_vec hF i m • MvPolynomial.X m : MvPolynomial X ℝ).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro x hx
    calc
    _ ≤ (MvPolynomial.X x).totalDegree :=
      MvPolynomial.totalDegree_smul_le (char_vec hF i x) (MvPolynomial.X x : MvPolynomial X ℝ)
    _ = 1 := by apply MvPolynomial.totalDegree_X
  have h (l : ℕ): (∑ m, char_vec hF i m • MvPolynomial.X m
      - (MvPolynomial.C l : MvPolynomial X ℝ)).totalDegree ≤ 1 := calc
    _ = (∑ m, char_vec hF i m • MvPolynomial.X m
      + (MvPolynomial.C (-l) : MvPolynomial X ℝ)).totalDegree := by
        rw [MvPolynomial.C_neg, Mathlib.Tactic.RingNF.add_neg]
    _ ≤ max
      (∑ m, char_vec hF i m • MvPolynomial.X m : MvPolynomial X ℝ).totalDegree
      (MvPolynomial.C (-l) : MvPolynomial X ℝ).totalDegree := by
      apply MvPolynomial.totalDegree_add
    _ ≤ _ := by
      simp only [MvPolynomial.totalDegree_C, zero_le, sup_of_le_left]
      exact h
  calc
  _ ≤ ∑ l ∈ L with l < #(F_sorted i).val,
    (∑ m : X, char_vec hF i m • MvPolynomial.X m
    - (MvPolynomial.C l : MvPolynomial X ℝ)).totalDegree := by
    apply MvPolynomial.totalDegree_finset_prod
  _ ≤ ∑ l ∈ L with l < #(F_sorted i).val, 1 := by exact sum_le_sum fun i_1 a ↦ h i_1
  _ = #{l ∈ L | l < #(F_sorted i).val} := by
    exact (card_eq_sum_ones {l ∈ L | l < #(F_sorted i).val}).symm
  _ ≤ _ := card_filter_le L fun l ↦ l < #(F_sorted i).val

-- Rewrite the evaluation of characteristic polynomial as a function
lemma char_pol_eval_eq (i : Fin #F) (x : X → ℝ): (char_pol L hF i).eval x
    = ∏ l ∈ L with l < #(F_sorted i).val, ((char_vec hF i) ⬝ᵥ x - l) := by
  unfold char_pol
  rw [@MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro l hl
  simp [(· ⬝ᵥ ·)]

-- Ω_char_pol translates characteristic polynomials to the function from Ω to ℝ via pol_to_eval
noncomputable def Ω_char_pol (i : Fin #F) (x : @Ω α X): ℝ := (char_pol L hF i).eval x

-- This lemma gives a more handy definition of Ω_char_pol
lemma Ω_char_pol_eq (i : Fin #F) : Ω_char_pol L hF i = pol_to_eval (char_pol L hF i) := rfl

-- Ω_char_pol_span is the span of all characteristic polynomials
def Ω_char_pol_span : Submodule ℝ (@Ω α X → ℝ) := Submodule.span ℝ (Set.range (Ω_char_pol L hF))

-- Show that the characteristic polynomial is also in the span of Ω_multilinear_set.
lemma Ω_char_pol_spec (i : Fin #F): Ω_char_pol L hF i ∈ Ω_multilinear_span L := by
  rw [Ω_char_pol_eq]
  exact Ω_multilinear_span_deg_le_mem L (char_pol L hF i) (char_pol_degree L hF i)

-- Show that the span of the characteristic polynomial is included in the span of Ω_multilinear_set.
lemma span_to_R_le_span_ml : (Ω_char_pol_span L hF) ≤ Ω_multilinear_span L := by
  unfold Ω_char_pol_span
  suffices Set.range (Ω_char_pol L hF) ⊆ (Ω_multilinear_span (X := X) L) by
    exact Submodule.span_le.mpr this
  intro x hx
  rw [@Set.mem_range] at hx
  obtain ⟨y, hy⟩ := hx
  subst hy
  exact Ω_char_pol_spec L hF y

-- Show that the rank of the characteristic polynomial is ≤ the cardinality of Ω_multilinear_set.
lemma dim_span_to_R_le :
    Module.rank ℝ (Ω_char_pol_span L hF) ≤ ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m:= by
  exact Preorder.le_trans (Module.rank ℝ (Ω_char_pol_span L hF))
    (Module.rank ℝ (Ω_multilinear_span (X := X) L))
    (↑(∑ m ∈ range (#L + 1), (#X).choose m))
    (Submodule.rank_mono (span_to_R_le_span_ml L hF)) (dim_Ω_multilinear_span L)

-- Show that the characteristic polynomial is non-zero for the characteristic vector of A.
lemma char_pol_spec_1 (i : Fin #F) : (char_pol L hF i).eval (char_vec hF i) ≠ 0 := by
  rw [char_pol_eval_eq L hF i (char_vec hF i)]
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
    (hintersect : intersecting F L): (char_pol L hF i).eval (char_vec hF j) = 0 := by
  rw [char_pol_eval_eq L hF i (char_vec hF j)]
  unfold intersecting at hintersect
  refine prod_eq_zero_iff.mpr ?_
  use #((F_sorted i).val ∩ (F_sorted j).val)
  rw [char_vec_spec, sub_self, propext (and_iff_left rfl), mem_filter]
  constructor
  · refine hintersect (F_sorted i) (F_sorted i).2 (F_sorted j) (F_sorted j).2 ?_
    exact Subtype.coe_ne_coe.mpr (neq_F_sorted i j hneq)
  · refine card_lt_card ?_
    rw [@Finset.ssubset_iff_subset_ne]
    constructor
    · exact inter_subset_left
    · rw [ne_eq, inter_eq_left]
      by_contra hcon
      have hle := sorted_F_sorted j i hji
      unfold card_le at hle
      rw [Bool.decide_iff] at hle
      have h := eq_of_subset_of_card_le hcon hle
      simp only [@SetCoe.ext_iff] at h
      exact (neq_F_sorted i j hneq) h

-- Show that the characteristic polynomials are in fact linear independent
lemma Ω_char_pol_lin_indep (hintersect : intersecting F L) :
    LinearIndependent ℝ (Ω_char_pol L hF) := by
  by_contra hcon
  rw [@Fintype.not_linearIndependent_iff] at hcon
  obtain ⟨g, hg, hi⟩ := hcon
  have h := Fin.find (fun i ↦ g i ≠ 0)
  have hexist := Fin.isSome_find_iff.mpr hi
  rw [@Option.isSome_iff_exists] at hexist
  obtain ⟨i, hi⟩ := hexist
  rw [@Fin.find_eq_some_iff] at hi
  obtain ⟨hi, hmin⟩ := hi
  have hsubst := congrFun hg (Ω_char_vec hF i)
  simp only [Ω_char_vec, sum_apply, Pi.smul_apply, Ω_char_pol, smul_eq_mul,
    Pi.zero_apply] at hsubst
  rw [Fin_sum_seperated #F _ i] at hsubst
  --Show that all the x before i gives zero since g x = 0 by hmin.
  have hless : ∑ x ∈ {x | x < i}, g x * (char_pol L hF x).eval (char_vec hF i) = 0 := by
    rw [Finset.sum_eq_zero]
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    suffices g x = 0 by exact mul_eq_zero_of_left this ((char_pol L hF x).eval (char_vec hF i))
    by_contra hcon2
    exact (not_le.mpr hx) (hmin x hcon2)
  --Show that all the x after i gives zero since char_pol = 0 by char_pol_spec_2.
  have hmore : ∑ x ∈ {x | i < x}, g x * (char_pol L hF x).eval (char_vec hF i) = 0 := by
    rw [Finset.sum_eq_zero]
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [char_pol_spec_2 L hF x i (ne_of_lt hx).symm hx hintersect]
    exact mul_zero (g x)
  --Thus Show that g i * char_pol F L i (char_vec F i) = 0, which contradicts char_pol_spec_1.
  simp only [hless, hmore, add_zero, mul_eq_zero] at hsubst
  cases hsubst with
  | inl h1 => exact hi h1
  | inr hi => exact char_pol_spec_1 L hF i hi

theorem Frankl_Wilson_Thoerem (hF : ∀ A ∈ F, A ⊆ X) (hintersect : intersecting F L):
    #F ≤ ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  have h := linearIndependent_span (Ω_char_pol_lin_indep L hF hintersect)
  apply LinearIndependent.cardinal_le_rank at h
  rw [Cardinal.mk_fintype, Fintype.card_fin] at h
  exact Nat.cast_le.mp (le_trans h (dim_span_to_R_le L hF))

end Frankl_Wilson
