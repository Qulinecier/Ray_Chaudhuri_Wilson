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
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

open Finset

universe u_1 u_2 u_3
variable {R : Type u_3} [Field R]

/-
This theorem (sorted_linearIndepOn) described a method often used here for proving linear
independence of functions to ℝ.

It says that if there exists a degree function (Sn) that find the degree of the functions to ℝ (S i)
from the index set ι (i ∈ ι) of the family of functions to ℝ (S), so that for any i, there exist an
element in (S i).support (a), so that if (Sn i) ≤ (Sn j) for some j, then (a) is never in the
support of (S j).

In paticular, let the degree function be the cardinality of the set A ∈ F, and the family of
functions to be the evaluation of characteristic polynomials (char_p A).eval (so the index set
is F), since for any A and B, #A ≤ #B implies that it is not possible that B ⊆ A, thus the
characteristic vector v_A is never in the support of (char_p B).eval for any B. The
requirement for the theorem is then reached and the functions can be proven to be
linear independent.
-/
-- ∃ x ∈ Finsupp.supported R R s, ∑ i ∈ x.support, x i • S i = 0 ∧ ¬x = 0

/--NEXT: let α be the set of all Ω_char_vec _ (hF _ (F_indexed i).2)--/

theorem sorted_linearComb_zero {α : Type u_1} {ι : Type u_2} {s : Set ι} [Fintype s]
    (S : ι → (α → R)) (Sn : ι → ℝ) (h : ∀ f ∈ s, ∃ a ∈ (S f).support, ∀ g ∈ s,
    Sn f ≤ Sn g → f ≠ g → a ∉ (S g).support) :
    ∀ f ∈ Finsupp.supported R R s, ∑ i ∈ f.support, f i • S i = 0 → f = 0 := by
  by_contra hcon
  simp at hcon
  obtain ⟨g, hg, hi, hgne⟩ := hcon
  have : DecidableEq ι := by exact Classical.typeDecidableEq ι
  have : DecidableEq (α → ℝ) := by exact Classical.typeDecidableEq (α → ℝ)
  have hs := (Finset.image Sn g.support).min'_mem (by
    by_contra hneg
    simp only [image_nonempty, not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at hneg
    exact hgne hneg)
  simp only [Set.toFinset_image, toFinset_coe, mem_image] at hs
  obtain ⟨a, ha, hsna⟩ := hs
  obtain ⟨as, has, hasu⟩ := h a (hg ha)
  have h : ∀ f ∈ g.support, f ≠ a → as ∉ (S f).support := by
    intro f hf hfa
    refine hasu f (hg hf) ?_ hfa.symm
    rw [hsna]
    apply Finset.min'_le
    rw [mem_image]
    use f
  have hcalc : (∑ i ∈ g.support, g i • S i) as = g a • (S a) as := calc
    (∑ i ∈ g.support, g i • S i) as = ∑ i ∈ g.support, g i • S i as := by simp
    _ = ∑ i ∈ g.support \ {a}, g i • S i as + g a • S a as := by
      exact Finset.sum_eq_sum_diff_singleton_add ha (fun i ↦ g i • S i as)
    _ = ∑ i ∈ g.support \ {a}, g i • 0 + g a • S a as := by
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      congr
      rw [mem_sdiff, mem_singleton] at hy
      have hans := h y hy.left hy.right
      simp at hans
      exact hans
    _ = _ := by simp
  simp only [hi, Pi.zero_apply, smul_eq_mul, zero_eq_mul] at hcalc
  cases hcalc with
  | inl h1 =>
    simp only [Finsupp.mem_support_iff, ne_eq] at ha
    exact ha h1
  | inr hi =>
    simp only [Function.mem_support, ne_eq] at has
    exact has hi

theorem sorted_linearIndepOn {α : Type u_1} {ι : Type u_2} {s : Set ι} [Fintype s]
    (S : ι → (α → R)) (Sn : ι → ℝ) (h : ∀ f ∈ s, ∃ a ∈ (S f).support, ∀ g ∈ s,
    Sn f ≤ Sn g → f ≠ g → a ∉ (S g).support) : LinearIndepOn R S s := by
  by_contra hcon
  rw [@linearDepOn_iff] at hcon
  suffices ¬ (∃ f ∈ Finsupp.supported R R s, ∑ i ∈ f.support, f i • S i = 0 ∧ f ≠ 0) by
    exact this hcon
  simp only [ne_eq, not_exists, not_and, not_not]
  exact sorted_linearComb_zero S Sn h

variable {α : Type} (n : ℕ) [DecidableEq α] {X: Finset α} {F: Finset (Finset α)} (L : Finset ℕ)

def uniform (F: Finset (Finset α)) (k : ℕ): Prop := ∀ A ∈ F, #A = k

def weak_uniform (F: Finset (Finset α)) (K : Finset ℕ) (L : Finset ℕ) :=
  (F.image card) ⊆ K ∧ ∀ A ∈ K, A > (#L - #(F.image card))

def weak_intersecting (F: Finset (Finset α)) (L : Finset ℕ) :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → #(A ∩ B) ∈ L

noncomputable instance : Fintype {x | ∃ A ∈ F, ∃ B ∈ F, A ≠ B ∧ x = #(A ∩ B)} := by
  refine Set.Finite.fintype ?_
  let Fc : Finset ℕ := image (fun x => #x) F
  by_cases hFc : Fc.Nonempty
  · have hFcm := Fc.max'_mem hFc
    simp only [Fc, mem_image] at hFcm
    obtain ⟨a, ha, hac⟩ := hFcm
    refine Set.Finite.subset (finite_toSet (range #a)) ?_
    intro x
    simp only [ne_eq, Set.mem_setOf_eq, coe_range, Set.mem_Iio, forall_exists_index, and_imp]
    rintro A hA B hB hneq rfl
    wlog hAB : #B ≤ #A generalizing A B
    · have := this B hB A hA (fun a ↦ hneq a.symm) (Nat.le_of_succ_le (not_le.mp hAB))
      rwa [@inter_comm] at this
    · have : #(A ∩ B) < #A := by
        apply card_lt_card
        simp only [Finset.ssubset_iff_subset_ne, inter_subset_left, ne_eq, inter_eq_left, true_and]
        by_contra hcon
        have : #A < #B := card_lt_card (HasSubset.Subset.ssubset_of_ne hcon hneq)
        rw [@lt_iff_not_le] at this
        exact this hAB
      refine Nat.lt_of_lt_of_le this ?_
      rw [hac]
      apply Finset.le_max'
      simp only [mem_image]
      use A
  · simp only [image_nonempty, not_nonempty_iff_eq_empty, Fc] at hFc
    subst hFc
    simp

def intersecting (F: Finset (Finset α)) (L : Finset ℕ) :=
  L = {x | ∃ A ∈ F, ∃ B ∈ F, A ≠ B ∧ x = #(A ∩ B)}.toFinset

lemma uniform_intersecting_card_le (F: Finset (Finset α)) (L : Finset ℕ) (hu : uniform F n)
    (hsi : intersecting F L) : #L ≤ n := by
  suffices ∀ i ∈ L, i < n by
    rw [← card_range n]
    refine card_le_card ?_
    intro x hx
    simp only [mem_range]
    exact this x hx
  intro i hi
  subst hsi
  simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hi
  obtain ⟨A, hA, B, hB, hneq, rfl⟩ := hi
  wlog hAB : #B ≤ #A generalizing A B
  · have := this B hB A hA (fun a ↦ hneq a.symm) (Nat.le_of_succ_le (not_le.mp hAB))
    rwa [@inter_comm] at this
  · have : #(A ∩ B) < #A := by
      apply card_lt_card
      rw [@Finset.ssubset_iff_subset_ne]
      constructor
      · exact inter_subset_left
      · by_contra hcon
        simp only [inter_eq_left] at hcon
        have : #A < #B := card_lt_card (HasSubset.Subset.ssubset_of_ne hcon hneq)
        rw [@lt_iff_not_le] at this
        exact this hAB
    refine Nat.lt_of_lt_of_le this ?_
    exact Nat.le_of_eq (hu A hA)

lemma uniform_weak_uniform (hn : 0 < n) (hsi : intersecting F L) :
    uniform F n → weak_uniform F {n} L := by
  intro hu
  have hF : ¬ F = ∅ → image card F = {n} := by
    intro hF
    ext x
    simp only [mem_image, mem_singleton, forall_exists_index, and_imp]
    constructor
    · rintro ⟨A, hA, rfl⟩; exact hu A hA
    · rintro ⟨rfl⟩
      rw [@eq_empty_iff_forall_not_mem] at hF
      simp only [not_forall, Decidable.not_not] at hF
      obtain ⟨a, ha⟩ := hF
      use a
      exact ⟨ha, hu a ha⟩
  by_cases hL : 0 < #L
  · by_cases hexist : ∃ a, a ∈ F
    · have hleft : image card F = {n} := by
        rw [← @not_forall_not, ← eq_empty_iff_forall_not_mem] at hexist
        exact hF hexist
      constructor
      · rw [hleft]
      · simp only [mem_singleton, hleft, card_singleton, gt_iff_lt, forall_eq]
        exact Nat.sub_one_lt_of_le hL (uniform_intersecting_card_le n F L hu hsi)
    · simp only [not_exists, ← @eq_empty_iff_forall_not_mem] at hexist
      subst hexist
      simp only [intersecting, not_mem_empty, ne_eq, false_and, exists_const, and_self,
        Set.setOf_false, Set.toFinset_empty] at hsi
      subst hsi
      simp at hL
  · simp only [card_pos, not_nonempty_iff_eq_empty] at hL
    subst hL
    constructor
    · simp only [subset_singleton_iff, image_eq_empty]
      by_cases hempt : F = ∅
      · exact Or.inl hempt
      · simp [hF, hempt]
    · simp [hn]

lemma intersecting_weak_intersecting {F: Finset (Finset α)} {L : Finset ℕ} :
    intersecting F L → weak_intersecting F L := by
  rintro hL A hA B hB hne
  subst hL
  simp only [Set.mem_toFinset, Set.mem_setOf_eq]
  use A
  simp only [hA, true_and]
  use B

def weak_intersecting_exist_intersecting {F: Finset (Finset α)} {L : Finset ℕ}:
    weak_intersecting F L → ∃ Ls ⊆ L, intersecting F Ls := by
  unfold intersecting weak_intersecting
  intro h
  use {x | ∃ A ∈ F, ∃ B ∈ F, A ≠ B ∧ x = #(A ∩ B)}.toFinset
  simp only [ne_eq, Set.toFinset_subset, Set.coe_toFinset, and_true]
  intro x
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  exact fun x_1 a x_2 a_1 a_2 a_3 ↦ Set.mem_of_eq_of_mem a_3 (h x_1 a x_2 a_1 a_2)


--Ω is defined as X → {0, 1} in paper, and in this code it is defined as a subset of X → R.
def Ω : Set (X → R) := { f : X → R | ∀ a, f a = 0 ∨ f a = 1 }

instance: Algebra R (@Ω R _ α X → R) := by infer_instance

/- The characteristic vector of a set A_i is a function from
  X to {0, 1} that indicates membership in A.-/
def char_vec (A : Finset α) (hA : A ⊆ X): X → R := fun a => if a.val ∈ A.val then 1 else 0

-- Show that the char_vec can be restricted to {0, 1}.
lemma char_vec_mem_Ω (A : Finset α) (hA : A ⊆ X) : (char_vec (R := R) A hA) ∈ Ω := by
  unfold char_vec Ω
  simp only [Subtype.forall, Set.mem_setOf_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    ite_eq_left_iff, zero_ne_one, Decidable.not_not]
  intro a b
  exact Decidable.not_or_of_imp fun a ↦ a

-- The char_vec with restricted codomain to {0, 1}.
noncomputable def Ω_char_vec (A : Finset α) (hA : A ⊆ X):
  @Ω R _ α X := ⟨char_vec A hA, char_vec_mem_Ω A hA⟩

-- Show that the inner product of characteristic vectors gives the card of the set intersection.
lemma char_vec_spec (A B : Finset α) (hA : A ⊆ X) (hB : B ⊆ X) :
    (char_vec A hA) ⬝ᵥ (char_vec (R := R) B hB) = #(A ∩ B) := by
  have h : (char_vec A hA) ⬝ᵥ (char_vec (R := R) B hB) =
      ∑ a : X, if a.val ∈ A ∩ B then 1 else 0 := by
    simp only [(· ⬝ᵥ ·)]
    refine congrArg univ.sum ?_
    unfold char_vec
    aesop
  rw [h]
  simp only [sum_boole, Nat.cast_inj]
  congr 1
  suffices {x | x ∈ A ∩ B} = A ∩ B by
    refine card_nbij (·.val) (fun a ↦ ?_) (fun x1 hx1 x2 hx2 hf =>by aesop) ?_
    · intro ha
      simp only [univ_eq_attach, mem_filter, mem_attach, true_and] at ha ⊢
      exact ha
    · intro y hy
      have hmem : y ∈ X := by
        simp only [coe_inter, Set.mem_inter_iff, mem_coe] at hy
        exact hA hy.left
      use ⟨y, hmem⟩
      simp only [univ_eq_attach, coe_filter, mem_attach, true_and, Set.mem_setOf_eq, and_true]
      exact hy
  ext a
  simp

-- pol_to_eval sends a MvPolynomial to its evaluation as a function from Ω to ℝ
def pol_to_eval : (MvPolynomial X R) →ₐ[R] (@Ω R _ α X → R) where
  toFun fp := fun x => fp.eval (σ := X) x
  map_one' := by aesop
  map_mul' := by aesop
  map_zero' := by aesop
  map_add' := by aesop
  commutes' := by aesop

noncomputable instance (x : @Ω R _ α X) (S : X →₀ ℕ): Decidable (S.support.toSet ⊆ x.1.support) :=
  Classical.propDecidable (S.support.toSet ⊆ x.1.support)

/- This lemma decode the pol_to_eval when the input happen to be a monomial: it become like a
  indicator function that gives 1 if the support of monomial is a subset of the input, else 0. -/
omit [DecidableEq α] in
lemma pol_to_eval_monomial_eq : ∀ S, pol_to_eval (MvPolynomial.monomial S 1) =
    (fun (x : @Ω R _ α X) => if S.support.toSet ⊆ x.1.support then 1 else 0) := by
  intro S
  ext x
  unfold pol_to_eval
  simp only [AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    MvPolynomial.eval_monomial, Finsupp.prod_pow, univ_eq_attach, one_mul]
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
      univ_eq_attach, mem_attach, pow_eq_zero_iff', true_and, not_not] at hax ha ⊢
    exact ⟨hax, ha⟩

/- Ω_multilinear_set is the set of all monic multilinear polynomials with totaldegree less than L,
  in the context of function from Ω to ℝ.-/
def Ω_multilinear_set : Set (@Ω R _ α X → R) := pol_to_eval ''
  {f | f.totalDegree ≤ n ∧ ∃ S : X →₀ ℕ, f = MvPolynomial.monomial S 1}

/- pol_power_shrink send a (Finsupp) S to a "shrinked" Finsupp, keeping S.support the same while
decreasing any non-zero terms to 1. It is used to decrease the degree of MvPolynomials to 1,
since they are equivalent in the perspective of functions from Ω to ℝ.
S is usually the degree of a MvPolynomial. -/
noncomputable def pol_power_shrink (S : X → ℕ) : X →₀ ℕ :=
  Finsupp.ofSupportFinite (fun x => if S x = 0 then 0 else 1) (by
    exact Set.toFinite (Function.support fun x ↦ if S x = 0 then 0 else 1))

-- A more handy definition of pol_power_shrink as a function
omit [DecidableEq α] in
lemma pol_power_shrink_spec (S : X →₀ ℕ) (x : X):
  (pol_power_shrink S) x = (fun x ↦ if S x = 0 then 0 else 1) x := rfl

omit [DecidableEq α] in
lemma pol_power_shrink_spec' (S : X → ℕ) (x : X):
  (pol_power_shrink S) x = (fun x ↦ if S x = 0 then 0 else 1) x := rfl

-- pol_power_shrink keeps the support unchanged
omit [DecidableEq α] in
lemma pol_power_shrink_support_linear (S : X →₀ ℕ) : (pol_power_shrink S).support = S.support := by
  ext x
  simp [pol_power_shrink_spec]

omit [DecidableEq α] in
lemma pol_power_shrink_support_linear' (S : X → ℕ) : (pol_power_shrink S).support = S.support := by
  ext x
  simp [pol_power_shrink_spec']

-- pol_power_shrink are equal iff the support of the original Finsupp is the same
omit [DecidableEq α] in
lemma pol_power_shrink_support_eq_iff' (S1 S2: X → ℕ):
    S1.support = S2.support ↔ pol_power_shrink S1 = pol_power_shrink S2:= by
  apply Iff.intro
  · intro hs
    ext x
    simp only [pol_power_shrink_spec']
    rw [@Set.ext_iff] at hs
    simp only [Function.mem_support, ne_eq, not_iff_not, Subtype.forall] at hs
    simp [hs x]
  · intro hp
    rw [← pol_power_shrink_support_linear', hp, pol_power_shrink_support_linear']

omit [DecidableEq α] in
lemma pol_power_shrink_support_eq_iff (S1 S2: X →₀ ℕ):
    S1.support = S2.support ↔ pol_power_shrink S1 = pol_power_shrink S2:= by
  suffices Function.support S1 = Function.support S2 ↔ pol_power_shrink S1 = pol_power_shrink S2 by
    simp [← this]
  apply pol_power_shrink_support_eq_iff'

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
lemma Ω_pol_spec_1 (S : X →₀ ℕ) : pol_to_eval (MvPolynomial.monomial S (1 : R)) =
    pol_to_eval (MvPolynomial.monomial (pol_power_shrink S) 1) := by
  ext x
  unfold pol_to_eval
  simp only [AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    MvPolynomial.eval_monomial, Finsupp.prod_pow, univ_eq_attach, one_mul]
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
    (MvPolynomial.monomial (pol_power_shrink S) (R := R) 1).totalDegree ≤
    (MvPolynomial.monomial (R := R) S 1).totalDegree := by
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
def ml_pol_deg_n_set : Set (MvPolynomial X R) :=
  {f | f.totalDegree = n ∧ ∃ S : X →₀ ℕ, f = MvPolynomial.monomial (pol_power_shrink S) 1}

-- state the definition of a MvPolynomial being in ml_pol_deg_n_set
omit [DecidableEq α] in
lemma ml_pol_deg_n_set_mem_def (f : MvPolynomial X R) (hd : f.totalDegree = n)
    (hf : ∃ S : X →₀ ℕ, f = MvPolynomial.monomial (pol_power_shrink S) 1) :
    f ∈ ml_pol_deg_n_set (X := X) n := by
  simp [ml_pol_deg_n_set, hf, hd]

-- Any MvPolynomial in (ml_pol_deg_n_set n) has degree equal to n.
def deg_n_to_deg_eq_n (f : ml_pol_deg_n_set (R := R) (X := X) n) : f.1.totalDegree = n := f.2.1

-- Choose a Finsupp as the degree (after shrink) of the MvPolynomial in (ml_pol_deg_n_set n).
noncomputable def deg_n_to_finsupp (f : ml_pol_deg_n_set (R := R) (X := X) n) : X →₀ ℕ :=
  f.2.2.choose

-- Show that the pol_power_shrink of the chosen Finsupp is indeed the degree of that MvPolynomial
noncomputable def deg_n_to_finsupp_spec (f : ml_pol_deg_n_set (R := R) (X := X) n) :
    f.1 = MvPolynomial.monomial  (pol_power_shrink (deg_n_to_finsupp n f)) 1 :=
  f.2.2.choose_spec

-- Show that support of deg_n_to_finsupp is a subset of X
lemma deg_n_to_choose_n_sub_X (f : ml_pol_deg_n_set (R := R) (X := X) n) :
    (deg_n_to_finsupp n f).support.image (Subtype.val) ⊆ X := by
  intro x hx
  simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hx
  obtain ⟨hx, _⟩ := hx
  exact hx

-- Show that support of deg_n_to_finsupp has the size of n
lemma deg_n_to_choose_n_card_n (f : ml_pol_deg_n_set (R := R) (X := X) n) :
    #((deg_n_to_finsupp n f).support.image (Subtype.val)) = n := by
  rw [card_image_iff.mpr Set.injOn_subtype_val,
    ← pol_power_shrink_support_linear (deg_n_to_finsupp n f)]
  simp only [← deg_n_to_deg_eq_n n f, deg_n_to_finsupp_spec n f, ne_eq,
    one_ne_zero, not_false_eq_true, MvPolynomial.totalDegree_monomial]
  exact card_pol_power_shrink_support (deg_n_to_finsupp n f)

/-deg_n_to_choose_n send a polynomial to its degree finsupp, which is in powersetCard n X.-/
noncomputable def deg_n_to_choose_n (f : ml_pol_deg_n_set (R := R) (X := X) n) :
    powersetCard n X := ⟨(deg_n_to_finsupp n f).support.image (Subtype.val), by
  simp [Finset.mem_powersetCard, deg_n_to_choose_n_sub_X, deg_n_to_choose_n_card_n]⟩

-- Show that deg_n_to_choose_n is injective
lemma deg_n_to_choose_n_inj : Function.Injective (deg_n_to_choose_n (R := R) (X := X) n) := by
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

noncomputable instance : Fintype (ml_pol_deg_n_set (R := R) (X := X) n) := by
  refine Set.Finite.fintype ?_
  exact Finite.of_injective (deg_n_to_choose_n (X := X) n) (deg_n_to_choose_n_inj (X := X) n)

-- Show that deg_n_to_choose_n is surjective
lemma deg_n_to_choose_n_suj : Function.Surjective (deg_n_to_choose_n (R := R) (X := X) n) := by
  intro y
  let S : X →₀ ℕ := Finsupp.ofSupportFinite (fun x => if x.1 ∈ y.1 then 1 else 0) (
    Set.toFinite (Function.support fun (x : X) => if x.1 ∈ y.1 then 1 else 0))
  have hSdef (x : X) : S x = (fun x => if x.1 ∈ y.1 then 1 else 0) x := rfl
  have hS : (pol_power_shrink S) = S := by
    ext x
    simp [pol_power_shrink_spec, hSdef]
  have hyx := (Finset.mem_powersetCard.mp y.2).left
  have hSy : S.support.image Subtype.val = y := by aesop
  let f1 := MvPolynomial.monomial (R := R) (pol_power_shrink S) 1
  let f : (ml_pol_deg_n_set (R := R) n) := ⟨f1, ml_pol_deg_n_set_mem_def n f1 (by
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
lemma deg_n_to_choose_n_bij : Function.Bijective (deg_n_to_choose_n (R := R) (X := X) n) :=
  ⟨deg_n_to_choose_n_inj n, deg_n_to_choose_n_suj n⟩

-- Using the bijection to show that the card of (ml_pol_deg_n_set n) is (#X).choose n
lemma card_ml_pol_deg_n_set : #(ml_pol_deg_n_set (R := R) (X := X) n).toFinset
    = Nat.choose #X n := calc
  _ = Fintype.card (ml_pol_deg_n_set (X := X) n) := by apply Set.toFinset_card
  _ = Fintype.card (powersetCard n X) := Fintype.card_of_bijective (deg_n_to_choose_n_bij n)
  _ = #(powersetCard n X) := Fintype.card_coe (powersetCard n X)
  _ = _ := card_powersetCard n X

-- ml_pol_deg_le_n_set is the set of all multilinear polynomials of degree less than or equal to n
def ml_pol_deg_le_n_set : Set (MvPolynomial X R) :=
  {f | f.totalDegree ≤ n ∧ ∃ S : X →₀ ℕ, f = MvPolynomial.monomial (pol_power_shrink S) 1}

omit [DecidableEq α] in
lemma ml_pol_deg_le_n_set_zero (hn0 : n = 0): ml_pol_deg_le_n_set (R := R) (X := X) n = {1} := by
  unfold ml_pol_deg_le_n_set
  subst hn0
  ext f
  simp only [nonpos_iff_eq_zero, Set.mem_setOf_eq, Set.mem_singleton_iff]
  have h1 : (MvPolynomial.monomial 0) 1 = (1 : MvPolynomial X R) := by simp
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
    rw [pol_power_shrink_spec]
    simp

-- show that (ml_pol_deg_n_set n)'s are parwise disjoint for different degree n
lemma disjoint_ml_pol_deg_n_set :
    (Finset.range (n + 1)).toSet.PairwiseDisjoint
    (fun m => (ml_pol_deg_n_set (R := R) (X := X) m).toFinset) := by
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
      (disjoint_ml_pol_deg_n_set (R := R) n)).toSet := by
    ext f
    simp only [ml_pol_deg_le_n_set, Set.mem_setOf_eq, ml_pol_deg_n_set, coe_disjiUnion, coe_range,
      Set.mem_Iio, Set.coe_toFinset, Set.mem_iUnion, exists_and_left, exists_prop, exists_eq_left',
      and_congr_left_iff, forall_exists_index]
    intro _ _
    exact Iff.symm Nat.lt_add_one_iff

noncomputable instance : Fintype (ml_pol_deg_le_n_set (R := R) (X := X) n) := by
  rw [multilinear_set_union_by_deg]
  apply FinsetCoe.fintype

/- Show that Ω_multilinear_set is indeed the multilinear polynomial with degree ≤ n in the
perspective of function from Ω to ℝ by pol_to_eval (the function of evaluation).-/
omit [DecidableEq α] in
lemma Ω_multilinear_set_eq : Ω_multilinear_set (R := R) (X := X) n = pol_to_eval ''
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

noncomputable instance : Fintype (Ω_multilinear_set (R := R) (X := X) n) := by
  rw [Ω_multilinear_set_eq]
  apply Fintype.ofFinite

-- Show that this "function of evaluation" is in fact bijective.
lemma pol_to_eval_bij : Set.BijOn (β := @Ω R _ α X → R) pol_to_eval
    (ml_pol_deg_le_n_set n) (Ω_multilinear_set (X := X) n) := by
  simp only [pol_to_eval, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
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
    let a : X → R := fun w => if w = x then 0 else 1
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
    ml_pol_deg_le_n_set (R := R) (X := X) n ≃ Ω_multilinear_set (R := R) (X := X) n :=
  Set.BijOn.equiv pol_to_eval (pol_to_eval_bij (X := X) n)

/- This theorem shows that the number of all multilinear monic monomials with degree n is
∑ m ∈ Finset.range (n + 1), Nat.choose #X m.-/
theorem card_ml_pol_deg_le_n_set : #(ml_pol_deg_le_n_set (R := R) (X := X) n).toFinset
    = ∑ m ∈ Finset.range (n + 1), Nat.choose #X m := calc
  _ = #((Finset.range (n + 1)).disjiUnion (fun m => (ml_pol_deg_n_set (X := X) m).toFinset)
      (disjoint_ml_pol_deg_n_set n)) := by
    congr
    simp only [multilinear_set_union_by_deg]
    simp
  _ = ∑ m ∈ Finset.range (n + 1), Nat.choose #X m := by
    rw [Finset.card_disjiUnion]
    congr
    ext m
    exact card_ml_pol_deg_n_set m

/- This theorem shows that the number of all functions of multilinear monic monomials with
degree n is ∑ m ∈ Finset.range (n + 1), Nat.choose #X m.-/
theorem card_Ω_multilinear_set : #(Ω_multilinear_set (R := R) (X := X) n).toFinset
    = ∑ m ∈ Finset.range (n + 1), Nat.choose #X m := by
  rw [← card_ml_pol_deg_le_n_set (R := R)]
  have h := pol_to_eval_bij (R := R) (X := X) n
  simp only [Set.toFinset_card]
  apply Fintype.card_congr
  exact (ml_equiv_Ω_ml n).symm

-- The span of Ω_multilinear_set
def Ω_multilinear_span : Submodule R (@Ω R _ α X → R) := Submodule.span R (Ω_multilinear_set #L)

-- Show that any monomials of degree no greater than #L is in the span of Ω_multilinear_set.
omit [DecidableEq α] in
theorem monomial_in_Ω_span (v : X →₀ ℕ) (hv : (v.sum fun x e ↦ e) ≤ #L):
    pol_to_eval (MvPolynomial.monomial (R := R) v 1) ∈ Ω_multilinear_span L := by
  unfold Ω_multilinear_span
  suffices pol_to_eval ((MvPolynomial.monomial v) (1 : R)) ∈ (Ω_multilinear_set (X := X) #L) by
    exact Submodule.mem_span.mpr fun p a ↦ a this
  simp only [Ω_multilinear_set, Set.mem_image]
  use (MvPolynomial.monomial v) 1
  constructor
  · simp only [Set.mem_setOf_eq, ne_eq, one_ne_zero, not_false_eq_true,
      MvPolynomial.totalDegree_monomial, MvPolynomial.monomial_left_inj, exists_eq', and_true]
    exact hv
  · rfl

omit [DecidableEq α] in
lemma Ω_multilinear_span_deg_le_mem (f : MvPolynomial X R) (hdeg : f.totalDegree ≤ #L) :
    pol_to_eval f ∈ Ω_multilinear_span (X := X) L := by
  rw [MvPolynomial.as_sum f, map_sum]
  apply Submodule.sum_mem
  intro v hv
  have hsmul (a : R): (MvPolynomial.monomial v a) =
    a • (MvPolynomial.monomial v 1) := by
    rw [@MvPolynomial.smul_monomial]
    simp
  suffices pol_to_eval ((MvPolynomial.monomial v) (1 : R)) ∈ Ω_multilinear_span L by
    rw [hsmul, map_smul]
    exact Submodule.smul_mem (Ω_multilinear_span L) (MvPolynomial.coeff v f) this
  apply monomial_in_Ω_span
  refine le_trans ?_ hdeg
  apply MvPolynomial.le_totalDegree
  exact hv

-- Show that the rank of the span of Ω_multilinear_set is = its cardinality
lemma dim_Ω_multilinear_span : Module.rank R (Ω_multilinear_span (R := R) (X := X) L) ≤
    ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  have h := rank_span_finset_le (R := R) (Ω_multilinear_set (R := R) (X := X) #L).toFinset
  rw [Set.coe_toFinset] at h
  rw [← card_Ω_multilinear_set (R := R)]
  exact h

variable (hF : ∀ A ∈ F, A ⊆ X)

namespace Frankl_Wilson

-- The characteristic polynomial of a set A
noncomputable def char_pol (A : F) : MvPolynomial X R :=
  ∏ l ∈ L with l < #A.val, (∑ m : X, ((char_vec (R := R) A (hF A A.2) m) • (MvPolynomial.X m))
  - (MvPolynomial.C l : MvPolynomial X R) )

-- Show that the total degree of the characteristic polynomial is no greater than #L
lemma char_pol_degree (A : F): (char_pol (R := R) L hF A).totalDegree ≤ #L := by
  unfold char_pol
  have hAX := hF A A.2
  have h : (∑ m, (char_vec (R := R) A hAX m) • MvPolynomial.X m : MvPolynomial X R).totalDegree
      ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro x hx
    calc
    _ ≤ (MvPolynomial.X x).totalDegree := MvPolynomial.totalDegree_smul_le
      (char_vec (R := R) A hAX x) (MvPolynomial.X x : MvPolynomial X R)
    _ = 1 := by apply MvPolynomial.totalDegree_X
  have h (l : ℕ): (∑ m, char_vec (R := R) A hAX m • MvPolynomial.X m
      - (MvPolynomial.C l : MvPolynomial X R)).totalDegree ≤ 1 := calc
    _ = (∑ m, char_vec (R := R) A hAX m • MvPolynomial.X m
      + (MvPolynomial.C (-l) : MvPolynomial X R)).totalDegree := by
        rw [MvPolynomial.C_neg, Mathlib.Tactic.RingNF.add_neg]
    _ ≤ max
      (∑ m, char_vec (R := R) A hAX m • MvPolynomial.X m : MvPolynomial X R).totalDegree
      (MvPolynomial.C (-l) : MvPolynomial X R).totalDegree := by
      apply MvPolynomial.totalDegree_add
    _ ≤ _ := by
      simp only [MvPolynomial.totalDegree_C, zero_le, sup_of_le_left]
      exact h
  calc
  _ ≤ ∑ l ∈ L with l < #A.val,
    (∑ m : X, (char_vec (R := R) A hAX m) • MvPolynomial.X m
    - (MvPolynomial.C l : MvPolynomial X R)).totalDegree := by
    apply MvPolynomial.totalDegree_finset_prod
  _ ≤ ∑ l ∈ L with l < #A.val, 1 := by exact sum_le_sum fun i_1 a ↦ h i_1
  _ = #{l ∈ L | l < #A.val} := (card_eq_sum_ones {l ∈ L | l < #A.val}).symm
  _ ≤ _ := card_filter_le L fun l ↦ l < #A.val

-- Rewrite the evaluation of characteristic polynomial as a function
lemma char_pol_eval_eq (A : F) (x : X → R): (char_pol L hF A).eval x
    = ∏ l ∈ L with l < #A.val, ((char_vec A (hF A A.2)) ⬝ᵥ x - l) := by
  unfold char_pol
  rw [@MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro l hl
  simp [(· ⬝ᵥ ·)]

-- Ω_char_pol translates characteristic polynomials to the function from Ω to ℝ via pol_to_eval
noncomputable def Ω_char_pol (A : F) (x : @Ω R _ α X): R := (char_pol L hF A).eval x

-- This lemma gives a more handy definition of Ω_char_pol
lemma Ω_char_pol_eq (A : F) : Ω_char_pol L hF A = pol_to_eval (char_pol (R := R) L hF A) := rfl

-- Ω_char_pol_span is the span of all characteristic polynomials
def Ω_char_pol_span : Submodule R (@Ω R _ α X → R) := Submodule.span R (Set.range (Ω_char_pol L hF))

-- Show that the characteristic polynomial is also in the span of Ω_multilinear_set.
lemma Ω_char_pol_spec (A : F): Ω_char_pol L hF A ∈ Ω_multilinear_span (R := R) L := by
  rw [Ω_char_pol_eq]
  exact Ω_multilinear_span_deg_le_mem L (char_pol L hF A) (char_pol_degree L hF A)

-- Show that the span of the characteristic polynomial is included in the span of Ω_multilinear_set.
lemma span_to_R_le_span_ml : (Ω_char_pol_span L hF) ≤ Ω_multilinear_span (R := R) L := by
  unfold Ω_char_pol_span
  suffices Set.range (Ω_char_pol (R := R) L hF) ⊆ (Ω_multilinear_span (R := R) (X := X) L) by
    exact Submodule.span_le.mpr this
  intro x hx
  rw [@Set.mem_range] at hx
  obtain ⟨y, hy⟩ := hx
  subst hy
  exact Ω_char_pol_spec L hF y

-- Show that the rank of the characteristic polynomial is ≤ the cardinality of Ω_multilinear_set.
lemma dim_span_to_R_le : Module.rank R (Ω_char_pol_span (R := R) L hF)
    ≤ ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m:= by
  exact Preorder.le_trans (Module.rank R (Ω_char_pol_span L hF))
    (Module.rank R (Ω_multilinear_span (X := X) L))
    (↑(∑ m ∈ range (#L + 1), (#X).choose m))
    (Submodule.rank_mono (span_to_R_le_span_ml L hF)) (dim_Ω_multilinear_span L)

-- Show that the characteristic polynomials are in fact linear independent
lemma Ω_char_pol_lin_indep (hintersect : weak_intersecting F L)
    (hspec1 : ∀ A : F , (char_pol (R := R) L hF A).eval (char_vec A (hF A A.2)) ≠ 0)
    (hspec2 : ∀ A B : F , A ≠ B → #B.val ≤ #A.val
    → (char_pol (R := R) L hF A).eval (char_vec B (hF B B.2)) = 0):
    LinearIndependent R (Ω_char_pol (R := R) L hF):= by
  rw [← linearIndepOn_univ]
  apply sorted_linearIndepOn (R := R) (Sn := fun x => #x.val)
  intro f _
  use Ω_char_vec f.val (hF f f.2)
  constructor
  · exact hspec1 f
  · intro g _ hfleg hfneg
    rw [Nat.cast_le] at hfleg
    simp only [Function.mem_support, ne_eq, not_not]
    exact hspec2 g f hfneg.symm hfleg

section Frankl_Wilson_Real

-- Show that the characteristic polynomial is non-zero for the characteristic vector of A.
lemma char_pol_spec_1 (A : F) : (char_pol (R := ℝ) L hF A).eval (char_vec A (hF A A.2)) ≠ 0 := by
  rw [char_pol_eval_eq L hF A (char_vec A (hF A A.2))]
  refine prod_ne_zero_iff.mpr ?_
  intro a ha
  rw [char_vec_spec, inter_self]
  norm_cast
  rw [Int.subNat_eq_zero_iff]
  rw [@mem_filter] at ha
  exact Nat.ne_of_lt' ha.2

/- Show that the characteristic polynomial is zero for
the characteristic vector of B with lower cardinality.-/
lemma char_pol_spec_2 (hintersect : weak_intersecting F L)
    (A B : F) (hneq : A ≠ B) (hji : #B.val ≤ #A.val) :
    (char_pol (R := ℝ) L hF A).eval (char_vec B (hF B B.2)) = 0 := by
  rw [char_pol_eval_eq L hF A (char_vec B (hF B B.2))]
  unfold weak_intersecting at hintersect
  refine prod_eq_zero_iff.mpr ?_
  use #(A.val ∩ B.val)
  rw [char_vec_spec, sub_self, propext (and_iff_left rfl), mem_filter]
  constructor
  · refine hintersect A A.2 B B.2 ?_
    exact Subtype.coe_ne_coe.mpr hneq
  · refine card_lt_card ?_
    rw [@Finset.ssubset_iff_subset_ne]
    constructor
    · exact inter_subset_left
    · rw [ne_eq, inter_eq_left]
      by_contra hcon
      have h := eq_of_subset_of_card_le hcon hji
      simp only [@SetCoe.ext_iff] at h
      exact hneq h

-- Theorem 1.3
theorem Frankl_Wilson_intersecting (hF : ∀ A ∈ F, A ⊆ X) (hintersect : weak_intersecting F L):
    #F ≤ ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  have h := linearIndependent_span (Ω_char_pol_lin_indep L hF hintersect (char_pol_spec_1 L hF)
    (char_pol_spec_2 L hF hintersect))
  apply LinearIndependent.cardinal_le_rank at h
  rw [Cardinal.mk_fintype, Fintype.card_coe] at h
  exact Nat.cast_le.mp (le_trans h (dim_span_to_R_le L hF))

end Frankl_Wilson_Real

/-
def modulo_intersecting {m : ℕ} (p : ℕ) [hp : Fact p.Prime] (F: Fin m → (Finset α))
    (hFNodup : Function.Injective F) (L : Fin m → Finset ℕ)
    (hL : ∀ i, (L i) ⊆ Finset.range p) := ∀ i, (#(F i) : ZMod p) ∉ (fun x => Nat.cast x) '' (L i)
  ∧ ∀ j, j < i → (#((F i) ∩ (F j)) : ZMod p) ∈ (fun x => Nat.cast x) '' (L i)

-- Show that the characteristic polynomial is non-zero for the characteristic vector of A.
lemma char_pol_spec_1 (A : F) : (char_pol (R := R) L hF A).eval (char_vec A (hF A A.2)) ≠ 0 := by
  rw [char_pol_eval_eq L hF A (char_vec A (hF A A.2))]
  refine prod_ne_zero_iff.mpr ?_
  intro a ha
  rw [char_vec_spec, inter_self]
  norm_cast
  rw [Int.subNat_eq_zero_iff]
  rw [@mem_filter] at ha
  exact Nat.ne_of_lt' ha.2

/- Show that the characteristic polynomial is zero for
the characteristic vector of B with lower cardinality.-/
lemma char_pol_spec_2 (hintersect : intersecting F L)
    (A B : F) (hneq : A ≠ B) (hji : #B.val ≤ #A.val) :
    (char_pol (R := ℝ) L hF A).eval (char_vec B (hF B B.2)) = 0 := by
  rw [char_pol_eval_eq L hF A (char_vec B (hF B B.2))]
  unfold intersecting at hintersect
  refine prod_eq_zero_iff.mpr ?_
  use #(A.val ∩ B.val)
  rw [char_vec_spec, sub_self, propext (and_iff_left rfl), mem_filter]
  constructor
  · refine hintersect A A.2 B B.2 ?_
    exact Subtype.coe_ne_coe.mpr hneq
  · refine card_lt_card ?_
    rw [@Finset.ssubset_iff_subset_ne]
    constructor
    · exact inter_subset_left
    · rw [ne_eq, inter_eq_left]
      by_contra hcon
      have h := eq_of_subset_of_card_le hcon hji
      simp only [@SetCoe.ext_iff] at h
      exact hneq h

theorem Frankl_Wilson_intersecting_generalized {m : ℕ} {p : ℕ} [hp : Fact p.Prime]
    {F: Fin m → (Finset α)} (hF : ∀ i, (F i) ⊆ X) {hFNodup : Function.Injective F}
    {L : Fin m → Finset ℕ} {hL : ∀ i, (L i) ⊆ Finset.range p}
    (hintersect : modulo_intersecting p F hFNodup L hL)
    {s : ℕ} (hLs : ∀ i, #(L i) ≤ s): m ≤ ∑ j ∈ Finset.range (s + 1), Nat.choose #X j := by
  sorry
-/
/-
noncomputable def F_sorted : Fin #F → (Finset α) :=
  fun i => (F.toList.mergeSort fun a b => #a ≤ #b)[i]

omit [DecidableEq α] in
lemma F_sorted_subst_X (hF : ∀ A ∈ F, A ⊆ X) : ∀ i : Fin #F, (F_sorted i) ⊆ X := by
  intro i
  apply hF
  rw [← Finset.mem_toList, ← List.mem_mergeSort]
  exact List.mem_of_getElem rfl

omit [DecidableEq α] in
lemma F_sorted_pair_get : ∀ (i j : Fin #F), i < j → F_sorted i ≠ F_sorted j:= by
  have h : (F.toList.mergeSort fun a b => #a ≤ #b).Nodup :=
    List.nodup_mergeSort.mpr (Finset.nodup_toList F)
  unfold List.Nodup at h
  rw [@List.pairwise_iff_get] at h
  intro i j
  exact h ⟨i, by simp⟩ ⟨j, by simp⟩

omit [DecidableEq α] in
lemma F_sorted_inj : Function.Injective (F_sorted : Fin #F → (Finset α)) := by
  unfold F_sorted
  intro a b hab
  simp only at hab
  by_contra hcon
  rw [← Ne.eq_def, ne_iff_lt_or_gt] at hcon
  rcases hcon with hl | hr
  · exact F_sorted_pair_get ⟨a, by simp⟩ ⟨b, by simp⟩ hl hab
  · exact F_sorted_pair_get ⟨b, by simp⟩ ⟨a, by simp⟩ hr hab.symm

noncomputable instance {i : Fin #F} : Fintype {l | l ∈ L ∧ l < #(F_sorted i)} :=
  (Set.fintypeSep L (fun l => l < #(F_sorted i)))

noncomputable def L_sorted : Fin #F → Finset ℕ := fun i => {l | l ∈ L ∧ l < #(F_sorted i)}.toFinset
-/
end Frankl_Wilson

theorem Lemma_2_1 (f : @Ω R _ α X → R) (hf : ∀ I , (hI : I ⊆ X) → #I ≤ n
    → f (Ω_char_vec I hI) ≠ 0) : LinearIndepOn R (fun I => pol_to_eval I * f)
    (ml_pol_deg_le_n_set (R := R) (X := X) n):= by
  apply sorted_linearIndepOn (R := R) (Sn := fun x => x.totalDegree)
  intro p1 hp1
  simp only [ml_pol_deg_le_n_set, Set.mem_setOf_eq] at hp1
  obtain ⟨hp1d, Sp1, rfl⟩ := hp1
  have hp1spec : image Subtype.val Sp1.support ⊆ X := by
    intro x
    simp only [mem_image, Finsupp.mem_support_iff, ne_eq, Subtype.exists, exists_and_right,
      exists_eq_right, forall_exists_index]
    exact fun x_1 h ↦ x_1
  use Ω_char_vec (image Subtype.val Sp1.support) hp1spec
  simp_all only [ne_eq, one_ne_zero, not_false_eq_true, MvPolynomial.totalDegree_monomial, ←
    card_pol_power_shrink_support, pol_power_shrink_support_linear, pol_to_eval_monomial_eq,
    Function.mem_support, Pi.mul_apply, ite_mul, one_mul, zero_mul, ite_eq_right_iff,
    Classical.not_imp, mul_eq_zero, not_or, not_and, not_not]
  constructor
  · constructor
    · intro a ha
      simp only [mem_coe, Finsupp.mem_support_iff, ne_eq] at ha
      simp [Ω_char_vec, char_vec, ha]
    · apply hf (image Subtype.val Sp1.support) hp1spec
      refine le_of_eq_of_le ?_ hp1d
      refine card_eq_of_equiv (Equiv.ofBijective (fun x => ⟨x.1, by simp only [mem_image,
        Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, coe_mem,
        exists_const]⟩) ?_).symm
      constructor
      · intro a b hab
        aesop
      · intro a
        use ⟨⟨a, hp1spec a.2⟩, by
          have := a.2
          rw [@mem_image] at this
          obtain ⟨b, ⟨hb, hbe⟩⟩ := this
          simp only [← hbe, hb]⟩
  · intro p2 hp2
    simp only [ml_pol_deg_le_n_set, Set.mem_setOf_eq] at hp2
    obtain ⟨hp2d, Sp2, rfl⟩ := hp2
    simp_all only [ne_eq, one_ne_zero, not_false_eq_true, MvPolynomial.totalDegree_monomial, ←
      card_pol_power_shrink_support, pol_power_shrink_support_linear, Nat.cast_le, and_true,
      MvPolynomial.monomial_left_inj, pol_to_eval_monomial_eq, ite_eq_right_iff, Classical.not_imp]
    intro hp12 hneq hi
    simp only [not_iff_not, ← pol_power_shrink_support_eq_iff] at hneq
    have hneg : (Ω_char_vec (R := R) (image Subtype.val Sp1.support) hp1spec).1.support
        = Sp1.support := by ext x; simp [Ω_char_vec, char_vec, not_iff_not]
    rw [hneg, coe_subset] at hi
    exfalso
    exact hneq (eq_of_subset_of_card_le hi hp12).symm

namespace Ray_Chaudhuri_Wilson



-- The characteristic polynomial of a set A
noncomputable def char_pol (A : F) : MvPolynomial X R :=
  ∏ l ∈ L with l < #A.val, (∑ m : X, ((char_vec (R := R) A (hF A A.2) m) • (MvPolynomial.X m))
  - (MvPolynomial.C l : MvPolynomial X R) )

-- Show that the total degree of the characteristic polynomial is no greater than #L
lemma char_pol_degree (A : F): (char_pol (R := R) L hF A).totalDegree ≤ #L := by
  unfold char_pol
  have hAX := hF A A.2
  have h : (∑ m, (char_vec (R := R) A hAX m) • MvPolynomial.X m : MvPolynomial X R).totalDegree
      ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro x hx
    calc
    _ ≤ (MvPolynomial.X x).totalDegree := MvPolynomial.totalDegree_smul_le
      (char_vec (R := R) A hAX x) (MvPolynomial.X x : MvPolynomial X R)
    _ = 1 := by apply MvPolynomial.totalDegree_X
  have h (l : ℕ): (∑ m, char_vec (R := R) A hAX m • MvPolynomial.X m
      - (MvPolynomial.C l : MvPolynomial X R)).totalDegree ≤ 1 := calc
    _ = (∑ m, char_vec (R := R) A hAX m • MvPolynomial.X m
      + (MvPolynomial.C (-l) : MvPolynomial X R)).totalDegree := by
        rw [MvPolynomial.C_neg, Mathlib.Tactic.RingNF.add_neg]
    _ ≤ max
      (∑ m, char_vec (R := R) A hAX m • MvPolynomial.X m : MvPolynomial X R).totalDegree
      (MvPolynomial.C (-l) : MvPolynomial X R).totalDegree := by
      apply MvPolynomial.totalDegree_add
    _ ≤ _ := by
      simp only [MvPolynomial.totalDegree_C, zero_le, sup_of_le_left]
      exact h
  calc
  _ ≤ ∑ l ∈ L with l < #A.val,
    (∑ m : X, (char_vec (R := R) A hAX m) • MvPolynomial.X m
    - (MvPolynomial.C l : MvPolynomial X R)).totalDegree := by
    apply MvPolynomial.totalDegree_finset_prod
  _ ≤ ∑ l ∈ L with l < #A.val, 1 := by exact sum_le_sum fun i_1 a ↦ h i_1
  _ = #{l ∈ L | l < #A.val} := (card_eq_sum_ones {l ∈ L | l < #A.val}).symm
  _ ≤ _ := card_filter_le L fun l ↦ l < #A.val

-- Rewrite the evaluation of characteristic polynomial as a function
lemma char_pol_eval_eq (A : F) (x : X → R): (char_pol L hF A).eval x
    = ∏ l ∈ L with l < #A.val, ((char_vec A (hF A A.2)) ⬝ᵥ x - l) := by
  unfold char_pol
  rw [@MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro l hl
  simp [(· ⬝ᵥ ·)]

noncomputable def F_indexed := (Finset.equivFinOfCardEq (n := #F) rfl).symm

-- Ω_char_pol translates characteristic polynomials to the function from Ω to ℝ via pol_to_eval
noncomputable def Ω_char_pol (i : Fin #F) (x : @Ω ℝ _ α X): ℝ :=
  (char_pol L hF (F_indexed i)).eval x

-- This lemma gives a more handy definition of Ω_char_pol
lemma Ω_char_pol_eq (i : Fin #F) : Ω_char_pol L hF i
    = pol_to_eval (char_pol L hF (F_indexed i)) := rfl

-- Show that the characteristic polynomial is also in the span of Ω_multilinear_set.
lemma Ω_char_pol_spec (i : Fin #F): Ω_char_pol L hF i ∈ Ω_multilinear_span L := by
  rw [Ω_char_pol_eq]
  exact Ω_multilinear_span_deg_le_mem L (char_pol L hF _) (char_pol_degree L hF _)

-- Show that the characteristic polynomial is non-zero for the characteristic vector of A.
lemma char_pol_spec_1 (i : Fin #F): Ω_char_pol L hF i
    (Ω_char_vec _ (hF _ (F_indexed i).2)) ≠ 0 := by
  suffices (char_pol (R := ℝ) L hF (F_indexed i)).eval (char_vec _ (hF _ (F_indexed i).2)) ≠ 0 by
    unfold Ω_char_pol Ω_char_vec
    exact this
  rw [char_pol_eval_eq L hF _ (char_vec _ (hF _ (F_indexed i).2))]
  refine prod_ne_zero_iff.mpr ?_
  intro a ha
  rw [char_vec_spec]
  norm_cast
  rw [inter_self, Int.subNat_eq_zero_iff]
  simp only [ne_eq, mem_filter] at ha
  exact Nat.ne_of_lt' ha.2

/- Show that the characteristic polynomial is zero for
the characteristic vector of B with lower cardinality.-/
lemma char_pol_spec_2 (hintersect : weak_intersecting F L)
    (i j : Fin #F) (hneq : i ≠ j) (hji : #(F_indexed j).val ≤ #(F_indexed i).val) :
    Ω_char_pol L hF i (Ω_char_vec _ (hF _ (F_indexed j).2)) = 0 := by
  unfold weak_intersecting at hintersect
  let A := (F_indexed i)
  let B := (F_indexed j)
  suffices (char_pol L hF A).eval (char_vec B (hF B B.2)) = (0 : ℝ) by
    simp only [Ω_char_pol, Ω_char_vec, this, B, A]
  have hneq : A ≠ B := by
    by_contra hcon
    exact hneq (Equiv.injective F_indexed hcon)
  rw [char_pol_eval_eq L hF A (char_vec B (hF B B.2))]
  refine prod_eq_zero_iff.mpr ?_
  use #(A.val ∩ B.val)
  rw [char_vec_spec, sub_self, propext (and_iff_left rfl), mem_filter]
  constructor
  · refine hintersect A A.2 B B.2 ?_
    exact Subtype.coe_ne_coe.mpr hneq
  · refine card_lt_card ?_
    rw [@Finset.ssubset_iff_subset_ne]
    constructor
    · exact inter_subset_left
    · rw [ne_eq, inter_eq_left]
      by_contra hcon
      have h := eq_of_subset_of_card_le hcon hji
      simp only [@SetCoe.ext_iff] at h
      exact hneq h

variable {K : Finset ℕ}

noncomputable def K_indexed (K : Finset ℕ) := Fintype.equivFinOfCardEq
    (h := ((by simp) : Fintype.card K = #K)).symm

noncomputable def swallow_pol (I : (@ml_pol_deg_le_n_set ℝ _ _ (#L - #K) X)) :=
  (I.val) * ∏ i : Fin #K, ((∑ j : X, (MvPolynomial.X (R := ℝ) j)) - K_indexed K i)

omit [DecidableEq α] in
lemma swallow_pol_degree (hL : #K ≤ #L) (I : (@ml_pol_deg_le_n_set ℝ
    _ _ (#L - #K) X)) : (swallow_pol L I).totalDegree ≤ #L := by
  suffices I.val.totalDegree + (∏ i : Fin #K,
      ((∑ j : X, (MvPolynomial.X (R := ℝ) j)) - K_indexed K i)).totalDegree ≤ #L by
    refine le_trans ?_ this
    apply MvPolynomial.totalDegree_mul
  have hI := I.2
  simp only [ml_pol_deg_le_n_set, Set.mem_setOf_eq] at hI
  suffices (∏ i : Fin #K,
      ((∑ j : X, (MvPolynomial.X (R := ℝ) j)) - K_indexed K i)).totalDegree ≤ #K by
    have hans := add_le_add hI.left this
    obtain ⟨lpred, hlp⟩ := Nat.exists_eq_add_of_le hL
    simp only [univ_eq_attach, hlp, add_tsub_cancel_left] at hans
    rw [Nat.add_comm] at hlp
    rwa [← hlp] at hans
  suffices ∀ i, ((∑ j : X, (MvPolynomial.X (R := ℝ) j)) - K_indexed K i).totalDegree ≤ 1 by
    calc
    _ ≤ ∑ i, (∑ j : X, MvPolynomial.X (R := ℝ) j - ((K_indexed K) i)).totalDegree := by
      apply MvPolynomial.totalDegree_finset_prod
    _ ≤ ∑ i : Fin #K, 1 := by
      apply Finset.sum_le_sum
      simpa only [mem_univ, this, forall_const]
    _ = #K := by simp
  intro i
  calc
  _ = (∑ j : X, MvPolynomial.X j - MvPolynomial.C (R := ℝ) (K_indexed K i)).totalDegree := by
    rw [map_natCast]
  _ = (∑ j : X, MvPolynomial.X j + (MvPolynomial.C (-K_indexed K i)
      : MvPolynomial X ℝ)).totalDegree := by rw [MvPolynomial.C_neg, Mathlib.Tactic.RingNF.add_neg]
  _ ≤ max (∑ j, MvPolynomial.X j).totalDegree (MvPolynomial.C
      (-K_indexed K i : ℝ)).totalDegree := by apply MvPolynomial.totalDegree_add
  _ = (∑ j : X, MvPolynomial.X (R := ℝ) j).totalDegree := by
    simp only [MvPolynomial.totalDegree_C, univ_eq_attach, zero_le, sup_of_le_left]
  _ ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    simp

noncomputable def ml_pol_deg_le_n_indexed := Fintype.equivFinOfCardEq
  (h :=  ((by simp only [Set.toFinset_card]) :
      Fintype.card (@ml_pol_deg_le_n_set ℝ _ _ (#L - #K) X)
    = #(@ml_pol_deg_le_n_set ℝ _ _ (#L - #K) X).toFinset)).symm

-- Ω_char_pol translates characteristic polynomials to the function from Ω to ℝ via pol_to_eval
noncomputable def Ω_swallow_pol (i : Fin #(@ml_pol_deg_le_n_set ℝ _ _ (#L - #K) X).toFinset)
    (x : @Ω ℝ _ α X): ℝ := (swallow_pol L (ml_pol_deg_le_n_indexed L i)).eval x

-- Show that the characteristic polynomial is also in the span of Ω_multilinear_set.
lemma Ω_swallow_pol_spec (hL : #K ≤ #L) (i : Fin #(@ml_pol_deg_le_n_set ℝ _ _
    (#L - #K) X).toFinset) : Ω_swallow_pol L i ∈ Ω_multilinear_span L := by
  exact Ω_multilinear_span_deg_le_mem L _ (swallow_pol_degree L hL _)

-- This lemma gives a more handy definition of Ω_char_pol in preperation for lemma 2.1
lemma Ω_swallow_pol_eq (i : Fin #(@ml_pol_deg_le_n_set ℝ _ _ (#L - #K) X).toFinset) :
    Ω_swallow_pol L i = pol_to_eval ((ml_pol_deg_le_n_indexed L i).val)
    * pol_to_eval (∏ i : Fin #K, ((∑ j : X, (MvPolynomial.X (R := ℝ) j))
    - K_indexed K i) : MvPolynomial X ℝ) := calc
  _ = pol_to_eval (swallow_pol L (ml_pol_deg_le_n_indexed L i)) := rfl
  _ = _ := by simp [swallow_pol]

lemma set_val_mem_card_subNat_eq {I : Finset α} (hI : I ⊆ X):
    (#{x : X | x.val ∈ I}) - (n : ℝ) = #I - n := by
  congr 2
  have hequiv : {x : X | x.val ∈ I} ≃ I := by
    refine Equiv.ofBijective (fun a => ⟨a.1.1, by have h := a.2; rwa [Set.mem_setOf_eq] at h⟩) ?_
    constructor
    · intro a b hab
      aesop
    · intro a
      use ⟨⟨a, hI a.2⟩, by simp⟩
  apply Finset.card_eq_of_equiv
  simp only [univ_eq_attach, mem_filter, mem_attach, true_and]
  exact hequiv

lemma swallow_pol_spec (hu : weak_uniform F K L) (i : Fin #(@ml_pol_deg_le_n_set ℝ _ _ (#L - #K) X
    ).toFinset) (j : Fin #F) : (Ω_swallow_pol L i) (Ω_char_vec _ (hF _ (F_indexed j).2)) = 0 := by
  rw [Ω_swallow_pol_eq]
  simp only [map_prod, map_sub, map_sum, map_natCast, Pi.natCast_def, Pi.mul_apply, prod_apply,
    Pi.sub_apply, sum_apply, mul_eq_zero, prod_eq_zero_iff]
  apply Or.inr
  unfold pol_to_eval
  simp only [AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_sub, map_sum,
    MvPolynomial.eval_X, map_natCast, Pi.natCast_def, Pi.mul_apply, Pi.sub_apply, sum_apply,
    mul_eq_zero]
  unfold Ω_char_vec char_vec
  simp only [mem_val, sum_boole]
  have hcard : #((F_indexed j).1) ∈ F.image card := by
    rw [mem_image]
    use (F_indexed j)
    simp
  have hcard : ∃ a, (K_indexed K) a = #((F_indexed j).1) := by
    rw [← @Set.mem_range]
    suffices (F.image card) ⊆ (Set.range fun a ↦ ((K_indexed K) a : ℕ)).toFinset by
      have this := this hcard
      simpa using this
    unfold weak_uniform at hu
    suffices (Set.range fun a ↦ ((K_indexed K) a : ℕ)).toFinset = K by
      rw [← this] at hu
      exact hu.1
    calc
    _ = (Set.range (Subtype.val (α := ℕ) ∘ fun a ↦ ((K_indexed K) a))).toFinset := by congr
    _ = _ := by ext x; simp
  obtain ⟨a, ha⟩ := hcard
  use a
  --use ⟨, by ⟩
  rw [set_val_mem_card_subNat_eq (hI := hF _ (F_indexed j).2)]
  norm_cast
  rw [Int.subNat_eq_zero_iff]
  simp only [mem_univ, true_and]
  exact ha.symm

noncomputable def Ω_pol_family (K : Finset ℕ) :=
  Fin.append (Ω_char_pol L hF) (Ω_swallow_pol (K := K) L)

def Ω_pol_span (K : Finset ℕ) : Submodule ℝ (@Ω ℝ _ α X → ℝ) :=
  Submodule.span ℝ (Set.range (Ω_pol_family L hF K))

-- Show that the span of the characteristic polynomial is included in the span of Ω_multilinear_set.
lemma span_to_R_le_span_ml (hL : #K ≤ #L) : (Ω_pol_span L hF K) ≤ Ω_multilinear_span L := by
  unfold Ω_pol_span
  suffices Set.range (Ω_pol_family L hF K) ⊆ (Ω_multilinear_span (R := ℝ) (X := X) L) by
    exact Submodule.span_le.mpr this
  intro x hx
  simp only [@Set.mem_range, Ω_pol_family] at hx
  obtain ⟨y, rfl⟩ := hx
  unfold Fin.append Fin.addCases
  by_cases hym : y.val < #F
  · simp [hym, Ω_char_pol_spec]
  · simp [hym, Ω_swallow_pol_spec L hL]

-- Show that the rank of the characteristic polynomial is ≤ the cardinality of Ω_multilinear_set.
lemma dim_span_to_R_le (hL : #K ≤ #L) : Module.rank ℝ (Ω_pol_span L hF K)
    ≤ ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m:= by
  exact Preorder.le_trans (Module.rank ℝ (Ω_pol_span L hF K))
    (Module.rank ℝ (Ω_multilinear_span (X := X) L))
    (↑(∑ m ∈ range (#L + 1), (#X).choose m))
    (Submodule.rank_mono (span_to_R_le_span_ml L hF hL)) (dim_Ω_multilinear_span L)

lemma forall_fin_add {n m : ℕ} {P : Fin (n + m) → Prop} :
    (∀ i : Fin (n + m), P i) ↔
      (∀ i : Fin n, P (Fin.castAdd m i)) ∧ (∀ j : Fin m, P (Fin.natAdd n j)) := by
  constructor
  · intro h
    exact ⟨fun i => h (Fin.castAdd m i), fun j => h (Fin.natAdd n j)⟩
  · rintro ⟨h₁, h₂⟩ i
    by_cases hi : i.val < n
    · have : i = Fin.castAdd m ⟨i, hi⟩ := by simp [Fin.castAdd, hi]
      rw [this]
      exact h₁ ⟨i, hi⟩
    · let j : Fin m := ⟨i.val - n, by
        have : i.val < n + m := i.is_lt
        refine Nat.sub_lt_right_of_lt_add (not_lt.mp hi) ?_
        rwa [Nat.add_comm m n]⟩
      have : i = Fin.natAdd n j := by
        rw [Fin.natAdd]
        unfold j
        have := (Nat.sub_add_cancel (not_lt.mp hi)).symm
        rw [Nat.add_comm (i.val - n) n] at this
        simp [← this]
      rw [this]
      exact h₂ j

lemma Ω_pol_family_left_coeff_zero (hwuni : weak_uniform F K L) (g : Fin (#F +
    #(ml_pol_deg_le_n_set (#L - #K)).toFinset) → ℝ) (hg : ∑ i, g i • Ω_pol_family L hF K i = 0)
    (hleft0 : ∀ (i : Fin #F), g (Fin.castAdd (#(ml_pol_deg_le_n_set (#L - #K)).toFinset) i) = 0) :
    ∀ (j : Fin #(ml_pol_deg_le_n_set (#L - #K)).toFinset), g (Fin.natAdd (#F) j) = 0 := by
  simp only [Ω_pol_family, Fin.sum_univ_add, hleft0, Fin.append_left, zero_smul, sum_const_zero,
    Fin.append_right, zero_add] at hg
  let f := fun j => g (Fin.natAdd (#F) j)
  suffices f = 0 by exact fun j ↦ congrFun this j
  change ∑ x, f x • Ω_swallow_pol L x = 0 at hg
  simp only [Ω_swallow_pol_eq] at hg
  have hlin := Lemma_2_1 (#L - #K) (pol_to_eval (∏ i : Fin #K,
      ((∑ j : X, (MvPolynomial.X (R := ℝ) j)) - K_indexed K i : MvPolynomial X ℝ))) (by
    intro I hI hId
    by_contra hcon
    simp only [pol_to_eval, Ω_char_vec, map_prod, map_sub, map_sum, AlgHom.coe_mk, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, MvPolynomial.eval_X, map_natCast, Pi.natCast_def, prod_apply,
      Pi.sub_apply, sum_apply, char_vec, mem_val, sum_boole, prod_eq_zero_iff, mem_univ,
      true_and] at hcon
    obtain ⟨a, hcon⟩ := hcon
    rw [set_val_mem_card_subNat_eq (hI := hI)] at hcon
    norm_cast at hcon
    rw [Int.subNat_eq_zero_iff] at hcon
    have ha := ((K_indexed K) a).2
    simp only [← hcon] at ha
    unfold weak_uniform at hwuni
    have hk : #(image card F) ≤ #K := card_le_card hwuni.1
    have hId : #I ≤ #L - #(F.image card) := le_trans hId (by apply Nat.sub_le_sub_left hk)
    rw [← Nat.Simproc.add_le_gt 0 (hwuni.2 #I ha)]
    simp only [zero_add, hId])
  rw [← linearIndependent_set_coe_iff, linearIndependent_iff'ₛ] at hlin
  let f' := f ∘ (ml_pol_deg_le_n_indexed L).symm
  have hequiv : ∑ i, f' i • (pol_to_eval i * pol_to_eval (∏ i : Fin #K,
      ((∑ j : X, (MvPolynomial.X (R := ℝ) j)) - K_indexed K i : MvPolynomial X ℝ))) = ∑ x, f x
      • (pol_to_eval ((ml_pol_deg_le_n_indexed L) x) * pol_to_eval (∏ i : Fin #K,
      ((∑ j : X, (MvPolynomial.X (R := ℝ) j)) - K_indexed K i : MvPolynomial X ℝ))) := by
    apply Fintype.sum_equiv (e := (ml_pol_deg_le_n_indexed L).symm)
    simp [f']
  rw [← hequiv] at hg
  have := hlin Finset.univ f' 0
  simp only [Function.comp_apply, Pi.zero_apply, zero_smul, sum_const_zero, mem_univ, forall_const,
    Subtype.forall] at this
  have := this hg
  simp [f'] at this
  ext x
  have hx : ∃ w, (ml_pol_deg_le_n_indexed L).symm ((ml_pol_deg_le_n_indexed L) w) = x := by
    use x; simp
  obtain ⟨w, hw⟩ := hx
  simp only [← hw, Equiv.symm_apply_apply, Pi.zero_apply]
  simp [← this ((ml_pol_deg_le_n_indexed L) w) (by simp)]

lemma restrict_sum_linear {n m : ℕ} {α : Type u_1} {f : Fin n → ℝ} {g : Fin m → ℝ}
    {p : Fin n → α → ℝ} {q : Fin m → α → ℝ} {S : Set α}
    [Fintype S] : S.restrict (∑ x, f x • p x + ∑ x, g x • q x) =
      (∑ x, f x • S.restrict (p x)) + (∑ x, g x • S.restrict (q x)) := by
  ext ⟨a, ha⟩
  simp [Set.restrict_apply, Finset.sum_apply, Pi.add_apply, Pi.smul_apply]

lemma Finsupp_sum_eq_Fintype_sum_univ {R : Type u_1} [Semiring R] {M : Type u_2} [AddCommMonoid M]
    [Module R M] {s : Type u_3} [Fintype s] {f : s →₀ R} {g : s → M} :
    ∑ x ∈ f.support, f x • g x = ∑ x, f x • g x := by
  classical
  rw [← @Fintype.sum_extend_by_zero]
  congr
  ext x
  simp only [Finsupp.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff]
  intro h
  simp [h]

-- Show that the characteristic polynomials are in fact linear independent
lemma Ω_pol_family_lin_indep (hL : #K ≤ #L) (hinter : weak_intersecting F L)
    (hwuni : weak_uniform F K L) : LinearIndependent ℝ (Ω_pol_family L hF K):= by
  by_contra hcon
  rw [@Fintype.not_linearIndependent_iff] at hcon
  obtain ⟨g, hg, hi⟩ := hcon
  suffices ∀ i, g i = 0 by aesop
  rw [forall_fin_add]
  suffices (∀ (i : Fin #F), g
      (Fin.castAdd (#(ml_pol_deg_le_n_set (#L - #K)).toFinset) i) = 0) by
    have h := Ω_pol_family_left_coeff_zero L hF hwuni _ hg this
    simp only [this, implies_true, h, and_self]
  simp only [Ω_pol_family, Fin.sum_univ_add, Fin.append_left, Fin.append_right] at hg
  let Ω_restrict := Set.range (fun i => (Ω_char_vec (R := ℝ) _ (hF _ (F_indexed i).2)))
  have : Fintype Ω_restrict := by apply Set.fintypeRange
  have hg := congrArg Ω_restrict.restrict hg
  rw [restrict_sum_linear] at hg
  change _ = 0 at hg
  have : ∀ x, Ω_restrict.restrict (Ω_swallow_pol L (K := K) x) = 0 := by
    intro x
    ext i
    have hi := i.2
    rw [Set.mem_range] at hi
    obtain ⟨y, hi⟩ := hi
    simp [← hi, swallow_pol_spec L hF hwuni x]
  simp only [this, smul_zero, sum_const_zero, add_zero] at hg
  have := @sorted_linearComb_zero _ _ _ _ Set.univ _
    (fun x => Ω_restrict.restrict (Ω_char_pol L hF x)) (fun x => #(F_indexed x).1)
  let f := fun i => g (Fin.castAdd (#(ml_pol_deg_le_n_set (#L - #K)).toFinset) i)
  suffices f = 0 by intro i; change f i = 0; exact congrFun this i
  let f_fin := Finsupp.equivFunOnFinite.symm f
  change ∑ x, f_fin x • Ω_restrict.restrict (Ω_char_pol L hF x) = 0 at hg
  suffices f_fin = 0 by ext x; change f_fin x = _; simp [this]
  apply this
  · simp only [Set.mem_univ, Function.mem_support, Set.restrict_apply, ne_eq, Nat.cast_le,
    Decidable.not_not, forall_const, Subtype.exists, exists_and_left, exists_prop]
    intro f
    use Ω_char_vec (R := ℝ) _ (hF _ (F_indexed f).2)
    use (by simp only [Subtype.coe_prop])
    simp only [Subtype.coe_eta, char_pol_spec_1, not_false_eq_true, Set.mem_range,
      exists_apply_eq_apply, true_and, Ω_restrict]
    intro g hgf hneg
    exact char_pol_spec_2 L hF hinter g f (fun a ↦ hneg a.symm) hgf
  · simp
  · rw [← hg]
    exact Finsupp_sum_eq_Fintype_sum_univ

theorem Ray_Chaudhuri_Wilson_Theorem_generalized_K_le_L
    (hKL : #K ≤ #L) (hF : ∀ A ∈ F, A ⊆ X) (hu : weak_uniform F K L)
    (hi : weak_intersecting F L): #F ≤ ∑ m ∈ Ico ((#L - #K) + 1) (#L + 1), Nat.choose #X m := by
  have h : ((#L - #K) + 1) ≤ (#L + 1) := by simp
  rw [← Nat.cast_le (α := ℝ), Nat.cast_sum, Finset.sum_Ico_eq_sub (fun x => ((#X).choose x : ℝ)) h]
  have h := linearIndependent_span (Ω_pol_family_lin_indep L hF hKL hi hu)
  apply LinearIndependent.cardinal_le_rank at h
  simp only [Set.toFinset_card, Cardinal.mk_fintype, Fintype.card_fin, Nat.cast_add] at h
  have hc := card_ml_pol_deg_le_n_set (R := ℝ) (X := X) (#L - #K)
  rw [Set.toFinset_card] at hc
  simp only [hc, Nat.sub_add_cancel hKL, Nat.cast_sum] at h
  have h := le_trans h (dim_span_to_R_le L hF hKL)
  norm_cast at h
  have hsumle : ∑ x ∈ range (#L - #K + 1), (#X).choose x ≤ ∑ x ∈ range (#L + 1),
      (#X).choose x := sum_le_sum_of_subset_of_nonneg (by simp) (by simp)
  rw [← Nat.le_sub_iff_add_le hsumle] at h
  have h := (Nat.cast_le (α := ℝ)).mpr h
  suffices (((∑ x ∈ range (#L + 1), (#X).choose x -
    ∑ x ∈ range (#L - #K + 1), (#X).choose x) :ℕ) : ℝ) =
    ∑ k ∈ range (#L + 1), ((#X).choose k : ℝ) -
    ∑ k ∈ range (#L - #K + 1), ((#X).choose k : ℝ) by
    rwa [this] at h
  simp only [← Nat.cast_sum]
  exact Nat.cast_sub hsumle

theorem Ray_Chaudhuri_Wilson_Theorem_generalized (hF : ∀ A ∈ F, A ⊆ X) (hu : weak_uniform F K L)
    (hi : weak_intersecting F L): #F ≤ ∑ m ∈ Ico (#L + 1 - #K) (#L + 1), Nat.choose #X m := by
  by_cases hKL : #K ≤ #L
  · have hans := Ray_Chaudhuri_Wilson_Theorem_generalized_K_le_L L hKL hF hu hi
    suffices #L - #K + 1 = #L + 1 - #K by rwa [← this]
    ring_nf
    exact (Nat.add_sub_assoc hKL 1).symm
  · have : #L + 1 - #K ≤ #L + 1 := by simp
    rw [← Nat.cast_le (α := ℝ), Nat.cast_sum,
      Finset.sum_Ico_eq_sub (fun x => ((#X).choose x : ℝ)) this]
    have : #L + 1 - #K = 0 := by
      rw [tsub_eq_zero_iff_le]
      simp only [not_le] at hKL
      exact hKL
    simp only [this, range_zero, sum_empty, sub_zero, ge_iff_le]
    simp only [← Nat.cast_sum, Nat.cast_le]
    exact Frankl_Wilson.Frankl_Wilson_intersecting L hF hi

theorem Ray_Chaudhuri_Wilson_Theorem (hF : ∀ A ∈ F, A ⊆ X) (huniform : uniform F n)
    (hintersect : intersecting F L): #F ≤ Nat.choose #X #L := by
  by_cases hn : 0 < n
  · have := uniform_weak_uniform n L hn hintersect huniform
    have hwi := intersecting_weak_intersecting hintersect
    have := Ray_Chaudhuri_Wilson_Theorem_generalized L hF this hwi
    simpa using this
  simp only [not_lt, nonpos_iff_eq_zero] at hn
  subst hn
  simp [uniform] at huniform
  have hF : F ⊆ {∅} := by
    intro x hx
    simp only [mem_singleton]
    exact huniform x hx
  calc
  _ ≤ #{∅} := card_le_card hF
  _ = 1 := rfl
  _ ≤ _ := by
    apply Nat.choose_pos
    suffices #L = 0 by rw [this]; exact Nat.zero_le #X
    simp only [card_eq_zero]
    rw [hintersect]
    ext x
    simp only [ne_eq, Set.mem_toFinset, Set.mem_setOf_eq, not_mem_empty, iff_false, not_exists,
      not_and]
    intro x1 hx1 x2 hx2 hneq
    exfalso
    rw [huniform x1 hx1, ← huniform x2 hx2] at hneq
    exact hneq rfl

end Ray_Chaudhuri_Wilson
