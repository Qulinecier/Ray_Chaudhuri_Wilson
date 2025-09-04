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

open Finset

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
universe u v in
theorem sorted_linearIndepOn {α : Type u} {ι : Type v} [DecidableEq ι] {s : Set ι} [Fintype s]
    (S : ι → (α → ℝ)) (Sn : ι → ℝ) (h : ∀ f ∈ s, ∃ a ∈ (S f).support, ∀ g ∈ s,
    Sn f ≤ Sn g → f ≠ g → a ∉ (S g).support) : LinearIndepOn ℝ S s := by
  by_contra hcon
  rw [@linearDepOn_iff] at hcon
  obtain ⟨g, hg, hi⟩ := hcon
  obtain ⟨hi, hgne⟩ := hi
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

variable {α : Type} (n : ℕ) [DecidableEq α] {X: Finset α} {F: Finset (Finset α)} (L : Finset ℕ)
variable (hF : ∀ A ∈ F, A ⊆ X)

def uniform (F: Finset (Finset α)) (k : ℕ): Prop := ∀ A ∈ F, #A = k

def intersecting (F: Finset (Finset α)) (L : Set ℕ) := ∀ A ∈ F, ∀ B ∈ F, A ≠ B → #(A ∩ B) ∈ L

--Ω is defined as X → {0, 1} in paper, and in this code it is defined as a subset of X → R.
def Ω : Set (X → ℝ) := { f : X → ℝ | ∀ a, f a = 0 ∨ f a = 1 }

instance: Module ℝ (@Ω α X → ℝ) := by infer_instance

/- The characteristic vector of a set A_i is a function from
  X to {0, 1} that indicates membership in A.-/
def char_vec (A : Finset α) (hA : A ⊆ X): X → ℝ := fun a => if a.val ∈ A.val then 1 else 0

-- Show that the char_vec can be restricted to {0, 1}.
lemma char_vec_mem_Ω (A : Finset α) (hA : A ⊆ X) : (char_vec A hA) ∈ Ω := by
  unfold char_vec Ω
  simp only [Subtype.forall, Set.mem_setOf_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    ite_eq_left_iff, zero_ne_one, Decidable.not_not]
  intro a b
  exact Decidable.not_or_of_imp fun a ↦ a

-- The char_vec with restricted codomain to {0, 1}.
noncomputable def Ω_char_vec (A : Finset α) (hA : A ⊆ X):
  @Ω α X := ⟨char_vec A hA, char_vec_mem_Ω A hA⟩

-- Show that the inner product of characteristic vectors gives the card of the set intersection.
theorem char_vec_spec (A B : Finset α) (hA : A ⊆ X) (hB : B ⊆ X) :
    (char_vec A hA) ⬝ᵥ (char_vec B hB) = #(A ∩ B) := by
  have h : (char_vec A hA) ⬝ᵥ (char_vec B hB) =
      ∑ a : X, if a.val ∈ A ∩ B then 1 else 0 := by
    simp only [(· ⬝ᵥ ·)]
    refine congrArg univ.sum ?_
    unfold char_vec
    aesop
  rw [h]
  simp only [sum_boole, Nat.cast_inj]
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
def pol_to_eval : (MvPolynomial X ℝ) →ₗ[ℝ] (@Ω α X → ℝ) where
  toFun fp := fun x => fp.eval (σ := X) x
  map_add' := by aesop
  map_smul' := by aesop

noncomputable instance (x : @Ω α X) (S : X →₀ ℕ): Decidable (S.support.toSet ⊆ x.1.support) :=
  Classical.propDecidable (S.support.toSet ⊆ x.1.support)

/- This lemma decode the pol_to_eval when the input happen to be a monomial: it become like a
  indicator function that gives 1 if the support of monomial is a subset of the input, else 0. -/
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
    simp only [multilinear_set_union_by_deg]
    simp
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

/- This theorem shows that the (monic multilinear polynomial of degree less than n) as evaluation
  function is independent. The rough idea of proving this is to assume exist a monomial p having
  non-zero coefficient with the least total degree and plug in the Ω_char_vec of the support set
  of the monomial's degree. Contradiction since ∑ x ∈ support, f x • (pol_to_eval x) v = 0 =>
  ∑ x ∈ support, f x • (pol_to_eval x) v = f p • (pol_to_eval p) v = f p • 1 = 0 -/
theorem Ω_multilinear_set_lin_indep : LinearIndepOn ℝ id (Ω_multilinear_set (X := X) n) := by
  rw [Ω_multilinear_set_eq]
  refine LinearIndepOn.id_image ?_
  apply sorted_linearIndepOn (Sn := fun x => x.totalDegree)
  intro f hf
  simp only [ml_pol_deg_le_n_set, Set.mem_setOf_eq] at hf
  obtain ⟨hfd, fS, hfS⟩ := hf
  use Ω_char_vec (Finset.image Subtype.val fS.support) (by
    intro a ha
    simp only [mem_image, Finsupp.mem_support_iff, ne_eq, Subtype.exists, exists_and_right,
      exists_eq_right] at ha
    obtain ⟨hx, _⟩ := ha
    exact hx)
  constructor
  · unfold Ω_char_vec char_vec
    simp only [hfS, pol_to_eval_monomial_eq, pol_power_shrink_support_linear, image_val,
      Multiset.mem_dedup, Subtype.val_injective, Multiset.mem_map_of_injective, mem_val,
      Finsupp.mem_support_iff, ne_eq, ite_not, Function.mem_support, ite_eq_right_iff, one_ne_zero,
      imp_false, not_not]
    intro a ha
    simp only [Function.mem_support, ne_eq, ite_eq_left_iff, one_ne_zero, imp_false,
      Decidable.not_not]
    exact Finsupp.mem_support_iff.mp ha
  intro g hg hfleg hfneg
  obtain ⟨hgd, gS, hgS⟩ := hg
  unfold Ω_char_vec char_vec
  simp only [hgS, pol_to_eval_monomial_eq, Function.mem_support, ne_eq, Decidable.not_not]
  simp only [pol_power_shrink_support_linear, image_val, Multiset.mem_dedup, Subtype.val_injective,
    Multiset.mem_map_of_injective, mem_val, Finsupp.mem_support_iff, ne_eq, ite_not,
    ite_eq_right_iff, one_ne_zero, imp_false]
  refine Set.not_subset.mpr ?_
  simp only [mem_coe, Finsupp.mem_support_iff, ne_eq, Function.mem_support, ite_eq_left_iff,
    one_ne_zero, imp_false, Decidable.not_not, Subtype.exists]
  suffices ¬ fS.support ≥ gS.support by
    simp only [ge_iff_le, le_eq_subset, not_subset, Finsupp.mem_support_iff, ne_eq,
      Decidable.not_not, Subtype.exists] at this
    exact this
  by_contra hcon
  simp only [hfS, ne_eq, one_ne_zero, not_false_eq_true, MvPolynomial.totalDegree_monomial, ←
    card_pol_power_shrink_support, pol_power_shrink_support_linear, hgS, Nat.cast_le] at hfleg
  have h : fS.support = gS.support := by exact (eq_of_subset_of_card_le hcon hfleg).symm
  rw [pol_power_shrink_support_eq_iff] at h
  rw [h, ← hgS] at hfS
  exact hfneg hfS

-- The span of Ω_multilinear_set
def Ω_multilinear_span : Submodule ℝ (@Ω α X → ℝ) := Submodule.span ℝ (Ω_multilinear_set #L)

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

-- Show that the rank of the span of Ω_multilinear_set is ≤ its cardinality
lemma dim_Ω_multilinear_span : Module.finrank ℝ (Ω_multilinear_span (X := X) L) =
    ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  rw [← card_Ω_multilinear_set, Set.toFinset_card]
  have h := finrank_span_eq_card (R := ℝ) (Ω_multilinear_set_lin_indep (X := X) #L)
  rw [← h]
  simp [Ω_multilinear_span]
  have h : Ω_multilinear_set (X := X) #L
      = Set.range fun (x : (Ω_multilinear_set #L) ) ↦ x.val := by simp
  rw [← h]

namespace Frankl_Wilson

-- The characteristic polynomial of a set A
noncomputable def char_pol (A : F) : MvPolynomial X ℝ :=
  ∏ l ∈ L with l < #A.val, (∑ m : X,
    ((char_vec A (hF A A.2) m) • (MvPolynomial.X m)) - (MvPolynomial.C l : MvPolynomial X ℝ) )

-- Show that the total degree of the characteristic polynomial is no greater than #L
lemma char_pol_degree (A : F): (char_pol L hF A).totalDegree ≤ #L := by
  unfold char_pol
  have hAX := hF A A.2
  have h : (∑ m, (char_vec A hAX m) • MvPolynomial.X m : MvPolynomial X ℝ).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro x hx
    calc
    _ ≤ (MvPolynomial.X x).totalDegree :=
      MvPolynomial.totalDegree_smul_le (char_vec A hAX x) (MvPolynomial.X x : MvPolynomial X ℝ)
    _ = 1 := by apply MvPolynomial.totalDegree_X
  have h (l : ℕ): (∑ m, char_vec A hAX m • MvPolynomial.X m
      - (MvPolynomial.C l : MvPolynomial X ℝ)).totalDegree ≤ 1 := calc
    _ = (∑ m, char_vec A hAX m • MvPolynomial.X m
      + (MvPolynomial.C (-l) : MvPolynomial X ℝ)).totalDegree := by
        rw [MvPolynomial.C_neg, Mathlib.Tactic.RingNF.add_neg]
    _ ≤ max
      (∑ m, char_vec A hAX m • MvPolynomial.X m : MvPolynomial X ℝ).totalDegree
      (MvPolynomial.C (-l) : MvPolynomial X ℝ).totalDegree := by
      apply MvPolynomial.totalDegree_add
    _ ≤ _ := by
      simp only [MvPolynomial.totalDegree_C, zero_le, sup_of_le_left]
      exact h
  calc
  _ ≤ ∑ l ∈ L with l < #A.val,
    (∑ m : X, (char_vec A hAX m) • MvPolynomial.X m
    - (MvPolynomial.C l : MvPolynomial X ℝ)).totalDegree := by
    apply MvPolynomial.totalDegree_finset_prod
  _ ≤ ∑ l ∈ L with l < #A.val, 1 := by exact sum_le_sum fun i_1 a ↦ h i_1
  _ = #{l ∈ L | l < #A.val} := (card_eq_sum_ones {l ∈ L | l < #A.val}).symm
  _ ≤ _ := card_filter_le L fun l ↦ l < #A.val

-- Rewrite the evaluation of characteristic polynomial as a function
lemma char_pol_eval_eq (A : F) (x : X → ℝ): (char_pol L hF A).eval x
    = ∏ l ∈ L with l < #A.val, ((char_vec A (hF A A.2)) ⬝ᵥ x - l) := by
  unfold char_pol
  rw [@MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro l hl
  simp [(· ⬝ᵥ ·)]

-- Ω_char_pol translates characteristic polynomials to the function from Ω to ℝ via pol_to_eval
noncomputable def Ω_char_pol (A : F) (x : @Ω α X): ℝ := (char_pol L hF A).eval x

-- This lemma gives a more handy definition of Ω_char_pol
lemma Ω_char_pol_eq (A : F) : Ω_char_pol L hF A = pol_to_eval (char_pol L hF A) := rfl

-- Ω_char_pol_span is the span of all characteristic polynomials
def Ω_char_pol_span : Submodule ℝ (@Ω α X → ℝ) := Submodule.span ℝ (Set.range (Ω_char_pol L hF))

-- Show that the characteristic polynomial is also in the span of Ω_multilinear_set.
lemma Ω_char_pol_spec (A : F): Ω_char_pol L hF A ∈ Ω_multilinear_span L := by
  rw [Ω_char_pol_eq]
  exact Ω_multilinear_span_deg_le_mem L (char_pol L hF A) (char_pol_degree L hF A)

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
  have : Module.Finite ℝ (Ω_multilinear_span (X := X) L) := by
    unfold Ω_multilinear_span
    refine Module.Finite.span_of_finite ℝ ?_
    exact Set.toFinite (Ω_multilinear_set #L)
  rw [← dim_Ω_multilinear_span L, Module.finrank_eq_rank]
  exact Submodule.rank_mono (span_to_R_le_span_ml L hF)

-- Show that the characteristic polynomial is non-zero for the characteristic vector of A.
lemma char_pol_spec_1 (A : F) : (char_pol L hF A).eval (char_vec A (hF A A.2)) ≠ 0 := by
  rw [char_pol_eval_eq L hF A (char_vec A (hF A A.2))]
  refine prod_ne_zero_iff.mpr ?_
  intro a ha
  rw [char_vec_spec]
  norm_cast
  rw [inter_self, Int.subNat_eq_zero_iff]
  rw [@mem_filter] at ha
  exact Nat.ne_of_lt' ha.2

/- Show that the characteristic polynomial is zero for
the characteristic vector of B with lower cardinality.-/
lemma char_pol_spec_2 (A B : F) (hneq : A ≠ B) (hji : #B.val ≤ #A.val)
    (hintersect : intersecting F L): (char_pol L hF A).eval (char_vec B (hF B B.2)) = 0 := by
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

-- Show that the characteristic polynomials are in fact linear independent
lemma Ω_char_pol_lin_indep (hintersect : intersecting F L) :
    LinearIndependent ℝ (Ω_char_pol L hF):= by
  rw [← linearIndepOn_univ]
  apply sorted_linearIndepOn (Sn := fun x => #x.val)
  intro f _
  use Ω_char_vec f.val (hF f f.2)
  constructor
  · exact char_pol_spec_1 L hF f
  · intro g _ hfleg hfneg
    rw [Nat.cast_le] at hfleg
    simp only [Function.mem_support, ne_eq, Decidable.not_not]
    exact char_pol_spec_2 L hF g f hfneg.symm hfleg hintersect

-- Theorem 1.3
theorem Frankl_Wilson_Thoerem (hF : ∀ A ∈ F, A ⊆ X) (hintersect : intersecting F L):
    #F ≤ ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  have h := linearIndependent_span (Ω_char_pol_lin_indep L hF hintersect)
  apply LinearIndependent.cardinal_le_rank at h
  rw [Cardinal.mk_fintype, Fintype.card_coe] at h
  exact Nat.cast_le.mp (le_trans h (dim_span_to_R_le L hF))

end Frankl_Wilson

def char_vec_N (A : Finset α) (hA : A ⊆ X) : X → ℕ := fun a => if a.val ∈ A.val then 1 else 0

noncomputable def char_vec_pol (A : Finset α) (hA : A ⊆ X) : MvPolynomial X ℝ:=
  MvPolynomial.monomial (R := ℝ) (pol_power_shrink (char_vec_N A hA)) 1

lemma pol_to_eval_char_vec (I : Finset α) (hI : I ⊆ X) (J : Finset α) (hJ : J ⊆ X) :
    pol_to_eval (char_vec_pol I hI) (Ω_char_vec J hJ) = if I ⊆ J then 1 else 0 := by
  simp only [char_vec_pol, Ω_char_vec, pol_to_eval_monomial_eq,
    pol_power_shrink_support_linear' (char_vec_N I hI), Function.support_subset_iff, char_vec_N,
    mem_val, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not,
    Function.mem_support, char_vec, Subtype.forall]
  congr
  rw [@Finset.subset_iff _ I J, eq_iff_iff]
  apply Iff.intro
  · intro h x hx
    exact h x (hI hx) hx
  · intro h x hx
    exact fun a ↦ h a

noncomputable instance (I : Set X): Fintype (I.image Subtype.val) := by
  exact Fintype.ofFinite (Subtype.val '' I)

omit [DecidableEq α] in
noncomputable def SetX_to_I (I : Set X) : Finset α := (I.image Subtype.val).toFinset

omit [DecidableEq α] in
lemma SetX_to_hI (I : Set X) : SetX_to_I I ⊆ X := fun a1 a ↦ (by
  simp only [SetX_to_I, Set.mem_toFinset, Set.mem_image, Subtype.exists, exists_and_right,
    exists_eq_right] at a
  obtain ⟨x, hx⟩ := a
  exact x)

theorem Lemma_2_1 (f : @Ω α X → ℝ) (hf : ∀ I, (hI : I ⊆ X) → #I ≤ n → f (Ω_char_vec I hI) ≠ 0) :
    LinearIndepOn ℝ (fun (x : Set X) => (pol_to_eval (char_vec_pol (SetX_to_I x) (SetX_to_hI x)) * f))
    {I | #(SetX_to_I I) ≤ n} := by

  sorry

namespace Ray_Chaudhuri_Wilson

-- The characteristic polynomial of a set A
noncomputable def char_pol (A : F) : MvPolynomial X ℝ :=
  ∏ l ∈ L with l ≠ #A.1, (∑ m : X,
    ((char_vec A (hF A A.2) m) • (MvPolynomial.X m)) - (MvPolynomial.C l : MvPolynomial X ℝ) )

-- Show that the total degree of the characteristic polynomial is no greater than #L
lemma char_pol_degree (A : F): (char_pol L hF A).totalDegree ≤ #L := by
  unfold char_pol
  have hAX := hF A A.2
  have h : (∑ m, (char_vec A hAX m) • MvPolynomial.X m : MvPolynomial X ℝ).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro x hx
    calc
    _ ≤ (MvPolynomial.X x).totalDegree :=
      MvPolynomial.totalDegree_smul_le (char_vec A hAX x) (MvPolynomial.X x : MvPolynomial X ℝ)
    _ = 1 := by apply MvPolynomial.totalDegree_X
  have h (l : ℕ): (∑ m, char_vec A hAX m • MvPolynomial.X m
      - (MvPolynomial.C l : MvPolynomial X ℝ)).totalDegree ≤ 1 := calc
    _ = (∑ m, char_vec A hAX m • MvPolynomial.X m
      + (MvPolynomial.C (-l) : MvPolynomial X ℝ)).totalDegree := by
        rw [MvPolynomial.C_neg, Mathlib.Tactic.RingNF.add_neg]
    _ ≤ max
      (∑ m, char_vec A hAX m • MvPolynomial.X m : MvPolynomial X ℝ).totalDegree
      (MvPolynomial.C (-l) : MvPolynomial X ℝ).totalDegree := by
      apply MvPolynomial.totalDegree_add
    _ ≤ _ := by
      simp only [MvPolynomial.totalDegree_C, zero_le, sup_of_le_left]
      exact h
  calc
  _ ≤ ∑ l ∈ L with l ≠ #A.1,
    (∑ m : X, (char_vec A hAX m) • MvPolynomial.X m
    - (MvPolynomial.C l : MvPolynomial X ℝ)).totalDegree := by
    apply MvPolynomial.totalDegree_finset_prod
  _ ≤ ∑ l ∈ L with l ≠ #A.1, 1 := by exact sum_le_sum fun i_1 a ↦ h i_1
  _ ≤ #L := by
    rw [← card_eq_sum_ones]
    apply card_filter_le

-- Rewrite the evaluation of characteristic polynomial as a function
lemma char_pol_eval_eq (A : F) (x : X → ℝ): (char_pol L hF A).eval x
    = ∏ l ∈ L with l ≠ #A.1, ((char_vec A (hF A A.2)) ⬝ᵥ x - l) := by
  unfold char_pol
  rw [@MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro l hl
  simp [(· ⬝ᵥ ·)]

-- Ω_char_pol translates characteristic polynomials to the function from Ω to ℝ via pol_to_eval
noncomputable def Ω_char_pol (A : F) (x : @Ω α X): ℝ := (char_pol L hF A).eval x

-- This lemma gives a more handy definition of Ω_char_pol
lemma Ω_char_pol_eq (A : F) : Ω_char_pol L hF A = pol_to_eval (char_pol L hF A) := rfl

-- Ω_char_pol_span is the span of all characteristic polynomials
def Ω_char_pol_span : Submodule ℝ (@Ω α X → ℝ) := Submodule.span ℝ (Set.range (Ω_char_pol L hF))

-- Show that the characteristic polynomial is also in the span of Ω_multilinear_set.
lemma Ω_char_pol_spec (A : F): Ω_char_pol L hF A ∈ Ω_multilinear_span L := by
  rw [Ω_char_pol_eq]
  exact Ω_multilinear_span_deg_le_mem L (char_pol L hF A) (char_pol_degree L hF A)

-- Show that the characteristic polynomial is non-zero for the characteristic vector of A.
lemma char_pol_spec_1 (A : F): (char_pol L hF A).eval (char_vec A (hF A A.2)) ≠ 0 := by
  rw [char_pol_eval_eq L hF A (char_vec A (hF A A.2))]
  refine prod_ne_zero_iff.mpr ?_
  intro a ha
  rw [char_vec_spec]
  norm_cast
  rw [inter_self, Int.subNat_eq_zero_iff]
  simp only [ne_eq, mem_filter] at ha
  exact fun a_1 ↦ ha.2 a_1.symm

/- Show that the characteristic polynomial is zero for
the characteristic vector of B with lower cardinality.-/
lemma char_pol_spec_2 (A B : F) (hneq : A ≠ B) (huniform : uniform F n)
    (hintersect : intersecting F L): (char_pol L hF A).eval (char_vec B (hF B B.2)) = 0 := by
  rw [char_pol_eval_eq L hF A (char_vec B (hF B B.2))]
  unfold intersecting at hintersect
  refine prod_eq_zero_iff.mpr ?_
  use #(A.val ∩ B.val)
  rw [char_vec_spec, sub_self, propext (and_iff_left rfl), mem_filter]
  constructor
  · refine hintersect A A.2 B B.2 ?_
    exact Subtype.coe_ne_coe.mpr hneq
  · refine Nat.ne_of_lt (card_lt_card ?_)
    rw [@Finset.ssubset_iff_subset_ne]
    constructor
    · exact inter_subset_left
    · rw [ne_eq, inter_eq_left]
      by_contra hcon
      have hneq : A.1 ≠ B.1 := Subtype.coe_ne_coe.mpr hneq
      have hneg : #A.1 < #B.1 := card_lt_card (HasSubset.Subset.ssubset_of_ne hcon hneq)
      unfold uniform at huniform
      simp [huniform] at hneg

lemma Ω_char_pol_lin_indep (hintersect : intersecting F L) :
    LinearIndepOn pol_to_eval := by -- remember that pol_to_eval is bijective on monic
  rw [← linearIndepOn_univ]
  apply sorted_linearIndepOn (Sn := fun x => #x.val)
  intro f _
  use Ω_char_vec f.val (hF f f.2)
  constructor
  · exact char_pol_spec_1 L hF f
  · intro g _ hfleg hfneg
    rw [Nat.cast_le] at hfleg
    simp only [Function.mem_support, ne_eq, Decidable.not_not]
    exact char_pol_spec_2 L hF g f hfneg.symm hfleg hintersect

theorem Ray_Chaudhuri_Wilson_Theorem (hF : ∀ A ∈ F, A ⊆ X) (huniform : uniform F n)
    (hintersect : intersecting F L): #F ≤ Nat.choose #X #L := by
  #check id
  sorry

end Ray_Chaudhuri_Wilson



example (z : ℤ) : (z / 1 : ℚ).num = z := by
  simp only [div_one, Rat.intCast_num]
