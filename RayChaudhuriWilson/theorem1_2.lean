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
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic


open Finset
variable {α : Type*} [DecidableEq α]


variable (X : Finset α) (n s k: ℕ) (p : ℕ) [hp : Fact p.Prime]
variable (F: Finset (powersetCard k X))
variable (μ : Fin (s + 1) →  ZMod p) (hμ : ∀ (i j : Fin (s + 1)), i ≠ j → μ i  ≠ μ j)

def uniform_mod := ∀ (A : F), (#A.val.val : ZMod p) = (μ 0)

def intersecting_mod:= ∀ (A B: F), ∃ (i: Fin (s + 1)), (i ≥ 1) ∧
  (#(A.val.val ∩ B.val.val): ZMod p) = μ i



def incidence_matrix (i j: ℕ) :Matrix (powersetCard i X) (powersetCard j X) (ZMod p) :=
  fun B => fun A => if B.val ⊆ A.val then 1 else 0

def Gram_matrix (i j: ℕ) := (Matrix.transpose (incidence_matrix X p i j)) * (incidence_matrix X p i j)



lemma exists_coe_M : ∃ (a : Finset.Icc 1 s → ZMod p), ∀ (x : ℕ), (∏ (i : Finset.Icc 1 s), (x - μ i))
  = ∑ (i : Finset.Icc 1 s), (a i) * (Nat.choose x i) := by sorry

def gram_M (a : Finset.Icc 1 s → ZMod p) := ∑ (i : Finset.Icc 1 s), (a i) • (Gram_matrix X p i k)

/-- The minor `M(𝓕)` of `Gram_matrix i j` obtained by restricting to
    rows/columns indexed by `𝓕 ⊆ powersetCard j X`. -/
noncomputable def M_minor (a : Finset.Icc 1 s → ZMod p) :
    Matrix {A // A ∈ F} {A // A ∈ F} (ZMod p) :=
  (gram_M X s k p a).submatrix (fun u => u) (fun v => v)


instance : Nontrivial (ZMod p):= ZMod.nontrivial_iff.mpr (Nat.Prime.ne_one hp.1)

instance: StrongRankCondition (ZMod p) := IsNoetherianRing.strongRankCondition (ZMod p)


lemma rank_minor_le_M (a : Finset.Icc 1 s → ZMod p): Matrix.rank (M_minor X s k p F a)
    ≤ Matrix.rank (gram_M X s k p a) := by
  --Matrix.rank_submatrix_le
  let he' : { x // x ∈ powersetCard k X } ≃ { x // x ∈ powersetCard k X } :={
    toFun := id
    invFun := id
    left_inv :=by exact congrFun rfl
    right_inv :=by exact congrFun rfl
  }

  let f' : { A // A ∈ F } → { x // x ∈ powersetCard k X } := fun u => u
  let M_minor' :Matrix {A // A ∈ F} { x // x ∈ powersetCard k X } (ZMod p) :=
    (gram_M X s k p a).submatrix f' he'
  #check Matrix.rank_submatrix_le
  have h1: Matrix.rank M_minor' ≤ Matrix.rank (gram_M X s k p a) :=by
    unfold M_minor'
    --apply Matrix.rank_submatrix_le
    exact Matrix.rank_submatrix_le f' he' (gram_M X s k p a)
  let M_minor_2 := Matrix.transpose M_minor'


  sorry

def vector_space_on_N := Submodule.span (ZMod p)
    ((fun r => (incidence_matrix X p s k) r) '' (Set.univ))

lemma dim_V_leq_binom_n_s : (Module.finrank (ZMod p) (vector_space_on_N X s k p)) ≤ (Nat.choose n s) := sorry


instance {i : ℕ}: Invertible (M_minor X s k p F a) := sorry

lemma rank_M_leq_rank_V (a : Finset.Icc 1 s → ZMod p): Matrix.rank (gram_M X s k p a)
  ≤ (Module.finrank (ZMod p) (vector_space_on_N X s k p)) := sorry

lemma det_M_neq_0_rank_M_eq_card_F (a : Finset.Icc 1 s → ZMod p): (Matrix.det (M_minor X s k p F a)) ≠ 0 →
  Matrix.rank (M_minor X s k p F a) = #F := sorry

lemma det_M_neq_0 (a : Finset.Icc 1 s → ZMod p): (Matrix.det (M_minor X s k p F a)) ≠ 0 := by sorry




theorem Frankl_Wilson_mod (μ : Fin (s + 1) →  ZMod p)
    (hμ : ∀ (i j : Fin (s + 1)), i ≠ j → μ i  ≠ μ j)
    (huniform_mod: uniform_mod X s k p F μ)
    (hintersect: intersecting_mod X s k p F μ): #F ≤ Nat.choose n s  := by
  obtain ⟨a, h⟩ := exists_coe_M s p μ
  rw [← det_M_neq_0_rank_M_eq_card_F X s k p F a (det_M_neq_0 X s k p F a)]
  exact le_trans (rank_minor_le_M X s k p F a) (le_trans (rank_M_leq_rank_V X s k p a)
    (dim_V_leq_binom_n_s X n s k p))
