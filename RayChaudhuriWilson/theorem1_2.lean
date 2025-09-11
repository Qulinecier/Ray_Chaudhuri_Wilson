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
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import RayChaudhuriWilson.intersection_card
import RayChaudhuriWilson.Matrix_rank
import RayChaudhuriWilson.Finset_card


open Finset
variable {α : Type} [DecidableEq α]


variable (X : Finset α) (n s k: ℕ) (p : ℕ) [hp : Fact p.Prime]
variable (F: Finset (powersetCard k X)) [hF: Fact (Nonempty F)]
variable (μ : Fin (s + 1) →  ZMod p) (hμ : ∀ (i j : Fin (s + 1)), i ≠ j → μ i  ≠ μ j)



def uniform_mod := ∀ (A : F), (#A.val.val : ZMod p) = (μ 0)

def intersecting_mod:= ∀ (A B: F), ∃ (i: Fin (s + 1)), (i ≥ 1) ∧
  (#(A.val.val ∩ B.val.val): ZMod p) = μ i

def μ_set: Finset (ZMod p) := { (n: ZMod p)| ∃ (A B : F), (#(A.val.val ∩ B.val.val):ZMod p) = n}

def μ_set' : Finset (ZMod p) := {μ i | (i : Fin (s + 1))}

variable (h_card : #(μ_set X k p F) = s + 1) (hμ': μ_set' s p μ = (μ_set X k p F))


def incidence_matrix (i j: ℕ) :Matrix (powersetCard i X) (powersetCard j X) ℝ :=
  fun B => fun A => if B.val ⊆ A.val then 1 else 0

def Gram_matrix (i j: ℕ) := (Matrix.transpose (incidence_matrix X i j))
  * (incidence_matrix X i j)

lemma incidence_mul_subset (i: Finset.range (s + 1)) (B : { x // x ∈ powersetCard i X })
    (A: { x // x ∈ powersetCard k X })
    (S: { x // x ∈ powersetCard s X }) :
    incidence_matrix X i s B S * incidence_matrix X s k S A  =
    if (B.val ⊆ S) ∧ (S.val ⊆ A) then 1 else 0 :=by
  unfold incidence_matrix
  by_cases h1: B.val ⊆ S
  · by_cases h2: S.val ⊆ A
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, mul_one]
    · rw [if_neg h2, if_neg (not_and.mpr fun a ↦ h2), mul_zero]
  · by_cases h2: S.val ⊆ A
    · rw [if_neg h1, if_neg (not_and.mpr fun a a_1 ↦ h1 a), zero_mul]
    · rw [if_neg h1, if_neg (not_and.mpr fun a a_1 ↦ h1 a), zero_mul]


lemma set_card_map (i: Finset.range (s + 1)) (B : { x // x ∈ powersetCard i X })
    (A: { x // x ∈ powersetCard k X }): {x ∈  powersetCard s X  | B.val ⊆ x ∧ x ⊆ A.val}
    = {x ∈ powersetCard s X | #(B.val ∩ x) = #B.val ∧ (x ⊆ A)} :=by
  ext x
  constructor
  · intro hx
    simp only [mem_filter, mem_powersetCard]at hx ⊢
    refine' ⟨hx.1, ⟨by rw [inter_eq_left.mpr hx.2.1], hx.2.2⟩ ⟩
  · intro hx
    simp only [mem_filter, mem_powersetCard] at hx ⊢
    refine' ⟨hx.1, ⟨inter_eq_left.mp ((Finset.eq_iff_card_le_of_subset (inter_subset_left)).mp
      (Nat.le_of_eq (id (Eq.symm hx.2.1)))), hx.2.2⟩ ⟩


lemma N_transpose_N_eq_coe_N (i: Finset.range (s + 1)) : (incidence_matrix X i s)
    * (incidence_matrix X s k) =
    (Nat.choose (k - i) (s - i)) • (incidence_matrix X i k) :=by
  funext B A
  rw [Matrix.mul_apply]
  simp_rw [Matrix.smul_apply, incidence_mul_subset]
  unfold incidence_matrix
  by_cases hBA: B.val ⊆ A.val
  · simp only [univ_eq_attach]
    rw [Finset.sum_attach (powersetCard s X)
      (fun (x: (Finset α)) => if (B.val ⊆ x) ∧ (x ⊆ A) then 1 else 0)]
    simp_rw [if_pos hBA, nsmul_eq_mul, mul_one, sum_boole]
    rw [set_card_map]
    simp_rw [card_set_subset_set_nat_choose s (#B.val) B.val A.val (le_of_eq_of_le
      ((mem_powersetCard.mp B.property).right) (mem_range_succ_iff.mp (i.property)))
      ((mem_powersetCard.mp B.property).left) ((mem_powersetCard.mp A.property).left),
      inter_eq_left.mpr hBA, Nat.choose_self, one_mul, card_sdiff hBA,
      (mem_powersetCard.mp B.property).right, (mem_powersetCard.mp A.property).right]
  · rw [if_neg hBA]
    simp only [nsmul_zero]
    have hBSA: ∀ (S : { x // x ∈ powersetCard s X }), ¬ ((B.val ⊆ S) ∧ (S.val ⊆ A)) :=by
      intro S
      by_contra h
      exact hBA (subset_trans h.1 h.2)
    simp_rw [hBSA, univ_eq_attach, reduceIte, sum_const_zero]

noncomputable instance: Module (ZMod p) (Polynomial (ZMod p)) := by infer_instance

def polyLe (n : ℕ) : Submodule (ZMod p) (Polynomial (ZMod p)) :=
{ carrier := { p | p.natDegree ≤ n },
  zero_mem' := by simp,
  add_mem' {p q} hp hq:= by
    apply le_trans (Polynomial.natDegree_add_le p q)
    exact max_le hp hq
  smul_mem' c p hp := by
    by_cases hc : c = 0
    · simp [hc]
    · simp only [Set.mem_setOf_eq]
      rw [Polynomial.natDegree_smul p hc]
      exact hp
}

noncomputable def binomVec (i : Finset.range (s + 1)) : (polyLe p s) := by
  refine' ⟨(1/(Nat.factorial i): ZMod p) • (descPochhammer (ZMod p) i.val), ?_⟩
  unfold polyLe
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq]
  by_cases hi: (1/(Nat.factorial i): ZMod p) = 0
  · rw [hi]
    simp only [zero_smul, Polynomial.natDegree_zero, zero_le]
  · rw [Polynomial.natDegree_smul _ hi, descPochhammer_natDegree]
    exact mem_range_succ_iff.mp i.property


lemma binomVec_linearIndependent :
    LinearIndependent (ZMod p) (fun i : Finset.range (s + 1) =>
    (binomVec (s:=s) p i : polyLe p s)) := by
  rw [linearIndependent_iff'']
  intro S c hc hcoe i
  sorry


lemma binomVec_span_top :
    ⊤ ≤ Submodule.span (ZMod p) (Set.range (fun i : Finset.range (s + 1) =>
    (binomVec (s:=s) p i : polyLe p s))) := by
  sorry

noncomputable def binomBasis : Module.Basis (Finset.range (s + 1)) (ZMod p) (polyLe p s):=by
  exact Module.Basis.mk (binomVec_linearIndependent s p) (binomVec_span_top s p)


lemma exists_coe_M_poly (f: Polynomial (ZMod p)) (hf: Polynomial.natDegree f ≤ s):
  ∃ (a : Finset.range (s + 1) → (ZMod p)), f
   = ∑ (i : Finset.range (s + 1)), (a i) • ((1/(Nat.factorial i): ZMod p) •
  (descPochhammer (ZMod p) i.val)) := by
  sorry
  done

lemma exists_coe_M : ∃ (a : Finset.range (s + 1) → ZMod p), ∀ (x : ℕ), (∏ (i : Finset.Icc 1 s),
  (x - μ (Fin.ofNat (s + 1) i.val))) = ∑ (i : Finset.range (s + 1)), (a i) * (Nat.choose x i) := by
  sorry

def gram_M (a : Finset.range (s + 1) → ZMod p) := ∑ (i : Finset.range (s + 1)), ((a i).val: ℝ) •
  (Gram_matrix X i k)

/-- The minor `M(𝓕)` of `Gram_matrix i j` obtained by restricting to
    rows/columns indexed by `𝓕 ⊆ powersetCard j X`. -/
noncomputable def M_minor (a : Finset.range (s + 1) → ZMod p) :
    Matrix {A // A ∈ F} {A // A ∈ F} ℝ :=
  (gram_M X s k p a).submatrix (fun u => u) (fun v => v)

instance : Nontrivial (ZMod p):= ZMod.nontrivial_iff.mpr (Nat.Prime.ne_one hp.1)

instance: StrongRankCondition (ZMod p) := IsNoetherianRing.strongRankCondition (ZMod p)

instance: Field (ZMod p) :=by infer_instance

omit hp in
lemma rank_minor_le_M (a : Finset.range (s + 1) → ZMod p): Matrix.rank (M_minor X s k p F a)
    ≤ Matrix.rank (gram_M X s k p a) := by
  exact rank_submatrix_le' (gram_M X s k p a) (fun (u: F) => (u: powersetCard k X))
    (fun (v: F) => (v: powersetCard k X))

def vector_space_on_N := Submodule.span ℝ (Set.range (incidence_matrix X s k).row)

lemma dim_V_leq_binom_n_s : (Module.finrank ℝ (vector_space_on_N X s k))
  ≤ (Nat.choose n s) := sorry


--instance (a : Finset.range (s + 1) → ZMod p) {i : ℕ}: Invertible (M_minor X s k p F a) := sorry

instance: Module.Finite ℝ  (vector_space_on_N X s k):=
  FiniteDimensional.finiteDimensional_submodule (vector_space_on_N X s k)

instance (a: ZMod p) (ha: a ≠ 0): Invertible a := by exact invertibleOfNonzero ha


lemma s_leq_k (h_card : #(μ_set X k p F) = s + 1) (hμ': μ_set' s p μ = (μ_set X k p F))
  (huniform_mod: uniform_mod X s k p F μ)
  (hintersect: intersecting_mod X s k p F μ): s ≤ k :=by
  unfold uniform_mod at huniform_mod
  unfold intersecting_mod at hintersect
  have h1: ∀ (A B : F), #(A.val.val ∩ B.val.val) ≤ k := by
    exact fun A B => le_of_le_of_eq (card_le_card (inter_subset_left))
      (mem_powersetCard.mp A.val.property).right
  let L: Finset ℕ := { n ∈ Finset.range (k+1) | ∃ (A B : F), #(A.val.val ∩ B.val.val) = n}
  have hL: #L ≤ k + 1 := by
    have hkL: k ∈ L := by
      unfold L
      simp only [Finset.mem_filter, *]
      refine' ⟨self_mem_range_succ k, ?_⟩
      let A := Classical.choice hF.out
      use A
      use A
      rw [inter_eq_right.mpr fun ⦃a⦄ a ↦ a]
      exact (mem_powersetCard.mp A.val.property).right
    rw [Finset.sup_eq_mem_and_le L k hkL (fun r => mem_range_succ_iff.mp (mem_of_mem_filter (r: ℕ) r.property))]
    apply Finset.card_le_sup_id_succ

  have hμL : #(μ_set' s p μ) ≤ #L := by
    rw [hμ']
    unfold μ_set
    unfold L
    simp only [Subtype.exists, exists_prop, mem_powersetCard, exists_and_right]
    
    apply Finset.card_le_card_of_surjOn (fun i : ℕ ↦ (i : ZMod p))
    unfold Set.SurjOn
    intro x hx
    

  -- have hL' : { n | ∃ (A B : F), #(A.val.val ∩ B.val.val) = n} ⊆ Finset.range (k+1) := by sorry

  -- have hL: Fintype L := by

  --   apply fintypeOfFinsetCardLe k
  --   intro s
  --   unfold L at s
  --   #check (s : Finset ℕ)









lemma row_N_i_k_in_V (i: Finset.range (s + 1)) (u: powersetCard i X ):
    incidence_matrix X i k u ∈ vector_space_on_N X s k := by
  have h1: ((Nat.choose (k - i) (s - i)) • (incidence_matrix X i k)) u
    ∈ vector_space_on_N X s k := by
    rw [← N_transpose_N_eq_coe_N, Matrix.mul_apply_eq_vecMul, Matrix.vecMul_eq_sum]
    apply Submodule.sum_mem
    intro v hv
    apply Submodule.smul_mem
    unfold vector_space_on_N; unfold Matrix.row
    rw [@Submodule.mem_span_range_iff_exists_fun]
    use fun (x: powersetCard s X)=> if x = v then (1: ℝ) else 0
    simp only [univ_eq_attach, ite_smul, one_smul, zero_smul, sum_ite_eq', mem_attach, ↓reduceIte]
  rw [Pi.smul_def] at h1
  simp only [nsmul_eq_mul] at h1
  have h2:  (Nat.cast (R := ℝ) ((k - i).choose (s - i)))⁻¹ •
    ((Nat.cast (R := ℝ ) ((k - i).choose (s - i))) • incidence_matrix X (i) k u)
    ∈ vector_space_on_N X s k :=by
    exact Submodule.smul_mem (vector_space_on_N X s k)
      ((Nat.cast (R := ℝ) ((k - i).choose (s - i)))⁻¹) h1
  rw [smul_smul] at h2
  have h_neq_zero: Nat.cast (R := ℝ) ((k - i).choose (s - i)) ≠ 0 := by
    have h : ((k - i).choose (s - i)) ≠ 0 := by
      by_contra hzero
      have h3:= Nat.choose_eq_zero_iff.mp hzero
      have h4: k < s := by exact lt_of_tsub_lt_tsub_right h3

      --TODO → 
      sorry
    exact Nat.cast_ne_zero.mpr h
  have hinvertible: Invertible (Nat.cast (R := ℝ ) ((k - i).choose (s - i))) :=
    invertibleOfNonzero h_neq_zero
  rw [inv_mul_cancel_of_invertible] at h2
  exact (Submodule.smul_mem_iff'' (vector_space_on_N X s k)).mp h1


omit hp in
lemma finrank_span_row_M_leq_dim_V (a : Finset.range (s + 1) → ZMod p):
  Module.finrank ℝ  (Submodule.span ℝ (Set.range (gram_M X s k p a).row))
  ≤ (Module.finrank ℝ  (vector_space_on_N X s k)) :=by
  apply Submodule.finrank_mono
  rw [Submodule.span_le, Set.range_subset_iff]
  intro r
  unfold gram_M; unfold Matrix.row
  rw [sum_fn, SetLike.mem_coe]
  apply Submodule.sum_mem
  intro i hi
  rw [Pi.smul_def]
  simp only
  apply Submodule.smul_mem
  unfold Gram_matrix
  rw [Matrix.mul_apply_eq_vecMul, Matrix.vecMul_eq_sum]
  apply Submodule.sum_mem
  intro u hu
  apply Submodule.smul_mem
  exact (row_N_i_k_in_V X s k i u)

lemma rank_M_leq_rank_V (a : Finset.range (s + 1) → ZMod p): Matrix.rank (gram_M X s k p a)
  ≤ (Module.finrank ℝ (vector_space_on_N X s k)) :=by
  exact le_of_eq_of_le (Matrix.rank_eq_finrank_span_row (gram_M X s k p a))
    (finrank_span_row_M_leq_dim_V X s k p a)

lemma det_M_neq_0_rank_M_eq_card_F (a : Finset.range (s + 1) → ZMod p): (Matrix.det (M_minor X s k p F a)) ≠ 0 →
  Matrix.rank (M_minor X s k p F a) = #F := sorry

lemma det_M_neq_0 (a : Finset.range (s + 1) → ZMod p): (Matrix.det (M_minor X s k p F a)) ≠ 0 := by sorry

theorem Frankl_Wilson_mod (μ : Fin (s + 1) →  ZMod p)
    (hμ : ∀ (i j : Fin (s + 1)), i ≠ j → μ i  ≠ μ j)
    (huniform_mod: uniform_mod X s k p F μ)
    (hintersect: intersecting_mod X s k p F μ): #F ≤ Nat.choose n s  := by
  obtain ⟨a, h⟩ := exists_coe_M s p μ
  rw [← det_M_neq_0_rank_M_eq_card_F X s k p F a (det_M_neq_0 X s k p F a)]
  exact le_trans (rank_minor_le_M X s k p F a) (le_trans (rank_M_leq_rank_V X s k p a)
    (dim_V_leq_binom_n_s X n s k))
