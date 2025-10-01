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
import Batteries.Data.Rat.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag
import RayChaudhuriWilson.intersection_card
import RayChaudhuriWilson.Matrix_rank
import RayChaudhuriWilson.Finset_card
import RayChaudhuriWilson.fin_strong_induction
import RayChaudhuriWilson.determinant
import RayChaudhuriWilson.BinomVecSpace

open Finset
variable {α : Type} [DecidableEq α]
variable (S : Finset α) (n s k: ℕ) (hs : s ≠ 0) [hS: Fact (#S = n)] (p : ℕ) [hp : Fact p.Prime]
variable (F: Finset (powersetCard k S)) [hF: Fact (Nonempty F)]
variable (μ : Fin (s + 1) →  ZMod p) (hμ : ∀ (i j : Fin (s + 1)), i ≠ j → μ i  ≠ μ j)

open Polynomial

noncomputable abbrev characteristicPoly₁ : Polynomial ℤ :=
    ∏ (i : Finset.Icc 1 s), (X- (Nat.cast (R := ℤ[X]) (μ (Fin.ofNat (s + 1) i)).val))

lemma natDegree_characteristicPoly₁_le: (characteristicPoly₁ s p μ).natDegree ≤ s := by
  unfold characteristicPoly₁
  by_cases h: ∃ i ∈ (Icc 1 s).attach, X - (Nat.cast (R := ℤ[X]) (μ (Fin.ofNat (s + 1) i)).val) = 0
  · have h2 : (characteristicPoly₁ s p μ).natDegree = 0 := by
      unfold characteristicPoly₁
      simp only [univ_eq_attach]
      rw [prod_eq_zero_iff.mpr h]
      rfl
    rw [h2]
    exact Nat.zero_le s
  · simp only [univ_eq_attach]
    rw [Polynomial.natDegree_prod]
    · have h1: ∀ i ∈ (Icc 1 s).attach,
          (X - (Nat.cast (R := ℤ[X]) (μ (Fin.ofNat (s + 1) i)).val)).natDegree = 1:=by
        intro i hi
        rw [← pow_one X]
        have h2 : (Nat.cast (R := ℤ[X]) (μ (Fin.ofNat (s + 1) i)).val) =
          C (R := ℤ) (μ (Fin.ofNat (s + 1) i)).val :=by
          simp only [Fin.ofNat_eq_cast, ZMod.natCast_val, eq_intCast, ZMod.intCast_cast]
        rw [h2, Polynomial.natDegree_X_pow_sub_C (n:= 1)]
      have h2 : ∑ i ∈ (Icc 1 s).attach, (X - (Nat.cast (R := ℤ[X])
        (μ (Fin.ofNat (s + 1) i)).val)).natDegree =
        ∑ i ∈ (Icc 1 s).attach, 1 :=by
        congr! with i hi
        specialize h1 i hi
        exact h1
      rw [h2]
      simp only [sum_const, card_attach, Nat.card_Icc, add_tsub_cancel_right, smul_eq_mul, mul_one,
        le_refl]
    · intro i
      by_contra h'
      apply h
      use i
      simp only [mem_attach, Fin.ofNat_eq_cast, ZMod.natCast_val] at h' ⊢
      simp only [ne_eq, forall_const, Decidable.not_not] at h'
      simp only [true_and]
      exact h'




#check exists_binomial_basis_expansion s (characteristicPoly₁ s p μ) (natDegree_characteristicPoly₁_le s p μ)

section Frankl_Wilson_mod
open Finset
variable {α : Type} [DecidableEq α]

variable (X : Finset α) (n s k: ℕ) (hs : s ≠ 0) [hX: Fact (#X = n)] (p : ℕ) [hp : Fact p.Prime]
variable (F: Finset (powersetCard k X)) [hF: Fact (Nonempty F)]
variable (μ : Fin (s + 1) →  ZMod p) (hμ : ∀ (i j : Fin (s + 1)), i ≠ j → μ i  ≠ μ j)

#check Rat.instIntCast

/-
def something (x : ℕ ) (i : Fin (s + 1)) (a : Fin (s + 1) → ZMod p): ZMod p :=
  (Rat.ofInt (a i).val) * (Nat.choose x i : ℚ)
-/
-- →

def uniform_mod := ∀ (A : F), (#A.val.val : ZMod p) = (μ 0)

def intersecting_mod:= ∀ (A B: F), (A ≠ B) → ∃ (i: Fin (s + 1)), (i ≥ 1) ∧
  (#(A.val.val ∩ B.val.val): ZMod p) = μ i

def μ_set: Finset (ZMod p) := { (n: ZMod p)| ∃ (A B : F), (#(A.val.val ∩ B.val.val):ZMod p) = n}

def μ_set' : Finset (ZMod p) := {μ i | (i : Fin (s + 1))}

variable (h_card : #(μ_set X k p F) = s + 1) (hμ': μ_set' s p μ = (μ_set X k p F))


def incidence_matrix (i j: ℕ) :Matrix (powersetCard i X) (powersetCard j X) ℚ :=
  fun B => fun A => if B.val ⊆ A.val then 1 else 0


def Gram_matrix (i j: ℕ) := (Matrix.transpose (incidence_matrix X i j))
  * (incidence_matrix X i j)

lemma incidence_mul_subset (i: Fin (s + 1)) (B : { x // x ∈ powersetCard i X })
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


lemma set_card_map (i: Fin (s + 1)) (B : { x // x ∈ powersetCard i X })
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


lemma N_transpose_N_eq_coe_N (i: Fin (s + 1)) : (incidence_matrix X i s)
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
    simp_rw [card_set_subset_set_nat_choose s (#B.val) B.val A.val
      (le_of_eq_of_le ((mem_powersetCard.mp B.property).right) (Fin.is_le i))
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

def gram_M (a : Fin (s + 1) → ZMod p) := ∑ (i : Fin (s + 1)), ((a i).val: ℚ) •
  (Gram_matrix X i k)

/-- The minor `M(𝓕)` of `Gram_matrix i j` obtained by restricting to
    rows/columns indexed by `𝓕 ⊆ powersetCard j X`. -/
noncomputable def M_minor (a : Fin (s + 1) → ZMod p) :
    Matrix {A // A ∈ F} {A // A ∈ F} ℚ :=
  (gram_M X s k p a).submatrix (fun u => u) (fun v => v)

omit hF in
lemma M_minor_entry_eq_sum_binom (a : Fin (s + 1) → ZMod p) (u v : F): ((M_minor X s k p F a) u v) =
  (∑ (i : Fin (s + 1)), (a i).val * (Nat.choose (#(u.val.val ∩ v.val.val)) i)) :=by
  simp only [M_minor, gram_M, Gram_matrix]
  unfold incidence_matrix
  simp only [ZMod.natCast_val, Matrix.submatrix_apply, Nat.cast_sum, Nat.cast_mul]
  rw [Fintype.sum_apply, Fintype.sum_apply]
  simp_rw [Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, mul_ite, mul_one, mul_zero]
  simp_rw [fun (i : Fin (s + 1)) => fun (A : powersetCard i.val X) => (ite_and (A.val ⊆ v.val.val)
    (A.val ⊆ u.val.val) (1 : ℚ) (0: ℚ)).symm]
  simp_rw [(Finset.subset_inter_iff).symm]
  congr! with i hi
  simp only [sum_boole, Rat.natCast_inj, univ_eq_attach]
  rw [card_attach_powersetCard_filter_of_subset _ _
    (fun ⦃a⦄ a_1 ↦ inter_subset_right ((inter_subset_inter
    (fun ⦃a⦄ a ↦ a) ((mem_powersetCard.1 (u.1).2).1)) a_1))]
  simp_rw [inter_comm]

abbrev weighted_binom_matrix (a : Fin (s + 1) → ZMod p) : Matrix F F ℤ := fun u => fun v =>
    ∑ (i : Fin (s + 1)), (a i).val * (Nat.choose (#(u.val.val ∩ v.val.val)) i)

omit hF in
lemma map_weighted_binom_matrix_eq_minor (a : Fin (s + 1) → ZMod p) :
    (weighted_binom_matrix X s k p F a).map (Int.cast (R := ℚ)) = M_minor X s k p F a :=by
  ext u v
  unfold weighted_binom_matrix
  rw [M_minor_entry_eq_sum_binom]
  simp only [ZMod.natCast_val, Matrix.map_apply, Int.cast_sum, Int.cast_mul, ZMod.intCast_cast,
    Int.cast_natCast, Nat.cast_sum, Nat.cast_mul]

abbrev W_minor (a : Fin (s + 1) → ZMod p) := (weighted_binom_matrix X s k p F a).map
  (Int.cast (R := ZMod p))

omit hF in
lemma characteristicPoly₁_eval_intersection_eq_zero
  (hs : s ≠ 0) (u v : F) (huv : u ≠ v) (hintersect: intersecting_mod X s k p F μ):
    Int.cast (R:= ZMod p)
    (eval (Nat.cast (R:= ℤ) #(u.val.val ∩ v.val.val))
    (characteristicPoly₁ s p μ)) = 0 :=by
  unfold characteristicPoly₁; unfold intersecting_mod at hintersect
  specialize hintersect u v huv
  have h : ∃ (i : Icc 1 s ), Int.cast (R:= ZMod p) (Polynomial.eval (Nat.cast (R:= ℤ) #(u.val.val ∩ v.val.val))
    ((Polynomial.X: Polynomial ℤ)- (Nat.cast (R := ℤ[X]) (μ (Fin.ofNat (s + 1) i)).val))) = 0 :=by
    cases' hintersect with i hi
    cases' hi with hl hr
    have hi' : i.val ∈ Icc 1 s  :=by
      simp only [mem_Icc]
      constructor
      · refine Nat.one_le_iff_ne_zero.mpr ?_
        have hi' : i ≠ 0 := by
          intro h'
          rw [h'] at hl
          exact Fin.not_lt.mpr hl (Fin.pos_iff_ne_zero.mpr (id (Ne.symm (by norm_num; exact hs))))
        exact Fin.val_ne_zero_iff.mpr hi'
      · exact Fin.is_le i
    use ⟨i.val, hi'⟩
    simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self, ZMod.natCast_val, eval_sub, eval_X]
    have h : eval (Nat.cast (R:= ℤ) #(u.val.val ∩ v.val.val)) (ZMod.cast (R := ℤ[X]) (μ i))
        =ZMod.cast (R := ℤ) (μ i) := by
      have h' : ZMod.cast (R := ℤ[X]) (μ i) = Polynomial.C (R:= ℤ) (ZMod.cast (R := ℤ) (μ i)) :=by
        simp only [eq_intCast, ZMod.intCast_cast]
      rw [h']
      exact eval_C
    simp only [Int.cast_sub, Int.cast_natCast]
    rw [h, hr]
    simp only [ZMod.intCast_cast, ZMod.cast_id', id_eq, sub_self]
  simp_rw [Polynomial.eval_prod, Int.cast_prod]
  rw [Finset.prod_eq_zero_iff]
  cases' h with a ha
  use a
  simp only [univ_eq_attach, mem_attach, true_and]
  exact ha

omit hF in
lemma W_minor_is_diag (hs : s ≠ 0) (μ : Fin (s + 1) →  ZMod p)
  (hintersect: intersecting_mod X s k p F μ) (a : Fin (s + 1) → ℤ )
    (ha : ∀ (x : ℕ), (Polynomial.eval (x : ℤ) (characteristicPoly₁ s p μ)) =
    ∑ (i : Fin (s + 1)), (a i) *(Nat.choose x i)):
  (W_minor X s k p F (fun i => (Int.cast (R:= ZMod p) (a i)))).IsDiag := by
  rw [Matrix.isDiag_iff_diagonal_diag]
  ext u v
  rw [Matrix.diagonal_apply, Matrix.diag_apply]
  unfold W_minor
  unfold weighted_binom_matrix
  simp only [ZMod.natCast_val, Matrix.map_apply, inter_self, Int.cast_sum, Int.cast_mul,
    ZMod.intCast_cast, ZMod.cast_id', id_eq, Int.cast_natCast]
  by_cases huv : u = v
  · rw [if_pos huv, huv]
    simp only [inter_self]
  · rw [if_neg huv]
    specialize ha #(u.val.val ∩ v.val.val)
    have ha' := congr_arg (Int.cast (R:= ZMod p)) ha
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at ha'
    rw [← ha', characteristicPoly₁_eval_intersection_eq_zero X s k p F μ hs u v huv hintersect]

omit hF in
lemma nonzero_det_W_minor (hs : s ≠ 0) (μ : Fin (s + 1) →  ZMod p)
    (huniform_mod: uniform_mod X s k p F μ)
    (hμ : ∀ (i j : Fin (s + 1)), i ≠ j → μ i  ≠ μ j)
    (hintersect: intersecting_mod X s k p F μ):
    ∃ (a : Fin (s + 1) → ZMod p), (W_minor X s k p F a).det ≠ 0 :=by
  obtain ⟨a, ha⟩ := exists_binomial_basis_expansion s (characteristicPoly₁ s p μ)
    (natDegree_characteristicPoly₁_le s p μ)
  use (fun i => (Int.cast (R:= ZMod p) (a i)))
  rw [← ((Matrix.isDiag_iff_diagonal_diag (W_minor X s k p F (fun i =>
    (Int.cast (R:= ZMod p) (a i))))).mp
    (W_minor_is_diag X s k p F hs μ hintersect a ha))]
  simp only [Matrix.det_diagonal, Matrix.diag_apply, W_minor,
    Matrix.map_apply, Int.cast_sum, ZMod.natCast_val, inter_self,
    Int.cast_mul, ZMod.intCast_cast, dvd_refl, ZMod.cast_intCast, Int.cast_natCast]
  rw [Finset.prod_ne_zero_iff]
  intro x hx
  specialize ha (#x.val.val)
  have ha' := congr_arg (Int.cast (R:= ZMod p)) ha
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at ha'
  rw [← ha']
  unfold characteristicPoly₁
  rw [Polynomial.eval_prod]
  simp only [Int.cast_prod]
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Polynomial.eval_sub]
  simp only [eval_X]
  have h1 : Polynomial.eval (Nat.cast (R := ℤ) #x.val.val)
    (Nat.cast (R:= ℤ[X]) (μ (Fin.ofNat (s + 1) i.val)).val) = Polynomial.eval
    (Nat.cast (R := ℤ) #x.val.val) (Polynomial.C (R:= ℤ) ((μ (Fin.ofNat (s + 1) i.val)).val)) := by
    simp only [Fin.ofNat_eq_cast, ZMod.natCast_val, eq_intCast, ZMod.intCast_cast]
  rw [h1]
  simp only [eval_C]
  simp only [Fin.ofNat_eq_cast, ZMod.natCast_val, Int.cast_sub, Int.cast_natCast, ZMod.intCast_cast,
    ZMod.cast_id', id_eq]
  rw [huniform_mod x]
  have h0i : (0: Fin (s + 1)) ≠ i.val := Nat.ne_of_lt (List.left_le_of_mem_range' i.2)
  have h0i':(0: Fin (s + 1)) ≠ (@Nat.cast (Fin (s + 1)) (Fin.NatCast.instNatCast (s + 1)) i.val):=by
    by_contra h'
    rw [h'] at h0i
    simp only [Fin.val_natCast, ne_eq, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, not_lt] at h0i
    have h3 : i.val < s + 1 := by exact Order.lt_add_one_iff.mpr ((mem_Icc.mp i.2).2)
    omega
  exact sub_ne_zero_of_ne (hμ 0
    (@Nat.cast (Fin (s + 1)) (Fin.NatCast.instNatCast (s + 1)) i.val) h0i')

instance : Nontrivial (ZMod p):= ZMod.nontrivial_iff.mpr (Nat.Prime.ne_one hp.1)

instance: StrongRankCondition (ZMod p) := IsNoetherianRing.strongRankCondition (ZMod p)

instance: Field (ZMod p) :=by infer_instance

omit hp hF in
lemma rank_minor_le_M (a : Fin (s + 1) → ZMod p): Matrix.rank (M_minor X s k p F a)
    ≤ Matrix.rank (gram_M X s k p a) := by
  exact rank_submatrix_le' (gram_M X s k p a) (fun (u: F) => (u: powersetCard k X))
    (fun (v: F) => (v: powersetCard k X))

def vector_space_on_N := Submodule.span ℚ (Set.range (incidence_matrix X s k).row)

lemma card_incidence_matrix: #(Set.range (incidence_matrix X s k).row).toFinset
    ≤ (Nat.choose n s) := by
  simp only [Set.toFinset_range]
  have h2: #(univ: Finset { x // x ∈ powersetCard s X }) = Nat.choose n s := by
    simp_rw [univ_eq_attach, card_attach, card_powersetCard, hX.1]
  rw [← h2]
  exact card_image_le

lemma dim_V_leq_binom_n_s : (Module.finrank ℚ (vector_space_on_N X s k))
  ≤ (Nat.choose n s) :=by
  unfold vector_space_on_N
  exact le_trans (finrank_span_le_card (R := ℚ)
    (Set.range (incidence_matrix X s k).row)) (card_incidence_matrix X n s k)



lemma s_leq_k (h_card : #(μ_set X k p F) = s + 1) (hμ': μ_set' s p μ = (μ_set X k p F)):
    s ≤ k :=by
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
    rw [Finset.sup_eq_mem_and_le L k hkL (fun r => mem_range_succ_iff.mp
      (mem_of_mem_filter (r: ℕ) r.property))]
    apply Finset.card_le_sup_id_succ
  have hμL : #(μ_set' s p μ) ≤ #L := by
    rw [hμ']
    unfold μ_set
    unfold L
    simp only [Subtype.exists, exists_prop, mem_powersetCard, exists_and_right]
    apply Finset.card_le_card_of_surjOn (fun i : ℕ ↦ (i : ZMod p))
    unfold Set.SurjOn
    intro x hx
    simp only [coe_filter, mem_range, Set.mem_image, Set.mem_setOf_eq]
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx
    obtain ⟨A, ⟨B, hAB⟩ ⟩ := hx
    use #(A.val.val ∩ B.val.val)
    constructor
    · constructor
      · apply Order.lt_add_one_iff.mpr
        simp_rw [← (mem_powersetCard.mp A.val.2).right]
        exact card_le_card (inter_subset_left)
      · use A
        use B
    · exact hAB
  rw [← hμ'] at h_card
  rw [h_card] at hμL
  exact Nat.le_of_lt_succ (le_trans hμL hL)

instance: Module.Finite ℚ (vector_space_on_N X s k):=
  FiniteDimensional.finiteDimensional_submodule (vector_space_on_N X s k)

instance (a: ZMod p) (ha: a ≠ 0): Invertible a := by exact invertibleOfNonzero ha


lemma row_N_i_k_in_V (p : ℕ) [hp : Fact p.Prime]
    (F: Finset (powersetCard k X)) [hF: Fact (Nonempty F)]
    (i: Fin (s + 1)) (u: powersetCard i X )
    (μ : Fin (s + 1) →  ZMod p)
    (h_card : #(μ_set X k p F) = s + 1) (hμ': μ_set' s p μ = (μ_set X k p F)):
    incidence_matrix X i k u ∈ vector_space_on_N X s k := by
  have h1: ((Nat.choose (k - i) (s - i)) • (incidence_matrix X i k)) u
    ∈ vector_space_on_N X s k := by
    rw [← N_transpose_N_eq_coe_N, Matrix.mul_apply_eq_vecMul, Matrix.vecMul_eq_sum]
    apply Submodule.sum_mem
    intro v hv
    apply Submodule.smul_mem
    unfold vector_space_on_N; unfold Matrix.row
    rw [@Submodule.mem_span_range_iff_exists_fun]
    use fun (x: powersetCard s X)=> if x = v then (1: ℚ) else 0
    simp only [univ_eq_attach, ite_smul, one_smul, zero_smul, sum_ite_eq', mem_attach, ↓reduceIte]
  rw [Pi.smul_def] at h1
  simp only [nsmul_eq_mul] at h1
  have h2:  (Nat.cast (R := ℚ) ((k - i).choose (s - i)))⁻¹ •
    ((Nat.cast (R := ℚ) ((k - i).choose (s - i))) • incidence_matrix X (i) k u)
    ∈ vector_space_on_N X s k := Submodule.smul_mem (vector_space_on_N X s k)
      ((Nat.cast (R := ℚ) ((k - i).choose (s - i)))⁻¹) h1
  rw [smul_smul] at h2
  have hinvertible: Invertible (Nat.cast (R := ℚ ) ((k - i).choose (s - i))) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (by_contra (fun hzero =>
    (Nat.not_lt.mpr (s_leq_k X s k p F μ h_card hμ'))
    (lt_of_tsub_lt_tsub_right (Nat.choose_eq_zero_iff.mp
    (Function.notMem_support.mp hzero))))))
  rw [inv_mul_cancel_of_invertible] at h2
  simp only [one_smul] at h2
  exact h2


omit hp in
lemma finrank_span_row_M_leq_dim_V (p : ℕ) [hp : Fact p.Prime]
  (F: Finset (powersetCard k X)) [hF: Fact (Nonempty F)]
  (a : Fin (s + 1) → ZMod p)
  (μ : Fin (s + 1) →  ZMod p)
  (h_card : #(μ_set X k p F) = s + 1) (hμ': μ_set' s p μ = (μ_set X k p F))
  :
  Module.finrank ℚ  (Submodule.span ℚ (Set.range (gram_M X s k p a).row))
  ≤ (Module.finrank ℚ  (vector_space_on_N X s k)) :=by
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
  exact (row_N_i_k_in_V X s k p F i u μ h_card hμ')

lemma rank_M_leq_rank_V
  (F: Finset (powersetCard k X)) [hF: Fact (Nonempty F)]
  (a : Fin (s + 1) → ZMod p)
  (μ : Fin (s + 1) →  ZMod p)
  (h_card : #(μ_set X k p F) = s + 1) (hμ': μ_set' s p μ = (μ_set X k p F))
  : Matrix.rank (gram_M X s k p a)
  ≤ (Module.finrank ℚ (vector_space_on_N X s k)) :=by
  exact le_of_eq_of_le (Matrix.rank_eq_finrank_span_row (gram_M X s k p a))
    (finrank_span_row_M_leq_dim_V X s k p F a μ h_card hμ')

omit hp hF in
lemma det_M_neq_0_rank_M_eq_card_F (a : Fin (s + 1) → ZMod p):
    (Matrix.det (M_minor X s k p F a)) ≠ 0 →
    Matrix.rank (M_minor X s k p F a) = #F :=
  fun h => by simp_rw [Matrix.rank_of_isUnit (M_minor X s k p F a)
    ((Matrix.isUnit_iff_isUnit_det (M_minor X s k p F a)).mpr (Ne.isUnit h)), Fintype.card_coe]

omit hF in
lemma det_M_neq_0 (μ : Fin (s + 1) →  ZMod p) (huniform_mod: uniform_mod X s k p F μ)
  (hs : s ≠ 0) (hμ : ∀ (i j : Fin (s + 1)), i ≠ j → μ i  ≠ μ j)
  (hintersect: intersecting_mod X s k p F μ): ∃ (a : Fin (s + 1) → ZMod p),
    (Matrix.det (M_minor X s k p F a)) ≠ 0 := by
  obtain ⟨a, ha⟩ := nonzero_det_W_minor X s k p F hs μ huniform_mod hμ hintersect
  have h1 := Matrix.det_ne_zero_of_rat_cast (weighted_binom_matrix X s k p F a)
  rw [map_weighted_binom_matrix_eq_minor] at h1
  use a
  apply h1
  apply Matrix.det_ne_zero_of_mod_cast p
  unfold W_minor at ha
  exact ha


theorem Frankl_Wilson_mod
    (F: Finset (powersetCard k X)) [hF: Fact (Nonempty F)]
    (μ : Fin (s + 1) →  ZMod p)
    (hs : s ≠ 0)
    (h_card : #(μ_set X k p F) = s + 1) (hμ': μ_set' s p μ = (μ_set X k p F))
    (hμ : ∀ (i j : Fin (s + 1)), i ≠ j → μ i  ≠ μ j)
    (huniform_mod: uniform_mod X s k p F μ)
    (hintersect: intersecting_mod X s k p F μ): #F ≤ Nat.choose n s  := by
  obtain ⟨a, ha⟩ := det_M_neq_0 X s k p F μ huniform_mod hs hμ hintersect
  rw [← det_M_neq_0_rank_M_eq_card_F X s k p F a ha]
  exact le_trans (rank_minor_le_M X s k p F a) (le_trans
    (rank_M_leq_rank_V X s k p F a μ h_card hμ') (dim_V_leq_binom_n_s X n s k))

end Frankl_Wilson_mod
