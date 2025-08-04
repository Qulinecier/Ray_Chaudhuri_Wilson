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




open Finset
variable {α : Type} (n : ℕ) [DecidableEq α]
variable {X: Finset α} (F: Finset X.powerset)

def uniform {X: Finset α} (F: Finset X.powerset) (k : ℕ) : Prop := ∀ (A : F), #A.val.val = k

def intersecting {X: Finset α} (F: Finset X.powerset) (L : Set ℕ) :=
  ∀ (A B: F), #(A.val.val ∩ B.val.val) ∈ L

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
    fun B => ∑ S ∈ powersetCard s X, if #(A ∩ S)  = μ then (subset_indicator F S B) else 0

variable (r: ℕ)
variable (A B : F)

/--Projection map from S to (A∩S, (B\A)∩ S)-/
def intersect_i: (a : Finset α) → a ∈ {S ∈ powersetCard s X | #(↑↑A ∩ S) = r ∧ S ⊆ ↑↑B}
    → Finset α × Finset α :=
  fun S ↦ fun _ ↦ ((A: Finset α) ∩ S, ((B: Finset α) \ (A: Finset α)) ∩ S)

/--Reverse map from (S.1, S.2) to S.1 ∪ S.2-/
def intersect_j: (a : Finset α × Finset α) →
    a ∈ powersetCard r (↑↑A ∩ ↑↑B) ×ˢ powersetCard (s - r) (↑↑B \ ↑↑A) → Finset α :=
  fun S ↦ fun _ ↦ S.1 ∪ S.2

/--
The cardinality of {S∈𝓟ₛ(X)| |A∩S|=r and S⊆B} is equal to the number of ways choosing r elements
in A∩B and s-r elements in B\A.
#{S∈𝓟ₛ(X)| |A∩S|=r and S⊆B} = #𝓟ᵣ(A∩B) × #𝓟ₛ₋ᵣ(B\A)
-/
lemma card_powerset_card_product (hrs : r ≤ s) : #{S ∈ powersetCard s X | #(A.val.val ∩ S) = r
    ∧ (S: Finset α) ⊆ (B: Finset α)} = #((powersetCard r ((A: Finset α) ∩ (B: Finset α))) ×ˢ
    (powersetCard (s-r) ((B: Finset α) \ (A: Finset α)))) :=by
  apply Finset.card_bij' (intersect_i F s r A B) (intersect_j F s r A B)
  · intro S hS
    unfold intersect_i
    unfold intersect_j
    simp only
    simp only [mem_filter, mem_powersetCard] at hS
    cases' hS with hS1 hS3
    cases' hS1 with hS1 hS2
    cases' hS3 with hS3 hS4
    rw [← union_inter_distrib_right]
    simp only [union_sdiff_self_eq_union, inter_eq_right]
    exact subset_trans hS4 subset_union_right
  · intro S hS
    unfold intersect_i
    unfold intersect_j
    simp only [mem_product, mem_powersetCard] at hS
    cases' hS with hS1 hS3
    cases' hS1 with hS1 hS2
    cases' hS3 with hS3 hS4
    rw [inter_union_distrib_left]
    have hdisj : Disjoint (A: Finset α) S.2 := by
      apply disjoint_of_subset_right hS3
      exact disjoint_sdiff
    rw [disjoint_iff_inter_eq_empty.mp hdisj, union_empty, inter_union_distrib_left,
      inter_comm, inter_eq_left.mpr (subset_inter_iff.mp hS1).left]
    have hdisj2 : Disjoint ((B: Finset α) \ (A:Finset α)) (A: Finset α) := by exact
      sdiff_disjoint
    have h1: ((B: Finset α) \ (A:Finset α)) ∩ S.1 ⊆
        ((B: Finset α) \ (A:Finset α)) ∩ (A: Finset α) := by
      exact inter_subset_inter_left (subset_inter_iff.mp hS1).left
    rw [disjoint_iff_inter_eq_empty.mp hdisj2] at h1
    rw [subset_empty.mp h1, empty_union, inter_eq_right.mpr hS3]
  · intro S hS
    unfold intersect_i
    simp only [mem_product, mem_powersetCard, inter_subset_left, true_and]
    simp only [mem_filter, mem_powersetCard] at hS
    cases' hS with h1 h2
    cases' h2 with h2 h3
    cases' h1 with h1 h4
    refine' ⟨⟨inter_subset_inter_left h3, h2⟩, ?_⟩
    have h5: ((B: Finset α) \ (A: Finset α)) ∩ S = ((B: Finset α) ∩ S) \ ((A: Finset α) ∩ S) := by
      ext x
      simp only [mem_inter, mem_sdiff, not_and]
      constructor
      · intro hx
        cases' hx with hx1 hx2
        cases' hx1 with hx1 hx3
        refine' ⟨⟨hx1, hx2⟩ , ?_⟩
        intro hx4
        exfalso
        apply hx3
        exact hx4
      · intro hx
        cases' hx with hx1 hx2
        cases' hx1 with hx1 hx3
        refine' ⟨⟨hx1, ?_⟩ , hx3⟩
        by_contra hA
        apply hx2
        · exact hA
        · exact hx3
    rw [h5, inter_eq_right.mpr h3, card_sdiff, h4, h2]
    exact inter_subset_right
  · intro S hS
    unfold intersect_j
    simp only [mem_filter, mem_powersetCard]
    simp only [mem_product, mem_powersetCard] at hS
    cases' hS with h1 h3
    cases' h1 with h1 h2
    cases' h3 with h3 h4
    refine' ⟨⟨?_, ?_⟩ , ⟨?_,
      union_subset (subset_inter_iff.mp h1).right (Subset.trans h3 sdiff_subset)⟩⟩
    · intro x hx
      by_cases hxS: x ∈ S.1
      · exact (mem_powerset.mp A.val.property) (mem_of_mem_filter x (h1 hxS))
      · have h5: x ∈ S.2 :=by
          rw [mem_union] at hx
          cases' hx with hx1 hx2
          · exfalso
            apply hxS
            exact hx1
          · exact hx2
        exact (mem_powerset.mp B.val.property) (mem_sdiff.mp (h3 h5)).left
    · have h5: #(S.1 ∪ S.2) = #S.1 + #S.2 := by
        rw [card_union_eq_card_add_card]
        apply disjoint_of_subset_left h1
        apply disjoint_of_subset_right h3
        apply disjoint_of_subset_left (inter_subset_left)
        exact disjoint_sdiff
      rw [h5, h2, h4, Nat.add_sub_cancel' hrs]
    · have hdisj: Disjoint (A: Finset α) S.2 := by
        apply disjoint_of_subset_right h3
        exact disjoint_sdiff
      rw [inter_union_distrib_left, inter_comm, inter_eq_left.mpr (subset_inter_iff.mp h1).left,
        disjoint_iff_inter_eq_empty.mp hdisj, union_empty]
      exact h2

/--
∑(S_bar: S∈𝓟ₛ(X), |S∩A|=r) = ∑μ∈L, binom(μ, r) * binom(k-μ, s-r)* H,
where H is the uniform intersection indicator
-/
lemma vector_sum_eq_intersection_sum (hintersect : intersecting F L)
    (huniform: uniform F k) (r : ℕ) (hrs : r ≤ s) (A : F):
    subset_intersection_indicator F s A r =
    ∑ (l∈ L), (Nat.choose l r) * (Nat.choose (k - l) (s - r))
    * (intersection_indicator F A l) := by
  unfold subset_intersection_indicator
  funext B
  simp only [Finset.sum_apply]
  unfold subset_indicator
  simp only [Pi.natCast_def, Pi.mul_apply, mul_ite, mul_one, mul_zero]
  unfold intersecting at hintersect
  have hAB := hintersect A B

  have h1: (∑ S ∈ powersetCard s X, if #(A.val.val ∩ S) = r then
      (if (S: Finset α) ⊆ (B: Finset α) then (1: ℝ) else 0) else 0)
    = ∑ (x ∈  L), ∑ S ∈  powersetCard s X,
    if ((#(A.val.val ∩ S) = r) ∧ ((S: Finset α) ⊆ (B: Finset α)))
    then (intersection_indicator F A x B) else 0 := by
    unfold intersection_indicator
    let p := ∑ S ∈ powersetCard s X, if #(A.val.val ∩ S) = r then
        (if (S: Finset α) ⊆ (B: Finset α) then (1: ℝ) else 0) else 0
    have h : p = ∑ x ∈  L, if #(A.val.val ∩ B.val.val) = x then p else 0 := by
      let f := fun x => if #(A.val.val ∩ B.val.val) = x then p else 0
      have h₀ : ∀ b ∈ L, b ≠ #(A.val.val ∩ B.val.val) → f b = 0 :=
        fun b a a ↦ if_neg (id (Ne.symm a))
      have h₁ : #(A.val.val ∩ B.val.val) ∉ L → f (#(A.val.val ∩ B.val.val)) = 0 := by
        intro h
        exfalso
        exact h hAB
      rw [Finset.sum_eq_single (#(A.val.val ∩ B.val.val)) h₀ h₁]
      exact (if_pos rfl).symm
    unfold p at h
    rw [h]
    congr! with x hx
    by_cases hP: #(A.val.val ∩ B.val.val) = x
    · rw [if_pos hP, inter_comm, if_pos hP]
      congr with S
      by_cases hAS: #(A.val.val ∩ S) = r
      · simp [hAS]
      · simp [hAS]
    · rw [if_neg hP, inter_comm, if_neg hP]
      simp only [univ_eq_attach, ite_self, sum_const_zero]

  rw [h1]

  congr! with μ hμ
  rw [(sum_filter (fun (S: Finset α) => (#(A.val.val ∩ S) = r)
    ∧ ((S: Finset α) ⊆ (B: Finset α))) fun a ↦ (intersection_indicator F A μ B)).symm]
  rw [sum_const]
  simp only [nsmul_eq_mul]
  unfold intersection_indicator
  by_cases hinter: #(B.val.val ∩ A.val.val) = μ
  · simp [hinter]
    unfold uniform at huniform
    have hB := huniform B
    have hA := huniform A
    rw [card_powerset_card_product F s r A B hrs]
    simp only [card_product, card_powersetCard, Nat.cast_mul]
    rw [inter_comm, hinter]
    have hdiff: (B: Finset α) \ (A: Finset α) = (B: Finset α) \ ((B: Finset α) ∩ (A: Finset α)) :=by
      simp only [sdiff_inter_self_left]
    rw [hdiff, card_sdiff, hB, hinter]
    simp only [inter_subset_left]
  · rw [if_neg hinter]
    simp only [mul_zero]


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

lemma subset_vector_span_dim_le (h: Submodule.span ℝ
  (toSet (subset_indicator_set F s)) = (⊤: Submodule ℝ (F → ℝ)))
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

instance: Fintype {x | x ∈ F} := by exact Set.fintypeMemFinset F

/-Set of H₀-/
noncomputable def subset_H :=
  Finset.image (fun (S : X.powerset) => (intersection_indicator F S k: F → ℝ)) F

/--span{intersecting indicator H} = ℝ^𝓕-/
lemma span_H (huniform: uniform F k): (⊤: Submodule ℝ (F → ℝ)) =
    Submodule.span ℝ (subset_H F k):=by
  refine' le_antisymm ?_ ?_
  · intro x hx
    unfold subset_H
    simp only [coe_image]
    have hx_coe: x = ∑ (S:F), (x S) • intersection_indicator F S k := by
      nth_rw 1 [(Basis.sum_repr (Pi.basisFun ℝ F) x).symm]
      congr! with A hA
      simp only [Pi.basisFun_apply]
      unfold intersection_indicator
      funext B
      by_cases hB: A = B
      · rw [hB]
        simp only [Pi.single_eq_same, inter_self]
        have hBk:= huniform B
        rw [if_pos]
        exact hBk
      · rw [Pi.single_eq_of_ne' hB 1]
        rw [if_neg]
        by_contra hAB
        have hAB_new : (A:Finset α ) ≠ (B: Finset α ) :=by
          by_contra h1
          exact hB (Subtype.eq (Subtype.eq h1))
        apply hAB_new
        have hBk:= huniform B
        have hAk:= huniform A
        have hkk: k ≤ k := by exact Nat.le_refl k
        have hBAB: #(B: Finset α) ≤ #((B: Finset α) ∩ (A: Finset α)) := by
          nth_rw 1 [← hBk] at hkk
          rw [← hAB] at hkk
          exact hkk
        have hABA: #(A: Finset α) ≤ #((B: Finset α) ∩ (A: Finset α)) := by
          nth_rw 1 [← hAk] at hkk
          rw [← hAB] at hkk
          exact hkk
        exact Eq.trans ((subset_iff_eq_of_card_le hABA).mp inter_subset_right).symm
          ((subset_iff_eq_of_card_le hBAB).mp inter_subset_left)
    rw [hx_coe]
    apply sum_mem
    intro A hA
    rw [Submodule.mem_span]
    intro V hV
    simp only [Set.image_subset_iff] at hV
    have hAp : ⟨A.val.val, A.val.property⟩ ∈ F :=by
      simp only [Subtype.coe_eta, coe_mem]
    have h:= hV hAp
    simp only [Set.mem_preimage, SetLike.mem_coe] at h
    exact Submodule.smul_mem V (x A) h
  · exact fun ⦃x⦄ a ↦ trivial

variable (hL: k∈L)

noncomputable def subset_G := ⋃ (r : Fin (s + 1)),
    toSet (Finset.image (fun (A: X.powerset) =>
    subset_intersection_indicator F s A r) F)

instance: Membership (Finset α) (Finset X.powerset)where
  mem := fun A => fun B => ∃ x ∈ A, x.val = B

noncomputable def enumL {s: ℕ} {L : Finset ℕ} (hL_card: #L = s + 1) : L ≃ Fin (s + 1) :=
  Finset.equivFinOfCardEq hL_card

variable (hL_card : #L = s + 1) (hL: k∈L)


noncomputable def coe_matrix: Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ := fun r => fun l =>
  (Nat.choose ((enumL hL_card).symm l) r) * (Nat.choose (k - ((enumL hL_card).symm l)) (s - r))

open Nat

def root_set := {(enumL hL_card).symm l | (l: Fin s)}

noncomputable def real_choose_poly (r : ℕ ) : Polynomial ℝ := (1/ (r !): ℝ ) • (descPochhammer ℝ r)

lemma real_choose_poly_eval_nat_choose (r u: ℕ): Polynomial.eval (u: ℝ) (real_choose_poly r)
  = (Nat.choose u r : ℝ ):= by
  unfold real_choose_poly
  rw [Nat.choose_eq_descFactorial_div_factorial,
    Polynomial.eval_smul, descPochhammer_eval_eq_descFactorial]
  simp only [one_div, smul_eq_mul]
  rw [mul_comm, Nat.cast_div]
  · rfl
  · exact factorial_dvd_descFactorial u r
  · exact cast_ne_zero.mpr (factorial_ne_zero r)

noncomputable def sum_coe_poly (v: Fin (s + 1) → ℝ) := ∑ (i : Fin (s + 1)), (v i) •
    (real_choose_poly (i : ℕ)) * (real_choose_poly (s - i)).comp
    ((Polynomial.C (k: ℝ)) - Polynomial.X)

noncomputable def sum_coe_poly' (v: Fin (s + 1) → ℝ) := ∑ (i : Fin (s + 1)), (v i) • ((1/(i !): ℝ ) •
    ((1/((s - i)!): ℝ ) • (descPochhammer ℝ i) *
    ((descPochhammer ℝ (s - i)).comp ((Polynomial.C (k: ℝ)) - Polynomial.X))))

/--A statement saying that all elements in root_set are the roots of sum_coe_poly-/
lemma sum_coe_poly'_natDegree_le_s : Polynomial.natDegree (sum_coe_poly' k s v) ≤ s := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r hr
    refine' le_trans (Polynomial.natDegree_smul_le (v r) (((1/(r !): ℝ ) • ((1/((s - r)!): ℝ ) •
      (descPochhammer ℝ r) * ((descPochhammer ℝ (s- r)).comp ((Polynomial.C (k: ℝ)) - Polynomial.X)))))) ?_
    refine' le_trans (Polynomial.natDegree_smul_le _ _) ?_
    rw [smul_mul_assoc]
    refine' le_trans (Polynomial.natDegree_smul_le _ _) ?_
    by_cases h1: descPochhammer ℝ r = 0
    · rw [h1]
      simp only [map_natCast, zero_mul, Polynomial.natDegree_zero, _root_.zero_le]
    · by_cases h2: (descPochhammer ℝ (s - r)).comp (Polynomial.C (k: ℝ) - Polynomial.X) = 0
      · rw [h2]
        simp only [mul_zero, Polynomial.natDegree_zero, _root_.zero_le]
      · rw [Polynomial.natDegree_mul]
        · simp only [descPochhammer_natDegree]
          rw [Polynomial.natDegree_comp]
          simp only [descPochhammer_natDegree]
          have h3 : (Polynomial.C (k: ℝ) - Polynomial.X).natDegree =
              (Polynomial.X :Polynomial ℝ).natDegree := by
            apply Polynomial.natDegree_sub_eq_right_of_natDegree_lt
            rw [Polynomial.natDegree_C (k: ℝ)]
            rw [Polynomial.natDegree_X]
            exact Nat.one_pos

          rw [h3]
          rw [Polynomial.natDegree_X]
          simp only [mul_one, ge_iff_le]
          rw [← add_tsub_assoc_of_le]
          · simp only [add_tsub_cancel_left, le_refl]
          · exact Fin.is_le r
        · exact h1
        · exact h2

lemma number_of_roots (v: Fin (s + 1) →  ℝ ) : #(sum_coe_poly' k s v).roots.toFinset ≤ s :=by
  have h1:= le_trans (Polynomial.card_roots' (sum_coe_poly' k s v))
    (sum_coe_poly'_natDegree_le_s k s)
  have h2:= Multiset.toFinset_card_le (sum_coe_poly' k s v).roots
  exact Nat.le_trans h2 h1


lemma card_roots_gt_natDegree_zero_polynomial (p : Polynomial ℝ) :
  Multiset.card p.roots > p.natDegree → p = 0 := by
  intro hp
  exfalso
  exact (lt_irrefl _ (lt_of_le_of_lt (Polynomial.card_roots' p) hp))

noncomputable def roots_set:= Finset.image (fun (l: Fin (s + 1)) => ((enumL hL_card).symm l: ℝ)) ⊤

lemma roots_subset_roots_set (h: ∀ (l : Fin (s+1)),
  Polynomial.eval (((enumL hL_card).symm l):ℝ)
  (sum_coe_poly' k s v) = 0): ¬ sum_coe_poly' k s v = 0 →
  (roots_set s L hL_card) ⊆ (sum_coe_poly' k s v).roots.toFinset :=by
  intro hne_zero x hx
  simp only [Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, Polynomial.IsRoot.def]
  constructor
  · exact hne_zero
  · unfold roots_set at hx
    simp only [top_eq_univ, mem_image, mem_univ, true_and] at hx
    cases' hx with l hl
    rw [← hl]
    exact h l

lemma descPochhammer_comp_eval_eq_descFactorial_comp (l : Fin (s + 1)) (i:ℕ ) (hrL: ∀(r:L), r≤k):
    Polynomial.eval (((enumL hL_card).symm l):ℝ )
    ((descPochhammer ℝ (s - i)).comp ((k: Polynomial ℝ) - Polynomial.X))
    = Nat.descFactorial (k - ((enumL hL_card).symm l): ℕ) (s- i):= by
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_sub, Polynomial.eval_natCast, Polynomial.eval_X]
  have h2: (k - ((enumL hL_card).symm l): ℝ ) = ((k - ((enumL hL_card).symm l): ℕ): ℝ) := by
    norm_cast
    rw [Int.ofNat_sub]
    rw [← @Int.subNatNat_eq_coe]
    exact hrL ((enumL hL_card).symm l)
  rw [h2]
  rw [descPochhammer_eval_eq_descFactorial]

lemma sum_cast (v : Fin (s + 1) → ℝ) : ∑ (i: Fin (s + 1)), (v i • ((i: ℕ)!: ℝ )⁻¹ •
    ((s - (i: ℕ ) : ℕ )!:ℝ)⁻¹ ) •  ( (Nat.descFactorial ((enumL hL_card).symm l) (i: ℕ ))
    * (Nat.descFactorial (k - ((enumL hL_card).symm l): ℕ) (s- (i: ℕ ))):ℝ) = ∑ x, (v x) •
    ↑((((enumL hL_card).symm l): ℕ).descFactorial ↑x / (↑x)! *
        ((k - ↑((enumL hL_card).symm l)).descFactorial (s - ↑x) / (s - ↑x)!))  :=by
  congr! 1 with x hx
  simp only [smul_eq_mul, cast_mul]
  rw [mul_assoc (v x) (((x: ℕ)!: ℝ )⁻¹ * ((s - (x: ℕ ) : ℕ )!:ℝ)⁻¹ ) _]
  rw [mul_assoc (((x: ℕ)!: ℝ )⁻¹) (((s - (x: ℕ ) : ℕ )!:ℝ)⁻¹ ) _]
  rw [← mul_assoc (((s - (x: ℕ ) : ℕ )!:ℝ)⁻¹ ) _ _]
  rw [mul_comm (((s - (x: ℕ ) : ℕ )!:ℝ)⁻¹ ) _]
  rw [mul_assoc _ (((s - (x: ℕ ) : ℕ )!:ℝ)⁻¹ ) _]
  rw [← mul_assoc (((x: ℕ)!: ℝ )⁻¹) _ _]
  simp only [mul_eq_mul_left_iff]
  left
  rw [Nat.cast_div]
  rw [mul_comm (((x: ℕ)!: ℝ )⁻¹) _]
  have h1: (Nat.descFactorial ((enumL hL_card).symm l) (x: ℕ )) * (((x: ℕ)!: ℝ )⁻¹) =
    (Nat.descFactorial ((enumL hL_card).symm l) (x: ℕ )) / ((x: ℕ)!: ℝ ) := by
    exact rfl
  rw [h1]
  · simp only [mul_eq_mul_left_iff]
    left
    rw [mul_comm]
    rw [Nat.cast_div]
    · rfl
    · exact factorial_dvd_descFactorial (k - ↑((enumL hL_card).symm l)) (s - ↑x)
    · exact cast_ne_zero.mpr (Nat.factorial_ne_zero (s- (x:ℕ)))
  · exact factorial_dvd_descFactorial ↑((enumL hL_card).symm l) ↑x
  · exact cast_ne_zero.mpr (Nat.factorial_ne_zero (x:ℕ))

lemma sum_coe_poly'_eval_zero (hv: (∑ (i: Fin (s + 1)), v i • fun l ↦
  ((((enumL hL_card).symm l):ℕ ).choose (i: ℕ) : ℝ) * ((k - ((enumL hL_card).symm l: ℕ)).choose (s - (i:ℕ)): ℝ)) = 0) (hrL: ∀(r:L), r≤k)
  : ∀ (l : Fin (s+1)), Polynomial.eval (((enumL hL_card).symm l):ℝ) (sum_coe_poly' k s v) = 0 :=by
  intro l
  have h1:= congrFun hv l
  simp only [sum_apply, Pi.smul_apply, Pi.zero_apply] at h1
  unfold sum_coe_poly'
  simp only [one_div, map_natCast, Algebra.smul_mul_assoc]
  have h2 : ∑ (x: Fin (s+1)), v x • ↑((((enumL hL_card).symm l):ℕ ).descFactorial ↑x / (↑x)! *
    ((k - ↑((enumL hL_card).symm l)).descFactorial (s - ↑x) / (s - ↑x)!))
    = ∑ (x: Fin (s+1)), (v x) • ((Nat.choose ((enumL hL_card).symm l: ℕ) (x : ℕ)) *
    (Nat.choose (k - ((enumL hL_card).symm l: ℕ )) (s - x : ℕ ):ℝ ): ℝ)
    :=by
    congr! 1 with x hx
    rw [Nat.choose_eq_descFactorial_div_factorial]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_cast
  rw [← h2] at h1
  rw [Polynomial.eval_finset_sum]
  have h3: ∑ (i: Fin (s + 1)), Polynomial.eval (((enumL hL_card).symm l):ℝ )
      (v i • ((i: ℕ)!: ℝ )⁻¹ • ((s - (i: ℕ ) : ℕ )!:ℝ)⁻¹ • (descPochhammer ℝ (i: ℕ )
      * (descPochhammer ℝ (s - (i:ℕ ))).comp ((k: Polynomial ℝ) - Polynomial.X)))
      = ∑ (i: Fin (s + 1)), (v i • ((i: ℕ)!: ℝ )⁻¹ • ((s - (i: ℕ ) : ℕ )!:ℝ)⁻¹ ) •
      (Polynomial.eval (((enumL hL_card).symm l):ℝ )
      ((descPochhammer ℝ (i: ℕ )
      * (descPochhammer ℝ (s - (i:ℕ ))).comp ((k: Polynomial ℝ) - Polynomial.X)))) := by
    congr! 1 with x hx
    rw [Polynomial.eval_smul]
    rw [Polynomial.eval_smul]
    rw [Polynomial.eval_smul]
    rw [← smul_assoc]
    rw [← smul_assoc]
    rw [smul_assoc (v x) _ _]
  rw [h3]
  have h4: ∑ (i: Fin (s + 1)), (v i • ((i: ℕ)!: ℝ )⁻¹ • ((s - (i: ℕ ) : ℕ )!:ℝ)⁻¹ ) •
    (Polynomial.eval (((enumL hL_card).symm l):ℝ )
    ((descPochhammer ℝ (i: ℕ )
    * (descPochhammer ℝ (s - (i:ℕ ))).comp ((k: Polynomial ℝ) - Polynomial.X))))
    = ∑ (i: Fin (s + 1)), (v i • ((i: ℕ)!: ℝ )⁻¹ • ((s - (i: ℕ ) : ℕ )!:ℝ)⁻¹ ) •
    ( (Polynomial.eval ((enumL hL_card).symm l:ℝ ) (descPochhammer ℝ (i: ℕ )))
    * (Polynomial.eval (((enumL hL_card).symm l):ℝ ) ((descPochhammer ℝ (s - (i:ℕ ))).comp
    ((k: Polynomial ℝ) - Polynomial.X)))) := by
      congr! 1 with x hx
      rw [Polynomial.eval_mul]
  rw [h4]
  have h5: ∑ (i: Fin (s + 1)), (v i • ((i: ℕ)!: ℝ )⁻¹ • ((s - (i: ℕ ) : ℕ )!:ℝ)⁻¹ ) •
    ( (Polynomial.eval ((enumL hL_card).symm l:ℝ ) (descPochhammer ℝ (i: ℕ )))
    * (Polynomial.eval (((enumL hL_card).symm l):ℝ ) ((descPochhammer ℝ (s - (i:ℕ ))).comp
    ((k: Polynomial ℝ) - Polynomial.X))))
    = ∑ (i: Fin (s + 1)), (v i • ((i: ℕ)!: ℝ )⁻¹ • ((s - (i: ℕ ) : ℕ )!:ℝ)⁻¹ ) •
    ( (Nat.descFactorial ((enumL hL_card).symm l) (i: ℕ ))
    * (Nat.descFactorial (k - ((enumL hL_card).symm l): ℕ) (s- (i: ℕ ))):ℝ) := by
      congr! 1 with x hx
      rw [descPochhammer_eval_eq_descFactorial]
      rw [descPochhammer_comp_eval_eq_descFactorial_comp]
      exact hrL
  rw [h5]
  have h6: ∑ (i: Fin (s + 1)), (v i • ((i: ℕ)!: ℝ )⁻¹ • ((s - (i: ℕ ) : ℕ )!:ℝ)⁻¹ ) •
    ( (Nat.descFactorial ((enumL hL_card).symm l) (i: ℕ ))
    * (Nat.descFactorial (k - ((enumL hL_card).symm l): ℕ) (s- (i: ℕ ))):ℝ) = ∑ x, (v x) •
    ↑((((enumL hL_card).symm l): ℕ).descFactorial ↑x / (↑x)! *
        ((k - ↑((enumL hL_card).symm l)).descFactorial (s - ↑x) / (s - ↑x)!)) :=by
    exact sum_cast k s L hL_card  v
  rw [h6]
  rw [h1]

lemma roots_card_le (v: Fin (s + 1) → ℝ) (hv: (∑ (i: Fin (s + 1)), v i • fun l ↦
    ((((enumL hL_card).symm l):ℕ ).choose (i: ℕ) : ℝ)
    * ((k - ((enumL hL_card).symm l: ℕ)).choose (s - (i:ℕ)): ℝ)) = 0)
    (hrL: ∀(r:L), r≤k) : ¬ sum_coe_poly' k s v = 0 →
    (sum_coe_poly' k s v).roots.toFinset.card ≥ #(roots_set s L hL_card) := by
  intro h
  have h1: (roots_set s L hL_card) ⊆ (sum_coe_poly' k s v).roots.toFinset :=by
    intro y hy
    unfold roots_set at hy
    simp only [top_eq_univ, mem_image, mem_univ, true_and] at hy
    cases' hy with x hx
    simp only [one_div, map_natCast, Algebra.smul_mul_assoc, Multiset.mem_toFinset,
      Polynomial.mem_roots', ne_eq, Polynomial.IsRoot.def]
    refine' ⟨h, ?_⟩
    rw [← hx, sum_coe_poly'_eval_zero _ _ _ _ hv hrL]
  exact card_le_card h1

noncomputable def enumL_f : ℝ → Fin (s + 1) :=
  fun x =>
    if hx : ∃ (l : L), (l : ℝ) = x then
      enumL hL_card (Classical.choose hx)
    else
      0

lemma card_roots_set_s_plus_1 : #(roots_set s L hL_card) = s+1 := by
  have hfin : #(⊤: Finset (Fin (s+1))) = s + 1 := by
    simp only [top_eq_univ, Finset.card_univ, Fintype.card_fin]

  refine' le_antisymm ?_ ?_
  ·
    have h1: #(roots_set s L hL_card) ≤ #(⊤: Finset (Fin (s+1))) := by
      unfold roots_set
      apply Finset.card_image_le
    simp only [top_eq_univ, Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  · have h1: #(⊤: Finset (Fin (s+1))) ≤ #(roots_set s L hL_card):= by
      apply Finset.card_le_card_of_surjOn (enumL_f s L hL_card)
      unfold Set.SurjOn
      intro x hx
      unfold enumL_f
      simp only [Set.mem_image]
      use (enumL (hL_card)).symm x
      constructor
      · simp only [mem_coe]
        unfold roots_set
        simp only [top_eq_univ, mem_image, mem_univ, Nat.cast_inj, true_and, exists_apply_eq_apply]
      · have h1 :  ∃ (l : L), (l : ℝ) = (enumL (hL_card)).symm x := by
          use (enumL (hL_card)).symm x
        split_ifs
        have h2 : (Classical.choose h1) = ((enumL hL_card).symm x: ℝ ) :=
          Classical.choose_spec h1
        have h3: Classical.choose h1 = (enumL hL_card).symm x := by
          rw [Subtype.ext_iff]
          norm_cast at h2
          simp only [Nat.cast_inj]
          exact h2
        rw [h3]
        simp only [Equiv.apply_symm_apply]
    rw [hfin] at h1
    exact h1

lemma fin_case_strong_induction_on {p : Fin (s + 1) → Prop} (a : Fin (s + 1)) (hz : p 0)
    (hi : ∀ n < s, (∀ m, m ≤ n → p m) → p (n + 1)) : p a := by
  let p' : ℕ → Prop := fun x => if x < s + 1 then p x else True
  have hz' : p' 0 := by
    unfold p'
    exact if_true_right.mpr fun a ↦ hz

  have hi' : ∀ (n : ℕ ), (∀ m, m ≤ n → p' m) → p' (n + 1) :=by
    intro n hsucc
    by_cases hns: n + 1 < s + 1
    · unfold p'
      rw [if_pos hns]
      specialize hi n
      unfold p' at hsucc
      norm_cast at hi
      apply hi
      · exact succ_lt_succ_iff.mp hns
      · intro m hm
        specialize hsucc m hm
        rw [if_pos (Nat.lt_trans (Order.lt_add_one_iff.mpr hm) hns )] at hsucc
        norm_cast at hsucc
    · unfold p'
      rw [if_neg hns]
      trivial
  have htrue: p' a := Nat.case_strong_induction_on a hz' hi'
  unfold p' at htrue
  have ha : ↑a < s + 1 := a.is_lt
  rw [if_pos ha] at htrue
  norm_cast at htrue

lemma Finset.card_le_sup_id_succ (L : Finset ℕ) : L.card ≤ (L.sup id) + 1 := by
  have : L ⊆ Finset.range ((L.sup id) + 1) :=
    fun x hx ↦ Finset.mem_range.2 ((Finset.le_sup (f := id) hx).trans_lt (Nat.lt_succ_self _))
  convert Finset.card_mono this
  simp only [card_range]

lemma k_max (hkL: k ∈ L) (hrL: ∀(r:L), r≤k): k = (L.sup id) := by
  have hsup_le : L.sup id ≤ k := Finset.sup_le fun x hx => hrL ⟨x, hx⟩
  have hle_sup : id k ≤ L.sup id :=by exact Finset.le_sup hkL
  exact Nat.le_antisymm hle_sup hsup_le

lemma s_sub_one_le_k (hL_card : #L = s + 1) (hL: k∈L) (hrL: ∀(r:L), r≤k) (hs : 0 < s) :  s - 1 < k := by
  have h1 := Finset.card_le_sup_id_succ L
  have h2:= k_max k L hL hrL
  rw [← h2] at h1
  rw [hL_card] at h1
  omega

lemma coef_zero (hL_card : #L = s + 1) (hL: k∈L) (hs : 0 < s) (hrL: ∀(r:L), r≤k) :
  sum_coe_poly k s v = 0 → ∀ (i : Fin (s + 1)), v i = 0 := by
  have h: s-1 < k :=  s_sub_one_le_k k s L hL_card hL hrL hs
  intro hzero i
  --induction' i using Fin.induction with j hj
  let p: Fin (s + 1) → Prop := fun x => (v x = 0)


  have hz: p (0: Fin (s+1)) := by
    let f: Fin (s + 1) → ℝ := fun i => Polynomial.eval ((0: Fin (s + 1)): ℝ) (v i •
    (real_choose_poly ↑i * (real_choose_poly (s - ↑i)).comp
    ((k: Polynomial ℝ ) - Polynomial.X)))
    have h0:= congrArg (Polynomial.eval ((0: Fin (s + 1)):ℝ)) hzero
    simp only [Polynomial.eval_zero] at h0
    unfold sum_coe_poly at h0
    simp only [one_div, map_natCast, Algebra.smul_mul_assoc] at h0
    rw [Polynomial.eval_finset_sum] at h0
    have h₀ : ∀ (b : Fin (s + 1)), b ≠ 0 → f b = 0 :=by
      intro x hx
      unfold f
      unfold real_choose_poly
      simp only [Fin.val_zero, CharP.cast_eq_zero, one_div, Polynomial.smul_comp,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Polynomial.eval_smul, Polynomial.eval_mul,
        Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_natCast, Polynomial.eval_X,
        sub_zero, smul_eq_mul, _root_.mul_eq_zero, inv_eq_zero, cast_eq_zero]
      right
      right
      right
      left
      rw [descPochhammer_eval_zero]
      rw [if_neg (Fin.val_ne_zero_iff.mpr hx)]
    rw [Finset.sum_eq_single_of_mem (0: Fin (s + 1))] at h0
    · unfold p
      simp only [Fin.val_zero, CharP.cast_eq_zero, tsub_zero, Polynomial.eval_smul,
        Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_natCast,
        Polynomial.eval_X, sub_zero, smul_eq_mul, _root_.mul_eq_zero] at h0
      cases' h0 with hp hp
      · exact hp
      · cases' hp with hp hp
        · exfalso
          unfold real_choose_poly at hp
          simp only [factorial_zero, cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self,
            descPochhammer_zero, one_smul, Polynomial.eval_one] at hp
        · exfalso
          unfold real_choose_poly at hp
          simp only [one_div, Polynomial.eval_smul, smul_eq_mul, _root_.mul_eq_zero, inv_eq_zero,
            cast_eq_zero] at hp
          cases' hp with hp hp
          · have hp':= Nat.factorial_pos s
            rw [hp] at hp'
            exact not_succ_le_zero 0 hp'
          · have hsk: ↑s - 1 < (k: ℝ ):= by
              norm_cast
              zify at h
              rw [Nat.cast_sub hs] at h
              exact h
            exfalso
            have h1 := descPochhammer_pos hsk
            rw [hp] at h1
            exact (lt_self_iff_false 0).mp h1
    · exact mem_univ 0
    · unfold f at h₀
      exact fun b a a ↦ h₀ b a

  apply fin_case_strong_induction_on s i hz
  intro j hjs hj
  have hj1 : (j + 1 : Fin (s + 1)) = (j + 1 : ℕ) := by norm_cast
  rw [hj1]
  generalize hj₁ : j + 1 = j₁ at *
  unfold p
  have hjj : ((j₁ : Fin (s + 1)) : ℕ) = j₁ :=
    (Fin.val_natCast _ _).trans (Nat.mod_eq_of_lt (by omega))
  let f: Fin (s + 1) → ℝ := fun i => Polynomial.eval j₁ (v i • real_choose_poly i *
    (real_choose_poly (s - i)).comp (Polynomial.C (k : ℝ ) - Polynomial.X))
  have h₀ : ∀ (b : Fin (s + 1)), b ≠ (j + 1: Fin (s + 1)) → f b = 0 :=by
    intro x hx
    unfold f
    unfold real_choose_poly
    simp only [one_div, map_natCast, Polynomial.smul_comp, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_sub, Polynomial.eval_natCast, Polynomial.eval_X, smul_eq_mul,
      _root_.mul_eq_zero, inv_eq_zero, cast_eq_zero]
    by_cases hx': x > j + 1
    · right
      right
      right
      left
      have hjs :  j₁ < x := by omega
      exact descPochhammer_eval_coe_nat_of_lt hjs (R := ℝ)
    · right
      left
      rw [hj1] at hx hx'
      have hj1s: j₁ < s + 1 := by omega
      have hx_nat: (x: ℕ ) ≠ j₁ := by
        intro h
        apply hx
        rw [Fin.ext_iff]
        rw [hjj]
        exact h
      have hx_nat': ¬(x: ℕ) > j₁ := by
        intro h
        apply hx'
        simp only [gt_iff_lt] at h ⊢
        rw [← hjj] at h
        rw [Fin.lt_iff_val_lt_val]
        exact h



      have hxj: (x: ℕ ) < j₁ := by omega
      have hxj': (x: ℕ ) ≤ j := by omega
      specialize hj (x: ℕ ) hxj'
      unfold p at hj
      convert hj
      simp only [Fin.cast_val_eq_self]

  -- let f:= fun (i: Fin (s + 1)) => (v i • real_choose_poly ↑i * (real_choose_poly
  -- (s - ↑i)).comp ((k: Polynomial ℝ ) - Polynomial.X))

  -- have h₀ : ∀ (b : Fin (s + 1)), b ≠ (j + 1: Fin (s + 1)) → f b = 0 :=by sorry
  have h0:= congrArg (Polynomial.eval (j₁ : ℝ)) hzero
  simp only [Polynomial.eval_zero] at h0
  unfold sum_coe_poly at h0
  rw [Polynomial.eval_finset_sum] at h0
  rw [Finset.sum_eq_single_of_mem (j₁ : Fin (s + 1))] at h0
  · rw [Polynomial.eval_mul, Polynomial.eval_smul, real_choose_poly_eval_nat_choose] at h0
    rw [Polynomial.eval_comp] at h0
    simp only [cast_add, cast_one, smul_eq_mul, map_natCast, Polynomial.eval_sub,
      Polynomial.eval_natCast, Polynomial.eval_X, _root_.mul_eq_zero, cast_eq_zero] at h0
    rw [← Nat.cast_sub, real_choose_poly_eval_nat_choose] at h0
    cases' h0 with hp hp
    · cases' hp with hp hp
      · exact hp
      · exfalso
        have h1:= Nat.choose_pos (Nat.le_refl j₁)
        rw [hjj] at hp
        rw [hp] at h1
        exact not_succ_le_zero 0 h1
    · exfalso
      have hks : (s - j₁) ≤ (k - j₁) :=
        by omega
      have h1:= Nat.choose_pos hks
      norm_cast at hp
      rw [hjj] at hp
      rw [hp] at h1
      exact not_succ_le_zero 0 h1
    · omega

  · simp only [mem_univ]

  · unfold f at h₀
    rw [hj1] at h₀

    exact fun b a a ↦ h₀ b a

variable (hrL: ∀(r:L), r≤k) (hs : 0 < s)

noncomputable instance: Invertible (coe_matrix k s L hL_card) := by
  unfold coe_matrix
  refine IsUnit.invertible ?_
  rw [← Matrix.linearIndependent_rows_iff_isUnit, Fintype.linearIndependent_iff]
  intro v hv

  have h: ∀ (l : Fin (s+1)), Polynomial.eval (((enumL hL_card).symm l):ℝ)
      (sum_coe_poly' k s v) = 0 :=by
    exact sum_coe_poly'_eval_zero k s L hL_card hv hrL
  have hzero' : sum_coe_poly' k s v = 0 :=by
    by_contra h
    have h3: ¬ (#(sum_coe_poly' k s v).roots.toFinset ≥ #(roots_set s L hL_card)) := by
      simp only [ge_iff_le, not_le]
      rw [card_roots_set_s_plus_1]
      have h4:=number_of_roots k s v
      omega
    apply h3
    exact (roots_card_le k s L hL_card v hv hrL) h
  have hzero : sum_coe_poly k s v = 0 :=by
    unfold sum_coe_poly' at hzero'
    unfold sum_coe_poly
    unfold real_choose_poly
    simp only [one_div, map_natCast, Algebra.smul_mul_assoc] at hzero'
    simp only [one_div, map_natCast, Polynomial.smul_comp, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc]
    rw [← hzero']
    congr! 1 with x hx
    rw [smul_comm]
    nth_rw 2 [smul_comm]

  exact coef_zero k s L hL_card hL hs hrL hzero




lemma span_G (hL_card : #L = s + 1) (hL: k∈L) (hrL: ∀(r:L), r≤k) (hs : 0 < s)
  (huniform: uniform F k)
  (hintersect : intersecting F L):
    Submodule.span ℝ (toSet (subset_H F k)) ≤
    Submodule.span ℝ (subset_G F s):= by
  unfold subset_H
  unfold subset_G
  simp only [coe_image]
  apply Submodule.span_le.2
  intro H hH
  simp only [SetLike.mem_coe]
  simp only [Set.mem_image, Set.mem_image, mem_coe, mem_powersetCard] at hH
  cases' hH with A hA
  rw [Submodule.span_iUnion]
  rw [@Submodule.mem_iSup_iff_exists_finset]
  use univ
  simp only [mem_univ, iSup_pos]
  cases' hA with hA1 hA2
  have himp_le : ⨆ (i: Fin (s + 1)), Submodule.span ℝ ({subset_intersection_indicator F s A i}) ≤
    ⨆ (i: Fin (s + 1)), Submodule.span ℝ ((fun (a: X.powerset) ↦
    subset_intersection_indicator F s (a: Finset α ) i) '' F) := by
    apply iSup_mono
    intro i
    apply Submodule.span_mono
    simp only [Set.singleton_subset_iff, Set.mem_image, mem_coe, Subtype.exists, mem_powerset,
      exists_and_right]
    use A
    constructor
    · have hAU : A.val ⊆ X :=by
        intro x hx
        have hh := A.2
        rw [@mem_powerset] at hh
        exact hh hx
      use hAU
    · rfl

  have hsmallspan: H ∈ ⨆ (i: Fin (s+1)), Submodule.span ℝ ({subset_intersection_indicator F s A i}):=by
    have hG:= fun r => fun hr =>  vector_sum_eq_intersection_sum F k s L
      hintersect huniform r hr ⟨A, hA1⟩
    let inter_matrix : Matrix (Fin (s+1)) F ℝ := fun l =>
      intersection_indicator F A ((enumL hL_card).symm l)
    let G_matrix: Matrix (Fin (s+1)) F ℝ:=  fun r => subset_intersection_indicator F s A r
    have hGmat : G_matrix = (coe_matrix k s L hL_card) *  inter_matrix := by
      unfold G_matrix
      unfold coe_matrix
      unfold inter_matrix
      funext r
      rw [hG r]
      · rw [Matrix.mul_apply_eq_vecMul, Matrix.vecMul_eq_sum, fun f ↦ Eq.symm (sum_coe_sort L f),
          Finset.sum_equiv (enumL hL_card)]
        · exact fun l => by refine' ⟨fun hl => mem_univ ((enumL hL_card) l), fun hl => mem_univ l⟩
        · intro l hl
          rw [Equiv.symm_apply_apply]
          rfl
      · exact Fin.le_last r

    have hInv: Invertible (coe_matrix k s L hL_card) :=
      instInvertibleMatrixFinHAddNatOfNatRealCoe_matrix k s L hL_card hL hrL hs
    have hGcoe : (coe_matrix k s L hL_card) ⁻¹ * G_matrix = inter_matrix := by
      rw [hGmat, ← Matrix.mul_assoc]
      simp only [Matrix.inv_mul_of_invertible, Matrix.one_mul]
    let k_fin := (enumL hL_card) ⟨k, hL⟩

    have hGcoe_k: ((coe_matrix k s L hL_card) ⁻¹ * G_matrix) k_fin = inter_matrix k_fin := by
      exact congrFun hGcoe k_fin

    unfold G_matrix at hGcoe_k
    unfold coe_matrix at hGcoe_k
    unfold inter_matrix at hGcoe_k
    rw [Equiv.symm_apply_apply, hA2] at hGcoe_k
    rw [← hGcoe_k, Matrix.mul_apply_eq_vecMul, Matrix.vecMul_eq_sum, ← Submodule.span_iUnion]
    apply sum_mem
    intro c hc
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp only [Set.iUnion_singleton_eq_range, Set.mem_range, exists_apply_eq_apply]

  have h: H ∈ ⨆ (i: Fin (s + 1)), Submodule.span ℝ ({subset_intersection_indicator F s A i})
    → H∈⨆ (i: Fin (s + 1)), Submodule.span ℝ ((fun (a: X.powerset) ↦
    subset_intersection_indicator F s (a: Finset α ) i) '' F):= by

      exact fun a ↦ himp_le hsmallspan

  exact h hsmallspan


theorem span_G_F : Submodule.span ℝ (subset_G F s) ≤
    Submodule.span ℝ (subset_indicator_set F s) := by
  unfold subset_G
  unfold subset_intersection_indicator
  rw [Submodule.span_iUnion]
  rw [@iSup_le_iff]
  intro i
  simp only [coe_image]
  apply Submodule.span_le.2
  intro x hx
  simp only [Set.mem_image, mem_coe, Subtype.exists, mem_powerset] at hx
  cases' hx with A hA
  cases' hA with hAX hA
  cases' hA with hA1 hA2
  simp only [SetLike.mem_coe]
  unfold subset_indicator_set
  simp only [coe_image]
  have hx: x= ∑ x ∈ powersetCard s X, fun B ↦  if #(A ∩ x) = i then subset_indicator F x B else 0 := by
    rw [← hA2]
    exact
      Eq.symm
        (sum_fn (powersetCard s X) fun c B ↦ if #(A ∩ c) = ↑i then subset_indicator F c B else 0)
  rw [hx]
  apply Submodule.sum_mem
  intro C hC
  let coe_AC:= if #(A ∩ C) = i then (1:ℝ ) else 0
  have h_C_fun : (fun B ↦ if #(A ∩ C) = i then subset_indicator F C B else 0) =
      (fun B ↦ coe_AC • (subset_indicator F C B)) := by
    funext B
    simp only [smul_eq_mul]
    unfold coe_AC
    exact Eq.symm (boole_mul (#(A ∩ C) = ↑i) (subset_indicator F C B))
  rw [h_C_fun]
  have h_fun_C : (fun B ↦ coe_AC • (subset_indicator F C B)) = coe_AC • (fun B ↦ subset_indicator F C B) := by
    funext B
    simp only [smul_eq_mul, Pi.smul_apply]
  rw [h_fun_C]
  apply Submodule.smul_mem
  have hB : (fun B ↦ subset_indicator F C B) = (subset_indicator F C) := by
    funext B
    simp
  rw [hB]
  rw [@Submodule.mem_span]
  intro V hV
  have hCV: subset_indicator F C ∈ (fun S ↦ subset_indicator F S) '' (powersetCard s X)  := by
    simp only [Set.mem_image, mem_coe, mem_powersetCard]
    use C
    constructor
    · rw [← Finset.mem_powersetCard]
      exact hC
    · rfl
  exact hV hCV

theorem span_bar (huniform: uniform F k) (hintersect : intersecting F L) (hL : #L = s + 1)
  (hkL: k ∈ L) (hrL: ∀(r:L), r≤k) (hs : 0 < s): Submodule.span ℝ (subset_indicator_set F s)
    = (⊤: Submodule ℝ (F → ℝ)) :=by
  refine' le_antisymm ?_ ?_
  · intro x hx
    trivial
  · rw [span_H F k huniform]
    have hG := span_G F k s L hL hkL hrL hs huniform hintersect
    have hGF := span_G_F F s
    exact fun ⦃x⦄ a ↦ hGF (hG a)

theorem Ray_Chaudhuri_Wilson (hX: #X = n) (huniform: uniform F k) (hintersect : intersecting F L)
    (hL : #L = s + 1) (hkL: k ∈ L) (hrL: ∀(r:L), r≤k) (hs : 0 < s): #F ≤ Nat.choose n s :=
    (subset_vector_span_dim_le n F s) (span_bar F k s L huniform hintersect hL hkL hrL hs) hX
