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

#check F



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


noncomputable def subset_G := ⋃ (r : Fin s),
    toSet (Finset.image (fun (A: X.powerset) =>
    subset_intersection_indicator F s A r) F)

instance: Membership (Finset α) (Finset X.powerset)where
  mem := fun A => fun B => ∃ x ∈ A, x.val = B

noncomputable def enumL {s: ℕ} {L : Finset ℕ} (hL_card: #L = s) : L ≃ Fin s :=
  Finset.equivFinOfCardEq hL_card

variable (hL_card : #L = s) (hL: k∈L)



lemma span_G (hL_card : #L = s) (hL: k∈L) (hrL: ∀(r:L), r≤k) (huniform: uniform F k)
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
  have himp_le : ⨆ (i: Fin s), Submodule.span ℝ ({subset_intersection_indicator F s A i}) ≤
    ⨆ (i: Fin s), Submodule.span ℝ ((fun (a: X.powerset) ↦
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

  have hsmallspan: H ∈ ⨆ (i: Fin s), Submodule.span ℝ ({subset_intersection_indicator F s A i}):=by
    have hG:= fun r => fun hr =>  vector_sum_eq_intersection_sum F k s L
      hintersect huniform r hr ⟨A, hA1⟩
    let inter_matrix : Matrix (Fin s) F ℝ := fun l =>
      intersection_indicator F A ((enumL hL_card).symm l)
    let coe_matrix: Matrix (Fin s) (Fin s) ℝ := fun r => fun l =>
      (Nat.choose ((enumL hL_card).symm l) r) * (Nat.choose (k - ((enumL hL_card).symm l)) (s - r))
    let G_matrix: Matrix (Fin s) F ℝ:=  fun r => subset_intersection_indicator F s A r
    have hGmat : G_matrix = coe_matrix *  inter_matrix := by
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
      · exact Fin.is_le'
    have hInv: Invertible coe_matrix := by
      unfold coe_matrix
      refine IsUnit.invertible ?_
      sorry
      -- ascPochhammer
      done
    have hGcoe : coe_matrix ⁻¹ * G_matrix = inter_matrix := by
      rw [hGmat, ← Matrix.mul_assoc]
      simp only [Matrix.inv_mul_of_invertible, Matrix.one_mul]
    let k_fin := (enumL hL_card) ⟨k, hL⟩

    have hGcoe_k: (coe_matrix ⁻¹ * G_matrix) k_fin = inter_matrix k_fin := by
      exact congrFun hGcoe k_fin

    unfold G_matrix at hGcoe_k
    unfold coe_matrix at hGcoe_k
    unfold inter_matrix at hGcoe_k
    rw [Equiv.symm_apply_apply, hA2] at hGcoe_k
    rw [← hGcoe_k]
    rw [Matrix.mul_apply_eq_vecMul]
    rw [Matrix.vecMul_eq_sum]
    rw [← Submodule.span_iUnion]
    apply sum_mem
    intro c hc
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp only [Set.iUnion_singleton_eq_range, Set.mem_range, exists_apply_eq_apply]

  have h: H ∈ ⨆ (i: Fin s), Submodule.span ℝ ({subset_intersection_indicator F s A i})
    → H∈⨆ (i: Fin s), Submodule.span ℝ ((fun (a: X.powerset) ↦
    subset_intersection_indicator F s (a: Finset α ) i) '' F):= by
      exact fun a ↦ himp_le hsmallspan

  apply h

  exact hsmallspan


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

theorem span_bar (huniform: uniform F k) (hintersect : intersecting F L) (hL : #L = s) (hkL: k ∈ L) (hrL: ∀(r:L), r≤k): Submodule.span ℝ (subset_indicator_set F s)
    = (⊤: Submodule ℝ (F → ℝ)) :=by
  refine' le_antisymm ?_ ?_
  · intro x hx
    trivial
  · rw [span_H F k huniform]
    have hG := span_G F k s L hL hkL hrL huniform hintersect
    have hGF := span_G_F F s
    exact fun ⦃x⦄ a ↦ hGF (hG a)



theorem Ray_Chaudhuri_Wilson (hX: #X = n) (huniform: uniform F k) (hintersect : intersecting F L)
    (hL : #L = s) (hkL: k ∈ L) (hrL: ∀(r:L), r≤k): #F ≤ Nat.choose n s :=
    (subset_vector_span_dim_le n F s) (span_bar F k s L huniform hintersect hL hkL hrL) hX
