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

def intersecting {X: Finset α} (F: Finset X.powerset) (L : Set ℕ) :=
  ∀ (A B: F), A ≠ B → #(A.val.val ∩ B.val.val) ∈ L

variable (L : Finset ℕ)

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
    refine card_nbij (·.val) (fun a ↦ ?_) (fun x1 hx1 x2 hx2 hf =>by aesop) ?_
    · intro ha
      simp only [univ_eq_attach, mem_filter, mem_attach, true_and] at ha ⊢
      exact ha
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
noncomputable def char_pol (i : Fin #F) : MvPolynomial X ℝ :=
  ∏ l ∈ L with l < #(F_sorted F i).val.val,
    (∑ m : X, ((char_vec F i m) • (MvPolynomial.X m)) - (MvPolynomial.C l : MvPolynomial X ℝ) )

lemma char_pol_degree (i : Fin #F): (char_pol F L i).totalDegree ≤ #L := by
  unfold char_pol
  have h : (∑ m, char_vec F i m • MvPolynomial.X m : MvPolynomial X ℝ).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro x hx
    calc
    _ ≤ (MvPolynomial.X x).totalDegree :=
      MvPolynomial.totalDegree_smul_le (char_vec F i x) (MvPolynomial.X x : MvPolynomial X ℝ)
    _ = 1 := by apply MvPolynomial.totalDegree_X
  have h (l : ℕ): (∑ m, char_vec F i m • MvPolynomial.X m
      - (MvPolynomial.C l : MvPolynomial X ℝ)).totalDegree ≤ 1 := calc
    _ = (∑ m, char_vec F i m • MvPolynomial.X m
      + (MvPolynomial.C (-l) : MvPolynomial X ℝ)).totalDegree := by
        rw [MvPolynomial.C_neg, Mathlib.Tactic.RingNF.add_neg]
    _ ≤ max
      (∑ m, char_vec F i m • MvPolynomial.X m : MvPolynomial X ℝ).totalDegree
      (MvPolynomial.C (-l) : MvPolynomial X ℝ).totalDegree := by
      apply MvPolynomial.totalDegree_add
    _ ≤ _ := by
      simp only [MvPolynomial.totalDegree_C, zero_le, sup_of_le_left]
      exact h
  calc
  _ ≤ ∑ l ∈ L with l < #(F_sorted F i).val.val,
    (∑ m : X, char_vec F i m • MvPolynomial.X m
    - (MvPolynomial.C l : MvPolynomial X ℝ)).totalDegree := by
    apply MvPolynomial.totalDegree_finset_prod
  _ ≤ ∑ l ∈ L with l < #(F_sorted F i).val.val, 1 := by exact sum_le_sum fun i_1 a ↦ h i_1
  _ = #{l ∈ L | l < #(F_sorted F i).val.val} := by
    exact (card_eq_sum_ones {l ∈ L | l < #(F_sorted F i).val.val}).symm
  _ ≤ _ := card_filter_le L fun l ↦ l < #(F_sorted F i).val.val

lemma char_pol_eval_eq (i : Fin #F) (x : X → ℝ): (char_pol F L i).eval x
    = ∏ l ∈ L with l < #(F_sorted F i).val.val, ((char_vec F i) ⬝ᵥ x - l) := by
  unfold char_pol
  rw [@MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro l hl
  simp [(· ⬝ᵥ ·)]

def pol_to_eval (fp : MvPolynomial X ℝ) : @Ω α X → ℝ := fun x => fp.eval (σ := X) x

omit [DecidableEq α] in
lemma pol_to_eval_linear {Y : Finset (X →₀ ℕ)} {f : (X →₀ ℕ) → MvPolynomial X ℝ}:
    pol_to_eval (∑ v ∈ Y, f v) = ∑ v ∈ Y, pol_to_eval (f v) := by
  unfold pol_to_eval
  simp only [map_sum]
  ext x
  simp

omit [DecidableEq α] in
lemma pol_to_eval_mul_const {v : MvPolynomial X ℝ} {a : ℝ}:
    pol_to_eval ((MvPolynomial.C (σ := X) a) * v) = a • pol_to_eval (v) := by
  unfold pol_to_eval
  ext x
  simp

noncomputable def Ω_char_pol (i : Fin #F) (x : @Ω α X): ℝ := (char_pol F L i).eval x

lemma Ω_char_pol_eq (i : Fin #F) : Ω_char_pol F L i = pol_to_eval (char_pol F L i) := rfl

def Ω_char_pol_span : Submodule ℝ (@Ω α X → ℝ) :=
  Submodule.span ℝ (Set.range (Ω_char_pol F L))

/- Ω_multilinear_set is the set of all monic multilinear polynomials with totaldegree less than L,
  in the context of function from Ω to ℝ.-/
def Ω_multilinear_set : Set (@Ω α X → ℝ) := pol_to_eval ''
  {f | f.totalDegree ≤ #L ∧ ∃ S : X →₀ ℕ, f = MvPolynomial.monomial S 1}

noncomputable def pol_power_shrink (S : X →₀ ℕ) : X →₀ ℕ :=
  Finsupp.ofSupportFinite (fun x => if S x = 0 then 0 else 1) (by
    exact Set.toFinite (Function.support fun x ↦ if S x = 0 then 0 else 1))

omit [DecidableEq α] in
lemma pol_power_shrink_spec (S : X →₀ ℕ) (x : X):
  (pol_power_shrink S) x = (fun x ↦ if S x = 0 then 0 else 1) x := rfl

omit [DecidableEq α] in
lemma pol_power_shrink_support_linear (S : X →₀ ℕ) : (pol_power_shrink S).support = S.support := by
  ext x
  simp [pol_power_shrink_spec]

omit [DecidableEq α] in
lemma pol_power_shrink_support_eq (S1 S2: X →₀ ℕ) (hs : S1.support = S2.support) :
    pol_power_shrink S1 = pol_power_shrink S2:= by
  ext x
  simp only [pol_power_shrink_spec]
  rw [@Finset.ext_iff] at hs
  simp only [Finsupp.mem_support_iff, ne_eq, Subtype.forall, not_iff_not] at hs
  simp [hs x]

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

def Ω_multilinear_pol_set : Set (MvPolynomial X ℝ) :=
  {f | f.totalDegree ≤ #L ∧ ∃ S : X →₀ ℕ, f = MvPolynomial.monomial (pol_power_shrink S) 1}

omit [DecidableEq α] in
lemma Ω_pol_spec_1 (S : X →₀ ℕ) : pol_to_eval (MvPolynomial.monomial S 1) =
    pol_to_eval (MvPolynomial.monomial (pol_power_shrink S) 1) := by
  ext x
  unfold pol_to_eval
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow, one_mul]
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

omit [DecidableEq α] in
lemma Ω_multilinear_set_eq : Ω_multilinear_set (X := X) L = pol_to_eval ''
    {f | f.totalDegree ≤ #L ∧ ∃ S : X →₀ ℕ, f = MvPolynomial.monomial (pol_power_shrink S) 1} := by
  unfold Ω_multilinear_set
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  apply Iff.intro
  · intro a
    obtain ⟨w, ⟨h, S, hwS⟩, hw⟩ := a
    subst hwS
    rw [Ω_pol_spec_1] at hw
    use ((MvPolynomial.monomial (pol_power_shrink S)) 1)
    constructor
    simp only [ne_eq, one_ne_zero, not_false_eq_true, MvPolynomial.monomial_left_inj, true_and]
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

-- The span of Ω_multilinear_set
def Ω_multilinear_span : Submodule ℝ (@Ω α X → ℝ) := Submodule.span ℝ (Ω_multilinear_set L)

noncomputable def deg_n_to_deg_condition (f : {f | f.totalDegree = n ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1}) : f.1.totalDegree = n := by
  have hmem := f.2
  rw [Set.mem_setOf_eq] at hmem
  exact hmem.1

noncomputable def deg_n_to_finsupp (f : {f | f.totalDegree = n ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1}) : X →₀ ℕ := by
  have hmem := f.2
  rw [Set.mem_setOf_eq] at hmem
  exact hmem.2.choose

noncomputable def deg_n_to_finsupp_spec (f : {f | f.totalDegree = n ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1}) :
    f.1 = MvPolynomial.monomial (R := ℝ) (pol_power_shrink (deg_n_to_finsupp n f)) 1 := by
  have hmem := f.2
  rw [Set.mem_setOf_eq] at hmem
  exact hmem.2.choose_spec

noncomputable def deg_n_to_choose_n (f : {f | f.totalDegree = n ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1}) : powersetCard n X :=
  ⟨(deg_n_to_finsupp n f).support.image (Subtype.val), by
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hx
      obtain ⟨hx, _⟩ := hx
      exact hx
    · rw [card_image_iff.mpr Set.injOn_subtype_val,
        ← pol_power_shrink_support_linear (deg_n_to_finsupp n f)]
      simp only [← deg_n_to_deg_condition n f, deg_n_to_finsupp_spec n f, ne_eq,
        one_ne_zero, not_false_eq_true, MvPolynomial.totalDegree_monomial]
      exact card_pol_power_shrink_support (deg_n_to_finsupp n f)⟩

lemma deg_n_to_choose_n_inj : Function.Injective (deg_n_to_choose_n (X := X) n) := by
  intro a b hab
  simp only [deg_n_to_choose_n, Subtype.mk.injEq] at hab
  suffices a.1 = b.1 by exact SetCoe.ext this
  simp only [Set.mem_setOf_eq, deg_n_to_finsupp_spec, ne_eq, one_ne_zero, not_false_eq_true,
    MvPolynomial.monomial_left_inj]
  apply pol_power_shrink_support_eq
  rw [@Finset.ext_iff] at hab
  ext x
  simp only [mem_image, Finsupp.mem_support_iff, ne_eq, Subtype.exists, exists_and_right,
    exists_eq_right] at hab ⊢
  have h := (hab x.1)
  simp only [Subtype.coe_eta, coe_mem, exists_const] at h
  exact h

noncomputable instance : Fintype {f | f.totalDegree = n ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1} := by
  refine Set.Finite.fintype ?_
  exact Finite.of_injective (deg_n_to_choose_n (X := X) n) (deg_n_to_choose_n_inj (X := X) n)

lemma card_pol_to_eval_image_deg_n_le : Fintype.card {f | f.totalDegree = n ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1} ≤ Nat.choose #X n := calc
  _ ≤ Fintype.card (powersetCard n X) :=
    Fintype.card_le_of_injective (deg_n_to_choose_n (X := X) n) (deg_n_to_choose_n_inj n)
  _ = #(powersetCard n X) := Fintype.card_coe (powersetCard n X)
  _ = _ := card_powersetCard n X

omit [DecidableEq α] in
lemma Ω_multilinear_set_union_by_deg : {f | f.totalDegree ≤ #L ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1} =
    (⋃ m ∈ Finset.range (#L + 1), {f | f.totalDegree = m ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1}) := by
    ext f
    simp only [Set.mem_setOf_eq, mem_range, Set.mem_iUnion, exists_and_left, exists_prop,
      exists_eq_left', and_congr_left_iff, forall_exists_index]
    intro _ _
    exact Iff.symm Nat.lt_add_one_iff

noncomputable instance : Fintype (Ω_multilinear_set (X := X) L) := by
  rw [Ω_multilinear_set_eq]
  refine Set.Finite.fintype ?_
  rw [Ω_multilinear_set_union_by_deg]
  apply Set.toFinite

lemma nat_card_pol_to_eval_image_deg_n_le : Nat.card {f | f.totalDegree = n ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1} ≤ Nat.choose #X n := calc
  _ ≤ Nat.card (powersetCard n X) :=
    Nat.card_le_card_of_injective (deg_n_to_choose_n (X := X) n) (deg_n_to_choose_n_inj n)
  _ = #(powersetCard n X) := Nat.card_eq_finsetCard (powersetCard n X)
  _ = _ := card_powersetCard n X

lemma encard_pol_to_eval_image_deg_n_le : {f | f.totalDegree = n ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1}.encard ≤ Nat.choose #X n := by
  let s := {f | f.totalDegree = n ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1}
  have h :s.encard = Nat.card s := by apply ENat.card_eq_coe_natCard
  rw [h]
  have := nat_card_pol_to_eval_image_deg_n_le n (X := X)
  norm_cast

variable {U : Type} in
lemma encard_iUnion_le (f : ℕ → Set U):
    (⋃ m ∈ Finset.range n, f m).encard ≤ ∑ m ∈ Finset.range n, (f m).encard := by
  induction' n with n hn
  · simp
  · have h : ⋃ m ∈ range (n + 1), f m = (⋃ m ∈ range n, f m) ∪ (f n) := by
      ext x
      simp only [mem_range, Set.mem_iUnion, exists_prop, Set.mem_union]
      apply Iff.intro
      · intro a
        obtain ⟨w, left, right⟩ := a
        by_cases hw : w = n
        · subst hw
          exact Or.inr right
        · rw [Order.lt_add_one_iff] at left
          exact Or.inl ⟨w, Nat.lt_of_le_of_ne left hw, right⟩
      · intro a
        cases a with
        | inl h =>
          obtain ⟨w, left, right⟩ := h
          exact ⟨w, (Nat.lt_add_right 1 left), right⟩
        | inr h_1 => exact ⟨n, lt_add_one n, h_1⟩
    rw [h]
    calc
    _ ≤ (⋃ m ∈ range n, f m).encard + (f n).encard := by apply Set.encard_union_le
    _ ≤ ∑ m ∈ range n, (f m).encard + (f n).encard := add_le_add_right hn (f n).encard
    _ = ∑ m ∈ range (n + 1), (f m).encard := (sum_range_succ (fun x ↦ (f x).encard) n).symm

omit [DecidableEq α] in
lemma Ω_multilinear_set_spec : (Ω_multilinear_set (X := X) L).encard ≤
    {f | f.totalDegree ≤ #L ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1}.encard := by
  rw [Ω_multilinear_set_eq]
  apply Set.encard_image_le pol_to_eval
    {f | f.totalDegree ≤ #L ∧ ∃ S, f = (MvPolynomial.monomial (pol_power_shrink S)) 1}

lemma encard_Ω_multilinear_set :
  (Ω_multilinear_set (X := X) L).encard ≤ (∑ m ∈ Finset.range (#L + 1), Nat.choose #X m) := by
  suffices {f | f.totalDegree ≤ #L ∧ ∃ S : X →₀ ℕ,
    f = MvPolynomial.monomial (R := ℝ) (pol_power_shrink S) 1}.encard ≤
    (∑ m ∈ Finset.range (#L + 1), Nat.choose #X m) by
    exact le_trans (Ω_multilinear_set_spec (X := X) L) this
  rw [Ω_multilinear_set_union_by_deg]
  have h : (⋃ m ∈ range (#L + 1),
    {f | f.totalDegree = m ∧ ∃ S,
    f = (MvPolynomial.monomial (R := ℝ) (σ := X) (pol_power_shrink S)) 1}).encard ≤
    ∑ m ∈ range (#L + 1),
    {f | f.totalDegree = m ∧ ∃ S,
    f = (MvPolynomial.monomial (R := ℝ) (σ := X) (pol_power_shrink S)) 1}.encard := by
    apply encard_iUnion_le
  refine le_trans h ?_
  rw [Nat.cast_sum (range (#L + 1)) (#X).choose]
  apply sum_le_sum
  intro i _
  exact encard_pol_to_eval_image_deg_n_le (X := X) i

lemma card_Ω_multilinear_set :
    #(Ω_multilinear_set (X := X) L).toFinset ≤ ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  have h := (encard_Ω_multilinear_set (X := X) L)
  have h2 := Set.encard_coe_eq_coe_finsetCard (Ω_multilinear_set (X := X) L).toFinset
  rw [Set.coe_toFinset] at h2
  rw [h2] at h
  norm_cast at h

lemma dim_Ω_multilinear_span : Module.rank ℝ (Ω_multilinear_span (X := X) L) ≤
    ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  have h := rank_span_finset_le (R := ℝ) (Ω_multilinear_set (X := X) L).toFinset
  rw [Set.coe_toFinset] at h
  have h2 := (card_Ω_multilinear_set (X := X) L)
  exact le_trans h (Nat.cast_le.mpr h2)

omit [DecidableEq α] in
lemma monomial_in_Ω_span (v : X →₀ ℕ) (hv : (v.sum fun x e ↦ e) ≤ #L):
    pol_to_eval (MvPolynomial.monomial (R := ℝ) v 1) ∈ Ω_multilinear_span L := by
  unfold Ω_multilinear_span
  suffices pol_to_eval ((MvPolynomial.monomial v) 1) ∈ (Ω_multilinear_set (X := X) L) by
    exact Submodule.mem_span.mpr fun p a ↦ a this
  simp only [Ω_multilinear_set, Set.mem_image]
  use (MvPolynomial.monomial v) 1
  constructor
  · simp only [Set.mem_setOf_eq, ne_eq, one_ne_zero, not_false_eq_true,
      MvPolynomial.totalDegree_monomial, MvPolynomial.monomial_left_inj, exists_eq', and_true]
    exact hv
  · rfl

lemma Ω_char_pol_spec (i : Fin #F): Ω_char_pol F L i ∈ Ω_multilinear_span L := by
  rw [Ω_char_pol_eq, MvPolynomial.as_sum (char_pol F L i), pol_to_eval_linear]
  apply Submodule.sum_mem
  intro v hv
  have hsmul (a : ℝ): (MvPolynomial.monomial v a) =
    (MvPolynomial.C (σ := X) a) * (MvPolynomial.monomial v 1) := by
    rw [← (MvPolynomial.smul_eq_C_mul (MvPolynomial.monomial v 1) a)]
    rw [@MvPolynomial.smul_monomial]
    simp
  suffices pol_to_eval ((MvPolynomial.monomial v) 1) ∈ Ω_multilinear_span L by
    rw [hsmul, pol_to_eval_mul_const]
    exact Submodule.smul_mem (Ω_multilinear_span L) (MvPolynomial.coeff v (char_pol F L i)) this
  apply monomial_in_Ω_span
  refine le_trans ?_ (char_pol_degree F L i)
  apply MvPolynomial.le_totalDegree
  exact hv

lemma span_to_R_le_span_ml : (Ω_char_pol_span F L) ≤ Ω_multilinear_span L := by
  unfold Ω_char_pol_span
  suffices Set.range (Ω_char_pol F L) ⊆ (Ω_multilinear_span (X := X) L) by
    exact Submodule.span_le.mpr this
  intro x hx
  rw [@Set.mem_range] at hx
  obtain ⟨y, hy⟩ := hx
  subst hy
  exact Ω_char_pol_spec F L y

lemma dim_span_to_R_le :
    Module.rank ℝ (Ω_char_pol_span F L) ≤ ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m:= by
  exact Preorder.le_trans (Module.rank ℝ (Ω_char_pol_span F L))
    (Module.rank ℝ (Ω_multilinear_span (X := X) L))
    (↑(∑ m ∈ range (#L + 1), (#X).choose m))
    (Submodule.rank_mono (span_to_R_le_span_ml F L)) (dim_Ω_multilinear_span L)

-- Show that the characteristic polynomial is non-zero for the characteristic vector of A.
lemma char_pol_spec_1 (i : Fin #F) : (char_pol F L i).eval (char_vec F i) ≠ 0 := by
  rw [char_pol_eval_eq F L i (char_vec F i)]
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
    (hintersect : intersecting F L): (char_pol F L i).eval (char_vec F j) = 0 := by
  rw [char_pol_eval_eq F L i (char_vec F j)]
  unfold intersecting at hintersect
  refine prod_eq_zero_iff.mpr ?_
  use #((F_sorted F i).val.val ∩ (F_sorted F j).val.val)
  rw [char_vec_spec, sub_self, propext (and_iff_left rfl), mem_filter]
  constructor
  · exact hintersect (F_sorted F i) (F_sorted F j) (neq_F_sorted F i j hneq)
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
  have hless : ∑ x ∈ {x | x < i}, g x * (char_pol F L x).eval (char_vec F i) = 0 := by
    rw [Finset.sum_eq_zero]
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    suffices g x = 0 by exact mul_eq_zero_of_left this ((char_pol F L x).eval (char_vec F i))
    by_contra hcon2
    exact (not_le.mpr hx) (hmin x hcon2)
  --Show that all the x after i gives zero since char_pol = 0 by char_pol_spec_2.
  have hmore : ∑ x ∈ {x | i < x}, g x * (char_pol F L x).eval (char_vec F i) = 0 := by
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

theorem Frankl_Wilson_Thoerem (hintersect : intersecting F L):
    #F ≤ ∑ m ∈ Finset.range (#L + 1), Nat.choose #X m := by
  have h := linearIndependent_span (Ω_char_pol_lin_indep F L hintersect)
  apply LinearIndependent.cardinal_le_rank at h
  rw [Cardinal.mk_fintype, Fintype.card_fin] at h
  exact Nat.cast_le.mp (le_trans h (dim_span_to_R_le F L))

end Frankl_Wilson
