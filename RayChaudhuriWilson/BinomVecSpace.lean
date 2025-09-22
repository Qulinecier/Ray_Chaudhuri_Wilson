import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Nat.Choose.Cast
import RayChaudhuriWilson.fin_strong_induction


section Polynomial

open Polynomial

variable (R : Type u) [Semiring R] [NoZeroSMulDivisors R R] (n : ℕ)

noncomputable instance: Module R (Polynomial R) := by infer_instance

/--Define a polynomial with degree lower than n-/
def natDegreeLE: Submodule R (Polynomial R) :=
{ carrier := { p | p.natDegree ≤ n },
  zero_mem' := by simp,
  add_mem' {p q} hp hq:= le_trans (natDegree_add_le p q) (max_le hp hq)
  smul_mem' c p hp := by
    by_cases hc : c = 0
    · simp [hc]
    · simp only [Set.mem_setOf_eq]
      rw [natDegree_smul p hc]
      exact hp
}

/--Define evaluation at point x for polynomial in natDegreeLe-/
def degreeLE_eval {R : Type u} [Semiring R] [NoZeroSMulDivisors R R]
    (p : degreeLE R n) (x_val: R):= eval x_val p.1

variable (p: natDegreeLE R n)

/--Equivalence between `natDegreeLE` and `degreeLE`-/
def natDegreeLE_linear_equiv_degreeLE: (natDegreeLE R n) ≃ₗ[R] (degreeLE R n)where
  toFun := fun p => ⟨p.1 ,
    Polynomial.mem_degreeLE.mpr (Polynomial.natDegree_le_iff_degree_le.mp p.2)⟩
  map_add' x y:= by simp only [Submodule.coe_add, AddMemClass.mk_add_mk]
  map_smul' x y := by simp only [SetLike.val_smul, RingHom.id_apply, SetLike.mk_smul_mk]
  invFun := fun p => ⟨p.1,
    Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp p.2)⟩
  left_inv p := by simp only [Subtype.coe_eta]
  right_inv p := by simp only [Subtype.coe_eta]

lemma rank_natDegreeLE_eq_rank_degreeLE: Module.finrank R (natDegreeLE R n)
    = Module.finrank R (degreeLE R n) :=
  LinearEquiv.finrank_eq (natDegreeLE_linear_equiv_degreeLE R n)


end Polynomial

section descPochhammer

open Polynomial

variable (s : ℕ)

/--Define 1/i! * (X * (X-1) * ... * (X - i + 1) ) as a polynomial of X-/
noncomputable def binomVec (i : Fin (s + 1)) : (degreeLE ℤ s) := by
  refine' ⟨descPochhammer ℤ i.val, ?_⟩
  rw [Polynomial.mem_degreeLE]
  rw [← natDegree_le_iff_degree_le]
  simp only [descPochhammer_natDegree]
  exact Fin.is_le i

open Finset

variable (c: Fin (s + 1) → ℤ)

lemma eval_descPochhammer_sum_zero_imp_c_zero (hzero: Polynomial.eval 0 (∑ (x: Fin (s + 1)),
    c x • descPochhammer ℤ x) = 0): c 0 = 0 := by
  rw [Polynomial.eval_finset_sum,
    Finset.sum_eq_single_of_mem (0: Fin (s + 1)) (mem_univ 0) (fun x huniv hx => by
      simp only [zsmul_eq_mul, Polynomial.eval_mul, Polynomial.eval_intCast, Int.cast_eq,
        mul_eq_zero]
      right
      rw [descPochhammer_eval_zero, if_neg (Fin.val_ne_zero_iff.mpr hx)])] at hzero
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, descPochhammer_zero, zsmul_eq_mul, mul_one,
    Polynomial.eval_intCast, Int.cast_eq] at hzero
  exact hzero

lemma binomVec_linearIndependent :
    LinearIndependent ℤ  (fun i : Fin (s + 1) =>
    (binomVec (s:=s) i : degreeLE ℤ s)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hcoe i
  let hp: Fin (s + 1) → Prop := fun x => (c x = 0)
  have hz: hp (0: Fin (s+1)) := by
    have h1:= congrArg (fun (f: degreeLE ℤ s) => (degreeLE_eval s f (0: ℤ))) hcoe
    unfold degreeLE_eval at h1
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul,
      ZeroMemClass.coe_zero, Polynomial.eval_zero] at h1
    exact eval_descPochhammer_sum_zero_imp_c_zero s c h1
  apply fin_case_strong_induction_on i hz
  intro j hjs hj
  generalize hj₁ : (@Nat.cast (Fin (s + 1)) (Fin.NatCast.instNatCast (s + 1)) (j + 1)) = j₁ at *
  have h1:= congrArg (fun (f:degreeLE ℤ s) => (degreeLE_eval s f j₁)) hcoe
  have hjj : j₁.val = j + 1 := by
    simp_rw [hj₁.symm, Fin.val_natCast, Nat.mod_succ_eq_iff_lt,
      Nat.succ_eq_add_one, add_lt_add_iff_right]
    exact hjs
  unfold hp
  simp [degreeLE_eval, AddSubmonoidClass.coe_finset_sum,
    ZeroMemClass.coe_zero, Polynomial.eval_zero] at h1
  rw [Polynomial.eval_finset_sum, Finset.sum_eq_single_of_mem j₁ (by simp)] at h1
  · simp only [Polynomial.eval_mul, Polynomial.eval_intCast, Int.cast_eq, mul_eq_zero] at h1
    cases' h1 with h1 h1
    · exact h1
    · exact False.elim (Ne.symm (ne_of_lt (descPochhammer_pos
          ((sub_lt_self_iff (j₁.val : ℤ)).mpr zero_lt_one))) h1)
  · intro b huniv hb
    simp only [Polynomial.eval_mul, Polynomial.eval_intCast, Int.cast_eq, mul_eq_zero]
    by_cases hbj : b > j₁
    · right; exact descPochhammer_eval_coe_nat_of_lt hbj
    · unfold hp at hj
      have hbj' := Std.lt_of_le_of_ne (Fin.not_lt.mp hbj) hb
      rw [← hj₁, ← (Fin.cast_val_eq_self b)] at hbj'
      specialize hj b.val <| Nat.le_of_lt_succ <|
        (Fin.natCast_lt_natCast (Fin.is_le b) hjs).mp hbj'
      rw [← Fin.cast_val_eq_self b]
      left
      exact hj

open Polynomial


lemma binomVec_span_eq_top_of_card_eq_finrank: ⊤ ≤ Submodule.span ℤ (
    Set.range (fun i : Fin (s + 1) => (binomVec (s:=s) i : degreeLE ℤ s))) := by
  suffices degreeLE ℤ s ≤ Submodule.span ℤ (Set.range (fun i : Fin (s + 1) =>
      (binomVec (s:=s) i).val)) by
    intro x
    simp only [Submodule.mem_top, forall_const]
    have := this x.2
    rw [@Submodule.mem_span_range_iff_exists_fun] at this ⊢
    obtain ⟨c, hc⟩ := this
    use c
    apply Subtype.eq
    simpa using hc
  simp only [degreeLE_eq_span_X_pow, Submodule.span_le]
  intro xd hxd
  simp only [coe_image, coe_range, Set.mem_image, Set.mem_Iio] at hxd
  obtain ⟨d, hd, rfl⟩ := hxd
  induction' d using Nat.strong_induction_on with d ih
  have hs : descPochhammer ℤ d ∈ Submodule.span ℤ (Set.range fun i ↦ (binomVec s i).val) := by
    simp [binomVec]
    rw [Submodule.mem_span_set']
    use 1, 1, fun x => ⟨descPochhammer ℤ d, by use ⟨d, hd⟩⟩
    simp
  rw [← eraseLead_add_monomial_natDegree_leadingCoeff (descPochhammer ℤ d)] at hs
  rw [monic_descPochhammer ℤ d, descPochhammer_natDegree, monomial_one_right_eq_X_pow] at hs
  refine (add_mem_cancel_left ?_).mp hs
  have hlt : degreeLT ℤ d ≤ Submodule.span ℤ (Set.range fun i ↦ (binomVec s i).val) := by
    rw [degreeLT_eq_span_X_pow, Submodule.span_le]
    intro _
    simp only [coe_image, coe_range, Set.mem_image, Set.mem_Iio, SetLike.mem_coe,
      forall_exists_index, and_imp]
    rintro m hm rfl
    exact ih m hm (Nat.lt_trans hm hd)
  apply hlt
  rw [mem_degreeLT]
  have hne0 := Monic.ne_zero (monic_descPochhammer ℤ d)
  have h := Polynomial.degree_eraseLead_lt hne0
  suffices (descPochhammer ℤ d).degree = d by rwa [this] at h
  rw [degree_eq_natDegree hne0, descPochhammer_natDegree]

noncomputable def binomBasis : Module.Basis (Fin (s + 1)) ℤ (degreeLE ℤ s):=by
  exact Module.Basis.mk (binomVec_linearIndependent s) (binomVec_span_eq_top_of_card_eq_finrank s)

lemma binomVec_sum_equivFun (f : Polynomial ℤ) (hf: f.natDegree ≤ s): ∃ (a : (Fin (s + 1)) → ℤ ),
    ∑ (i : (Fin (s + 1))), a i • (descPochhammer ℤ i.val) = f := by
  have hf' : f ∈ degreeLE ℤ s :=by
    rw [mem_degreeLE, ← natDegree_le_iff_degree_le]
    exact hf
  have hf_coe := Module.Basis.sum_equivFun (binomBasis s) ⟨f, hf'⟩
  unfold binomBasis at hf_coe
  simp only [Module.Basis.equivFun_apply, Module.Basis.mk_repr, Module.Basis.coe_mk] at hf_coe
  unfold binomVec at hf_coe
  simp only [SetLike.mk_smul_mk] at hf_coe
  have hf_coe' := congr_arg (fun (g: degreeLE ℤ s) => g.1) hf_coe
  simp only [AddSubmonoidClass.coe_finset_sum] at hf_coe'
  exact
    Exists.intro
      (⇑((binomVec_linearIndependent s).repr
          ⟨⟨f, hf'⟩, binomVec_span_eq_top_of_card_eq_finrank s Submodule.mem_top⟩))
      hf_coe'

lemma temp1 (f : Polynomial ℤ) (hf: f.natDegree ≤ s):
    ∃ (a : Fin (s + 1) → ℤ), ∀ (x : ℤ), Polynomial.eval x f =
    ∑ (i : Fin (s + 1)), (a i) • (Polynomial.eval x (descPochhammer ℤ i.val)) := by
  have h1 := binomVec_sum_equivFun s f hf
  cases' h1 with a ha
  use a
  intro x
  rw [← ha, Polynomial.eval_finset_sum]
  simp only [zsmul_eq_mul, eval_mul, eval_intCast, Int.cast_eq]

lemma temp2 (f : Polynomial ℤ ) (hf: f.natDegree ≤ s):
    ∃ (a : Fin (s + 1) → ℤ ), ∀ (x : ℕ), Polynomial.eval (x : ℤ) f =
    ∑ (i : Fin (s + 1)), (a i) • (Polynomial.eval (x : ℤ) (descPochhammer ℤ i.val)) := by
  have h1 := temp1 s f hf
  cases' h1 with a ha
  use a
  intro x
  specialize ha x
  exact ha

#check Rat.num_intCast
#check Rat.instIntCast
#check Rat.ofInt
-- Rat → Int




lemma temp3 (f : Polynomial ℤ ) (hf: f.natDegree ≤ s):
    ∃ (a : Fin (s + 1) → ℤ ), ∀ (x : ℕ), Int.cast (R:= ℚ) (Polynomial.eval (x : ℤ) f) =
    ∑ (i : Fin (s + 1)), (a i) •
    (Int.cast (R:= ℚ) (Polynomial.eval (x : ℤ) (descPochhammer ℤ i.val))) := by
  have h1 := temp2 s f hf
  cases' h1 with a ha
  use a
  intro x
  specialize ha x
  have h2 := congr_arg (Int.cast (R:= ℚ)) ha
  simp only [Int.cast_sum] at h2
  rw [h2]
  congr! with i hi
  simp only [Int.cast_mul, descPochhammer_eval_cast, Int.cast_natCast, zsmul_eq_mul]
  rfl

lemma nat_factorial_inv_one (a : ℕ ): a.factorial * (1/ a.factorial) = (1 : ℚ ) :=by
  exact mul_one_div_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a))


lemma temp4 (f : Polynomial ℤ ) (hf: f.natDegree ≤ s):
    ∃ (a : Fin (s + 1) → ℤ ), ∀ (x : ℕ), Int.cast (R:= ℚ) (Polynomial.eval (x : ℤ) f) =
    ∑ (i : Fin (s + 1)), (a i) •
    ((i.val).factorial* (1/ (i.val).factorial) *Int.cast (R:= ℚ) (Polynomial.eval (x : ℤ)
    (descPochhammer ℤ i.val))) := by
  simp_rw [nat_factorial_inv_one]
  have h1 := temp3 s f hf
  cases' h1 with a ha
  use a
  intro x
  specialize ha x
  rw [ha]
  simp only [descPochhammer_eval_cast, Int.cast_natCast, zsmul_eq_mul, one_mul]


lemma temp5 (f : Polynomial ℤ ) (hf: f.natDegree ≤ s):
    ∃ (a : Fin (s + 1) → ℤ ), ∀ (x : ℕ), Int.cast (R:= ℚ) (Polynomial.eval (x : ℤ) f) =
    ∑ (i : Fin (s + 1)), (a i) •
    ((i.val).factorial * (Int.cast (R:= ℚ) (Polynomial.eval (x : ℤ)
    (descPochhammer ℤ i.val)))/(Nat.cast (R:= ℚ) (i.val).factorial)) := by
  have h1 := temp4 s f hf
  cases' h1 with a ha
  use a
  intro x
  specialize ha x
  rw [ha]
  simp only [one_div, descPochhammer_eval_cast, Int.cast_natCast, zsmul_eq_mul]
  simp_rw [mul_assoc]
  congr with i
  simp only [mul_eq_mul_left_iff, Rat.intCast_eq_zero]
  left
  rw [← mul_div]
  simp only [mul_eq_mul_left_iff, Rat.natCast_eq_zero]
  left
  rw [mul_comm]
  exact rfl

lemma temp6 (f : Polynomial ℤ ) (hf: f.natDegree ≤ s):
    ∃ (a : Fin (s + 1) → ℤ ), ∀ (x : ℕ), Int.cast (R:= ℚ) (Polynomial.eval (x : ℤ) f) =
    ∑ (i : Fin (s + 1)), (a i) *
    ((i.val).factorial * (Nat.choose x i)) := by
  have h1 := temp5 s f hf
  cases' h1 with a ha
  use a
  intro x
  specialize ha x
  rw [ha]
  simp only [descPochhammer_eval_cast, Int.cast_natCast, zsmul_eq_mul, Int.cast_sum, Int.cast_mul]
  congr with i
  simp only [mul_eq_mul_left_iff, Rat.intCast_eq_zero]
  left
  rw [← mul_div]
  simp only [mul_eq_mul_left_iff, Rat.natCast_eq_zero]
  left
  rw [Nat.cast_choose_eq_descPochhammer_div]

-- f (∑ a, g (a)) = ∑ a, f g (a)

lemma nat_cast_int_rat (a : ℕ): (Nat.cast (R:= ℚ) a) = Int.cast (R:=ℚ) (Nat.cast (R:= ℤ) a) :=by
  simp only [Int.cast_natCast]



@[simp]
lemma instCast_sum (f : Fin (s + 1) → ℤ) (S: Finset (Fin (s + 1))) : (Int.cast (R:= ℚ) (∑ x ∈ S, f x)).num
  = ∑ x ∈ S, (Int.cast (R:= ℚ) (f x)).num := by
  let g : ℤ →+ ℤ :={
    toFun := fun x =>  (Int.cast (R:= ℚ) x).num
    map_zero' := by simp only [Int.cast_zero, Rat.num_ofNat]
    map_add' x y:= by simp only [Rat.intCast_num]
  }

  have h1:= map_sum g f S
  unfold g at h1
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h1
  exact h1


lemma temp7 (f : Polynomial ℤ ) (hf: f.natDegree ≤ s):
    ∃ (a : Fin (s + 1) → ℤ ), ∀ (x : ℕ), (Polynomial.eval (x : ℤ) f) =
    ∑ (i : Fin (s + 1)), (a i) *
    ((i.val).factorial * (Nat.choose x i)) := by
  have h1 := temp6 s f hf
  cases' h1 with a ha
  use a
  intro x
  specialize ha x
  have ha' := congr_arg (fun (a : ℚ) => a.num) ha
  simp only [Rat.intCast_num, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at ha'
  simp_rw [nat_cast_int_rat] at ha'
  simp_rw [(Rat.intCast_mul _ _).symm] at ha'
  rw [ha']
  rw [← Int.cast_sum]
  rw [instCast_sum]
  rfl


end descPochhammer
