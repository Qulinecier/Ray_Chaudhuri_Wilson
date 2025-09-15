import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import RayChaudhuriWilson.fin_strong_induction

section Polynomial

open Polynomial

variable (R : Type u) [Semiring R] [NoZeroSMulDivisors R R] (n : ℕ)

noncomputable instance: Module ℚ (Polynomial ℚ) := by infer_instance

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
def natDegreeLE_eval {R : Type u} [Semiring R] [NoZeroSMulDivisors R R]
    (p : natDegreeLE R n) (x_val: R):= eval x_val p.1

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

variable (s : ℕ)

/--Define 1/i! * (X * (X-1) * ... * (X - i + 1) ) as a polynomial of X-/
noncomputable def binomVec (i : Fin (s + 1)) : (natDegreeLE ℚ s) := by
  refine' ⟨(1/(Nat.factorial i): ℚ) • (descPochhammer ℚ i.val), ?_⟩
  unfold natDegreeLE
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq]
  by_cases hi: (1/(Nat.factorial i): ℚ) = 0
  · rw [hi]
    simp only [zero_smul, Polynomial.natDegree_zero, zero_le]
  · rw [Polynomial.natDegree_smul _ hi, descPochhammer_natDegree]
    exact Fin.is_le i

open Finset

variable (c: Fin (s + 1) → ℚ)

lemma eval_descPochhammer_sum_zero_imp_c_zero (hzero: Polynomial.eval 0 (∑ (x: Fin (s + 1)),
    c x • ((x.val).factorial: ℚ)⁻¹ • descPochhammer ℚ ↑x) = 0): c 0 = 0 := by
  rw [Polynomial.eval_finset_sum,
    Finset.sum_eq_single_of_mem (0: Fin (s + 1)) (mem_univ 0) (fun x huniv hx => by
      simp only [Polynomial.eval_smul, smul_eq_mul, mul_eq_zero, inv_eq_zero]
      right; right
      rw [descPochhammer_eval_zero, if_neg (Fin.val_ne_zero_iff.mpr hx)])] at hzero
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.factorial_zero, Nat.cast_one, inv_one,
  descPochhammer_zero, one_smul, Polynomial.eval_smul, Polynomial.eval_one, smul_eq_mul,
  mul_one] at hzero
  exact hzero

lemma binomVec_linearIndependent :
    LinearIndependent ℚ (fun i : Fin (s + 1) =>
    (binomVec (s:=s) i : natDegreeLE ℚ s)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hcoe i
  simp only [binomVec, one_div, SetLike.mk_smul_mk] at hcoe
  let hp: Fin (s + 1) → Prop := fun x => (c x = 0)
  have hz: hp (0: Fin (s+1)) := by
    have h1:= congrArg (fun (f: natDegreeLE ℚ s) => (natDegreeLE_eval s f (0: ℚ))) hcoe
    unfold natDegreeLE_eval at h1
    simp only [AddSubmonoidClass.coe_finset_sum,
      ZeroMemClass.coe_zero, Polynomial.eval_zero] at h1
    exact eval_descPochhammer_sum_zero_imp_c_zero s c h1
  apply fin_case_strong_induction_on i hz
  intro j hjs hj
  generalize hj₁ : (@Nat.cast (Fin (s + 1)) (Fin.NatCast.instNatCast (s + 1)) (j + 1)) = j₁ at *
  have h1:= congrArg (fun (f: natDegreeLE ℚ s) => (natDegreeLE_eval s f j₁)) hcoe
  have hjj : j₁.val = j + 1 := by
    simp_rw [hj₁.symm, Fin.val_natCast, Nat.mod_succ_eq_iff_lt,
      Nat.succ_eq_add_one, add_lt_add_iff_right]
    exact hjs
  unfold hp
  simp [natDegreeLE_eval, AddSubmonoidClass.coe_finset_sum,
    ZeroMemClass.coe_zero, Polynomial.eval_zero] at h1
  rw [Polynomial.eval_finset_sum, Finset.sum_eq_single_of_mem j₁ (by simp)] at h1
  · simp only [Polynomial.eval_smul, smul_eq_mul, mul_eq_zero, inv_eq_zero] at h1
    cases' h1 with h1 h1
    · exact h1
    · cases' h1 with h1 h1
      · exact False.elim (Nat.factorial_ne_zero j₁ (Rat.natCast_eq_zero.mp h1))
      · exact False.elim (Ne.symm (ne_of_lt (descPochhammer_pos
          ((sub_lt_self_iff (j₁.val : ℚ)).mpr zero_lt_one))) h1)
  · intro b huniv hb
    simp only [Polynomial.eval_smul, smul_eq_mul, mul_eq_zero, inv_eq_zero, Rat.natCast_eq_zero]
    by_cases hbj : b > j₁
    · right; right; exact descPochhammer_eval_coe_nat_of_lt hbj
    · unfold hp at hj
      have hbj' := Std.lt_of_le_of_ne (Fin.not_lt.mp hbj) hb
      rw [← hj₁, ← (Fin.cast_val_eq_self b)] at hbj'
      specialize hj b.val <| Nat.le_of_lt_succ <|
        (Fin.natCast_lt_natCast (Fin.is_le b) hjs).mp hbj'
      rw [← Fin.cast_val_eq_self b]
      left
      exact hj

open Polynomial

lemma binomVec.span_eq_top_of_card_eq_finrank: Submodule.span ℚ (Set.range (fun i : Fin (s + 1) =>
    (binomVec (s:=s) i : natDegreeLE ℚ s))) = ⊤ := by
  apply LinearIndependent.span_eq_top_of_card_eq_finrank (binomVec_linearIndependent s)
  simp only [Fintype.card_fin]
  rw [rank_natDegreeLE_eq_rank_degreeLE ℚ s, ← Polynomial.degreeLT_succ_eq_degreeLE,
    LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv ℚ (s + 1))]
  exact Eq.symm (Module.finrank_fin_fun ℚ)

end descPochhammer
