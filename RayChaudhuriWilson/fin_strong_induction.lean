import Mathlib.Data.Nat.SuccPred

lemma fin_case_strong_induction_on {s: ℕ} {p : Fin (s + 1) → Prop} (a : Fin (s + 1)) (hz : p 0)
    (hi : ∀ (n: ℕ), n < s →
    (∀ (m : ℕ ), m ≤ n → p (@Nat.cast (Fin (s + 1)) (Fin.NatCast.instNatCast (s + 1)) m) )
    → p (@Nat.cast (Fin (s + 1)) (Fin.NatCast.instNatCast (s + 1)) (n + 1))) : p a := by
  let p' : ℕ → Prop := fun x => if x < s + 1 then
    p (@Nat.cast (Fin (s + 1)) (Fin.NatCast.instNatCast (s + 1)) x) else True
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
      apply hi
      · exact Nat.succ_lt_succ_iff.mp hns
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
