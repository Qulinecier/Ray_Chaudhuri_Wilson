import Mathlib.Data.Finset.Lattice.Fold

variable (L : Finset ℕ) (k : ℕ)

lemma Finset.card_le_sup_id_succ (L : Finset ℕ) : L.card ≤ (L.sup id) + 1 := by
  have : L ⊆ Finset.range ((L.sup id) + 1) :=
    fun x hx ↦ Finset.mem_range.2 ((Finset.le_sup (f := id) hx).trans_lt (Nat.lt_succ_self _))
  convert Finset.card_mono this
  simp only [card_range]

lemma Finset.sup_eq_mem_and_le (hkL: k ∈ L) (hrL: ∀(r:L), r≤k): k = (L.sup id) := by
  have hsup_le : L.sup id ≤ k := Finset.sup_le fun x hx => hrL ⟨x, hx⟩
  have hle_sup : id k ≤ L.sup id :=by exact Finset.le_sup hkL
  exact Nat.le_antisymm hle_sup hsup_le
