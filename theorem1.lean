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

open Finset
variable {α : Type} (n : ℕ) [DecidableEq α]
variable {X: Finset α} (F: Finset X.powerset)











def uniform {X: Finset α} (F: Finset X.powerset) (k : ℕ) : Prop := ∀ (A : F), #A.val.val = k





def intersecting {X: Finset α} (F: Finset X.powerset) (L : Set ℕ) :=
  ∀ (A B: F), #(A.val.val ∩ B.val.val) ∈ L



variable (k s: ℕ) (L : Finset ℕ)


instance: Module ℝ (F → ℝ) := sorry


instance: Module ℝ (F → ℝ) := sorry




def S_bar (S : Finset α): F → ℝ  :=
def S_bar (S : Finset α): F → ℝ  :=
    fun A => if S ⊆ A then 1 else 0

<<<<<<< HEAD
/--The intersection indicator vector of subset S: H = ∑(B:B ∈ F,|B∩S|=μ)-/
def intersection_indicator (S: Finset α) (μ : ℕ): F → ℝ :=
    fun B => if #(B ∩ S) = μ then 1 else 0

/--The indicator combine both subset and intersection, i.e. G = ∑(S_bar: S∈ 𝓟ₛ(X), |S∩A| = μ)-/
def subset_intersection_indicator (A: Finset α) (μ : ℕ): F → ℝ :=
    fun B => ∑ (S: powersetCard s X), if #(A ∩ S)  = μ then (subset_indicator F S B) else 0

variable (r: ℕ)

--TODO
lemma indicator_eq (A: Finset α): subset_intersection_indicator F s A r =
    ∑ (l: L), (Nat.choose l r) * (Nat.choose (#A - l) (s - r))
    * (intersection_indicator F A l) := by
  unfold subset_intersection_indicator
  funext B
  simp only [Finset.sum_apply]
  unfold subset_indicator
  unfold intersection_indicator
  simp only [Pi.natCast_def, Pi.mul_apply, mul_ite, mul_one, mul_zero]

  have h1: (∑ (S: powersetCard s X), if #(A ∩ S) = r then (if (S: Finset α) ⊆ (B: Finset α) then (1: ℝ) else 0) else 0)
    = ∑ (x : L), (∑ (S: powersetCard s X),
    if (#(S ∩ (B: Finset α)) = x) then (if #(A ∩ S) = r then
    (if (S: Finset α) ⊆ (B: Finset α) then (1: ℝ) else 0) else 0) else 0) := by sorry

  rw [h1]
  sorry

=======
example (f: ℕ →  ℕ ) (h : (a:ℕ) = b) : f a =  f b := by exact congrArg f h
>>>>>>> parent of 030fdbe (added G_r)

variable (S: X.powerset)
theorem span_bar: Submodule.span ℝ { f | ∃ (S : X.powerset), f = S_bar F S ∧ #S.val = s}
    = (⊤: Submodule ℝ (F → ℝ)) := sorry
theorem span_bar: Submodule.span ℝ { f | ∃ (S : X.powerset), f = S_bar F S ∧ #S.val = s}
    = (⊤: Submodule ℝ (F → ℝ)) := sorry

#check { x // x ∈ X.powerset }
#check { x // x ∈ X.powerset }

theorem finrank_R {β: Type} (ι : Finset β):
    Module.finrank ℝ (ι → ℝ) = Fintype.card ι := by
  simp [Module.finrank]
theorem finrank_R {β: Type} (ι : Finset β):
    Module.finrank ℝ (ι → ℝ) = Fintype.card ι := by
  simp [Module.finrank]

theorem finrank_pi (ι : Type) [Fintype ι]:
theorem finrank_pi (ι : Type) [Fintype ι]:
    Module.finrank ℝ (ι → ℝ) = Fintype.card ι := by
  simp [Module.finrank]

lemma F_rank : Module.finrank ℝ (⊤: Submodule ℝ (F → ℝ)) = #F := by
lemma F_rank : Module.finrank ℝ (⊤: Submodule ℝ (F → ℝ)) = #F := by
  simp only [finrank_top]
  have h:= finrank_pi { x // x ∈ F }
  have h:= finrank_pi { x // x ∈ F }
  rw [← Fintype.card_coe F]
  exact h


noncomputable def S_bar_set :=
  Finset.image (fun (S : Finset α) => (S_bar F S: F → ℝ)) (powersetCard s X)
  exact h


noncomputable def S_bar_set :=
  Finset.image (fun (S : Finset α) => (S_bar F S: F → ℝ)) (powersetCard s X)


lemma S_bar_rank (hX : #X = n): #(S_bar_set F s)
lemma S_bar_rank (hX : #X = n): #(S_bar_set F s)
    ≤ Nat.choose n s := by
  have h1 : #(S_bar_set F s) ≤ #(powersetCard s X) := by
  have h1 : #(S_bar_set F s) ≤ #(powersetCard s X) := by
    exact Finset.card_image_le
  have h2 : #(powersetCard s X) = n.choose s := by
    have h := (Finset.card_powersetCard s X).symm
    rw [hX] at h
    exact h.symm
  rw [h2.symm]
  exact h1



example (h: Submodule.span ℝ (S_bar_set F s) = (⊤: Submodule ℝ (F → ℝ))):
    #F ≤ Nat.choose n s := by
  have h1 : Module.finrank ℝ (Submodule.span ℝ { f | ∃ (S : X.powerset), f = S_bar F S ∧ #S.val = s})


example (h: Submodule.span ℝ (S_bar_set F s) = (⊤: Submodule ℝ (F → ℝ))):
    #F ≤ Nat.choose n s := by
  have h1 : Module.finrank ℝ (Submodule.span ℝ { f | ∃ (S : X.powerset), f = S_bar F S ∧ #S.val = s})
      = Module.finrank ℝ (⊤: Submodule ℝ (F → ℝ)) := by
    rw [h]
  rw [F_rank] at h1
  have hF : Fintype F := sorry
  have h2 := S_bar_rank n { x // x ∈ powerset X} s
  have h3 : Module.finrank ℝ (Submodule.span ℝ
      { f | ∃ (S : X.powerset), f = S_bar F S ∧ #S.val = s})
      ≤ #{ f | ∃ (S : X.powerset), f = S_bar F S ∧ #S.val = s} := sorry
  have hF : Fintype F := sorry
  have h2 := S_bar_rank n { x // x ∈ powerset X} s
  have h3 : Module.finrank ℝ (Submodule.span ℝ
      { f | ∃ (S : X.powerset), f = S_bar F S ∧ #S.val = s})
      ≤ #{ f | ∃ (S : X.powerset), f = S_bar F S ∧ #S.val = s} := sorry
  rw [h1] at h3
  exact Nat.le_trans h3 h2

  done
  done

theorem Ray_Chaudhuri_Wilson (huniform: uniform F k) (hintersect : intersecting F L)
    (hL : #L = s): #F ≤ Nat.choose n s := by sorry



def vector_space_F (F: Finset X.powerset) := F → ℝ



def vector_space_F (F: Finset X.powerset) := F → ℝ
