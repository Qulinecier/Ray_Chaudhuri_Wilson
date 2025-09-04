import Mathlib.LinearAlgebra.Matrix.Rank

variable {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4}
variable [Fintype l] [Fintype n] [Fintype o]
variable {R : Type uR} [Field R]
variable (A : Matrix m n R) (r : l → m) (c : o → n)

lemma rank_submatrix_le': (A.submatrix r c).rank ≤ A.rank := by
  apply le_trans ?_ (Matrix.rank_submatrix_le r (Equiv.refl n) A)
  rw [← Matrix.rank_transpose]
  nth_rw 2 [← Matrix.rank_transpose]
  exact Matrix.rank_submatrix_le c (Equiv.refl l) (Matrix.transpose (A.submatrix r (Equiv.refl n)))
