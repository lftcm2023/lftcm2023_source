/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Polyrith

/-
In the following example, we exhibit the LHS of the goal as an element of the ideal generated
by the LHS-RHS's of the two hypotheses.
-/

example {x y z w : ℂ} (h₁ : x * z = y ^ 2) (h₂ : y * w = z ^ 2) : z * (x * w - y * z) = 0 := by
  linear_combination w * h₁ + y * h₂

/-
The following examples can of course can be solved with `rw`, but `linear_combination` works as well!
-/
example {a b : ℚ} (h : a = b) : a ^ 2 = b ^ 2 := by linear_combination (a + b) * h


example {a b : ℚ} (h : a = b) : a ^ 3 = b ^ 3 := by linear_combination (a ^ 2 + a * b + b ^ 2) * h


/-
If we don't give parameters, then `linear_combination` is a synonim for `ring`
-/
example (m n : ℤ) : (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  linear_combination

/-
Your turn!
-/

example {x y : ℝ} (h₁ : x + 3 = 5) (h₂ : 2 * x - y * x = 0) : y = 2 := by
  sorry
example {x y : ℝ} (h₁ : x - y = 4) (h₂ : x * y = 1) : (x + y) ^ 2 = 20 := by
  sorry
example {a b c d e f : ℤ} (h₁ : a * d = b * c) (h₂ : c * f = d * e) : d * (a * f - b * e) = 0 := by
  sorry
example {u v : ℝ} (h₁ : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by
  sorry
example {z : ℝ} (h₁ : z ^ 2 + 1 = 0) : z ^ 4 + z ^ 3 + 2 * z ^ 2 + z + 3 = 2 := by
  sorry
example {p q r : ℚ} (h₁ : p + q + r = 0) (h₂ : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 := by
  sorry
