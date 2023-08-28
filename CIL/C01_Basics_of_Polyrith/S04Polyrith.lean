/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Polyrith

/-
Just replace the sorries with `polyrith` and enjoy! This tactic uses Sage (online access required)
to suggest a `linear_combination` application.
-/

example {a b : ℂ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 := by sorry

example {m n : ℤ} (h : m - n = 0) : m = n := by sorry

example {K : Type _} [Field K] [CharZero K] {s : K} (hs : 3 * s + 1 = 4) : s = 1 := by sorry

example {p q : ℂ} (h₁ : p + 2 * q = 4) (h₂ : p - 2 * q = 2) : 2 * p = 6 := by sorry

example {x y z w : ℂ} (h₁ : x * z = y ^ 2) (h₂ : y * w = z ^ 2) : z * (x * w - y * z) = 0 := by
  sorry

example {a b : ℚ} (h : a = b) : a ^ 2 = b ^ 2 := by sorry

example {a b : ℚ} (h : a = b) : a ^ 3 = b ^ 3 := by sorry

example (m n : ℤ) : (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by sorry
