/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Polyrith

/-
We will focus on proving algebraic identities that follow from other identities
that we may have in the list of hypotheses. Below is an illustrative example,
solved using a `calc` block. Note that each of the steps consists of either
checking an algebraic equality (via the `ring` tactic) or substituting (via `rw`).
-/

example {a b : ℂ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 :=
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * b := by rw [h₁]
    _ = -6 + 5 * (b + 2) := by ring
    _ = -6 + 5 * 3 := by rw [h₂]
    _ = 9 := by ring

/-
When we work with ℝ, we can use a very powerful tactic called `linarith` (or `nlinarith`), which
is designed to prove inequalities. But equalities are combined inequalities, and so this tactic
still works.
-/

example {a b : ℝ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 := by linarith

/-
However, `linarith` needs a linearly ordered field to work, so for example in ℂ we are out of luck.
Luckily for us, there is a "shortcut" tactic that streamlines the long proof that we had before.
-/

example {a b : ℂ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 := by linear_combination h₁ + 5 * h₂


example {m n : ℤ} (h : m - n = 0) : m = n := by linear_combination h


example {K : Type _} [Field K] [CharZero K] {s : K} (hs : 3 * s + 1 = 4) : s = 1 := by
  linear_combination 1 / 3 * hs


example {p q : ℂ} (h₁ : p + 2 * q = 4) (h₂ : p - 2 * q = 2) : 2 * p = 6 := by
  linear_combination h₁ + h₂

/-
Your turn!
-/

example {x y : ℤ} (h₁ : 2 * x + y = 4) (h₂ : x + y = 1) : x = 3 := by
  sorry
example {r s : ℝ} (h₁ : r + 2 * s = -1) (h₂ : s = 3) : r = -7 := by
  sorry
example {c : ℚ} (h₁ : 4 * c + 1 = 3 * c - 2) : c = -3 := by
  sorry
example {x y : ℤ} (h₁ : x - 3 * y = 5) (h₂ : y = 3) : x = 14 := by
  sorry
example {x y : ℤ} (h₁ : 2 * x - y = 4) (h₂ : y - x + 1 = 2) : x = 5 := by
  sorry
example {x y : ℝ} (h₁ : x = 3) (h₂ : y = 4 * x - 3) : y = 9 := by
  sorry
example {a b c : ℝ} (h₁ : a + 2 * b + 3 * c = 7) (h₂ : b + 2 * c = 3) (h₃ : c = 1) : a = 2 := by
  sorry
example {a b : ℝ} (h₁ : a + 2 * b = 4) (h₂ : a - b = 1) : a = 2 := by
  sorry
example {u v : ℚ} (h₁ : u + 2 * v = 4) (h₂ : u - 2 * v = 6) : u = 5 := by
  sorry
example {u v : ℚ} (h₁ : 4 * u + v = 3) (h₂ : v = 2) : u = 1 / 4 := by
  sorry
