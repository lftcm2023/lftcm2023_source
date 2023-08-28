/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth, Marc Masdeu
-/
import Mathlib.Tactic.Polyrith


example {x : ℚ} (hx : x ^ 2 - 4 * x = - 4) : x = 2 := by sorry -- polyrith
-- polyrith failed to retrieve a solution from Sage! ValueError: polynomial is not in the ideal


example {x : ℤ} (hx : x ^ 2 - 4 * x = -4) : x = 2 := by
  have : (x - 2) ^ 2 = 0 := by sorry -- polyrith
  have := pow_eq_zero this
  sorry -- polyrith


example {r s : ℚ} (hr : r ≠ 1) (h : r * s - 2 = s - 2 * r) : s = -2 := by
  have hr' : r - 1 ≠ 0
  · contrapose! hr
    sorry -- polyrith
  apply mul_left_cancel₀ hr'
  sorry -- polyrith


example {r s : ℚ} (h : r * s - 2 = s - 2 * r) : True := by
  have : (r - 1) * (s + 2) = 0 := by sorry -- polyrith
  cases' eq_zero_or_eq_zero_of_mul_eq_zero this with H H
  · -- the case `r - 1 = 0`
    exact trivial
  · -- the case `s + 2 = 0`
    exact trivial
