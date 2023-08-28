/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Julian Kuelshammer, Heather Macbeth, Marc Masdeu
-/
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Polyrith


#check Nat.centralBinom
-- Nat.centralBinom (n : ℕ) : ℕ

#check Nat.succ_mul_centralBinom_succ

#check Nat.succ_ne_zero
-- Nat.succ_ne_zero (n : ℕ) : Nat.succ n ≠ 0

instance hm : HMul ℚ ℕ ℚ := ⟨(· * ·)⟩

example {i j : ℕ} :
    ((i + 1).centralBinom : ℚ) * j.centralBinom * (i - j + 1) / (2 * (i + j + 1) * (i + j + 2)) -
        i.centralBinom * (j + 1).centralBinom * (i - j - 1) / (2 * (i + j + 1) * (i + j + 2)) =
      i.centralBinom / (i + 1) * (j.centralBinom / (j + 1)) := by
have h₁ : ((i : ℚ) + 1) * (i + 1).centralBinom = 2 * (2 * i + 1) * i.centralBinom
· sorry
sorry
