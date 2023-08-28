/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth, Marc Masdeu
-/
import Mathlib.Data.Polynomial.Basic
import Mathlib.Tactic.Polyrith

open Polynomial

open scoped Polynomial

/-- The Chebyshev polynomials, defined recursively.-/
noncomputable def t : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => 2 * X * t (n + 1) - t n

-- now record the three pieces of the recursive definition for easy access
theorem t_zero : t 0 = 1 := rfl

theorem t_one : t 1 = X := rfl

theorem t_add_two (n : ℕ) : t (n + 2) = 2 * X * t (n + 1) - t n := by rw [t]

/-
The goal of this section is to prove the following formula, namely that for all m and k,
2 T(m) T(m+k) = T(2m + k) + T(k).

The proof is by induction on m, using the previous two cases.
The paper proof (of the inductive step) goes as this:
    2T(m+2)T((m+2)+k)
    =2(2xT(m+1)-T(m))T(m+k+2)
    =2x(2T(m+1)T((m+1)+(k+1)))-2T(m)T(m+(k+2))
    =2x(T(2(m+1)+(k+1))+T(k+1))-(T(2m+(k+2))+T(k+2))
    =(2xT(2m+k+3)-T(2m+k+2))+(2xT(k+1)-T(k+2))
    =T(2(m+2)+k)+T(k)

-/

/-- The product of two Chebyshev polynomials is the sum of two other Chebyshev polynomials. -/
theorem mul_t : ∀ m : ℕ, ∀ k, 2 * t m * t (m + k) = t (2 * m + k) + t k
  | 0 => by
    sorry
  | 1 => by
    sorry
  | m + 2 => by
    intro k
    have h₁ := t_add_two (m + 37) -- not actually a relevant input value!
    have h₂ := t_add_two (37 + m) -- not actually a relevant input value!
    ring_nf at h₁ h₂ ⊢
    sorry
