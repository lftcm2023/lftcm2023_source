/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: François Sunatori, Heather Macbeth, Marc Masdeu
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Polyrith
import CIL.Attr

noncomputable section

open Complex

open scoped ComplexConjugate

local notation "|" x "|" => Complex.abs x

/-! This file contains a lot of computationally-intensive evaluation of operations on the complex
numbers. We speed it up slightly by specifiying in advance the path the simplifier should take.
-/
attribute [complex_simps] normSq_eq_abs normSq_eq_conj_mul_self norm_eq_abs ofReal_pow ofReal_one map_sub map_one


example {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) : f I = I ∨ f I = -I :=
  by
  have key : (f I - I) * (conj (f I) - conj (-I)) = 0 :=
    by
    have H₁ := congr_arg (λ t ↦ (((t ^ 2) : ℝ) : ℂ)) (f.norm_map (I - 1))
    have H₂ := congr_arg (λ t ↦ (((t ^ 2) : ℝ) : ℂ)) (f.norm_map I)
    have h₂ : conj (-I) = I := by norm_num
    replace H₁ : (conj (f I) - 1) * (f I - 1) = (conj I - 1) * (I - 1)
    · simpa [h, h₂, ←normSq_eq_abs, normSq_eq_conj_mul_self, norm_eq_abs] using H₁
    replace H₂ : conj (f I) * f I = conj I * I
    · simp only [h, h₂, ←normSq_eq_abs, normSq_eq_conj_mul_self, norm_eq_abs] at H₂
      exact H₂
    linear_combination I * H₁ - (-1 + I) * H₂ - (f I - I) * h₂
  -- From `key`, we deduce that either `f I - I = 0` or `conj (f I) - conj (- I) = 0`.
  cases' eq_zero_or_eq_zero_of_mul_eq_zero key with hI hI
  · sorry
  · sorry
