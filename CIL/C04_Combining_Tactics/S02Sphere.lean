/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Heather Macbeth, Marc Masdeu
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Subtype
import Mathlib.GroupTheory.GroupAction.Prod
import Mathlib.Tactic.Polyrith

set_option quotPrecheck false
noncomputable section


-- introduce notation for the circle
local notation "𝕊" => {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 1}

/-- Stereographic projection, forward direction. This is a map from `ℝ × ℝ` to `ℝ`. It is smooth
away from the horizontal line `p.2 = 1`.  It restricts on the unit circle to the stereographic
projection. -/
def stereoToFun (p : 𝕊) : ℝ :=
  2 * p.1.1 / (1 - p.1.2)

@[simp]
theorem stereoToFun_apply (p : 𝕊) : stereoToFun p = 2 * p.1.1 / (1 - p.1.2) := rfl

/-- Stereographic projection, reverse direction.  This is a map from `ℝ` to the unit circle `𝕊` in
`ℝ × ℝ`. -/
def stereoInvFun (w : ℝ) : 𝕊 :=
  ⟨(w ^ 2 + 4)⁻¹ • (4 * w, w ^ 2 - 4), sorry⟩

@[simp]
theorem stereoInvFun_apply (w : ℝ) :
    (stereoInvFun w : ℝ × ℝ) = (w ^ 2 + 4)⁻¹ • (4 * w, w ^ 2 - 4) :=
  rfl

open Subtype

theorem stereoInvFun_ne_north_pole (w : ℝ) : stereoInvFun w ≠ (⟨(0, 1), by simp⟩ : 𝕊) := by
  dsimp
  rw [Subtype.ext_iff, Prod.mk.inj_iff]
  dsimp
  intro h
  sorry

theorem stereo_left_inv {p : 𝕊} (hp : (p : ℝ × ℝ) ≠ (0, 1)) : stereoInvFun (stereoToFun p) = p := by
  ext1
  obtain ⟨⟨x, y⟩, pythag⟩ := p
  dsimp at pythag hp ⊢
  rw [Prod.mk.inj_iff] at hp ⊢
  sorry

theorem stereo_right_inv (w : ℝ) : stereoToFun (stereoInvFun w) = w := by
  sorry

/-- Stereographic projection, as a bijection to `ℝ` from the complement of `(0, 1)` in the unit
circle `𝕊` in `ℝ × ℝ`. -/
def stereographicProjection : ({(⟨(0, 1), by simp⟩ : 𝕊)}ᶜ : Set 𝕊) ≃ ℝ
    where
  toFun := stereoToFun ∘ (·)
  invFun w := ⟨stereoInvFun w, stereoInvFun_ne_north_pole w⟩
  left_inv p := sorry
  right_inv w := stereo_right_inv w
