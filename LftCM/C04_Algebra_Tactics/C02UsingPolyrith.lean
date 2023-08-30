/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth, Marc Masdeu
-/
import Mathlib.Data.Polynomial.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Polyrith
import Mathlib.Analysis.Quaternion
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GroupPower.Ring
import LftCM.Attr

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue #2220

noncomputable section
open Polynomial Complex Quaternion
open scoped ComplexConjugate Quaternion

/-! This file contains a lot of computationally-intensive evaluation of operations on the complex
numbers, matrices and quaternions.
We speed it up slightly by specifiying in advance the path the simplifier should take.
-/
attribute [complex_simps] normSq_eq_conj_mul_self norm_eq_abs ofReal_pow ofReal_one
  map_sub map_one conj_neg_I
attribute [quaternion_simps] Matrix.head_cons Matrix.cons_vec_bit0_eq_alt0 Matrix.cons_val_zero
  Matrix.cons_val_one Matrix.cons_vecAppend Matrix.cons_vecAlt0 Matrix.cons_val' Matrix.empty_val'
  Matrix.empty_vecAlt0 Matrix.empty_vecAppend Matrix.one_apply_eq Matrix.one_apply_ne
  MulZeroClass.zero_mul one_pow add_zero eq_self_iff_true MulZeroClass.mul_zero zero_pow' tsub_zero
  Matrix.vecHead Matrix.vecTail Matrix.cons_mul Matrix.cons_vecMul
  Matrix.cons_val_zero Matrix.cons_val_one Matrix.empty_vecMul Matrix.empty_vecAppend
  Matrix.empty_mul Matrix.one_apply_eq Matrix.one_apply_ne Matrix.conjTranspose_apply
  Matrix.head_cons Matrix.one_fin_three Matrix.mul_apply Fin.sum_univ_succ
  Quaternion.one_re Quaternion.one_imI Quaternion.one_imJ Quaternion.one_imK
  Quaternion.neg_re Quaternion.neg_imI Quaternion.neg_imJ Quaternion.neg_imK
  MonoidHom.mem_mker Set.mem_insert_iff Set.mem_singleton_iff Matrix.one_apply_eq
  Subtype.ext_iff Subtype.coe_mk SetLike.mem_coe
  Pi.add_apply Pi.smul_apply Pi.zero_apply
  Fin.succ_zero_eq_one Fin.succ_one_eq_two
  QuaternionAlgebra.ext_iff Set.mem_insert_iff Set.mem_singleton_iff
  IsROrC.star_def IsROrC.conj_to_real Algebra.id.smul_eq_mul Submonoid.coe_one neg_zero
  Function.comp_apply Quaternion.coe_one Quaternion.coe_zero
  Quaternion.ext_iff zero_mul



/-
We will introduce the Chebyshev polynomials and prove an identity involving them,
-/

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
    = 2(2xT(m+1)-T(m))T(m+k+2)
    = 2x(2T(m+1)T((m+1)+(k+1)))-2T(m)T(m+(k+2))
    = 2x(T(2(m+1)+(k+1))+T(k+1))-(T(2m+(k+2))+T(k+2))
    = (2xT(2m+k+3)-T(2m+k+2))+(2xT(k+1)-T(k+2))
    = T(2(m+2)+k)+T(k)
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
    ring_nf at h₁ h₂ ⊢ -- note the effect of this on the hypotheses
    -- To finish the proof, introduce with `have`'s the necessary applications of the induction
    -- hypothesis and of the recursive definition. Then a call to `polyrith` will suffice.
    sorry

/-
The next goal is to prove the following fact about complex isometries:
we will prove that if f : ℂ → ℂ is an ℝ-linear isometry taking 1 to 1, then f(i) is either
i or -i. That is, f is either the identity or complex conjugation.

The key is to prove first that
$$
(f(i) - i) (\overline{f(i)} - \overline{-i}) = 0,
$$
and then deduce the result using that $ℂ$ is a domain.
-/
example {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) : f I = I ∨ f I = -I := by
  have key : (f I - I) * (conj (f I) - conj (-I)) = 0
  · have H₁ := congr_arg (λ t ↦ (((t ^ 2) : ℝ) : ℂ)) (f.norm_map (I - 1))
    have H₂ := congr_arg (λ t ↦ (((t ^ 2) : ℝ) : ℂ)) (f.norm_map I)
    simp only [h, ←normSq_eq_abs, complex_simps] at H₁ H₂ ⊢
    linear_combination I * H₁ + (-(1 * I) + 1) * H₂
  -- From `key`, we deduce that either `f I - I = 0` or `conj (f I) - conj (- I) = 0`.
  cases' eq_zero_or_eq_zero_of_mul_eq_zero key with hI hI
  · sorry
  · sorry -- use here that conjugation is injective

/-- Explicit matrix formula for the double cover of SO(3, ℝ) by the unit quaternions. -/
@[quaternion_simps]
def Quaternion.toMatrix (a : ℍ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let ⟨x, y, z, w⟩ := a
  ![![x ^ 2 + y ^ 2 - z ^ 2 - w ^ 2, 2 * (y * z - w * x), 2 * (y * w + z * x)],
    ![2 * (y * z + w * x), x ^ 2 + z ^ 2 - y ^ 2 - w ^ 2, 2 * (z * w - y * x)],
    ![2 * (y * w - z * x), 2 * (z * w + y * x), x ^ 2 + w ^ 2 - y ^ 2 - z ^ 2]]

/-- The explicit matrix formula `to_matrix` defines a monoid homomorphism from the quaternions into
the algebra of 3x3 matrices. -/
@[quaternion_simps] def Quaternion.toMatrixHom' : ℍ →* Matrix (Fin 3) (Fin 3) ℝ
    where
  toFun := Quaternion.toMatrix
  map_one' :=
    show Quaternion.toMatrix ⟨1, 0, 0, 0⟩ = 1 by
      ext (i j); fin_cases i <;> fin_cases j <;>
        simp [quaternion_simps]
  map_mul' := by
    rintro ⟨x, y, z, w⟩ ⟨r, s, t, u⟩
    show Quaternion.toMatrix ⟨_, _, _, _⟩
      = Quaternion.toMatrix ⟨_, _, _, _⟩ * Quaternion.toMatrix ⟨_, _, _, _⟩
    ext (i j); fin_cases i <;> fin_cases j <;> (simp [quaternion_simps]; ring)


def unitQuaternions : Submonoid ℍ :=
  MonoidHom.mker ((Quaternion.normSq : ℍ →*₀ ℝ) : ℍ →* ℝ)

@[simp high] theorem mem_unitQuaternions (a : ℍ) :
    a ∈ unitQuaternions ↔ a.re ^ 2 + a.imI ^ 2 + a.imJ ^ 2 + a.imK ^ 2 = 1 := by
  simp [←Quaternion.normSq_def']
  exact Iff.rfl


/-- The group of unit quaternions. -/
def unitQuaternions' : Subgroup (Units ℍ) where
  toSubmonoid := {
    carrier := {x | x.val ∈ unitQuaternions}
    mul_mem' := by
      rintro ⟨a, a', _, _⟩ ⟨b, b', _, _⟩
      simp [quaternion_simps] at *
      intro H1 H2
      linear_combination H1 + (a.re ^ 2 + a.imI ^ 2 + a.imJ ^ 2 + a.imK ^ 2) * H2
    one_mem' := by
      simp [quaternion_simps]
  }
  inv_mem' := by
    rintro ⟨a, b, h, h'⟩
    intro H
    simp at H ⊢
    have hre := Quaternion.mul_re a b
    have hI := Quaternion.mul_imI a b
    have hJ := Quaternion.mul_imJ a b
    have hK := Quaternion.mul_imK a b
    sorry -- Just a simp and a call to polyrith


/-- The explicit matrix formula `to_matrix` sends a unit quaternion to an element of SO(3, ℝ). -/
theorem toMatrix_mem_orthogonal {a : ℍ} (ha : a ∈ unitQuaternions) :
    toMatrix a ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  cases' a with x y z w
  have H : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 1 := by rwa [mem_unitQuaternions] at ha
  ext (i j)
  fin_cases i <;> fin_cases j <;> simp [quaternion_simps]
  · sorry -- polyrith
  · sorry -- polyrith
  · sorry -- polyrith
  · sorry -- polyrith
  · sorry -- polyrith
  · sorry -- polyrith
  · sorry -- polyrith
  · sorry -- polyrith
  · sorry -- polyrith

/-- Double cover of SO(3, ℝ) by the unit quaternions, as a homomorphism of monoids. This is obtained
by restriction of the homomorphism `quaternion.to_matrix_hom'` from `ℍ` into the 3x3 matrices; it is
well-defined by `to_matrix_mem_orthogonal`. -/
@[quaternion_simps]
def toMatrixHom : unitQuaternions →* Matrix.orthogonalGroup (Fin 3) ℝ :=
  (toMatrixHom'.restrict unitQuaternions).codRestrict (Matrix.orthogonalGroup (Fin 3) ℝ) fun a =>
    toMatrix_mem_orthogonal a.prop


/-- The unit quaternion -1 (the quaternion -1 together with a proof that its norm is one). -/
@[quaternion_simps]
noncomputable def negOne : unitQuaternions :=
  ⟨-1, show (⟨_, _, _, _⟩ : ℍ) ∈ _ by rw [mem_unitQuaternions]; norm_num ⟩

@[quaternion_simps]
theorem coe_negOne : (negOne : ℍ) = -1 := rfl

/-- Verify the "double cover" property of the homomorphism from unit quaternions to SO(3, ℝ): the
kernel is {1, -1}. -/
theorem toMatrixHom_mker : (MonoidHom.mker toMatrixHom : Set unitQuaternions) = {1, negOne} := by
  ext a
  obtain ⟨⟨x, y, z, w⟩, h⟩ := a
  have H : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 1 := by rwa [mem_unitQuaternions] at h
  simp [quaternion_simps]
  constructor
  -- hard direction: a quaternion in the kernel is ±1
  · intro h1
    have h₀₁ := congr_fun₂ h1 0 1
    -- Add more matrix entry inspections here as needed, and adjust the simplification line.
    -- The `polyrith` applications that follow will be broken until you do this!
    have hy : y = 0 := by sorry -- polyrith
    have hz : z = 0 := by sorry -- polyrith
    have hw : w = 0 := by sorry -- polyrith
    have hx : x ^ 2 = (1 : ℝ) ^ 2 := sorry -- polyrith
    -- now do a case division depending on the two cases for `x ^ 2 = 1 ^ 2`
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hx
    cases' hx with hx hx
    · simp [hx, hy, hz, hw]
    · simp [hx, hy, hz, hw]
  -- easy direction: ±1 are in the kernel
  rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> (ext (i j); fin_cases i <;> fin_cases j) <;>
  simp [quaternion_simps]
