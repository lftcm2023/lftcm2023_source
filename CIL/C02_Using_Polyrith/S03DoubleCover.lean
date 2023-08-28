/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth, Marc Masdeu
-/
import Mathlib.Analysis.Quaternion
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Polyrith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GroupPower.Ring
import CIL.Attr

open scoped Quaternion

noncomputable section

/-! This file contains a lot of computationally-intensive evaluation of matrices and quaternions.
We speed it up slightly by specifiying in advance the path the simplifier should take. -/


local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue #2220

/-- Explicit matrix formula for the double cover of SO(3, ℝ) by the unit quaternions. -/
@[quaternion_simps]
def Quaternion.toMatrix (a : ℍ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let ⟨x, y, z, w⟩ := a
  ![![x ^ 2 + y ^ 2 - z ^ 2 - w ^ 2, 2 * (y * z - w * x), 2 * (y * w + z * x)],
    ![2 * (y * z + w * x), x ^ 2 + z ^ 2 - y ^ 2 - w ^ 2, 2 * (z * w - y * x)],
    ![2 * (y * w - z * x), 2 * (z * w + y * x), x ^ 2 + w ^ 2 - y ^ 2 - z ^ 2]]

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
  QuaternionAlgebra.ext_iff
  Quaternion.toMatrix Set.mem_insert_iff Set.mem_singleton_iff
  IsROrC.star_def IsROrC.conj_to_real Algebra.id.smul_eq_mul Submonoid.coe_one neg_zero
  Function.comp_apply Quaternion.coe_one Quaternion.coe_zero
  Quaternion.ext_iff zero_mul

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

/-- The group (we only prove it to be a monoid) of unit quaternions. -/
def unitQuaternions : Submonoid ℍ :=
  MonoidHom.mker ((Quaternion.normSq : ℍ →*₀ ℝ) : ℍ →* ℝ)

@[simp high] theorem mem_unitQuaternions (a : ℍ) :
    a ∈ unitQuaternions ↔ a.re ^ 2 + a.imI ^ 2 + a.imJ ^ 2 + a.imK ^ 2 = 1 := by
  simp [←Quaternion.normSq_def']
  exact Iff.rfl


#check Matrix.orthogonalGroup (Fin 3) ℝ

namespace unitQuaternions

open Quaternion


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
  ⟨-1, show (⟨_, _, _, _⟩ : ℍ) ∈ _ by
    rw [mem_unitQuaternions]
    norm_num ⟩

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
    have hy : y = 0
    · sorry -- polyrith
    have hz : z = 0
    · sorry -- polyrith
    have hw : w = 0
    · sorry -- polyrith
    have hx : x ^ 2 = (1 : ℝ) ^ 2
    · sorry  -- TODO fill this in
    -- now do a case division depending on the two cases for `x ^ 2 = 1 ^ 2`
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hx
    cases' hx with hx hx
    · simp [hx, hy, hz, hw]
    · simp [hx, hy, hz, hw]
  -- easy direction: ±1 are in the kernel
  rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> ext (i j); fin_cases i <;> fin_cases j
  · simp [quaternion_simps]
  · simp [quaternion_simps]
  · simp [quaternion_simps]
  · simp [quaternion_simps]
  · simp [quaternion_simps]
  · simp [quaternion_simps]
  · simp [quaternion_simps]
  · simp [quaternion_simps]
  · simp [quaternion_simps]
  · simp [quaternion_simps]

end unitQuaternions
