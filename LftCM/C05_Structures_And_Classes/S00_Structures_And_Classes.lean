import Mathlib.Data.Real.NNReal
import Mathlib.Data.Fin.VecNotation

open scoped NNReal

/-!
-- SOLUTIONS:
# Structures and classes (SOLUTIONS)
-- EXAMPLES:
# Structures and classes
-- BOTH:

These follow the slides at http://eric-wieser.github.io/lftcm-2023

It is easiest to find the exercises in this file by turning on the outline view.
You can do this with `Ctrl+Shift+P` (`Cmd+Shift+P` on MacOS), typing "outline", and selecting
"Explorer: focus on outline view". A pane will open in the bottom left of VSCode, which reflects the
`section`s in this file.

If you get bored of these exercises, feel free to move onto the exercises in MIL, especially
`S03_Building_the_Gaussian_Integers`. You will need to read MIL alongside the lean file in order
to see the explanation of the exercise!

-- SOLUTIONS:
If you're struggling, don't forget that this IS the solutions file!
-- EXAMPLES:
If you're struggling, don't forget the solutions are in the repo too.
-- BOTH:
Some exercises rely on you having solved (or copied the solutions from) previous exercises.
-/

/-! ## Defining structures -/
section defining_structures

/-! ### The basics-/
section the_basics

section slides

structure Card where
  suit : Fin 4
  value : Fin 13  -- ace = 0

structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

structure DirectedLineSegment where
  src : Point
  dst : Point

/-! Various equivalent ways to construct a `Point` -/

def myPoint : Point where
  x := 2
  y := -1
  z := 4

def myPoint'' : Point :=
  { x := 2, y := -1, z := 4 }

def myPoint''' : Point :=
  ⟨2, -1, 4⟩

def myPoint'''' :=
  Point.mk 2 (-1) 4

end slides

section exercise
/-! ### EXERCISE 1

try out the `_` 💡 feature: put your cursor on the `_` and click the lightbulb.  -/

-- you can assume clubs are suit `0`
-- SOLUTIONS:
def twoOfClubs : Card where
  suit := 0
  value := 2
/- EXAMPLES:
def twoOfClubs : Card := _
BOTH: -/

-- make a list of cards of different numbers but the same suit; 💡 on `_` works inside other expressions too
def threeOfAKind : List Card :=
-- SOLUTIONS:
  [⟨0, 2⟩, {
    suit := 0
    value := 3
  }, { suit := 0, value := 4}]
/- EXAMPLES:
  [sorry, sorry, sorry]
BOTH: -/

end exercise

section slides

/-! Examples of nested structures -/

def mySegment : DirectedLineSegment where
  src := {  -- `where` syntax doesn't work here
    x := 0
    y := 1
    z := 2
  }
  dst := ⟨3, 4, 5⟩

def mySegment' : DirectedLineSegment :=
  ⟨⟨0, 1, 2⟩, ⟨3, 4, 5⟩⟩

end slides

section exercise
/-! ### EXERCISE 2

1. Define the type of 3D spheres, in terms of a center and radius.
   Use the `Point` structure we already defined. Note: you can use `ℝ≥0` instead of `ℝ` to ensure
   the radius is not negative! -/

structure Sphere :=
  -- write your definition here
-- SOLUTIONS:
  center : Point
  radius : ℝ≥0
-- BOTH:

/-!
2. Construct the unit sphere at the point (1, 2, 2) of radius 3
-/

-- SOLUTIONS:
example : Sphere where
  center := ⟨1, 2, 2⟩
  radius := 3
/- EXAMPLES:
example : Sphere := sorry
BOTH: -/

end exercise

section slides

/-! Structures with functions -/

structure RealSeq where
  term : ℕ → ℝ

structure BundledTuple where
  n : ℕ
  term : Fin n → ℝ

structure NatRel where
  rel : ℕ → ℕ → Prop

def squares' : RealSeq where
  term n := (n : ℝ) ^ n

def adjacentRel' : NatRel where
  rel m n := m = n + 1 ∨ m + 1 = n

def SumIsTwo : NatRel where
  rel
  | 0, 2 | 1, 1 | 2, 0 => True
  | _, _ => False

def myTuple : BundledTuple where
  n := 3
  term := ![1, 2, 3]

end slides

section exercise
/-! ### EXERCISE 3

1. Define the Real sequence of all zeros
-/

-- SOLUTIONS:
def allZeroSeq : RealSeq where
  term _i := 0
/- EXAMPLES:
def allZeroSeq : RealSeq := sorry
BOTH: -/


/-!
2. Define a real sequence of alternating `1`s and `-1`s
-/

-- you write the def this time!
-- SOLUTIONS:
def alternatingSeq : RealSeq where
  term i := (-1)^i
-- BOTH:

/-!
3. Define the type of re-colorings of a 8x8 chessboard, labeling each square as black or white.
   Note that the type for `[0,8)` is `Fin 8`. -/

structure Chessboard8x8Coloring where
  -- your fields here
-- SOLUTIONS:
  IsBlack : Fin 8 → Fin 8 → Prop
  -- or: `IsBlack : Fin 8 → Fin 8 → Bool`
-- BOTH:

/-!
4. Define the standard coloring on a chessboard.
-/

-- SOLUTIONS:
def Chessboard8x8Coloring.standard : Chessboard8x8Coloring where
  IsBlack i j := i = j  -- or `≠` if you prefer!

/- EXAMPLES:
def Chessboard8x8Coloring.standard : Chessboard8x8Coloring := sorry
BOTH: -/

end exercise

end the_basics

/-! ### Functions and operators -/
section functions_and_operators

section slides

def Point.add (a b : Point) : Point where
  x := Point.x a + Point.x b
  y := a.y + b.y
  z := a.z + b.z

namespace Point

def add' (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add'' : Point → Point → Point
| ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ =>
    ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

end Point

end slides

section exercise
/-! ### EXERCISE 4 -/

/-!
1. Define the vector dot product of two points, as a real number. You can choose whether to use
   pattern matching or projection notation
-/
-- SOLUTIONS:
def Point.dotProduct (p1 p2 : Point) : ℝ := p1.x*p2.x + p1.y*p2.y + p1.z*p2.z
def Point.dotProduct' : Point → Point → ℝ
| ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => x₁*x₂ + y₁*y₂ + z₁*z₂
/- EXAMPLES:
def Point.dotProduct : ℝ := sorry
BOTH: -/

/-!
2. Define a function to determine if three playing cards form a run (within a suit); for instance
   3♠, 4♠, 5♠
-/
-- SOLUTIONS:
def Card.IsAscendingRun (a b c : Card) : Prop :=
  a.suit = b.suit ∧ b.suit = c.suit ∧
  (a.value + 1 : ℕ) = b.value ∧ (b.value + 1 : ℕ) = c.value
/- EXAMPLES:
def Card.IsAscendingRun (a b c : Card) : Prop := sorry
BOTH: -/

end exercise

section slides

/-! Parametrization -/

structure Point' (R : Type) where
  x : R
  y : R
  z : R
deriving Repr -- needed for the `#eval` below to print nicely

def myRealPoint : Point' ℝ where
  x := 2
  y := -1
  z := 4

def myIntPoint : Point' ℤ :=
  Point'.mk 2 (-1) 4

-- a bonus: integer points can be `#eval`uated (i.e. run as a program)
#eval myIntPoint

/-! Operators -/

instance : Add Point where
  add a b :=
    { x := a.x + b.x
      y := a.y + b.y
      z := a.z + b.z }

example : Point := ⟨1, 0, 0⟩ + ⟨0, 1, 0⟩

-- this finds the instance we just defined; you can ctrl+click in the info view to jump back to
-- where we defined it. Note the auto-generated name.
#synth Add Point

-- This option shows exactly what Lean is doing; click the `▶`s in the infoview to expand.
-- You'll see that it finds all of
-- `#[@AddZeroClass.toAdd, @AddSemigroup.toAdd, @Distrib.toAdd, instAddPoint]` to try, but tries the
-- last one first.
set_option trace.Meta.synthInstance true in
#synth Add Point

end slides

section exercise
/-! ### EXERCISE 5

1. Define the following notations for `Point`.
   Note that the `💡` trick works just fine for `instance` too -/
-- SOLUTIONS:
instance : Zero Point where
  zero := ⟨0, 0, 0⟩
instance : SMul ℝ Point where
  smul r p := ⟨r * p.x, r * p.y, r * p.z⟩ -- scalar multiplication
instance : Neg Point where
  neg | ⟨x, y, z⟩ => ⟨-x, -y, -z⟩
/- EXAMPLES:
instance : Zero Point := sorry
instance : SMul ℝ Point := sorry -- scalar multiplication
instance : Neg Point := sorry
BOTH: -/

/-!
2. Now do the same thing for `Point' R`. Note that for this to make sense, we need to assume that
   `R` already has a Zero / Mul / Neg; we do this with square brackets. Try removing `[Zero R]` to
   see where lean complains.
-/
variable {R : Type}

-- SOLUTIONS:
instance [Zero R] : Zero (Point' R) where
  zero := ⟨0, 0, 0⟩
instance [Add R] : Add (Point' R) where
  add p1 p2 := ⟨p1.x + p2.x, p1.y + p2.y, p1.z + p2.z⟩
instance [Mul R] : SMul R (Point' R) where
  smul r p := ⟨r * p.x, r * p.y, r * p.z⟩-- scalar multiplication
instance [Neg R] : Neg (Point' R) where
  neg | ⟨x, y, z⟩ => ⟨-x, -y, -z⟩
/- EXAMPLES:
instance [Zero R] : Zero (Point' R) := sorry
instance [Add R] : Add (Point' R) := sorry
instance [Mul R] : SMul R (Point' R) := sorry
instance [Neg R] : Neg (Point' R) := sorry
BOTH: -/

-- will succeed once you complete the above
#eval (⟨1, 2, 3⟩ : Point' ℤ) + (10 : ℤ) • (⟨10, 20, 30⟩ : Point' ℤ)

end exercise

end functions_and_operators

end defining_structures

/-! ## Proofs with structures -/
section proofs_with_structures

section slides
variable {R : Type}

/-- Basic proofs about definitions -/

@[simp] theorem add_x [Add R] (a b : Point' R) : (a + b).x = a.x + b.x :=
  rfl
@[simp] theorem add_y [Add R] (a b : Point' R) : (a + b).y = a.y + b.y :=
  rfl
@[simp] theorem add_z [Add R] (a b : Point' R) : (a + b).z = a.z + b.z :=
  rfl

@[simp] theorem smul_x [Mul R] (r : R) (a : Point' R) : (r • a).x = r • a.x :=
  rfl
@[simp] theorem smul_y [Mul R] (r : R) (a : Point' R) : (r • a).y = r • a.y :=
  rfl
@[simp] theorem smul_z [Mul R] (r : R) (a : Point' R) : (r • a).z = r • a.z :=
  rfl

@[simp] theorem zero_x [Zero R] : (0 : Point' R).x = 0 :=
  rfl
@[simp] theorem zero_y [Zero R]: (0 : Point' R).y = 0 :=
  rfl
@[simp] theorem zero_z [Zero R] : (0 : Point' R).z = 0 :=
  rfl

example : ((⟨1, 2, 3⟩ : Point' ℝ) + (⟨10, 20, 30⟩ : Point' ℝ)).x = 11 := by
  dsimp -- goal is now `1 + 10 = 11`
  norm_num

end slides

section exercise
/-! ### EXERCISE 6 -/
variable {R : Type}
/-
1. Write lemmas like the above for `neg`. If you get an error like
   ```
   failed to synthesize instance
     Neg R
   ```
   this means you forgot to add `[Neg R]` to the arguments. Note that this advice does not always
   work: if you already have `[Semiring R]` (introduced in a later talk), you should switch to
   `[Ring R]` instead of `[Semiring R] [Neg R]`.
-/

-- SOLUTIONS:
@[simp] theorem neg_x [Neg R]  (a : Point' R) : (-a).x = -a.x := rfl
@[simp] theorem neg_y [Neg R] (a : Point' R) : (-a).y = -a.y := rfl
@[simp] theorem neg_z [Neg R] (a : Point' R) : (-a).z = -a.z := rfl
/- EXAMPLES:
@[simp] theorem neg_x : sorry := sorry
@[simp] theorem neg_y : sorry := sorry
@[simp] theorem neg_z : sorry := sorry
BOTH: -/

end exercise

section slides

example {a b : Point}
    (hx : a.x = b.x)
    (hy : a.y = b.y)
    (hz : a.z = b.z) : a = b := by
  obtain ⟨a_x, a_y, a_z⟩ := a  -- or `cases' a with a_x a_y a_z`, or `cases a` for worse names
  obtain ⟨a_b, b_y, b_z⟩ := b
  dsimp only at *
  /- look at the goal here; `obtain` split `a` and `b` into pieces -/
  rw [hx, hy, hz]

/-!
Could also have written
```lean
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ
```
instead we'll add the attribute retrospectively
-/
attribute [ext] Point Point'

example {a b : Point}
    (hx : a.x = b.x)
    (hy : a.y = b.y)
    (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption

protected theorem Point.add_comm (a b : Point) :
    a + b = b + a := by
  ext <;> dsimp <;> apply add_comm

-- or

example (a b : Point) :
    a + b = b + a := by
  ext
  dsimp
  · apply add_comm
  · apply add_comm
  · apply add_comm

-- or

example (a b : Point) :
    a + b = b + a := by
  ext
  dsimp
  case x => apply add_comm
  case y => apply add_comm
  case z => apply add_comm

end slides

section exercise
/-! ### EXERCISE 7 -/
variable {R : Type}

/--
1. Prove that addition is associative on `Point`
-/

protected theorem Point.add_assoc (a b c : Point) :
    (a + b) + c = a + (b + c) := by
-- SOLUTIONS:
  ext <;> dsimp <;> apply add_assoc
/- EXAMPLES:
  sorry
BOTH: -/

/-
2. State and prove that `a + 0 = a` and `0 + a = a`
-/
-- SOLUTIONS:
protected theorem Point.add_zero (a : Point) :
    a + 0 = a := by
  ext <;> dsimp <;> apply add_zero

protected theorem Point.zero_add (a : Point) :
    a + 0 = a := by
  ext <;> dsimp <;> apply add_zero
-- BOTH:

/-
3. State and prove that `-a + a = 0` (hint: `add_left_neg`)
-/

-- SOLUTIONS:
protected theorem Point.add_left_neg (a : Point) :
    -a + a = 0 := by
  ext <;> dsimp <;> apply add_left_neg
-- BOTH:

end exercise

section proofs_within_structures

section slides

@[ext]
structure OpenDisc2D (r : ℝ) where
  x : ℝ
  y : ℝ
  mem_disc : x^2 + y^2 < r^2

def unitDiscZero : OpenDisc2D 1 where
  x := 0
  y := 0
  mem_disc := by
    -- goal is 0 ^ 2 + 0 ^ 2 < 1 ^ 2
    norm_num

example (p : OpenDisc2D 1) : p.x ≠ 2 := by
  intro hx            -- hx : p.x = 2
  have := p.mem_disc  -- this : p.x ^ 2 + p.y ^ 2 < 1 ^ 2
  nlinarith

@[ext]
structure EvenNat where
  n : ℕ
  is_even : Even n

@[ext]
structure MyPythagoreanTriple where
  a : ℕ
  b : ℕ
  c : ℕ
  sq_add_sq : a^2 + b^2 = c^2

@[ext]
structure RootOf (f : ℝ → ℝ) where
  x : ℝ
  is_root : f x = 0

-- without the `: Prop`, we can't use this with `↔`
structure IsFizzBuzz (n : ℕ) : Prop where
  is_fizz : 3 ∣ n
  is_buzz : 5 ∣ n

end slides

section exercise
/-! ### EXERCISE 8

Don't forget to use the 💡 feature!
-/

/-
1. Define a Pythagorean triple
-/
example : MyPythagoreanTriple :=
-- SOLUTIONS:
  ⟨3, 4, 5, by ring⟩
/- EXAMPLES:
  sorry
BOTH: -/

/-
2. Provide a root of `x^2 - 4`
-/
example : RootOf (fun x ↦ x^2 - 4) :=
  ⟨-2, by ring⟩
/- EXAMPLES:
  sorry
BOTH: -/

/-
3. Define addition on even natural numbers.
   You might find `Even.add` helpful
-/
instance : Add EvenNat where
-- SOLUTIONS:
  add x y := {
    n := x.n + y.n
    is_even := Even.add x.is_even y.is_even
  }
/- EXAMPLES:
  add x y := sorry
BOTH: -/

/-
4. Show that `IsFizzBuzz` is the same as divisibility by 3 and 5
-/

lemma isFizzBuzz_iff_dvd_and_dvd (n : ℕ) : IsFizzBuzz n ↔ 3 ∣ n ∧ 5 ∣ n := by
-- SOLUTIONS:
  constructor
  · rintro h
    exact ⟨h.is_fizz, h.is_buzz⟩
  · rintro h
    exact ⟨h.left, h.right⟩
/- EXAMPLES:
  sorry
BOTH: -/

end exercise

/- Builtin types-/
section slides

-- ctrl-click on `Prod` to see its definition
#print Prod
#print Subtype

end slides

section exercise
/-! ### EXERCISE 9

Here we show that the composition of builtin structures is the same as our custom structures.
Note that `≃` is notation for `Equiv`, which is itself a structure
(right click -> "peek definition" will show you how it is defined).
-/
#check Equiv
/--
1. Show that our point type is equivalent to a triplet of real numbers. N
-/

def Point.equivProdProd : Point ≃ ℝ × ℝ × ℝ where
-- SOLUTIONS:
  toFun p := ⟨p.x, p.y, p.z⟩
  invFun p := { x := p.fst, y := p.snd.fst, z := p.snd.snd }
  left_inv p := by
    cases p
    rfl
  right_inv t := by
    cases t
    rfl
/- EXAMPLES:
  toFun p := sorry
  invFun t := sorry
  left_inv p := by
    sorry
  right_inv t := by
    sorry
BOTH: -/

/-
2. Show that our OpenDisc2D type is isomorphic to a subtype
-/
-- SOLUTIONS:
def OpenDisc2D.equiv (r) : OpenDisc2D r ≃ {x : ℝ × ℝ // x.1^2 + x.2^2 < r ^ 2} where
  toFun o := ⟨(o.x, o.y), o.mem_disc⟩
  invFun s := { x := s.val.fst, y := s.val.snd, mem_disc := s.property }
  left_inv o := by
    ext <;> rfl
  right_inv s := by
    ext <;> rfl
/- EXAMPLES:
def OpenDisc2D.equiv (r) : OpenDisc2D r ≃ {x : ℝ × ℝ // x.1^2 + x.2^2 < r ^ 2} :=
  sorry
BOTH: -/

end exercise

end proofs_within_structures

end proofs_with_structures

/-! ## Algebraic structures -/
section algebraic_structures

section slides

class DirectTranslation.PartialOrder (P : Type) where  -- a set $P$ and
  le : P → P → Prop               -- a binary relation $\le$ on $P$
  le_trans : Transitive le        -- that is transitive
  le_antirefl : AntiSymmetric le  -- and antisymmetric

class DirectTranslation.Group (G : Type) where     -- a set $G$ with
  mul : G → G → G             -- an associative binary operation,
  mul_assoc : Associative mul
  one : G                     -- an identity element $1$, and
  one_mul : LeftIdentity mul one
  mul_one : RightIdentity mul one
  inv : G → G                 -- returns an inverse for each $g$ in $G$.
  mul_right_inv :
    RightInverse mul inv one

/-- A simpler version of `Group` -/
class LFTCM.Group (G : Type) extends Mul G, One G, Inv G where
  mul_assoc : ∀ x y z : G, (x * y) * z = x * (y * z)
  mul_one : ∀ x : G, x * 1 = x
  one_mul : ∀ x : G, 1 * x = x
  mul_left_inv : ∀ x : G, x⁻¹ * x = 1

variable {α : Type}

/- These already exist
```
instance : One (Equiv.Perm α) where
  one := Equiv.refl _
instance : Mul (Equiv.Perm α) where
  mul x y := x.trans y
instance : Inv (Equiv.Perm α) where
  inv x := x.symm
```
-/
#synth One (Equiv.Perm α)
#synth Mul (Equiv.Perm α)
#synth Inv (Equiv.Perm α)

instance : LFTCM.Group (Equiv.Perm α) where
  mul_assoc e₁ e₂ e₃ := by
    ext
    dsimp
  mul_one e := by
    ext
    dsimp
  one_mul e := by
    ext
    dsimp
  mul_left_inv e := by
    ext
    exact e.symm_apply_apply _

end slides

section exercise

/-! ### EXERCISE 10

1. In the style of `LFTCM.Group`, write a typeclass for additive groups
-/

/-- A simpler version of `AddGroup`. You will need to `extend` the appropriate notation, and write
the fields. -/
-- SOLUTIONS:
class MyAddGroup (G : Type) extends Add G, Zero G, Neg G where
  add_assoc : ∀ x y z : G, (x + y) + z = x + (y + z)
  add_zero : ∀ x : G, x + 0 = x
  zero_add : ∀ x : G, 0 + x = x
  add_left_neg : ∀ x : G, -x + x = 0
/- EXAMPLES:
class MyAddGroup (G : Type) where
  -- add your fields here
BOTH: -/

/-
2. Prove that `Point' R` forms an additive group when `R` does
-/

instance {R} [MyAddGroup R] : MyAddGroup (Point' R) where
  add_assoc p q r := by
    -- note that because we are inventing our own `AddGroup`,
    -- we can't use the builtin `add_assoc` lemma
    ext <;> dsimp
    · apply MyAddGroup.add_assoc
    · apply MyAddGroup.add_assoc
    · apply MyAddGroup.add_assoc
-- SOLUTIONS:
  add_zero p := by ext <;> apply MyAddGroup.add_zero
  zero_add p := by ext <;> apply MyAddGroup.zero_add
  add_left_neg p := by ext <;> apply MyAddGroup.add_left_neg
/- EXAMPLES:
  add_assoc p q r:= _
  add_zero p := _
  zero_add p := _
  add_left_neg p := _
BOTH: -/
end exercise

section exercise

/-! ### EXERCISE 11

1. Do the same as in exercise 10, but for "real" mathlib additive groups
-/
instance {R} [AddGroup R] : AddGroup (Point' R) where
  add_assoc p q r := by
    -- now we can use the real `add_assoc`
    ext <;> dsimp
    · apply add_assoc
    · apply add_assoc
    · apply add_assoc
-- SOLUTIONS:
  add_zero p := by ext <;> apply add_zero
  zero_add p := by ext <;> apply zero_add
  add_left_neg p := by ext <;> apply add_left_neg
/- EXAMPLES:
  add_assoc p q r:= _
  add_zero p := _
  zero_add p := _
  add_left_neg p := _
BOTH: -/

-- the trace is slightly more interesting here; first it tries `[AddGroup R]`
variable {R} [AddGroup R]  in
set_option trace.Meta.synthInstance true in
#synth AddGroup (Point' R)

end exercise

section slides

/-- Advanced: forgetful inheritance -/
example {α : Type} :
    Group (Equiv.Perm α) where
  mul := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  npow := sorry            -- optional
  npow_zero := sorry       -- optional
  npow_succ := sorry       -- optional
  inv := sorry
  div := sorry             -- optional
  div_eq_mul_inv := sorry  -- optional
  zpow := sorry            -- optional
  zpow_zero' := sorry      -- optional
  zpow_succ' := sorry      -- optional
  zpow_neg' := sorry       -- optional
  mul_left_inv := sorry
-- no need to fill the above, this is not an exercise!

end slides

namespace LFTCM

@[ext]
structure MulOpposite (α : Type) where op ::
  unop : α

namespace MulOpposite

instance {α} [One α] : One (MulOpposite α) where
  one := op 1

@[simp] theorem op_one {α} [One α] : op (1 : α) = 1 := rfl
@[simp] theorem unop_one {α} [One α] : (unop 1 : α) = 1 := rfl

instance {α} [Mul α] : Mul (MulOpposite α) where
  mul x y := op (unop y * unop x)

@[simp] theorem op_mul {α} [Mul α] (a b : α) :
  op (a * b : α) = op b * op a := rfl
@[simp] theorem unop_mul {α} [Mul α] (a b : MulOpposite α) :
  (unop (a * b) : α) = unop b * unop a := rfl

instance {α} [Inv α] : Inv (MulOpposite α) where
  inv x := op (x.unop⁻¹)

@[simp] theorem op_inv {α} [Inv α] (x : α) : op (x⁻¹) = (op x)⁻¹ := rfl
@[simp] theorem unop_inv {α} [Inv α] (x : MulOpposite α) :
  (unop (x⁻¹) : α) = (unop x)⁻¹ := rfl

end MulOpposite

end LFTCM

open LFTCM.MulOpposite

section exercise
/-! ### EXERCISE 12

1. Show that `MulOpposite α` is a group when `α` is. Remember the advice about deleting the
  un-needed fields. You can also delete `one`, `mul`, and `inv` as they are found from the above.
-/
-- SOLUTIONS:
instance {α} [Group α] : Group (LFTCM.MulOpposite α) where
  mul_assoc a b c := by ext; simp [mul_assoc]
  mul_one a := by ext; simp
  one_mul a := by ext; simp
  mul_left_inv a := by ext; simp
/- EXAMPLES:
instance {α} [Group α] : Group (MulOpposite α) :=
  sorry
BOTH: -/

end exercise

end algebraic_structures
