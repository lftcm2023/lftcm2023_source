import Mathlib.Data.Real.NNReal
import Mathlib.Data.Fin.VecNotation

open scoped NNReal

/-!
# Structures and classes

These follow the slides at http://eric-wieser.github.io/<tba>

It is easiest to find the exercises in this file by turning on the outline view.
You can do this with `Ctrl+Shift+P` (`Cmd+Shift+P` on MacOS), typing "outline", and selecting
"Explorer: focus on outline view". A pane will open in the bottom left of VS, which reflects the
`section`s in this file.

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

-- make a list of cards of different numbers but the same suit; 💡 works inside other expressions too
def threeOfAKind : List Card :=
-- SOLUTIONS:
  [⟨0, 2⟩, {
    suit := 0
    value := 3
  }, { suit := 0, value := 4}]
/- EXAMPLES:
  -- [sorry, sorry, sorry]
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

/-- Basic proofs about definitions -/

@[simp] theorem add_x (a b : Point) : (a + b).x = a.x + b.x :=
  rfl
@[simp] theorem add_y (a b : Point) : (a + b).y = a.y + b.y :=
  rfl
@[simp] theorem add_z (a b : Point) : (a + b).z = a.z + b.z :=
  rfl

@[simp] theorem smul_x (r : ℝ) (a : Point) : (r • a).x = r • a.x :=
  rfl
@[simp] theorem smul_y (r : ℝ) (a : Point) : (r • a).y = r • a.y :=
  rfl
@[simp] theorem smul_z (r : ℝ) (a : Point) : (r • a).z = r • a.z :=
  rfl

@[simp] theorem zero_x : (0 : Point).x = 0 :=
  rfl
@[simp] theorem zero_y : (0 : Point).y = 0 :=
  rfl
@[simp] theorem zero_z : (0 : Point).z = 0 :=
  rfl

example : ((⟨1, 2, 3⟩ : Point) + (⟨10, 20, 30⟩ : Point)).x = 11 := by
  dsimp -- goal is now `1 + 10 = 11`
  norm_num

end slides

section exercise
/-! ### EXERCISE 6 -/

/-
1. Write lemmas like the above for `neg`
-/

-- SOLUTIONS:
@[simp] theorem neg_x (a : Point) : (-a).x = -a.x := rfl
@[simp] theorem neg_y (a : Point) : (-a).y = -a.y := rfl
@[simp] theorem neg_z (a : Point) : (-a).z = -a.z := rfl
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
attribute [ext] Point

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

end proofs_within_structures

section slides

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

structure EvenNat where
  n : ℕ
  is_even : Even n

structure PythagoreanTriple where
  a : ℕ
  b : ℕ
  c : ℕ
  sq_add_sq : a^2 + b^2 = c^2

structure RootOf (f : ℝ → ℝ) where
  x : ℝ
  is_root : f x = 0

end slides

section exercise
/-! ### EXERCISE 8

Don't forget to use the 💡 feature!
-/

/-
1. Define a pythogorean triple
-/
example : PythagoreanTriple :=
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

end exercise

end proofs_with_structures
