import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.Tactic.Polyrith

namespace lftcm2023

/- TEXT:
.. _section_hierarchies_basics:

Basics
------

At the very bottom of all hierarchies in Lean, we find data-carrying
classes. The following class records that the given type ``α`` is endowed with
a distinguished element called ``one``. At this stage, it has no property at all.
BOTH: -/

-- QUOTE:
class One (α : Type) where
  /-- The element one -/
  one : α
-- QUOTE.

/- TEXT:
Since we'll make a much heavier use of classes in this chapter, we need to understand some
more details about what the ``class`` command is doing.
First, the ``class`` command above defines a structure ``One`` with parameter ``α : Type`` and
a single field ``one``. It also mark this structure as a class so that arguments of type
``One₁ α`` for some type ``α`` will be inferrable using the instance resolution procedure,
as long as they are marked as instance-implicit, ie appear between square brackets.
Those two effects could also have been achieved using the ``structure`` command with ``class``
attribute, ie writing ``@[class] structure`` instance of ``class``. But the class command also
ensures that ``One α`` appears as an instance-implicit argument in its own fields. Compare:
BOTH: -/

-- QUOTE:
#check One.one -- lftcm2023.One.one {α : Type} [self : One α] : α

@[class] structure One' (α : Type) where
  /-- The element one -/
  one : α

#check One'.one -- lftcm2023.One'.one {α : Type} (self : One' α) : α

-- QUOTE.

/- TEXT:
In the second check, we can see that ``self : One' α`` is an explicit argument.
Let us make sure the first version is indeed usable without any explicit argument.
BOTH: -/

-- QUOTE:
example (α : Type) [One α] : α := One.one
-- QUOTE.

/- TEXT:
Remark: in the above example, the argument ``One α`` is marked as instance-implicit,
which is a bit silly since this affects only *uses* of the declaration and declaration created by
the ``example`` command cannot be used. However it allows to avoid giving a name to that
argument and, more importantly, it starts installing the good habit of marking ``One α``
arguments as instance-implicit.

Another remark is that all this will work only when Lean knows what is ``α``. In the above
example, leaving out the type ascription ``: α`` would generate an error message like:
``typeclass instance problem is stuck, it is often due to metavariables One (?m.263 α)``
where ``?m.263 α`` means "some type depending on ``α``" (and 263 is simply an auto-generated
index that would be useful to distinguish between several unknown things). Another way
to avoid this issue would be to use a type annotation, as in:
BOTH: -/
-- QUOTE:
example (α : Type) [One α] := (One.one : α)
-- QUOTE.

/- TEXT:
You may have already encountered that issue when playing with limits of sequences
in :numref:`sequences_and_convergence` if you tried to state for instance that
``0 < 1`` without telling Lean whether you meant this inequality to be about natural numbers
or real numbers.

Our next task is to assign a notation to ``One.one``.
BOTH: -/
-- QUOTE:
instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

example {α : Type} [One α] : α := 1

example {α : Type} [One α] : (1 : α) = 1 := rfl
-- QUOTE.


/- TEXT:
As in the ``One`` example, the operation has no property at all at this stage. Let us
now define the class of semigroup structures where the operation is denoted by ``*``.
For now, we define it by hand as a structure with two fields, a ``Mul`` instance and some
``Prop``-valued field ``mul_assoc`` asserting associativity of ``*``.
BOTH: -/

-- QUOTE:
class Semigroup' (α : Type) where
  toMul : Mul α
  /-- Multiplication is associative -/
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
-- QUOTE.

/- TEXT:
Note that while stating `mul_assoc`, the previously defined field `toMul` is in the local
context hence can be used when Lean searches for an instance of `Mul α` to make sense
of `a * b`. However this `toMul` field does not become part of the type class instances database.
Hence doing ``example {α : Type} [Semigroup' α] (a b : α) : α := a * b`` would fail with
error message ``failed to synthesize instance Mul α``.

We can fix this by adding the ``instance`` attribute later.
BOTH: -/

-- QUOTE:
attribute [instance] Semigroup'.toMul

example {α : Type} [Semigroup' α] (a b : α) : α := a * b
-- QUOTE.

/- TEXT:
Before building up, we need a more convenient way to extend structures than explicitly
writing fields like `toMul` and adding the instance attribute by hand. The ``class``
supports this using the ``extends`` syntax as in:
BOTH: -/

-- QUOTE:
class Semigroup (α : Type) extends Mul α where
  /-- Multiplication is associative -/
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)

example {α : Type} [Semigroup α] (a b : α) : α := a * b
-- QUOTE.

/- TEXT:
Note this syntax is also available in the ``structure`` command, although it that
case it fixes only the hurdle of writing fields such as `toMul` since there
is no instance to define in that case.


Let us now try to combine a multiplication operation and a distinguished one with axioms saying
this element is neutral on both sides.
BOTH: -/
-- QUOTE:
class MulOneClass (α : Type) extends One α, Mul α where
  /-- One is a left neutral element for multiplication. -/
  one_mul : ∀ a : α, (1 : α) * a = a
  /-- One is a right neutral element for multiplication -/
  mul_one : ∀ a : α, a * (1 : α) = a

-- QUOTE.

/- TEXT:
In the next example, we tell Lean that ``α`` has a ``MulOneClass`` structure and state a
property that uses both a `Mul` instance and a `One` instance. In order to see how Lean finds
those instances we set a tracing option whose result can be seen in the info view. This result
is rather terse by default but can be expended by clicking one lines ending with black arrows.
It includes failed attempts where Lean tried to find instances before having enough type
information to succeed. The successful attempts do involve the instances generated by the
``extends`` syntax.
BOTH: -/

-- QUOTE:
set_option trace.Meta.synthInstance true in
example {α : Type} [MulOneClass α] (a b : α) : Prop := a * b = 1
-- QUOTE.

/- TEXT:
Note that we don't need to include extra fields where combining existing classes. Hence we can
define monoids as:
BOTH: -/

-- QUOTE:
class Monoid (α : Type) extends Semigroup α, MulOneClass α
-- QUOTE.

/- TEXT:
While the above definition seems straightforward, it hides an important subtlety. Both
``Semigroup α`` and ``MulOneClass α`` extend ``Mul α``, so one could fear that having
a ``Monoid α`` instance gives two unrelated multiplication operations on ``α``, one coming from
a field ``Monoid.toSemigroup`` and one coming from a field ``Monoid.toMulOneClass``.

Indeed if we try to build a monoid class by hand using:
BOTH: -/

-- QUOTE:
class MonoidBad (α : Type) where
  toSemigroup : Semigroup α
  toMulOneClass : MulOneClass α
-- QUOTE.

/- TEXT:
then we get two completely unrelated multiplication operations
``MonoidBad.toSemigroup.toMul.mul`` and ``MonoidBad.toMulOneClass.toMul.mul``.

The version generated using the ``extends`` syntax does not have this defect.
BOTH: -/

-- QUOTE:
example {α : Type} [Monoid α] :
  (Monoid.toSemigroup.toMul.mul : α → α → α) = Monoid.toMulOneClass.toMul.mul := rfl
-- QUOTE.

/- TEXT:
So the ``class`` command did some magic for us (and the ``structure`` command would have done it
too). An easy way to see what are the fields of our classes is to check their constructor. Compare:
BOTH: -/

-- QUOTE:
/- lftcm2023.MonoidBad.mk {α : Type} (toSemigroup : Semigroup α) (toMulOneClass : MulOneClass α) : MonoidBad α -/
#check MonoidBad.mk

/- lftcm2023.Monoid.mk {α : Type} [toSemigroup : Semigroup α] [toOne : One α] (one_mul : ∀ (a : α), 1 * a = a)
  (mul_one : ∀ (a : α), a * 1 = a) : Monoid α -/
#check Monoid.mk
-- QUOTE.

/- TEXT:
So we see that ``Monoid`` takes ``Semigroup α`` argument as expected but then it won't
take a would-be overlapping ``MulOneClass α`` argument but instead tears it apart and includes
only the non-overlapping parts. And it also auto-generated an instance ``Monoid.toMulOneClass``
which is *not* a field but has the expected signature which, from the end-user point of view,
restores the symmetry between the two extended classes ``Semigroup`` and ``MulOneClass``.
BOTH: -/

-- QUOTE:
#check Monoid.toSemigroup
#check Monoid.toMulOneClass
-- QUOTE.

/- TEXT:
We are now very close to defining groups. We could add to the monoid structure a field asserting
the existence of an inverse for every element. But then we would need to work to access these
inverses. In practice it is more convenient to add it as data. To optimize reusability,
we define a new data-carrying class, and then give it some notation.
BOTH: -/

-- QUOTE:
class Group (G : Type) extends Monoid G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1
-- QUOTE.

/- TEXT:
The above definition may seem too weak, we only ask that ``a⁻¹`` is a left-inverse of ``a``.
But the other side is automatic. In order to prove that, we need a preliminary lemma.
BOTH: -/

-- QUOTE:
lemma left_inv_eq_right_inv {M : Type} [Monoid M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← MulOneClass.one_mul c, ← hba, Semigroup.mul_assoc, hac, MulOneClass.mul_one b]
-- QUOTE.

/- TEXT:
In this lemma, it is pretty annoying to give full names, especially since it requires knowing
which part of the hierarchy provides those facts. One way to fix this is to use the ``export``
command to copy those facts as lemmas in the root name space.
BOTH: -/

-- QUOTE:
export MulOneClass (one_mul mul_one)
export Semigroup (mul_assoc)
export Group (inv_mul)
-- QUOTE.

/- TEXT:
We can then rewrite the above proof as:
BOTH: -/

-- QUOTE:
example {M : Type} [Monoid M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]
-- QUOTE.

/- TEXT:
It is now your turn to prove things about our algebraic structures.
BOTH: -/

-- QUOTE:
lemma inv_eq_of_mul {G : Type} [Group G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  left_inv_eq_right_inv (inv_mul a) h
-- BOTH:
-- QUOTE.


/- TEXT:
At this stage we would like to move on to define rings, but there is a serious issue.
A ring structure on a type contains both an additive group structure and a multiplicative
monoid structure, and some properties about their interaction. But so far we hard-coded
a notation ``*`` for all our operations. More fundamentally, the type class system
assumes every type has only one instance of each type class. There are various
ways to solve this issue. Surprisingly Mathlib uses the naive idea to duplicate
everything for additive and multiplicative theories with the help of some code-generating
attribute. Structures and classes are defined in both additive and multiplicative notation
with an attribute ``to_additive`` linking them. In case of multiple inheritance like for
semi-groups, the auto-generated "symmetry-restoring" instances need also to be marked.
This is a bit technical you don't need to understand details. The important point is that
lemmas are then only stated in multiplicative notation and marked with the attribute ``to_additive``
to generate the additive version as ``left_inv_eq_right_inv'`` with it's auto-generated additive
version ``left_neg_eq_right_neg'``. In order to check the name of this additive version we
used the ``whatsnew in`` command on top of ``left_inv_eq_right_inv'``.
BOTH: -/

-- QUOTE:

class Zero (α : Type) where
  /-- The element zero -/
  zero : α

attribute [to_additive] One

instance Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

attribute [to_additive existing Zero.toOfNat0] One.toOfNat1

class AddSemigroup (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)

attribute [to_additive] Semigroup

class AddZeroClass (α : Type) extends Zero α, Add α where
  /-- Zero is a left neutral element for addition. -/
  zero_add : ∀ a : α, (0 : α) + a = a
  /-- Zero is a right neutral element for addition -/
  add_zero : ∀ a : α, a + (0 : α) = a

attribute [to_additive] MulOneClass


class AddMonoid (α : Type) extends AddSemigroup α, AddZeroClass α

attribute [to_additive] Monoid

export Semigroup (mul_assoc)
export AddSemigroup (add_assoc)


attribute [to_additive existing] Monoid.toMulOneClass


#check AddMonoid.mk
whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]

#check left_neg_eq_right_neg'
-- QUOTE.

/- TEXT:
Equipped with this technology, we can easily define also commutative semigroups, monoids and
groups, and then define rings.

BOTH: -/
-- QUOTE:
class AddCommSemigroup (α : Type) extends AddSemigroup α where
  add_comm : ∀ a b : α, a + b = b + a
-- QUOTE.

@[to_additive]
class CommSemigroup (α : Type) extends Semigroup α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid (α : Type) extends AddMonoid α, AddCommSemigroup α

export CommSemigroup (mul_comm)
export AddCommSemigroup (add_comm)

@[to_additive]
class CommMonoid (α : Type) extends Monoid α, CommSemigroup α

class AddGroup (G : Type) extends AddMonoid G, Neg G where
  neg_add : ∀ a : G, -a + a = 0


attribute [to_additive] Group left_inv_eq_right_inv inv_eq_of_mul

export AddGroup (neg_add)

-- QUOTE:
@[to_additive (attr := simp)]
lemma mul_inv (G : Type) [Group G] (a : G) : a * a⁻¹ = 1 :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  by
    rw [← inv_mul a⁻¹, inv_eq_of_mul (inv_mul a)]
-- QUOTE.



/- TEXT:
We should remember to tagged lemmas with ``simp`` when appropriate.
BOTH: -/

-- QUOTE:
attribute [simp] Group.inv_mul AddGroup.neg_add
attribute [simp] MulOneClass.one_mul AddZeroClass.zero_add
attribute [simp] MulOneClass.mul_one AddZeroClass.add_zero
-- QUOTE.


@[to_additive]
lemma mul_left_cancel {G : Type} [Group G] {a b c : G} (h : a * b = a * c) : b = c := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simpa [← mul_assoc] using congr_arg (a⁻¹ * ·) h
-- BOTH:


@[to_additive]
lemma mul_right_cancel {G : Type} [Group G] {a b c : G} (h : b * a = c * a) : b = c := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simpa [mul_assoc] using congr_arg (· * a⁻¹) h
-- BOTH:

class AddCommGroup (G : Type) extends AddGroup G, AddCommMonoid G

@[to_additive]
class CommGroup (G : Type) extends Group G, CommMonoid G


/- TEXT:
We are now ready for rings. For demonstration purposes we won't assume that addition is
commutative, and then immediately provide an instance of ``AddCommGroup``. Mathlib does not
play this game, first because in practice this does not make any ring instance easier and
also because Mathlib's algebraic hierarchy goes through semi-rings which are like rings but without
opposites so that the proof below does not work for them. What we gain here, besides a nice exercise
if you have never seen it, is an example of building an instance using the syntax that allows
to provide a parent structure and some extra fields.
BOTH: -/


/-- Typeclass for expressing that a type `α` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : α`. -/
class MulZeroClass (α : Type) extends Mul α, Zero α where
  /-- Zero is a left absorbing element for multiplication -/
  zero_mul : ∀ a : α, (0 : α) * a = 0
  /-- Zero is a right absorbing element for multiplication -/
  mul_zero : ∀ a : α, a * (0 : α) = 0


-- QUOTE:
class Ring (R : Type) extends AddGroup R, Monoid R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring R] : AddCommGroup R :=
{ Ring.toAddGroup with
  add_comm := by
/- EXAMPLES:
    sorry }
SOLUTIONS: -/
    intro a b
    have : a + (a + b + b) = a + (b + a + b) := calc
      a + (a + b + b) = (a + a) + (b + b) := by rw [add_assoc, add_assoc]
      _ = (1 * a + 1 * a) + (1 * b + 1 * b) := by simp
      _ = (1 + 1) * a + (1 + 1) * b := by simp [Ring.right_distrib]
      _ = (1 + 1) * (a + b) := by simp [Ring.left_distrib]
      _ = 1 * (a + b) + 1 * (a + b) := by simp [Ring.right_distrib]
      _ = (a + b) + (a + b) := by simp
      _ = a + (b + a + b) := by simp [add_assoc]
    exact add_right_cancel (add_left_cancel this) }
-- QUOTE.
/- TEXT:
Of course we can also build concrete instances, such as a ring structure on integers (of course
the instance below uses that all the work is already done in Mathlib).
BOTH: -/

-- QUOTE:
instance : Ring ℤ where
  add := (· + ·)
  add_assoc := _root_.add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc := _root_.mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
-- QUOTE.

/- TEXT:

We now want to discuss algebraic structures involving several types. The prime example
is modules over rings. If you don't know what is a module, you can pretend it means vector space
and think that all our rings are fields. Those structures are commutative additive groups
equipped with a scalar multiplication by elements of some ring.

We first define the data-carrying type class of scalar multiplication by some type ``α`` on some
type ``β``, and give it a right associative notation.
BOTH: -/

-- QUOTE:
class SMul (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul.smul
-- QUOTE.

/- TEXT:
Then we can define modules (again think about vector spaces if you don't know what is a module).
BOTH: -/

-- QUOTE:
class Module (R : Type) [Ring R] (M : Type) [AddCommGroup M] extends SMul R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n
-- QUOTE.

/- TEXT:
There is something interesting going on here. While it isn't too surprising that the
ring structure on ``R`` is a parameter in this definition, you probably expected ``AddCommGroup M``
to be part of the ``extends`` clause just as ``SMul R M`` is.  Trying to do that would lead
to a mysterious sounding error message:
``cannot find synthesization order for instance odule.toAddCommGroup₃ with type (R : Type) → [inst : Ring R] → {M : Type} → [self : Module R M] → AddCommGroup₃ M
all remaining arguments have metavariables: Ring ?R @Module₁ ?R ?inst✝ M``.
In order to understand this message, you need to remember that such an ``extends`` clause would
lead to a field ``Module.toAddCommGroup₃`` marked as an instance. This instance
would have the signature appearing in the error message:
``(R : Type) → [inst : Ring R] → {M : Type} → [self : Module R M] → AddCommGroup M``.
With such an instance in the type class database, each time Lean would look for a
``AddCommGroup M`` instance for some ``M``, it would need to go hunting for a completely
unspecified type ``R`` and a ``Ring R`` instance before embarking on the main quest of finding a
``Module R M`` instance. Those two side-quests are represented by the meta-variables mentioned in
the error message and denoted by ``?R`` and ``?inst✝`` there. Such a ``Module.toAddCommGroup``
instance would then be a huge trap for the instance resolution procedure and then ``class`` command
refuses to set it up.

What about ``extends SMul R M`` then? That one creates a field
``Module.toSMul : {R : Type} →  [inst : Ring R] → {M : Type} → [inst_1 : AddCommGroup M] → [self : Module R M] → SMul R M``
whose end result ``SMul R M`` mentions both ``R`` and ``M`` so this field can
safely be used as an instance. The rule is easy to remember: each class appearing in the
``extends`` clause should mention every type appearing in the parameters.

Let us create our first module instance: a ring is a module over itself using its multiplication
as a scalar multiplication.
BOTH: -/
-- QUOTE:
instance selfModule (R : Type) [Ring R] : Module R R where
  smul := fun r s ↦ r * s
  zero_smul := Ring.zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc
  add_smul := Ring.right_distrib
  smul_add := Ring.left_distrib
-- QUOTE.
/- TEXT:
As a second example, every abelian group is a module over ``ℤ`` (this is one of the reason to
generalize the theory of vector spaces by allowing non-invertible scalars). First one can define
scalar multiplication by a natural number for any type equipped with a zero and an addition:
``n • a`` is defined as ``a + ⋯ + a`` where ``a`` appears ``n`` times. Then this is extended
to scalar multiplication by an integer by ensuring ``(-1) • a = -a``.
BOTH: -/
-- QUOTE:

def nsmul {M  : Type} [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul n a

def zsmul {M : Type} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul n a
  | Int.negSucc n, a => -nsmul n.succ a

-- QUOTE.
/- TEXT:
Proving this gives rise to a module structure is a bit tedious and not interesting for the
current discussion, so we will sorry all axioms. You are *not* asked to replace those sorries
with proofs. If you insist on doing it then you will probably want to state and prove several
intermediate lemmas about ``nsmul₁`` and ``zsmul₁``.
BOTH: -/
-- QUOTE:

instance abGrpModule (A : Type) [AddCommGroup A] : Module ℤ A where
  smul := zsmul
  zero_smul := sorry
  one_smul := sorry
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry
-- QUOTE.
/- TEXT:
A much more important issue is that we now have two module structures over the ring ``ℤ``
for ``ℤ`` itself: ``abGrpModule ℤ`` since ``ℤ`` is a abelian group, and ``selfModule ℤ`` since
``ℤ`` is a ring. Those two module structure correspond to the same abelian group structure,
but it is not obvious that they have the same scalar multiplication. They actually do, but
this isn't true by definition, it requires a proof. This is very bad news for the type class
instance resolution procedure and will lead to very frustrating failures for users of this
hierarchy. When directly asked to find an instance, Lean will pick one, and we can see
which one using:
BOTH: -/
-- QUOTE:

#synth Module ℤ ℤ -- abGrpModule ℤ

-- QUOTE.
/- TEXT:
But in a more indirect context it can happen that Lean infers the one and then gets confused.
This situation is known as a bad diamond. This refers to the way one can draw the paths from ``ℤ``
to its ``Module ℤ`` going through either ``AddCommGroup ℤ`` or ``Ring ℤ``.

It is important to understand that not all diamonds are bad. In fact there are diamonds everywhere
in Mathlib, and also in this chapter. Already at the very beginning we saw one can go
from ``Monoid α`` to ``Mul α`` through either ``Semigroup α`` or ``MulOneClass α`` and
thanks to the work done by the ``class`` command, the resulting two ``Mul α`` instances
are definitionally equal. In particular a diamond having a ``Prop``-valued class at the bottom
cannot be bad since any too proofs of the same statement are definitionally equal.

But the diamond we created with modules is definitely bad. The offending piece is the ``smul``
field which is data, not a proof, and we have two constructions that are not definitionally equal.
The robust way of fixing this issue is to make sure that going from a rich structure to a
poor structure is always done by forgetting data, not by defining data. This well-known pattern
as been named "forgetful inheritance" and extensively discussed in
https://inria.hal.science/hal-02463336.

In our concrete case, we can modify the definition of ``AddMonoid`` to include a ``nsmul`` data
field and some ``Prop``-valued fields ensuring this operation is provably the one we constructed
above. Those fields are given default values using ``:=`` after their type in the definition below.
Thanks to these default values, most instances would be constructed exactly as with our previous
definitions. But in the special case of ``ℤ`` we will be able to provide specific values.
BOTH: -/
-- QUOTE:

class AddMonoid' (M : Type) extends AddSemigroup M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid' M] : SMul ℕ M := ⟨AddMonoid'.nsmul⟩
-- QUOTE.
/- TEXT:

Let us check we can still construct a product monoid instance without providing the ``nsmul``
related fields.
BOTH: -/
-- QUOTE:

instance (M N : Type) [AddMonoid' M] [AddMonoid' N] : AddMonoid' (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc := fun a b c ↦ by ext <;> apply add_assoc
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply AddZeroClass.zero_add
  add_zero := fun a ↦ by ext <;> apply AddZeroClass.add_zero
-- QUOTE.
/- TEXT:
And now let us handle the special case of ``ℤ`` where we want to build ``nsmul`` using the coercion
of ``ℕ`` to ``ℤ`` and the multiplication on ``ℤ``. Note in particular how the proof fields
contain more work than in the default value above.
BOTH: -/
-- QUOTE:

instance : AddMonoid' ℤ where
  add := (· + ·)
  add_assoc := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]
-- QUOTE.
/- TEXT:
Let us check we solved our issue. Because Lean already has a definition of scalar multiplication
of a natural number and an integer, and we want to make sure our instance is used, we won't use
the ``•`` notation but call ``SMul.mul`` and explicitly provide our instance defined above.
BOTH: -/
-- QUOTE:

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
-- QUOTE.
/- TEXT:
This story then continues with incorporating a ``zsmul`` field into the definition of groups
and similar tricks. You are now ready to read the definition of monoids, groups, rings and modules
in Mathlib. There are more complicated than what we have seen here, because they are part of a huge
hierarchy, but all principles have been explained above.
-/


/- TEXT:

Morphisms
---------

So far in this chapter, we discussed how to create a hierarchy of mathematical structures.
But defining structures is not really completed until we have morphisms. There are two
main approaches here. The most obvious one is to define a predicate on functions.
BOTH: -/

-- QUOTE:
def isMonoidHomBad {G H : Type} [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'
-- QUOTE.
/- TEXT:
In this definition, it is a bit unpleasant to use a conjunction. In particular users
will need to remember the ordering we chose when they want to access the two conditions.
So we could use a structure instead.

BOTH: -/
-- QUOTE:
structure isMonoidHomBad' {G H : Type} [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'
-- QUOTE.
/- TEXT:
Once we are here, it is even tempting to make it a class and use the type class instance resolution
procedure to automatically infer ``isMonoidHom₂`` for complicated functions out of instances for
simpler functions. For instance a composition of monoid morphisms is a monoid morphism and this
seems like a useful instance. However such an instance would be very tricky for the resolution
procedure since it would need to hunt down ``g ∘ f`` everywhere. Seeing it failing in ``g (f x)``
would be very frustrating. More generally one must always keep in mind that recognizing which
function is applied in a given expression is a very difficult problem, called the "higher-order
unification problem". So Mathlib does not use this class approach.

A more fundamental question is whether we use predicates as above (using either a ``def`` or a
``structure``) or use structures bundling a function and predicates. This is partly a psychological
issue. It is extremely rare to consider a function between monoids that is not a morphism.
It really feels like "monoid morphism" is not an adjective you can assign to a bare function,
it is a noun. On the other hand one can argue that a continuous function between topological spaces
is really a function that happens to be continuous.

BOTH: -/

-- QUOTE:
@[ext]
structure MonoidHom (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'

-- QUOTE.
/- TEXT:
Of course we don't want to type ``toFun`` everywhere so we register a coercion using
the ``CoeFun`` type class. Its first argument is the type we want to coerce to a function.
The second argument describes the target function type. In our case it is always ``G → H``
for every ``f : MonoidHom₁ G H``. We also tag ``MonoidHom₁.toFun`` with the ``coe`` attribute to
make sure it is displayed almost invisibly in the tactic state, simply by a ``↑`` prefix.

BOTH: -/
-- QUOTE:
instance {G H : Type} [Monoid G] [Monoid H] : CoeFun (MonoidHom G H) (fun _ ↦ G → H) where
  coe := MonoidHom.toFun

attribute [coe] MonoidHom.toFun
-- QUOTE.

/- TEXT:
Let us check we can indeed apply a bundled monoid morphism to an element.

BOTH: -/

-- QUOTE:
example {G H : Type} [Monoid G] [Monoid H] (f : MonoidHom G H) : f 1 = 1 :=  f.map_one
-- QUOTE.
/- TEXT:
We can do the same with other kind of morphisms until we reach ring morphisms.

BOTH: -/

-- QUOTE:
@[ext]
structure AddMonoidHom (G H : Type) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance (G H : Type) [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom.toFun

attribute [coe] AddMonoidHom.toFun

@[ext]
structure RingHom (R S : Type) [Ring R] [Ring S] extends MonoidHom R S, AddMonoidHom R S

-- QUOTE.

/- TEXT:
There are a couple of issues about this approach. A minor one is we don't quite know where to put
the ``coe`` attribute since the ``RingHom.toFun`` does not exist, the relevant function is
``MonoidHom.toFun ∘ RingHom.toMonoidHom₁`` which is not a declaration that can be tagged with an
attribute (but we could still define a ``CoeFun  (RingHom R S) (fun _ ↦ R → S)`` instance).
A much more important one is that lemmas about monoid morphisms won't directly apply
to ring morphisms. This leaves the alternative of either juggling with ``RingHom.toMonoidHom``
each time we want to apply a monoid morphism lemma or restate every such lemmas for ring morphisms.
Neither option is appealing so Mathlib uses a new hierarchy trick here. The idea is to define
a type class for objects that are at least monoid morphisms, instantiate that class with both monoid
morphisms and ring morphisms and use it to state every lemma. In the definition below,
``F`` could be ``MonoidHom M N``, or ``RingHom₁ M N`` if ``M`` and ``N`` have a ring structure.

BOTH: -/

-- QUOTE:
class MonoidHomClass' (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'
-- QUOTE.

/- TEXT:
However there is a problem with the above implementation. We haven't registered a coercion to
function instance yet. Let us try to do it now.

BOTH: -/

-- QUOTE:
def badInst (M N F : Type) [Monoid M] [Monoid N] [MonoidHomClass' F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass'.toFun
-- QUOTE.

/- TEXT:
Making the an instance would be bad. When faced with something like ``f x`` where the type of ``f``
is not a function type, Lean will try to find a ``CoeFun`` instance to coerce ``f`` into a function.
The above function has type:
``{M N F : Type} → [Monoid M] → [Monoid N] → [MonoidHomClass' F M N] → CoeFun F (fun x ↦ M → N)``
so, when it trying to apply it, it wouldn't be a priori clear to Lean in which order the unknown
types ``M``, ``N`` and ``F`` should be inferred. This is a kind of bad instance that is slightly
different from the one we saw already, but it boils down to the same issue: without knowing ``M``,
Lean would have to search for a monoid instance on an unknown type, hence hopelessly try *every*
monoid instance in the database. If you are curious to see the effect of such an instance you
can type ``set_option synthInstance.checkSynthOrder false in`` on top of the above declaration,
replace ``def badInst`` with ``instance``, and look for random failures in this file.

Here the solution is easy, we need to tell Lean to first search what is ``F`` and then deduce ``M``
and ``N``. This is done using the ``outParam`` function. This function is defined as the identity
function, but is still recognized by the type class machinery and triggers the desired behavior.
Hence we can retry defining our class, paying attention to the ``outParam`` function:
BOTH: -/

-- QUOTE:
class MonoidHomClass'' (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance (M N F : Type) [Monoid M] [Monoid N] [MonoidHomClass'' F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass''.toFun

attribute [coe] MonoidHomClass''.toFun
-- QUOTE.

/- TEXT:
Now we can proceed with our plan to instantiate this class.

BOTH: -/

-- QUOTE:
instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass'' (MonoidHom M N) M N where
  toFun := MonoidHom.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass'' (RingHom R S) R S where
  toFun := fun f ↦ f.toMonoidHom.toFun
  map_one := fun f ↦ f.toMonoidHom.map_one
  map_mul := fun f ↦ f.toMonoidHom.map_mul
-- QUOTE.

/- TEXT:
As promised every lemma we prove about ``f : F`` assuming an instance of ``MonoidHomClass'' F`` will
apply both to monoid morphisms and ring morphisms.
Let us see an example lemma and check it applies to both situations.
BOTH: -/

-- QUOTE:
lemma map_inv_of_inv {M N F : Type} [Monoid M] [Monoid N] [MonoidHomClass'' F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass''.map_mul, h, MonoidHomClass''.map_one]

example (M N : Type) [Monoid M] [Monoid N] (f : MonoidHom M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map_inv_of_inv f h

example (R S : Type)  [Ring R] [Ring S] (f : RingHom R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map_inv_of_inv f h

-- QUOTE.

/- TEXT:
At first sight, it may look like we got back to our old bad idea of making ``MonoidHom`` a class.
But we haven't. Everything is shifted one level of abstraction up. The type class resolution
procedure won't be looking for functions, it will be looking for either
``MonoidHom`` or ``RingHom``.

One remaining issue with our approach is the presence of repetitive code around the ``toFun``
field and the corresponding ``CoeFun`` instance and ``coe`` attribute. It would also be better
to record that this pattern is used only for function with extra properties, meaning that the
coercion to functions should be injective. So Mathlib adds one more layer of abstraction with
the base class ``FunLike``. Let us redefine our ``MonoidHomClass`` on top of this base layer.

BOTH: -/

-- QUOTE:
class MonoidHomClass (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    FunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass (MonoidHom M N) M N where
  coe := MonoidHom.toFun
  coe_injective' := MonoidHom.ext
  map_one := MonoidHom.map_one
  map_mul := MonoidHom.map_mul
-- QUOTE.

/- TEXT:
Of course the hierarchy of morphisms does not stop here. We could go on and define a class
``RingHomClass`` extending ``MonoidHomClass`` and instantiate it on ``RingHom`` and
then later on ``AlgebraHom`` (algebras are rings with some extra structure). But we've
covered the main formalization ideas used in Mathlib for morphisms and you should be ready
to understand how morphisms are defined in Mathlib.
BOTH: -/

/- TEXT:

Sub-objects
-----------

After defining some algebraic structure and its morphisms, the next step is to consider sets
that inherit this algebraic structure, for instance subgroups or subrings.
This largely overlaps our previous topic. Indeed a set in ``X`` is implemented as a function from
``X`` to ``Prop`` so sub-objects are function satisfying a certain predicate.
Hence we can reuse of lot of the ideas that led to the ``FunLike`` class and its descendants.
We won't reuse ``FunLike`` itself because this would break the abstraction barrier from ``Set X``
to ``X → Prop``. Instead there is a ``SetLike`` class. Instead of wrapping an injection into a
function type, that class wraps an injection into a ``Set`` type and defines the corresponding
coercion and ``Membership`` instance.

BOTH: -/

-- QUOTE:
@[ext]
structure Submonoid (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance (M : Type) [Monoid M] : SetLike (Submonoid M) M where
  coe := Submonoid.carrier
  coe_injective' := Submonoid.ext

-- QUOTE.

/- TEXT:
Equipped with the above ``SetLike`` instance, we can already state naturally that
a submonoid ``N`` contains ``1`` without using ``N.carrier``.
We can also silently treat ``N`` as a set in ``M`` as take its direct image under a map.
BOTH: -/

-- QUOTE:
example (M : Type) [Monoid M] (N : Submonoid M) : 1 ∈ N := N.one_mem

example (M : Type) [Monoid M] (N : Submonoid M) (α : Type) (f : M → α) := f '' N
-- QUOTE.

/- TEXT:
We also have a coercion to ``Type`` which uses ``Subtype`` so, given a submonoid ``N`` we can write
a parameter ``(x : N)`` which can be coerced to an element of ``M`` belonging to ``N``.

BOTH: -/

-- QUOTE:
example (M : Type) [Monoid M] (N : Submonoid M) (x : N) : (x : M) ∈ N := x.property
-- QUOTE.

/- TEXT:
Using this coercion to ``Type`` we can also tackle the task of equipping a submonoid with a
monoid structure. We will use the coercion from the type associated to ``N`` as above, and the
lemma ``SetCoe.ext`` asserting this coercion is injective. Both are provided by the ``SetLike``
instance.

BOTH: -/

-- QUOTE:
instance SubMonoidMonoid {M : Type} [Monoid M] (N : Submonoid M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))
-- QUOTE.

/- TEXT:

In order to apply lemmas about submonoids to subgroups or subrings, we need a class, just
like for morphisms. Note this class take a ``SetLike`` instance as a parameter so it does not need
a carrier field and can use the membership notation in its fields.
BOTH: -/

-- QUOTE:
class SubmonoidClass (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance (M: Type) [Monoid M] : SubmonoidClass (Submonoid M) M where
  mul_mem := Submonoid.mul_mem
  one_mem := Submonoid.one_mem
-- QUOTE.

/- TEXT:

As an exercise you should define a ``Subgroup`` structure, endow it with a ``SetLike`` instance
and a ``SubmonoidClass`` instance, put a ``Group`` instance on the subtype associated to a
``Subgroup`` and define a ``SubgroupClass`` class.

SOLUTIONS: -/
@[ext]
structure Subgroup (G : Type) [Group G] extends Submonoid G where
  /-- The inverse of an element of a subgroup belongs to the subgroup. -/
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier


/-- Subgroups in `M` can be seen as sets in `M`. -/
instance (G : Type) [Group G] : SetLike (Subgroup G) G where
  coe := fun H ↦ H.toSubmonoid.carrier
  coe_injective' := Subgroup.ext

instance (G : Type) [Group G] (H : Subgroup G) : Group H :=
{ SubMonoidMonoid H.toSubmonoid with
  inv := fun x ↦ ⟨x⁻¹, H.inv_mem x.property⟩
  inv_mul := fun x ↦ SetCoe.ext (inv_mul (x : G))
  }

class SubgroupClass (S : Type) (G : Type) [Group G] [SetLike S G]
    extends SubmonoidClass S G  : Prop where
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance (G : Type) [Group G] : SubmonoidClass (Subgroup G) G where
  mul_mem := fun H ↦ H.toSubmonoid.mul_mem
  one_mem := fun H ↦ H.toSubmonoid.one_mem

instance (G : Type) [Group G] : SubgroupClass (Subgroup G) G :=
{ (inferInstance : SubmonoidClass (Subgroup G) G) with
  inv_mem := Subgroup.inv_mem }

/- TEXT:
Another very important thing to know about subobjects of a given algebraic object in Mathlib
always form a complete lattice, and this structure is used a lot. For instance you may look for
the lemma saying that an intersection of submonoids is a submonoid. But this won't be a lemma,
this will be an infimum construction. Let us do the case of two submonoids.

BOTH: -/

-- QUOTE:
instance (M : Type) [Monoid M] : Inf (Submonoid M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩
-- QUOTE.

/- TEXT:
This allows to get the intersections of two submonoids as a submonoid.

BOTH: -/

-- QUOTE:
example (M : Type) [Monoid M] (N P : Submonoid M) : Submonoid M := N ⊓ P
-- QUOTE.

/- TEXT:
You may think it's a shame that we had to use the inf symbol ``⊓`` in the above example instead
of the intersection symbol ``∩``. But think about the supremum. The union of two submonoids is not
a submonoid. However submonoids still form a lattice (even a complete one). Actually ``N ⊔ P`` is
the submonoid generated by the union of ``N`` and ``P`` and of course it would be very confusing to
denote it by ``N ∪ P``. So you can see the use of ``N ⊓ P`` as much more consistent. It is also
a lot more consistent across various kind of algebraic structures. It may look a bit weird at first
to see the sum of two vector subspace ``E`` and ``F`` denoted by ``E ⊔ F`` instead of ``E + F``.
But you will get used to it. And soon you will consider the ``E + F`` notation as a distraction
emphasizing the anecdotal fact that elements of ``E ⊔ F`` can be written as a sum of an element of
``E`` and an element of ``F`` instead of emphasizing the fundamental fact that ``E ⊔ F`` is the
smallest vector subspace containing both ``E`` and ``F``.

Our last topic for this chapter is that of quotients. Again we want to explain how
convenient notation are built and code duplication is avoided in Mathlib. Here the main device
is the ``HasQuotient`` class which allows notations like ``M ⧸ N``. Beware the quotient symbol
``⧸`` is a special unicode character, not a regular ASCII division symbol.

As an example, we will build the quotient of a commutative monoid by a submonoid, leave proofs
to you. In the last example, you can use ``Setoid.refl`` but it won't automatically pick up
the relevant ``Setoid`` structure. You can fix this issue by providing all arguments using
the ``@`` syntax, as in ``@Setoid.refl M N.Setoid``.

BOTH: -/

-- QUOTE:
def Submonoid.Setoid {M : Type} [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
      rintro a b c ⟨w, hw, z, hz, h⟩ ⟨w', hw', z', hz', h'⟩
      refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩
      rw [← mul_assoc, h, CommSemigroup.mul_comm b, mul_assoc, h', ← mul_assoc, CommSemigroup.mul_comm z, mul_assoc]
-- BOTH:
  }

instance (M : Type) [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk {M : Type} [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance (M : Type) [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro a₁ b₁ ⟨w, hw, z, hz, ha⟩ a₂ b₂ ⟨w', hw', z', hz', hb⟩
    refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩
    rw [mul_comm w, ← mul_assoc, mul_assoc a₁, hb, mul_comm, ← mul_assoc, mul_comm w, ha,
        mul_assoc, mul_comm z, mul_assoc b₂, mul_comm z', mul_assoc]
-- BOTH:
        )
  mul_assoc := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    apply Quotient.sound
    dsimp only
    rw [mul_assoc]
    apply @Setoid.refl M N.Setoid
-- BOTH:
  one := QuotientMonoid.mk N 1
  one_mul := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro ⟨a⟩ ; apply Quotient.sound ; dsimp only ; rw [one_mul] ; apply @Setoid.refl M N.Setoid
-- BOTH:
  mul_one := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro ⟨a⟩ ; apply Quotient.sound ; dsimp only ; rw [mul_one] ; apply @Setoid.refl M N.Setoid
-- QUOTE.
end lftcm2023
