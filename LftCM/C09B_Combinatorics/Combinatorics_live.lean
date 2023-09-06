import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic
import Mathlib.Combinatorics.Pigeonhole

-- # Combinatorics

-- Combinatorics is characterised by typically having
-- very few, very simple definitions...
-- But the proofs are difficult!

#check Set
#check Set ℕ
#check Finset
#check Finset ℕ

def ExampleFinset : Finset ℕ := {5, 1, 2, 0}

#eval ExampleFinset

def SecondFinset : Finset ℕ := {3, 1}

#eval ExampleFinset ∪ SecondFinset

example : SecondFinset = {1, 3} := by
  rw [SecondFinset, Finset.pair_comm]

example {x y : ℕ} : ({x, y} : Finset ℕ) = {y, x} := by
  rw [Finset.pair_comm]

#synth Union (Finset ℕ)           -- allows me to use ∪ on Finsets
#synth Inter (Finset ℕ)           -- allows me to use ∩ on Finsets
#synth Insert ℕ (Finset ℕ)        -- allows me to use insert
#synth EmptyCollection (Finset ℕ) -- allows me to use ∅
#synth HasSubset (Finset ℕ)       -- ⊆
#synth SDiff (Finset ℕ)           -- \
#synth Singleton ℕ (Finset ℕ)     -- {x}

#check Finset.biUnion             -- bounded indexed union
variable (s : Finset ℕ) (a : ℕ)
#check s.erase a              -- erase an element
#check Finset.image
#check Finset.filter
#check Finset.range
#check (· ⁻¹' ·)

#check Fintype

variable (α : Type) [Fintype α]
#check Fintype.card α
example (α : Type) [Fintype α] (x : α) : x ∈ Finset.univ := by simp

#check Finset.sum
#check Finset.prod

open BigOperators

#eval ∑ i in ExampleFinset, i ^ 2
#eval ExampleFinset

example : ∑ i in ExampleFinset, i ^ 2 = 30 := rfl

#check Finset.prod_insert
#check Finset.sum_insert

example {s : Finset ℝ} : 0 ≤ ∑ i in s, i ^ 2 := by
  -- apply?
  refine Finset.sum_nonneg ?_
  intro i _
  nlinarith


-- ## Interactive!!

open Classical
open Finset

#check Finset.sum_const
#check Finset.sum_congr

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ (t.filter (r a ·)).card)
    (h_right : ∀ b ∈ t, (s.filter (r · b)).card = 1) :
  3 * s.card ≤ t.card :=
calc 3 * s.card = ∑ a in s, 3 := by
        simp only [sum_const, smul_eq_mul]
        rw [mul_comm]
     _ ≤ ∑ a in s, (t.filter (r a ·)).card := sum_le_sum h_left
     _ = ∑ a in s, ∑ b in t, if r a b then 1 else 0 := by
        apply Finset.sum_congr
        · rfl
        intros x _hx
        simp
     _ = ∑ b in t, ∑ a in s, if r a b then 1 else 0 := by
        rw [sum_comm]
     _ = ∑ b in t, (s.filter (r · b)).card := by simp
     _ = ∑ b in t, 1 := by
        apply Finset.sum_congr
        · rfl
        exact h_right
     _ = t.card := by simp

lemma Nat.coprime_self_add_one (n : ℕ) :
    Nat.coprime n (n + 1) := by simp

#check exists_lt_card_fiber_of_mul_lt_card_of_maps_to
example {n : ℕ} (A : Finset ℕ)
  (hA : A.card = n + 1)
  (hA' : A ⊆ Finset.range (2 * n)) :
    ∃ x y, x ∈ A ∧ y ∈ A ∧ Nat.coprime x y := by
  have hf : ∀ (a : ℕ), a ∈ A → a / 2 ∈ range n := by
    intros a ha
    simp only [mem_range]
    specialize hA' ha
    rw [mem_range] at hA'
    exact Nat.div_lt_of_lt_mul hA'
  have hn : card (range n) * 1 < card A := by
    simp
    rw [hA]
    simp
  have := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hn
  rcases this with ⟨y, hy, hy'⟩
  rw [mem_range] at hy
  rw [one_lt_card] at hy'
  simp only [mem_filter] at hy'
  rcases hy' with ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, hab⟩
  wlog hab' : a < b generalizing a b
  · apply this b hb hb' a hab.symm ha ha'
    rw [not_lt] at hab'
    exact Nat.lt_of_le_of_ne hab' hab.symm
  suffices : b = a + 1
  · use a, b, ha, hb
    rw [this]
    exact Nat.coprime_self_add_one a
  by_contra'
  have : a + 2 ≤ b
  · rw [Nat.succ_le]
    exact Nat.lt_of_le_of_ne hab' (id (Ne.symm this))
  have : (a + 2) / 2 ≤ b / 2
  · exact Nat.div_le_div_right this
  simp only [zero_lt_two, Nat.add_div_right] at this
  rw [@Nat.succ_le] at this
  rw [ha', hb'] at this
  simp only [lt_self_iff_false] at this


  -- have := Nat.mod_two_eq_zero_or_one a
  -- have := Nat.mod_add_div a 2
  -- have :


  -- use a, b, ha, hb




example {n : ℕ} (A : Finset ℕ)
  (hA : A.card = n + 1)
  (hA' : A ⊆ Finset.Ioc 0 (2 * n)) :
    ∃ x y, x ∈ A ∧ y ∈ A ∧ x ∣ y := by
  sorry
