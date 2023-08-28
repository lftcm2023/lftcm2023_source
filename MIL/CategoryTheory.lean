import Mathlib.CategoryTheory.Limits.Yoneda

open CategoryTheory

/-!
# Category Theory

* Acknowledgements: I only contributed miniscule amounts to the category theory library. It's
maintained by Reid Barton, Riccardo Brasca, Johan Commelin, Markus Himmel, Bhavik Mheta, Scott Morrison,
Joël Riou, and Adam Topaz.

## Challenges

Category is generally regarded a *challenging field* to formalise for several reasons:
* We need dependent types because we don't want a plain type of morphisms: -/
  structure FlatCat  where
    Obj : Type u
    Mor : Type v
    dom : Mor → Obj
    cod : Mor → Obj
    id : Obj → Mor
    id_dom : dom (id X) = X
    id_cod : cod (id X) = X
    -- ...
  /-! but instead -/
  structure NonFlatCat where
    Obj : Type u
    Mor : Obj → Obj → Type v
    id : (X : Obj) → Mor X X
    -- ...
/-!
* Need categories to be doubly universe polymorphic!
* "Silent" reassociation and application of unit laws in proofs.
* Frequent usage of "canonical this and that" -- being *a limit* vs. being *the limit*.
* That's not even starting to touch the pain of formalising *higher* category theory.

## Overview of the Basic Notions
-/
#check @Category
#check CategoryTheory.Functor
#check _ ⟶ _  -- Type morphisms using \hom
#check _ ≫ _  -- Type composition using \gg

section

variable {C : Type} [Category C] {W X Y Z : C}

example (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (g' : W ⟶ Y) (e : f ≫ g = g') :
    f ≫ (g ≫ h) = g' ≫ h := by
  slice_lhs 1 2 =>
    rw [e]

end
