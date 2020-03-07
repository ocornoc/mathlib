/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group
import category_theory.limits.shapes.kernels

open category_theory
open category_theory.limits

/-!
# Basic setup of the category of abelian groups

We demonstrate using the objects of `Ab`, which are bundled `add_comm_group`,
and the morphisms, which are `add_monoid_hom` (aka `→+`).
-/

-- We decide to work in `Type 0`,
-- so we can work with concrete examples like `ℤ`, without using `ulift`.
local notation `Ab` := Ab.{0}

-- An object of `Ab` is a bundled `add_comm_group`.
-- If an appropriate instance is available, we can use `AddCommGroup.of` to lift
-- a type to a bundled object.
def Z : Ab := AddCommGroup.of ℤ
def Q : Ab := AddCommGroup.of ℚ

-- There's a coercion back from `Ab` to `Type`,
-- so we can just use objects in `Ab` as if they were the underlying type.
example : Q := (1/3 : ℚ)
-- (Note in the next line we're using the usual function arrow,
-- not the category theory morphism arrow ⟶)
example : Z → Q := λ i, (int.cast i : ℚ)

-- Morphisms are `Ab` are just bundled morphisms, i.e. `add_monoid_hom`:
example : (Z →+ Q) = (Z ⟶ Q) := rfl
example : (Z ⟶ Q) :=
{ to_fun := λ i, (int.cast i : ℚ),
  map_zero' := rfl,
  map_add' := int.cast_add, }
-- This means we can use lemmas about `add_monoid_hom` when we need to:
example (f : Z ⟶ Q) (z₁ z₂ : Z) : f (z₁ + z₂) = f z₁ + f z₂ := by rw add_monoid_hom.map_add


/-!
# Limits and colimits in `Ab`
-/

example (G H : Ab) (f : G ⟶ H) : Ab := kernel f

example (G H : Ab) (f : G ⟶ H) [epi f] : kernel (cokernel.π f) ≅ H := as_iso (kernel.ι (cokernel.π f))

-- Since `Ab` has equalizers, we automatically get the fact that
-- in the factorization of `f` as `G --(factor_thru_image f)--> image f --(image.ι f)--> H`,
-- the morphism `factor_thru_image` is epic.
example (G H : Ab) (f : G ⟶ H) : epi (factor_thru_image f) := by apply_instance

-- Using this, we can build the map which is an isomorphism iff `G --f--> H --g--> K` is exact:
noncomputable example {G H K : Ab} (f : G ⟶ H) (g : H ⟶ K) (w : f ≫ g = 0) : image f ⟶ kernel g :=
kernel.lift g (image.ι f)
begin
  apply (cancel_epi (factor_thru_image f)).1,
  simp [w],
end
