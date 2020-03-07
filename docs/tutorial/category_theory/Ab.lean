/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group
import category_theory.limits.shapes.kernels

open category_theory
open category_theory.limits

local notation `Ab` := Ab.{0}

/-!
Some small examples of using limits and colimits in `Ab`, the category of additive commutative groups.
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
