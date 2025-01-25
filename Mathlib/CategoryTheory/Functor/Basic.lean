/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Combinatorics.Quiver.Prefunctor

/-!
# Functors

Defines a functor between categories, extending a `Prefunctor` between quivers.

Introduces, in the `CategoryTheory` scope, notations `C ⥤ D` for the type of all functors
from `C` to `D`, `𝟭` for the identity functor and `⋙` for functor composition.

TODO: Switch to using the `⇒` arrow.
-/


namespace CategoryTheory

-- declare the `v`'s first; see note [CategoryTheory universes].
universe v v₁ v₂ v₃ u u₁ u₂ u₃

section

/-- `Functor C D` represents a functor between categories `C` and `D`.

To apply a functor `F` to an object use `F.obj X`, and to a morphism use `F.map f`.

The axiom `map_id` expresses preservation of identities, and
`map_comp` expresses functoriality. -/
@[stacks 001B]
structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    extends Prefunctor C D : Type max v₁ v₂ u₁ u₂ where
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) := by aesop_cat
  /-- A functor preserves composition. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g := by aesop_cat

/-- The prefunctor between the underlying quivers. -/
add_decl_doc Functor.toPrefunctor

end

/-- Notation for a functor between categories. -/
-- A functor is basically a function, so give ⥤ a similar precedence to → (25).
-- For example, `C × D ⥤ E` should parse as `(C × D) ⥤ E` not `C × (D ⥤ E)`.
scoped [CategoryTheory] infixr:26 " ⥤ " => Functor -- type as \func

attribute [simp] Functor.map_id Functor.map_comp

-- Note: We manually add this lemma which could be generated by `reassoc`,
-- since we will import this file into `Mathlib/Tactic/Reassoc.lean`.
lemma Functor.map_comp_assoc {C : Type u₁} [Category C] {D : Type u₂} [Category D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) {W : D} (h : F.obj Z ⟶ W) :
    (F.map (f ≫ g)) ≫ h = F.map f ≫ F.map g ≫ h := by
  rw [F.map_comp, Category.assoc]

namespace Functor

section

variable (C : Type u₁) [Category.{v₁} C]

initialize_simps_projections Functor

-- We don't use `@[simps]` here because we want `C` implicit for the simp lemmas.
/-- `𝟭 C` is the identity functor on a category `C`. -/
protected def id : C ⥤ C where
  obj X := X
  map f := f

/-- Notation for the identity functor on a category. -/
scoped [CategoryTheory] notation "𝟭" => Functor.id -- Type this as `\sb1`

instance : Inhabited (C ⥤ C) :=
  ⟨Functor.id C⟩

variable {C}

@[simp]
theorem id_obj (X : C) : (𝟭 C).obj X = X := rfl

@[simp]
theorem id_map {X Y : C} (f : X ⟶ Y) : (𝟭 C).map f = f := rfl

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- `F ⋙ G` is the composition of a functor `F` and a functor `G` (`F` first, then `G`).
-/
@[simps obj]
def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
  map_comp := by intros; dsimp; rw [F.map_comp, G.map_comp]

/-- Notation for composition of functors. -/
scoped [CategoryTheory] infixr:80 " ⋙ " => Functor.comp

@[simp]
theorem comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := rfl

-- These are not simp lemmas because rewriting along equalities between functors
-- is not necessarily a good idea.
-- Natural isomorphisms are also provided in `Whiskering.lean`.
protected theorem comp_id (F : C ⥤ D) : F ⋙ 𝟭 D = F := by cases F; rfl

protected theorem id_comp (F : C ⥤ D) : 𝟭 C ⋙ F = F := by cases F; rfl

@[simp]
theorem map_dite (F : C ⥤ D) {X Y : C} {P : Prop} [Decidable P]
    (f : P → (X ⟶ Y)) (g : ¬P → (X ⟶ Y)) :
    F.map (if h : P then f h else g h) = if h : P then F.map (f h) else F.map (g h) := by
  aesop_cat

@[simp]
theorem toPrefunctor_comp (F : C ⥤ D) (G : D ⥤ E) :
    F.toPrefunctor.comp G.toPrefunctor = (F ⋙ G).toPrefunctor := rfl

end

end Functor

end CategoryTheory
