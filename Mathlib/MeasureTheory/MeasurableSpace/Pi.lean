/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.PiSystem

/-!
# Bases of the indexed product σ-algebra

In this file we prove several versions of the following lemma:

given a finite indexed collection of measurable spaces `α i`,
if the σ-algebra on each `α i` is generated by `C i`,
then the sets `{x | ∀ i, x i ∈ s i}`, where `s i ∈ C i`,
generate the σ-algebra on the indexed product of `α i`s.
-/

noncomputable section

open Function Set Filter MeasurableSpace Encodable

variable {ι : Type*} {α : ι → Type*}

/-! We start with some measurability properties -/

lemma MeasurableSpace.pi_eq_generateFrom_projections {mα : ∀ i, MeasurableSpace (α i)} :
    pi = generateFrom {B | ∃ (i : ι) (A : Set (α i)), MeasurableSet A ∧ eval i ⁻¹' A = B} := by
  simp only [pi, ← generateFrom_iUnion_measurableSet, iUnion_setOf, measurableSet_comap]

/-- Boxes formed by π-systems form a π-system. -/
theorem IsPiSystem.pi {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsPiSystem (C i)) :
    IsPiSystem (pi univ '' pi univ C) := by
  rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩ hst
  rw [← pi_inter_distrib] at hst ⊢; rw [univ_pi_nonempty_iff] at hst
  exact mem_image_of_mem _ fun i _ => hC i _ (hs₁ i (mem_univ i)) _ (hs₂ i (mem_univ i)) (hst i)

/-- Boxes form a π-system. -/
theorem isPiSystem_pi [∀ i, MeasurableSpace (α i)] :
    IsPiSystem (pi univ '' pi univ fun i => { s : Set (α i) | MeasurableSet s }) :=
  IsPiSystem.pi fun _ => isPiSystem_measurableSet

section Finite

variable [Finite ι]

/-- Boxes of countably spanning sets are countably spanning. -/
theorem IsCountablySpanning.pi {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsCountablySpanning (C i)) :
    IsCountablySpanning (pi univ '' pi univ C) := by
  choose s h1s h2s using hC
  cases nonempty_encodable (ι → ℕ)
  let e : ℕ → ι → ℕ := fun n => (@decode (ι → ℕ) _ n).iget
  refine ⟨fun n => Set.pi univ fun i => s i (e n i), fun n =>
    mem_image_of_mem _ fun i _ => h1s i _, ?_⟩
  simp_rw
    [e, (surjective_decode_iget (ι → ℕ)).iUnion_comp fun x => Set.pi univ fun i => s i (x i),
    iUnion_univ_pi s, h2s, pi_univ]

/-- The product of generated σ-algebras is the one generated by boxes, if both generating sets
  are countably spanning. -/
theorem generateFrom_pi_eq {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsCountablySpanning (C i)) :
    (@MeasurableSpace.pi _ _ fun i => generateFrom (C i)) =
    generateFrom (pi univ '' pi univ C) := by
  classical
  cases nonempty_encodable ι
  apply le_antisymm
  · refine iSup_le ?_; intro i; rw [comap_generateFrom]
    apply generateFrom_le; rintro _ ⟨s, hs, rfl⟩
    choose t h1t h2t using hC
    simp_rw [eval_preimage, ← h2t]
    rw [← @iUnion_const _ ℕ _ s]
    have : Set.pi univ (update (fun i' : ι => iUnion (t i')) i (⋃ _ : ℕ, s)) =
        Set.pi univ fun k => ⋃ j : ℕ,
        @update ι (fun i' => Set (α i')) _ (fun i' => t i' j) i s k := by
      ext; simp_rw [mem_univ_pi]; apply forall_congr'; intro i'
      by_cases h : i' = i
      · subst h; simp
      · rw [← Ne] at h; simp [h]
    rw [this, ← iUnion_univ_pi]
    apply MeasurableSet.iUnion
    intro n; apply measurableSet_generateFrom
    apply mem_image_of_mem; intro j _; dsimp only
    by_cases h : j = i
    · subst h; rwa [update_self]
    · rw [update_of_ne h]; apply h1t
  · apply generateFrom_le; rintro _ ⟨s, hs, rfl⟩
    rw [univ_pi_eq_iInter]; apply MeasurableSet.iInter; intro i
    apply @measurable_pi_apply _ _ (fun i => generateFrom (C i))
    exact measurableSet_generateFrom (hs i (mem_univ i))

/-- If `C` and `D` generate the σ-algebras on `α` resp. `β`, then rectangles formed by `C` and `D`
  generate the σ-algebra on `α × β`. -/
theorem generateFrom_eq_pi [h : ∀ i, MeasurableSpace (α i)] {C : ∀ i, Set (Set (α i))}
    (hC : ∀ i, generateFrom (C i) = h i) (h2C : ∀ i, IsCountablySpanning (C i)) :
    generateFrom (pi univ '' pi univ C) = MeasurableSpace.pi := by
  simp only [← funext hC, generateFrom_pi_eq h2C]

/-- The product σ-algebra is generated from boxes, i.e. `s ×ˢ t` for sets `s : set α` and
  `t : set β`. -/
theorem generateFrom_pi [∀ i, MeasurableSpace (α i)] :
    generateFrom (pi univ '' pi univ fun i => { s : Set (α i) | MeasurableSet s }) =
      MeasurableSpace.pi :=
  generateFrom_eq_pi (fun _ => generateFrom_measurableSet) fun _ =>
    isCountablySpanning_measurableSet

end Finite
