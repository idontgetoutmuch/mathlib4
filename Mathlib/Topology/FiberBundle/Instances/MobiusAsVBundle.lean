/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/
import Mathlib.Topology.FiberBundle.Instances.GBundleDefs
import Mathlib.Topology.FiberBundle.Instances.Mobius
import Mathlib

set_option linter.style.longLine false
set_option linter.style.lambdaSyntax false
set_option linter.style.cdot false

open Bundle Topology MulAction Set

def cavbCoordChange
  (i j : atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
  (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
  EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))

noncomputable
def CylinderAsVectorBundle : VectorBundleCore ℝ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1))
                          (atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))  where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart (EuclideanSpace ℝ (Fin 1))
  mem_baseSet_at := mem_chart_source (EuclideanSpace ℝ (Fin 1))
  coordChange i j x := cavbCoordChange i j x
  coordChange_self _ _ _ _ := rfl
  continuousOn_coordChange i j := by

    let s := ((fun i ↦ i.1.source) i ∩ (fun i ↦ i.1.source) j)
    let f := fun (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) ↦ ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
    let g : EuclideanSpace ℝ (Fin 1) → (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 1)) :=
      fun y => (fun x => f x y)

    have h0 : ∀ (y : EuclideanSpace ℝ (Fin 1)), ContinuousOn (g y) s := by
      intro y
      have h1 : ContinuousOn (fun x => f x y) s := continuousOn_const
      exact h1

    have h2 : ContinuousOn f s ↔
     ∀ (y : EuclideanSpace ℝ (Fin 1)), ContinuousOn (fun x ↦ f x y) s := continuousOn_clm_apply

    have h3 : ContinuousOn ((fun x ↦ ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))))
                           ((fun i ↦ i.1.source) i ∩ (fun i ↦ i.1.source) j) := h2.mpr h0

    exact h3

  coordChange_comp i j k x hx v := rfl

noncomputable
def MyCoordChangeL : Fin 2 → Fin 2 → (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → EuclideanSpace ℝ (Fin 1) →L[ℝ]  EuclideanSpace ℝ (Fin 1)
  | 0, 0, _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
  | 0, 1, x => if (x.val 1) > 0 then ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) else -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
  | 1, 0, x => if (x.val 1) > 0 then ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) else -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
  | 1, 1, _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))

theorem MyCoordChange_selfL : ∀ (i : Fin 2),
    ∀ x ∈ (fun i => if i = 0 then U.source else V.source) i,
    ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChangeL i i x v = v := by
    intro i x h v
    have h : MyCoordChangeL i i x v = v :=
      match i with
        | 0 => rfl
        | 1 => rfl
    exact h

lemma l00 : ContinuousOn (MyCoordChangeL 0 0) U.source := by
  let f := fun (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) ↦ ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
  have h1 : (MyCoordChangeL 0 0) = f := rfl
  let g : EuclideanSpace ℝ (Fin 1) → (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 1)) :=
      fun y => (fun x => f x y)
  have h2 : ∀ (y : EuclideanSpace ℝ (Fin 1)), ContinuousOn (g y) U.source := by
      intro y
      have h1 : ContinuousOn (fun x => f x y) U.source := continuousOn_const
      exact h1
  have h3 : ContinuousOn f U.source ↔
     ∀ (y : EuclideanSpace ℝ (Fin 1)), ContinuousOn (fun x ↦ f x y) U.source := continuousOn_clm_apply

  have h4 : ContinuousOn ((fun x ↦ ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))))
                          U.source := h3.mpr h2

  exact h4

def sl1 : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := { x | 0 < x.val 1 }
def sl2 : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := { x | 0 > x.val 1 }

lemma h6 : (sl1 ∪ sl2) = (({x | x.val 1 > 0} ∪ {x | x.val 1 < 0})) := by
    ext ⟨p, v⟩
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, Set.mem_setOf_eq]
    exact Iff.rfl

lemma h_eq_on_pre : ∀ x ∈ sl1, ∀ (v : EuclideanSpace ℝ (Fin 1)), (MyCoordChangeL 0 1 x) v = v := by
    intro x hx v
    have h0 :
      ((MyCoordChangeL 0 1 x) v) =
      (if (x.val 1) > 0 then ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
                          else -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) v := rfl

    have h2 :(x.val 1) > 0 := by exact hx

    have h4 :
      ((MyCoordChangeL 0 1 x) v) = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) v := by
        rw [if_pos h2] at h0
        exact h0

    have h5 : ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) v = v := rfl

    have h6 : ((MyCoordChangeL 0 1 x) v) = v := by rw [h5] at h4; exact h4

    exact h6

lemma h_eq_on2_pre : ∀ x ∈ sl2, ∀ (v : EuclideanSpace ℝ (Fin 1)), (MyCoordChangeL 0 1 x) v = -v := by
    intro x hx v
    have h0 :
      ((MyCoordChangeL 0 1 x) v) =
      (if (x.val 1) > 0 then ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
                          else -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) v := rfl

    have h2 : ¬ (x.val 1 > 0) := not_lt_of_gt hx

    have h4 :
      ((MyCoordChangeL 0 1 x) v) = -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) v := by
        rw [if_neg h2] at h0
        exact h0

    have h5 : ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) v = v := rfl

    have h6 : ((MyCoordChangeL 0 1 x) v) = -v := by rw [h5] at h4; exact h4

    exact h6

lemma h7 :
    EqOn (fun x => ((MyCoordChangeL 0 1 x.1) x.2)) Prod.snd s1 →
    ContinuousOn (fun x => ((MyCoordChangeL 0 1 x.1) x.2)) s1 :=
      continuous_snd.continuousOn.congr

theorem sl1_open : IsOpen sl1 :=
  isOpen_induced_iff.mpr ⟨{ x : EuclideanSpace ℝ (Fin 2) | x 1 > 0 },
    isOpen_lt continuous_const (continuous_apply 1), rfl⟩

theorem sl2_open : IsOpen sl2 := by
  have h2 (i : Fin 2) : Continuous fun (x : EuclideanSpace ℝ (Fin 2)) => x i := continuous_apply i
  exact isOpen_induced_iff.mpr ⟨{ x : EuclideanSpace ℝ (Fin 2) | x 1 < 0 },
    isOpen_lt (h2 1) continuous_const, rfl⟩

lemma l01 : ContinuousOn (MyCoordChangeL 0 1) (U.source ∩ V.source) := by
  let f := fun (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) ↦
            if (x.val 1) > 0 then ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
                             else -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
  have h1 : (MyCoordChangeL 0 1) = f := rfl
  let g : EuclideanSpace ℝ (Fin 1) → (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 1)) :=
      fun y => (fun x => f x y)

  have hb5 : ∀ (v : EuclideanSpace ℝ (Fin 1)), ContinuousOn (fun x => v) sl1 := fun v => continuousOn_const
  have hb6 : ∀ (v : EuclideanSpace ℝ (Fin 1)), EqOn (fun x => v) (g v) sl1 := by
    intro v x hx
    have hb6a:  (fun x => v) x = v := rfl
    have hb6b : g v x = v := h_eq_on_pre x hx v
    rw [hb6b]
  have h7 : ∀ (v : EuclideanSpace ℝ (Fin 1)), ContinuousOn (g v) sl1 := by
    intro v
    have h1 : EqOn (fun x => v) (g v) sl1 := hb6 v
    have h2 : ContinuousOn (fun x => v) sl1 := hb5 v
    have h3 : ContinuousOn (g v) sl1 := ContinuousOn.congr h2 h1.symm
    exact h3

  have hc5 : ∀ (v : EuclideanSpace ℝ (Fin 1)), ContinuousOn (fun x => -v) sl2 := fun v => continuousOn_const.neg
  have hc6 : ∀ (v : EuclideanSpace ℝ (Fin 1)), EqOn (fun x => -v) (g v) sl2 := by
    intro v x hx
    have hb6a:  (fun x => v) x = v := rfl
    have hb6b : g v x = -v := h_eq_on2_pre x hx v
    rw [hb6b]
  have hc7 : ∀ (v : EuclideanSpace ℝ (Fin 1)), ContinuousOn (g v) sl2 := by
    intro v
    have h1 : EqOn (fun x => -v) (g v) sl2 := hc6 v
    have h2 : ContinuousOn (fun x => -v) sl2 := hc5 v
    have h3 : ContinuousOn (g v) sl2 := ContinuousOn.congr h2 h1.symm
    exact h3

  have hp : ∀ (v : EuclideanSpace ℝ (Fin 1)), ContinuousOn (g v) (sl1 ∪ sl2) := by
    intro v
    have hp1 : ContinuousOn (g v) (sl1 ∪ sl2) := continuous_on_union_of_open sl1_open sl2_open (h7 v) (hc7 v)
    exact hp1

  have hz : (U.source ∩ V.source) = sl1 ∪ sl2 := SulSource

  have h8 : ∀ (v : EuclideanSpace ℝ (Fin 1)), ContinuousOn (g v) (U.source ∩ V.source) := by
    rw [hz]
    exact hp

  have h3 : ContinuousOn f (U.source ∩ V.source) ↔
     ∀ (y : EuclideanSpace ℝ (Fin 1)), ContinuousOn (fun x ↦ f x y) (U.source ∩ V.source) := continuousOn_clm_apply

  have h4 : ContinuousOn f (U.source ∩ V.source) := h3.mpr h8

  exact h4

noncomputable
def MobiusAsVectorBundle : VectorBundleCore ℝ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) (Fin 2) where
  baseSet i := if i = 0 then U.source else V.source
  isOpen_baseSet := by
    intro i
    dsimp only
    split
    · exact U.open_source
    · exact V.open_source
  indexAt x := if (x.val 0) > 0 then 0 else 1
  mem_baseSet_at := my_mem_baseSet_at
  coordChange := MyCoordChangeL
  coordChange_self := MyCoordChange_selfL
  continuousOn_coordChange := by
    intro i j
    fin_cases i
    · fin_cases j
      . have h2 : ContinuousOn (MyCoordChangeL ((fun i ↦ i) 0) ((fun i ↦ i) 0))
                  ((fun i ↦ if i = 0 then U.source else V.source) ((fun i ↦ i) 0) ∩
                   (fun i ↦ if i = 0 then U.source else V.source) ((fun i ↦ i) 0)) := by
          simp
          exact l00
        exact h2
      · exact l01
    · fin_cases j
      · exact sorry
      · exact sorry
  coordChange_comp := sorry
