/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Data.Real.StarOrdered
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.FiberBundle.Instances.Mobius

set_option linter.style.longLine false

noncomputable
def MyCoordChangeL :
  Fin 2 → Fin 2 →
  (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) →
  EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)
  | 0, 0, _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
  | 1, 1, _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
  | 0, 1, x =>
      if x.val 1 > 0 then
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
      else
        -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
  | 1, 0, x =>
      if x.val 1 > 0 then
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
      else
        -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))

theorem MyCoordChangeL_self : ∀ (i : Fin 2),
    ∀ x ∈ (fun i => if i = 0 then U.source else V.source) i,
    ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChangeL i i x v = v := by
    intro i x h v
    have h : MyCoordChangeL i i x v = v :=
      match i with
        | 0 => rfl
        | 1 => rfl
    exact h

theorem t1001L (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) (v : EuclideanSpace ℝ (Fin 1)) :
    MyCoordChangeL 1 0 x (MyCoordChangeL 0 1 x v) = v := by
  simp_all only [MyCoordChangeL]
  by_cases h : (x.val 1) > 0
  case pos => rw [if_pos h, ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]
  case neg => rw [if_neg h]
              rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
                  ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]
              rw [neg_eq_iff_eq_neg]

theorem t0110L (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
               (v : EuclideanSpace ℝ (Fin 1)) :
    MyCoordChangeL 0 1 x (MyCoordChangeL 1 0 x v) = v := by
  simp_all only [MyCoordChangeL]
  by_cases h : (x.val 1) > 0
  case pos => rw [if_pos h, ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]
  case neg => rw [if_neg h]
              rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
                  ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]
              rw [neg_neg]

theorem MyCoordChangeL_comp : ∀ (i j k : Fin 2),
  ∀ x ∈ (fun i => if i = 0 then U.source else V.source) i ∩
        (fun i => if i = 0 then U.source else V.source) j ∩
        (fun i => if i = 0 then U.source else V.source) k,
    ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChangeL j k x (MyCoordChangeL i j x v) = MyCoordChangeL i k x v := by
    intro i j k x h v
    have h : MyCoordChangeL j k x (MyCoordChangeL i j x v) = MyCoordChangeL i k x v :=
      match i, j, k with
        | 0, 0, 0 => rfl
        | 0, 0, 1 => rfl
        | 0, 1, 0 => t1001L x v
        | 0, 1, 1 => rfl
        | 1, 0, 0 => rfl
        | 1, 0, 1 => t0110L x v
        | 1, 1, 0 => rfl
        | 1, 1, 1 => rfl
    exact h


theorem MyCoordChange_eval_eq :
  ∀ i j (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (v : EuclideanSpace ℝ (Fin 1)),
    MyCoordChange i j x v = (MyCoordChangeL i j x) v
  | 0, 0, _, v => rfl
  | 1, 1, _, v => rfl
  | 0, 1, x, v =>
    if h : x.val 1 > 0 then by
      simp only [MyCoordChange, MyCoordChangeL, if_pos h, ContinuousLinearMap.id_apply]
    else by
      simp only [MyCoordChange, MyCoordChangeL, if_neg h, ContinuousLinearMap.neg_apply,
                 ContinuousLinearMap.id_apply]
  | 1, 0, x, v =>
    if h : x.val 1 > 0 then by
      simp only [MyCoordChange, MyCoordChangeL, if_pos h, ContinuousLinearMap.id_apply]
    else by
      simp only [MyCoordChange, MyCoordChangeL, if_neg h, ContinuousLinearMap.neg_apply,
                 ContinuousLinearMap.id_apply]

theorem t01L : ContinuousOn (fun p => MyCoordChangeL 0 1 p) ((U.source ∩ V.source)) := by
  let f (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) := if x.val 1 > 0
    then ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
    else -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
  let c := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
  let d := -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))
  let g := fun _ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 => c
  let h := fun _ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 => d

  have h_eq : ∀ x, x.val 1 > 0 → f x = g x := by
    intros x hx
    simp only [f]
    rw [if_pos hx]

  have h_er : ∀ x, x.val 1 < 0 → f x = h x := by
    intros x hx
    simp only [f, h]
    rw [if_neg (by linarith : ¬x.val 1 > 0)]

  have h1 : ContinuousOn f {x | x.val 1 > 0} := by
    apply ContinuousOn.congr _ h_eq
    · exact continuousOn_const

  have h2 : ContinuousOn f {x | x.val 1 < 0} := by
    apply ContinuousOn.congr _ h_er
    · exact continuousOn_const

  have h3 : ContinuousOn f ({x | x.val 1 > 0} ∪ {x | x.val 1 < 0}) :=
    ContinuousOn.union_of_isOpen h1 h2 tOpen tOpen'

  have h4 : U.source ∩ V.source = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := SulSource
  rw [h4]

  have h5 : f = fun p => MyCoordChangeL 0 1 p := by
    funext p
    dsimp [f, MyCoordChangeL]

  rw [h5] at h3

  exact h3

theorem t10L : ContinuousOn (fun p => MyCoordChangeL 1 0 p) ((V.source ∩ U.source)) := by
  rw [Set.inter_comm]
  exact t01L

theorem uk : ∀ (i j : Fin 2),
  ContinuousOn (MyCoordChangeL i j)
   ((if i = 0 then U.source else V.source) ∩ if j = 0 then U.source else V.source) := by
    intro i j
    fin_cases i
    · fin_cases j
      · exact continuous_const.continuousOn
      · simp
        exact t01L
    · fin_cases j
      · simp
        exact t10L
      · exact continuous_const.continuousOn


noncomputable
def MobiusAsVectorBundle : VectorBundleCore ℝ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) (Fin 2) where
  baseSet i := if i = 0 then U.source else V.source
  isOpen_baseSet i := by
    split
    · exact U.open_source
    · exact V.open_source
  indexAt x := if (x.val 0) > 0 then 0 else 1
  mem_baseSet_at := my_mem_baseSet_at
  coordChange := MyCoordChangeL
  coordChange_self := MyCoordChangeL_self
  continuousOn_coordChange := uk
  coordChange_comp := MyCoordChangeL_comp

open Bundle
open Manifold

#synth ChartedSpace ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))
                    (TotalSpace (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber)

#synth ContMDiffVectorBundle 0 (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber (𝓡 1)

#synth ContMDiffVectorBundle ⊤ (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber (𝓡 1)


#check VectorBundle
#check trivializationAt
#check VectorPrebundle.toVectorBundle
#check FiberPrebundle.toFiberBundle

#check VectorBundleCore.fiberBundle

#check MobiusAsVectorBundle.fiberBundle
#check MobiusAsVectorBundle.fiberBundle.trivializationAt
#check FiberBundle.trivializationAt'

noncomputable
def e := MobiusAsVectorBundle.localTriv 0

noncomputable
def e' := MobiusAsVectorBundle.localTriv 1

instance  : Trivialization.IsLinear ℝ e :=
  VectorBundleCore.localTriv.isLinear MobiusAsVectorBundle 0

instance  : Trivialization.IsLinear ℝ e' :=
  VectorBundleCore.localTriv.isLinear MobiusAsVectorBundle 1

noncomputable
def φ (x : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) )) :
  (EuclideanSpace ℝ (Fin 1)) →L[ℝ] (EuclideanSpace ℝ (Fin 1)) :=
    (Trivialization.coordChangeL ℝ e e' x)

example : ContMDiffOn (𝓡 1)
              𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
              ⊤ φ (e.baseSet ∩ e'.baseSet) := sorry

noncomputable
instance : ContMDiffVectorBundle ⊤ (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber (𝓡 1) :=
{
  contMDiffOn_coordChangeL := fun e e' [MemTrivializationAtlas e] [MemTrivializationAtlas e'] =>

    let h1 : ContMDiffOn (𝓡 1)
              𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
              ⊤
              (fun b => (Trivialization.coordChangeL ℝ e e' b
                          : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)))
              (e.baseSet ∩ e'.baseSet) := sorry
    h1
}


instance : ContMDiffVectorBundle ⊤ (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber (𝓡 1) := by

  refine { contMDiffOn_coordChangeL := ?_ }
  refine fun e e' [MemTrivializationAtlas e] [MemTrivializationAtlas e'] ↦ ?_

  have h1 : ContMDiffOn (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ⊤
    (fun b ↦ (Trivialization.coordChangeL ℝ e e' b : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))) (e.baseSet ∩ e'.baseSet) := sorry
  exact h1
