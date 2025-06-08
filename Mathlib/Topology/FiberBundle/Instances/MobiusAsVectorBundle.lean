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

theorem MyContinuousOn_coordChangeL : ∀ (i j : Fin 2),
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
  continuousOn_coordChange := MyContinuousOn_coordChangeL
  coordChange_comp := MyCoordChangeL_comp

open Bundle Manifold Trivialization VectorBundleCore Topology

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

noncomputable
def φ00 (x : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) )) :
  (EuclideanSpace ℝ (Fin 1)) →L[ℝ] (EuclideanSpace ℝ (Fin 1)) :=
    (Trivialization.coordChangeL ℝ e e x)

noncomputable
def φ10 (x : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) )) :
  (EuclideanSpace ℝ (Fin 1)) →L[ℝ] (EuclideanSpace ℝ (Fin 1)) :=
    (Trivialization.coordChangeL ℝ e' e x)

noncomputable
def φ11 (x : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) )) :
  (EuclideanSpace ℝ (Fin 1)) →L[ℝ] (EuclideanSpace ℝ (Fin 1)) :=
    (Trivialization.coordChangeL ℝ e' e' x)

lemma φ_eq_coordChange' :
  ∀ x, x ∈ e.baseSet ∩ e'.baseSet →
    φ x = MobiusAsVectorBundle.coordChange 0 1 x := by
  intros x hx
  apply ContinuousLinearMap.ext
  intro y
  exact VectorBundleCore.localTriv_coordChange_eq MobiusAsVectorBundle 0 1 hx y

lemma φ10_eq_coordChange :
  ∀ x, x ∈ e'.baseSet ∩ e.baseSet →
    φ10 x = MobiusAsVectorBundle.coordChange 1 0 x := by
  intros x hx
  apply ContinuousLinearMap.ext
  intro y
  exact VectorBundleCore.localTriv_coordChange_eq MobiusAsVectorBundle 1 0 hx y

lemma φ00_eq_coordChange :
  ∀ x, x ∈ e.baseSet ∩ e.baseSet →
    φ00 x = MobiusAsVectorBundle.coordChange 0 0 x := by
  intros x hx
  apply ContinuousLinearMap.ext
  intro y
  exact VectorBundleCore.localTriv_coordChange_eq MobiusAsVectorBundle 0 0 hx y

lemma φ11_eq_coordChange :
  ∀ x, x ∈ e'.baseSet ∩ e'.baseSet →
    φ11 x = MobiusAsVectorBundle.coordChange 1 1 x := by
  intros x hx
  apply ContinuousLinearMap.ext
  intro y
  exact VectorBundleCore.localTriv_coordChange_eq MobiusAsVectorBundle 1 1 hx y

lemma hh00 : ContMDiffOn (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ⊤
 (MobiusAsVectorBundle.coordChange 0 0) (e.baseSet ∩ e.baseSet) := contMDiffOn_const

lemma hh11 : ContMDiffOn (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ⊤
 (MobiusAsVectorBundle.coordChange 1 1) (e'.baseSet ∩ e'.baseSet) := contMDiffOn_const

lemma hh01 : ContMDiffOn (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ⊤
 (MobiusAsVectorBundle.coordChange 0 1) (e.baseSet ∩ e'.baseSet) := by

  have h0 : MobiusAsVectorBundle.coordChange 0 1 = MyCoordChangeL 0 1 := rfl

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

  have h1_const_pt : ∀ x ∈ {x | x.val 1 > 0},
    ContMDiffWithinAt (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
                      ⊤ g {x | x.val 1 > 0} x :=
    fun x hx => contMDiffWithinAt_const

  have h2 : ∀ x ∈ {x | x.val 1 > 0},
  ContMDiffWithinAt (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    ⊤ f {x | x.val 1 > 0} x :=
    fun x hx => ContMDiffWithinAt.congr (h1_const_pt x hx) (fun y hy => h_eq y hy) (h_eq x hx)

  have h1 : ContMDiffOn (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ⊤ f {x | x.val 1 > 0} := h2

  have ha_const_pt : ∀ x ∈ {x | x.val 1 < 0},
    ContMDiffWithinAt (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
                      ⊤ h {x | x.val 1 < 0} x :=
    fun x hx => contMDiffWithinAt_const

  have hb : ∀ x ∈ {x | x.val 1 < 0},
  ContMDiffWithinAt (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    ⊤ f {x | x.val 1 < 0} x :=
    fun x hx => ContMDiffWithinAt.congr (ha_const_pt x hx) (fun y hy => h_er y hy) (h_er x hx)

  have hc : ContMDiffOn (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ⊤ f {x | x.val 1 < 0} := hb

  have h6 : ContMDiffOn (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ⊤ f ({x | x.val 1 > 0} ∪ {x | x.val 1 < 0}) := by
    intro x hx
    rcases (Set.mem_union x _ _).1 hx with (hxp | hxn)
    · have h61 : {x | x.val 1 > 0} ∈ 𝓝 x := tOpen.mem_nhds hxp
      have h62 : ContMDiffAt (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ⊤ f x :=
       ContMDiffOn.contMDiffAt h1 h61
      have h63 : ContMDiffWithinAt (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ⊤ f
                                    ({y | y.val 1 > 0} ∪ {y | y.val 1 < 0}) x := h62.contMDiffWithinAt
      exact h63
    · have h61 : {x | x.val 1 < 0} ∈ 𝓝 x := tOpen'.mem_nhds hxn
      have h62 : ContMDiffAt (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ⊤ f x :=
       ContMDiffOn.contMDiffAt hc h61
      have h63 : ContMDiffWithinAt (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ⊤ f
                                    ({y | y.val 1 > 0} ∪ {y | y.val 1 < 0}) x := h62.contMDiffWithinAt
      exact h63

  have he : U.source = e.baseSet := rfl
  have he' : V.source = e'.baseSet := rfl

  have h4 : U.source ∩ V.source = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := SulSource
  rw [<-he, <-he', h4]

  exact h6

lemma hh10 : ContMDiffOn (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1)) ⊤
 (MobiusAsVectorBundle.coordChange 0 1) (e.baseSet ∩ e'.baseSet) := hh01

lemma c00 : ContMDiffOn (𝓡 1)
              𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
              ⊤ φ00 (e.baseSet ∩ e.baseSet) := by
  apply ContMDiffOn.congr hh00
  intros x hx
  exact φ00_eq_coordChange x (Set.mem_inter hx.1 hx.1)

lemma c01 : ContMDiffOn (𝓡 1)
              𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
              ⊤ φ (e.baseSet ∩ e'.baseSet) := by
  apply ContMDiffOn.congr hh01
  intros x hx
  exact φ_eq_coordChange' x hx

lemma c10' : ContMDiffOn (𝓡 1)
              𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
              ⊤ φ10 (e.baseSet ∩ e'.baseSet) := by
  apply ContMDiffOn.congr hh10
  intros x hx
  have h1 : x ∈ e'.baseSet ∩ e.baseSet := Set.mem_inter hx.2 hx.1
  exact φ10_eq_coordChange x h1

lemma c10 : ContMDiffOn (𝓡 1)
              𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
              ⊤ φ10 (e'.baseSet ∩ e.baseSet) := by
  rw [Set.inter_comm]
  exact c10'

lemma c11 : ContMDiffOn (𝓡 1)
              𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
              ⊤ φ11 (e'.baseSet ∩ e'.baseSet) := by
  apply ContMDiffOn.congr hh11
  intros x hx
  exact φ11_eq_coordChange x (Set.mem_inter hx.1 hx.1)

#check vectorBundle MobiusAsVectorBundle

#synth VectorBundle ℝ (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber

lemma trivialization_mem_iff (e : Trivialization _ _) :
    MemTrivializationAtlas e ↔
    e = MobiusAsVectorBundle.localTriv 0 ∨ e = MobiusAsVectorBundle.localTriv 1 := by
  dsimp [MemTrivializationAtlas, MobiusAsVectorBundle]
  constructor
  · intro h
    simp only [Set.mem_range] at h
    obtain ⟨i, rfl⟩ := h
    fin_cases i
    · left; rfl
    · right; rfl
  · intro h
    cases h with
    | inl h0 => exact ⟨0, h0.symm⟩
    | inr h1 => exact ⟨1, h1.symm⟩

noncomputable
instance : ContMDiffVectorBundle ⊤ (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber (𝓡 1) :=
{
  contMDiffOn_coordChangeL := fun e e' mem_e mem_e' =>
    match (trivialization_mem_iff e).mp mem_e, (trivialization_mem_iff e').mp mem_e' with
    | Or.inl l00, Or.inl r00 => by subst l00; subst r00; exact c00
    | Or.inl l01, Or.inr r01 => by subst l01; subst r01; exact c01
    | Or.inr l10, Or.inl r10 => by subst l10; subst r10; exact c10
    | Or.inr l11, Or.inr r11 => by subst l11; subst r11; exact c11
}

#synth ContMDiffVectorBundle ⊤ (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber (𝓡 1)

noncomputable
instance : ChartedSpace ((EuclideanSpace ℝ (Fin 1)) × (EuclideanSpace ℝ (Fin 1)))
                       (TotalSpace (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber)
 := ChartedSpace.comp
  (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))
  (TotalSpace (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber)

noncomputable
instance : ChartedSpace (EuclideanSpace ℝ (Fin (1 + 1))) (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber) := by
  exact ChartedSpace.comp
    (EuclideanSpace ℝ (Fin (1 + 1)))
    ((EuclideanSpace ℝ (Fin 1)) × (EuclideanSpace ℝ (Fin 1)))
    (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber)

#synth VectorBundle ℝ (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber
#synth ContMDiffVectorBundle ⊤ (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber (𝓡 1)

#synth IsManifold ((𝓡 1).prod (𝓡 1)) ⊤ (TotalSpace (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber)

#synth IsManifold (𝓡 2) 0 (TotalSpace (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber)
#synth IsManifold (𝓡 2) ⊤ (TotalSpace (EuclideanSpace ℝ (Fin 1)) MobiusAsVectorBundle.Fiber)
