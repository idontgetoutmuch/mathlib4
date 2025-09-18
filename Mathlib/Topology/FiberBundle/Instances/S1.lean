/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/
import Mathlib

set_option linter.style.longLine false

open Function Set
open IsManifold Manifold

def MobiusBase := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

structure S1 where
  point : MobiusBase

instance : Coe S1 (EuclideanSpace ℝ (Fin 2)) where
  coe w := w.point

/-
FIXME
-/
lemma sumOfSquares : ∀ (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1),
      (y.val 0) ^ 2 + (y.val 1) ^ 2 = 1 := by
  let A := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  let B := { x : EuclideanSpace ℝ (Fin 2) | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2}
  have h1 : A = B := by
    exact EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
  intro y
  have h2 : y.val ∈ A := y.prop
  have h3 : y.val ∈ B := by
    rw [h1] at h2
    exact h2
  have h4 : ∑ i : Fin 2, y.val i ^ 2 = 1 ^ 2 := by
    simp at h3
    exact h3
  have h5 : (y.val 0) ^ 2 + (y.val 1) ^ 2 = 1 := by
    rwa [Fin.sum_univ_two, one_pow] at h4
  exact h5

instance : Neg S1 where
  neg x :=
    let a := x.point.val 0
    let b := x.point.val 1
    have h1 : x.point.val ∈ MobiusBase := x.point.prop
    have h2 : Metric.sphere 0 1 = {x : EuclideanSpace ℝ (Fin 2) | ∑ i, (x i) ^ 2 = 1 ^ 2} :=
      EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
    have h3 : a ^ 2 + b ^ 2 = 1 := sumOfSquares x.point
    have h4 : (-a) ^ 2 = a ^ 2 := neg_pow_two a
    have h5 : (-b) ^ 2 = b ^ 2 := neg_pow_two b
    have h6 : (-a) ^ 2 + (-b) ^ 2 = 1 := by rw [<-h4, <-h5] at h3; exact h3
    have h7 : ![ -a, -b] ∈ {x : EuclideanSpace ℝ (Fin 2) | ∑ i, (x i) ^ 2 = 1 ^ 2} := by
      simp [Fin.sum_univ_two]
      exact h6
    have : ![ -a, -b ] ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [<-h2] at h7; exact h7
    ⟨![ -a, -b ], this⟩

lemma S1.ext_iff (x y : S1) : x = y ↔ x.point = y.point := by
  apply Iff.intro
  · intro h; rw [h]
  · intro h; cases x; cases y; simp_all

lemma S1.mk_inj (x y : _) : (S1.mk x = S1.mk y) ↔ (x = y) := by
  apply Iff.intro
  · intro h; cases h; rfl
  · intro h; rw [h]

theorem S1.mk_injective : Function.Injective S1.mk :=
  fun _ _ h ↦ (S1.mk_inj _ _).mp h

lemma S1MobiusBase (x : S1) (y : MobiusBase) : x = S1.mk y ↔ x.point = y :=
  S1.ext_iff x (S1.mk y)

inductive Pole
| north
| south
deriving DecidableEq

instance : TopologicalSpace S1 :=
  TopologicalSpace.induced S1.point instTopologicalSpaceSubtype

open Topology

lemma S1_mk_image_open_iff_source_open (φ : PartialHomeomorph MobiusBase (EuclideanSpace ℝ (Fin 1)))
  (hφ : IsOpen φ.source) : IsOpen (S1.mk '' φ.source) := by
  rw [isOpen_induced_iff]
  use φ.source
  constructor
  · exact hφ
  · ext x
    constructor
    · intro hx
      exact ⟨x.point, hx, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha

def north' := (!₂[0, 1] : EuclideanSpace ℝ (Fin 2))
def south' := (!₂[0, -1] : EuclideanSpace ℝ (Fin 2))

theorem hnorth : north' ∈ Metric.sphere 0 1 := by
  rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)]
  simp [north']

theorem hsouth : south' ∈ Metric.sphere 0 1 := by
  rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)]
  simp [south']

def north_pt := (⟨north', hnorth⟩ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
def south_pt := (⟨south', hsouth⟩ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

noncomputable def φₙ := chartAt (EuclideanSpace ℝ (Fin 1)) north_pt
noncomputable def φₛ := chartAt (EuclideanSpace ℝ (Fin 1)) south_pt

example : φₙ ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      chart_mem_maximalAtlas north_pt

example : φₛ ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      chart_mem_maximalAtlas south_pt

example : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (↑φₛ ∘ ↑φₙ.symm) (φₙ.target ∩ φₙ.symm ⁻¹' φₛ.source) := by
  have hU : φₙ ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      chart_mem_maximalAtlas north_pt
  have hV : φₛ ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      chart_mem_maximalAtlas south_pt
  let overlap := φₙ.target ∩ φₙ.symm ⁻¹' φₛ.source
  have h1 : overlap ⊆ φₙ.target := fun x hx => hx.1
  have h2 : overlap ⊆ φₙ.symm ⁻¹' φₛ.source := fun x hx => hx.2
  have h3 := (contMDiffOn_symm_of_mem_maximalAtlas hU).mono h1
  have h4 :  ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (↑φₛ ∘ ↑φₙ.symm) overlap := (contMDiffOn_of_mem_maximalAtlas hV).comp h3 h2
  exact h4

lemma ChartChangeSmoothOn'
    {M E H : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M]
    [ChartedSpace H M]
    [IsManifold I ⊤ M]
    {φ₀ φ₁ : PartialHomeomorph M H}
    (hU : φ₀ ∈ maximalAtlas I ⊤ M)
    (hV : φ₁ ∈ maximalAtlas I ⊤ M) :
    ContMDiffOn I I ⊤ (φ₁ ∘ φ₀.symm)
      (φ₀.target ∩ φ₀.symm ⁻¹' φ₁.source) := by
  let overlap := φ₀.target ∩ φ₀.symm ⁻¹' φ₁.source
  have h1 : overlap ⊆ φ₀.target := fun x hx => hx.1
  have h2 : overlap ⊆ φ₀.symm ⁻¹' φ₁.source := fun x hx => hx.2
  have h3 := (contMDiffOn_symm_of_mem_maximalAtlas hU).mono h1
  exact (contMDiffOn_of_mem_maximalAtlas hV).comp h3 h2

noncomputable
 def φN (φₙ : PartialHomeomorph (↑MobiusBase) (EuclideanSpace ℝ (Fin 1))) : PartialHomeomorph S1 (EuclideanSpace ℝ (Fin 1)) :=
{ toFun := fun s => φₙ s.point,
  invFun := fun x => S1.mk (φₙ.invFun x),
  source := S1.mk '' φₙ.source,
  target := φₙ.target,
  map_source' := by
    rintro ⟨p, hp⟩ ⟨a, ha, eq⟩
    have : a = ⟨p, hp⟩ := by
      injection eq with h'
    rw [<-this]
    exact φₙ.map_source' ha
  map_target' := by
    intro x hx
    have h1 : φₙ.invFun x ∈ φₙ.source := φₙ.map_target' hx
    have h2 : { point := φₙ.invFun x } ∈ S1.mk '' φₙ.source := mem_image_of_mem S1.mk h1
    exact h2,
  left_inv' := by
    rintro ⟨p, hp⟩ ⟨a, ha, eq⟩
    have : a = ⟨p, hp⟩ := by
      injection eq with h'
    rw [<-this]
    have h0 : (φₙ.invFun (φₙ ({ point := a } : S1).point)) = ({ point := a } : S1).point :=
      PartialHomeomorph.left_inv φₙ ha
    have h1 : S1.mk (φₙ.invFun (φₙ ({ point := a } : S1).point)) = S1.mk a := congrArg S1.mk h0
    exact h1,
  right_inv' := by
    intro x hx
    have h1 : φₙ.invFun x ∈ φₙ.source := φₙ.map_target' hx
    have h2 : φₙ (φₙ.symm x) = x := PartialHomeomorph.right_inv φₙ hx
    exact h2,
  open_source := S1_mk_image_open_iff_source_open φₙ φₙ.open_source,
  open_target := φₙ.open_target,
  continuousOn_toFun := by
    have ha : ContinuousOn S1.point univ := by
      have ha1 : Continuous S1.point := continuous_induced_dom
      have ha2 : ContinuousOn S1.point univ := continuousOn_univ.mpr ha1
      exact ha2
    have hc : ContinuousOn S1.point (S1.mk '' φₙ.source) := ContinuousOn.mono ha fun ⦃a⦄ a ↦ trivial
    have hd : MapsTo S1.point (S1.mk '' φₙ.source) φₙ.source := mapsTo_image_iff.mpr fun ⦃x⦄ a ↦ a
    have hb : ContinuousOn φₙ φₙ.source := φₙ.continuousOn_toFun
    have h1 : ContinuousOn (fun s ↦ φₙ s.point) (S1.mk '' φₙ.source) := by
      exact ContinuousOn.comp hb hc hd
    exact h1,
  continuousOn_invFun := by
    have h1 : Continuous S1.mk := by
      have h : Continuous (S1.point ∘ S1.mk) := continuous_id
      have h2 : Continuous S1.mk ↔ Continuous (S1.point ∘ S1.mk) := continuous_induced_rng
      exact h2.mpr h
    have ha : ContinuousOn S1.mk univ := continuousOn_univ.mpr h1
    have h2 : ContinuousOn φₙ.invFun φₙ.target := φₙ.continuousOn_invFun
    have hb : MapsTo φₙ.invFun φₙ.target univ := fun ⦃x⦄ a ↦ trivial
    have h3 : ContinuousOn (fun x ↦ S1.mk (φₙ.invFun x)) φₙ.target := by
      exact ContinuousOn.comp ha h2 hb
    exact h3
}

noncomputable
def baseAtlas'' : Set (PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1))) :=
  {φₙ, φₛ}

noncomputable
def baseAtlas' : Set (PartialHomeomorph S1 (EuclideanSpace ℝ (Fin 1))) :=
  {φN φₙ, φN φₛ}

lemma liftedPts : ∀ xh φₙ, (S1.mk xh) ∈ (φN φₙ).source ↔ xh ∈ φₙ.source := by
  intro xh φₙ
  apply Iff.intro
  · have h1 : (φN φₙ).source = S1.mk '' φₙ.source := rfl
    rw [h1]
    intro hx
    obtain ⟨a, ha, urk⟩ := hx
    have h2 : S1.mk a = S1.mk xh := urk
    have h3 : a = xh := by
      apply_fun S1.point at h2
      simp at h2
      exact h2
    rw [<-h3]
    exact ha
  · have h1 : (φN φₙ).source = S1.mk '' φₙ.source := rfl
    rw [h1]
    intro hx
    exact mem_image_of_mem S1.mk hx

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
  ⟨(finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)⟩

lemma hφₙ.source : φₙ.source = { x | x ≠ -north_pt } :=
  calc φₙ.source = (chartAt (EuclideanSpace ℝ (Fin 1)) north_pt).source := rfl
    _ = (stereographic' 1 (-north_pt)).source := rfl
    _ = {-north_pt}ᶜ := stereographic'_source (-north_pt)
    _ = { x | x ≠ -north_pt } := rfl

lemma hφₛ.source : φₛ.source = { x | x ≠ -south_pt } :=
  calc φₛ.source = (chartAt (EuclideanSpace ℝ (Fin 1)) south_pt).source := rfl
    _ = (stereographic' 1 (-south_pt)).source := rfl
    _ = {-south_pt}ᶜ := stereographic'_source (-south_pt)
    _ = { x | x ≠ -south_pt } := rfl

lemma hφₛ.target : φₛ.target = univ :=
  calc φₛ.target = (chartAt (EuclideanSpace ℝ (Fin 1)) south_pt).target := rfl
    _ = (stereographic' 1 (-south_pt)).target := rfl
    _ = univ := stereographic'_target (-south_pt)

lemma hφₙ.target : φₙ.target = univ :=
  calc φₙ.target = (chartAt (EuclideanSpace ℝ (Fin 1)) north_pt).target := rfl
    _ = (stereographic' 1 (-north_pt)).target := rfl
    _ = univ := stereographic'_target (-north_pt)

lemma fooN : { point := north_pt } ∈ (φN φₙ).source := by
  have h5 : north_pt.val 1 = 1 := rfl
  have h7 : north_pt ≠ -north_pt := by
    intro h_eq
    have h_contra : north_pt.val 1 = -north_pt.val 1 := congrFun (congrArg Subtype.val h_eq) 1
    rw [h5] at h_contra
    linarith
  have h3 : { point := north_pt } ∈ (φN φₙ).source ↔ north_pt ∈ φₙ.source := liftedPts north_pt φₙ
  have h4 : north_pt ∈ { x | x ≠ -north_pt } := h7
  have h6 : { point := north_pt } ∈ (φN φₙ).source ↔ north_pt ∈ { x | x ≠ -north_pt } := by
    rw [hφₙ.source] at h3
    exact h3
  have h8 : { point := north_pt } ∈ (φN φₙ).source := h6.mpr h4
  exact h8

lemma fooN' x (hx : x ≠ -north_pt) :  { point := x } ∈ (φN φₙ).source := by
  have h3 : ∀ x, { point := x } ∈ (φN φₙ).source ↔ x ∈ φₙ.source := fun x => liftedPts x φₙ
  have h4 : x ∈ { x | x ≠ -north_pt } := hx
  have h6 : ∀ x, { point := x } ∈ (φN φₙ).source ↔ x ∈ { x | x ≠ -north_pt } := by
    rw [hφₙ.source] at h3
    exact h3
  have h8 : { point := x } ∈ (φN φₙ).source := (h6 x).mpr h4
  exact h8

lemma southIsNotNorth : south_pt ≠ -south_pt := by
  have h5 : south_pt.val 1 = -1 := rfl
  intro h_eq
  have h_contra : south_pt.val 1 = -south_pt.val 1 := congrFun (congrArg Subtype.val h_eq) 1
  rw [h5] at h_contra
  linarith

lemma fooS : { point := south_pt } ∈ (φN φₛ).source := by
  have h5 : south_pt.val 1 = -1 := rfl
  have h7 : south_pt ≠ -south_pt := by
    intro h_eq
    have h_contra : south_pt.val 1 = -south_pt.val 1 := congrFun (congrArg Subtype.val h_eq) 1
    rw [h5] at h_contra
    linarith
  have h3 : { point := south_pt } ∈ (φN φₛ).source ↔ south_pt ∈ φₛ.source := liftedPts south_pt φₛ
  have h4 : south_pt ∈ { x | x ≠ -south_pt } := h7
  have h6 : { point := south_pt } ∈ (φN φₛ).source ↔ south_pt ∈ { x | x ≠ -south_pt } := by
    rw [hφₛ.source] at h3
    exact h3
  have h8 : { point := south_pt } ∈ (φN φₛ).source := h6.mpr h4
  exact h8

lemma fooS' x (hx : x ≠ -south_pt) :  { point := x } ∈ (φN φₛ).source := by
  have h3 : ∀ x, { point := x } ∈ (φN φₛ).source ↔ x ∈ φₛ.source := fun x => liftedPts x φₛ
  have h4 : x ∈ { x | x ≠ -south_pt } := hx
  have h6 : ∀ x, { point := x } ∈ (φN φₛ).source ↔ x ∈ { x | x ≠ -south_pt } := by
    rw [hφₛ.source] at h3
    exact h3
  have h8 : { point := x } ∈ (φN φₛ).source := (h6 x).mpr h4
  exact h8

lemma myNeg (a b : ℝ) : -!₂[a, b] = !₂[-a, -b] := by
  let x := ![a, b]
  let y := ![-a, -b]
  have h1 : -(![a, b]) = ![-a, -b] := by simp
  have h2 : -x = y := by rw [h1]
  have h3 : (WithLp.equiv 2 (Fin 2 → ℝ)) (-x) = -(WithLp.equiv 2 (Fin 2 → ℝ)) x := WithLp.ofLp_neg 2 x
  rw [h2] at h3
  exact h3.symm

lemma bar : north_pt = -south_pt := by
  have hc : -!₂[(0 : ℝ), -1] = !₂[0, 1] := by rw [myNeg (0 : ℝ) (-1 : ℝ)]; simp
  exact SetCoe.ext (id (Eq.symm hc))

lemma bar' : south_pt = -north_pt := by
  have hc : -!₂[(0 : ℝ), 1] = !₂[0, -1] := by rw [myNeg (0 : ℝ) (1 : ℝ)]; simp
  exact SetCoe.ext (id (Eq.symm hc))

open Pole

/-
FIXME
-/
theorem sob : ∀ (x : S1), x ∈ if (if x.point = north_pt then north else south) = north then (φN φₙ).source else (φN φₛ).source := by
  intro x
  by_cases h : x.point = north_pt
  case pos => have h1 : x.point = north_pt := h
              rw [if_pos h]
              simp
              have h2 : x = S1.mk north_pt ↔ x.point = (S1.mk north_pt).point := S1.ext_iff x (S1.mk north_pt)
              rw [h2.mpr h]
              exact fooN
  case neg => have h1 : x.point ≠ north_pt := h
              have h4 : x.point ≠ -south_pt := by rw [bar] at h1; exact h1
              rw [if_neg h]
              have h6 : φₛ.source = { x | x ≠ -south_pt } := hφₛ.source
              have h5 : x.point ∈ { x | x ≠ -south_pt } := h4
              have h7 : x.point ∈ φₛ.source := by rw [<-h6] at h5; exact h5
              have h8 : { point := x.point } ∈ (φN φₛ).source ↔ x.point ∈ φₛ.source := liftedPts x.point φₛ
              have h9 : x ∈ (φN φₛ).source := h8.mpr h7
              exact h9

lemma my_mem_chart_source' : ∀ (x : S1), x ∈ (if x.point = north_pt then φN φₙ else φN φₛ).source := by
  intro x
  by_cases h : x.point = north_pt
  case pos => have h1 : x.point = north_pt := h
              rw [if_pos h]
              have h2 : x = S1.mk north_pt ↔ x.point = (S1.mk north_pt).point := S1.ext_iff x (S1.mk north_pt)
              rw [h2.mpr h]
              exact fooN
  case neg => have h1 : x.point ≠ north_pt := h
              have h4 : x.point ≠ -south_pt := by rw [bar] at h1; exact h1
              rw [if_neg h]
              have h6 : φₛ.source = { x | x ≠ -south_pt } := hφₛ.source
              have h5 : x.point ∈ { x | x ≠ -south_pt } := h4
              have h7 : x.point ∈ φₛ.source := by rw [<-h6] at h5; exact h5
              have h8 : { point := x.point } ∈ (φN φₛ).source ↔ x.point ∈ φₛ.source := liftedPts x.point φₛ
              have h9 : x ∈ (φN φₛ).source := h8.mpr h7
              exact h9

noncomputable instance S1.chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 1)) S1 :=
{ atlas := baseAtlas',
  chartAt := fun x =>
    if x.point = north_pt then φN φₙ else φN φₛ,
  mem_chart_source := my_mem_chart_source'
  chart_mem_atlas := by
    intro x
    dsimp
    split_ifs with h
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
}

lemma SmoothInner
  (φₙ : PartialHomeomorph ↑MobiusBase (EuclideanSpace ℝ (Fin 1)))
  (φₛ : PartialHomeomorph ↑MobiusBase (EuclideanSpace ℝ (Fin 1)))
  (ha : φₙ ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
  (hb : φₛ ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
  : ContDiffOn ℝ ⊤ (φₙ.symm ≫ₕ φₛ) (φₙ.symm ≫ₕ φₛ).source := by
    rw [← contMDiffOn_iff_contDiffOn]
    convert ChartChangeSmoothOn' ha hb using 1

lemma φN_symm_source_preimage_eq
  (φₙ : PartialHomeomorph ↑MobiusBase (EuclideanSpace ℝ (Fin 1)))
  (φₛ : PartialHomeomorph ↑MobiusBase (EuclideanSpace ℝ (Fin 1))) :
    (φN φₙ).symm ⁻¹' (φN φₛ).source = φₙ.symm ⁻¹' φₛ.source := by
  unfold φN
  simp
  ext x
  apply Iff.intro
  · intro hx
    obtain ⟨z, hz₁, hz₂⟩ := hx
    simp
    have h2 : S1.mk z = S1.mk (φₙ.symm x) := hz₂
    have h3 : S1.mk z = S1.mk (φₙ.symm x) → z = φₙ.symm x := (S1.ext_iff (S1.mk z) ( S1.mk (φₙ.symm x))).mp
    have h5 : z = φₙ.symm x := h3 h2
    rw [h5] at hz₁
    exact hz₁
  · intro hx
    exact mem_preimage.mpr (mem_image_of_mem S1.mk hx)

lemma hh2 : (↑(𝓡 1).symm ⁻¹' ((φN φₙ).symm ≫ₕ φN φₛ).source ∩ range ↑(𝓡 1)) =
            (φₙ.symm ≫ₕ φₛ).source := by
  simp
  have h3 : (φN φₙ).target = φₙ.target := rfl
  have h4 : ↑(φN φₙ).symm ⁻¹' (φN φₛ).source = ↑φₙ.symm ⁻¹' φₛ.source := φN_symm_source_preimage_eq φₙ φₛ
  rw [h3]
  exact congrArg (Inter.inter φₙ.target) h4

lemma hh3 : (↑(𝓡 1).symm ⁻¹' ((φN φₛ).symm ≫ₕ φN φₙ).source ∩ range ↑(𝓡 1)) =
            (φₛ.symm ≫ₕ φₙ).source := by
  simp
  have h3 : (φN φₛ).target = φₛ.target := rfl
  have h4 : ↑(φN φₛ).symm ⁻¹' (φN φₙ).source = ↑φₛ.symm ⁻¹' φₙ.source := φN_symm_source_preimage_eq φₛ φₙ
  rw [h3]
  exact congrArg (Inter.inter φₛ.target) h4

lemma hh1 : (↑(𝓡 1).symm ⁻¹' ((φN φₙ).symm ≫ₕ φN φₙ).source ∩ range ↑(𝓡 1)) =
            (φₙ.symm ≫ₕ φₙ).source := by
  simp
  have h3 : (φN φₙ).target = φₙ.target := rfl
  have h4 : ↑(φN φₙ).symm ⁻¹' (φN φₙ).source = ↑φₙ.symm ⁻¹' φₙ.source := φN_symm_source_preimage_eq φₙ φₙ
  rw [h3]
  exact congrArg (Inter.inter φₙ.target) h4

lemma hh4 : (↑(𝓡 1).symm ⁻¹' ((φN φₛ).symm ≫ₕ φN φₛ).source ∩ range ↑(𝓡 1)) =
            (φₛ.symm ≫ₕ φₛ).source := by
  simp
  have h3 : (φN φₛ).target = φₛ.target := rfl
  have h4 : ↑(φN φₛ).symm ⁻¹' (φN φₛ).source = ↑φₛ.symm ⁻¹' φₛ.source := φN_symm_source_preimage_eq φₛ φₛ
  rw [h3]
  exact congrArg (Inter.inter φₛ.target) h4

lemma gg1 : ContDiffOn ℝ ⊤ (↑(𝓡 1) ∘ ↑((φN φₙ).symm ≫ₕ φN φₙ) ∘ ↑(𝓡 1).symm)
  (↑(𝓡 1).symm ⁻¹' ((φN φₙ).symm ≫ₕ φN φₙ).source ∩ range ↑(𝓡 1)) := by
  have h1 : (↑(𝓡 1) ∘ ↑((φN φₙ).symm ≫ₕ φN φₛ) ∘ ↑(𝓡 1).symm) = (φₙ.symm ≫ₕ φₛ) := by
    exact rfl
  have h4 : ContDiffOn ℝ ⊤ (↑ (↑(𝓡 1) ∘ ↑((φN φₙ).symm ≫ₕ φN φₙ) ∘ ↑(𝓡 1).symm))
                      (φₙ.symm ≫ₕ φₙ).source :=
                        SmoothInner φₙ φₙ
                                   (chart_mem_maximalAtlas north_pt)
                                   (chart_mem_maximalAtlas north_pt)
  have h5 : (↑(𝓡 1).symm ⁻¹' ((φN φₙ).symm ≫ₕ φN φₙ).source ∩ range ↑(𝓡 1)) =
            (φₙ.symm ≫ₕ φₙ).source := hh1
  rw [<-h5] at h4
  exact h4

lemma gg2 : ContDiffOn ℝ ⊤ (↑(𝓡 1) ∘ ↑((φN φₙ).symm ≫ₕ φN φₛ) ∘ ↑(𝓡 1).symm)
  (↑(𝓡 1).symm ⁻¹' ((φN φₙ).symm ≫ₕ φN φₛ).source ∩ range ↑(𝓡 1)) := by
  have h1 : (↑(𝓡 1) ∘ ↑((φN φₙ).symm ≫ₕ φN φₛ) ∘ ↑(𝓡 1).symm) = (φₙ.symm ≫ₕ φₛ) := by
    exact rfl
  have h4 : ContDiffOn ℝ ⊤ (↑ (↑(𝓡 1) ∘ ↑((φN φₙ).symm ≫ₕ φN φₛ) ∘ ↑(𝓡 1).symm))
                      (φₙ.symm ≫ₕ φₛ).source := SmoothInner φₙ φₛ
                                                            (chart_mem_maximalAtlas north_pt)
                                                            (chart_mem_maximalAtlas south_pt)
  have h5 : (↑(𝓡 1).symm ⁻¹' ((φN φₙ).symm ≫ₕ φN φₛ).source ∩ range ↑(𝓡 1)) =
            (φₙ.symm ≫ₕ φₛ).source := hh2
  rw [<-h5] at h4
  exact h4

lemma gg3 : ContDiffOn ℝ ⊤ (↑(𝓡 1) ∘ ↑((φN φₛ).symm ≫ₕ φN φₙ) ∘ ↑(𝓡 1).symm)
  (↑(𝓡 1).symm ⁻¹' ((φN φₛ).symm ≫ₕ φN φₙ).source ∩ range ↑(𝓡 1)) := by
  have h1 : (↑(𝓡 1) ∘ ↑((φN φₛ).symm ≫ₕ φN φₙ) ∘ ↑(𝓡 1).symm) = (φₛ.symm ≫ₕ φₙ) := by
    exact rfl
  have h4 : ContDiffOn ℝ ⊤ (↑ (↑(𝓡 1) ∘ ↑((φN φₛ).symm ≫ₕ φN φₙ) ∘ ↑(𝓡 1).symm))
                      (φₛ.symm ≫ₕ φₙ).source :=
                        SmoothInner φₛ φₙ
                          (chart_mem_maximalAtlas south_pt)
                          (chart_mem_maximalAtlas north_pt)
  have h5 : (↑(𝓡 1).symm ⁻¹' ((φN φₛ).symm ≫ₕ φN φₙ).source ∩ range ↑(𝓡 1)) =
            (φₛ.symm ≫ₕ φₙ).source := hh3
  rw [<-h5] at h4
  exact h4

lemma gg4 : ContDiffOn ℝ ⊤ (↑(𝓡 1) ∘ ↑((φN φₛ).symm ≫ₕ φN φₛ) ∘ ↑(𝓡 1).symm)
  (↑(𝓡 1).symm ⁻¹' ((φN φₛ).symm ≫ₕ φN φₛ).source ∩ range ↑(𝓡 1)) := by
  have h4 : ContDiffOn ℝ ⊤ (↑ (↑(𝓡 1) ∘ ↑((φN φₛ).symm ≫ₕ φN φₛ) ∘ ↑(𝓡 1).symm))
                      (φₛ.symm ≫ₕ φₛ).source :=
                        SmoothInner φₛ φₛ
                                   (chart_mem_maximalAtlas south_pt)
                                   (chart_mem_maximalAtlas south_pt)
  have h5 : (↑(𝓡 1).symm ⁻¹' ((φN φₛ).symm ≫ₕ φN φₛ).source ∩ range ↑(𝓡 1)) =
            (φₛ.symm ≫ₕ φₛ).source := hh4
  rw [<-h5] at h4
  exact h4

lemma fff : ∀ (e e' : PartialHomeomorph S1 (EuclideanSpace ℝ (Fin 1))),
  e ∈ atlas (EuclideanSpace ℝ (Fin 1)) S1 →
    e' ∈ atlas (EuclideanSpace ℝ (Fin 1)) S1 →
      ContDiffOn ℝ ⊤ (↑(𝓡 1) ∘ ↑(e.symm ≫ₕ e') ∘ ↑(𝓡 1).symm) (↑(𝓡 1).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range ↑(𝓡 1)) := by
  intros e e' he he'
  rcases he with (rfl | rfl)
  · rcases he' with (rfl | rfl)
    · exact gg1
    · exact gg2
  · rcases he' with (rfl | rfl)
    · exact gg3
    · exact gg4

instance S1.Smooth : @IsManifold ℝ _ _ _ _ _ _ (𝓡 1) ⊤ S1 _ S1.chartedSpace := by
  apply isManifold_of_contDiffOn
  exact fff
