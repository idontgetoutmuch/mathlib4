/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/
import Mathlib

set_option linter.style.longLine false

open Function Set
open IsManifold Manifold

def x := (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))

theorem h : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rw [EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one), mem_setOf]
  simp [x]

def u := (!₂[-1, 0] : EuclideanSpace ℝ (Fin 2))

theorem g : u ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rw [EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one), mem_setOf]
  simp [u]

def xh := ((⟨x, h⟩ :  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ))
def ug := ((⟨u, g⟩ :  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ))

/-- The constructed chart at u in the standard unit sphere S¹. -/
noncomputable def φ₁ := chartAt (EuclideanSpace ℝ (Fin 1))
  (⟨u, g⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

/-- The constructed chart at x in the standard unit sphere S¹. -/
noncomputable def φ₀ := chartAt (EuclideanSpace ℝ (Fin 1))
  (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

def MobiusBase := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

structure S1 where
  point : MobiusBase

instance : Coe S1 (EuclideanSpace ℝ (Fin 2)) where
  coe w := w.point

lemma S1.ext_iff (x y : S1) : x = y ↔ x.point = y.point := by
  apply Iff.intro
  · intro h; rw [h]
  · intro h; cases x; cases y; simp_all

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
def baseAtlas' : Set (PartialHomeomorph S1 (EuclideanSpace ℝ (Fin 1))) :=
  {φN φₙ, φN φₛ}

noncomputable
def baseAtlas : Set (PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1))) :=
  {φ₀, φ₁}

#synth ChartedSpace (EuclideanSpace ℝ (Fin 1)) S1

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

#synth ChartedSpace (EuclideanSpace ℝ (Fin 1)) S1

open Bundle

noncomputable
def MyCoordChange' : Pole → Pole → S1 → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
  | north, north, _, α => α
  | north, south, x, α => if x.point.val 0 > 0 then α else -α
  | south, north, x, α => if x.point.val 0 > 0 then α else -α
  | south, south, _, α => α

theorem MyCoordChange_self' : ∀ (i : Pole),
    ∀ x ∈ (fun i => if i = north then (φN φₙ).source else (φN φₛ).source) i,
    ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChange' i i x v = v := by
    intro i x h v
    have h : MyCoordChange' i i x v = v :=
      match i with
        | north => rfl
        | south => rfl
    exact h

theorem MyCoordChange_comp' : ∀ (i j k : Pole),
  ∀ x ∈ (fun i => if i = north then (φN φₙ).source else (φN φₛ).source) i ∩
        (fun i => if i = north then (φN φₙ).source else (φN φₛ).source) j ∩
        (fun i => if i = north then (φN φₙ).source else (φN φₛ).source) k,
    ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChange' j k x (MyCoordChange' i j x v) = MyCoordChange' i k x v := by
    intro i j k x h v
    have h : MyCoordChange' j k x (MyCoordChange' i j x v) = MyCoordChange' i k x v :=
      match i, j, k with
        | north, north, north => rfl
        | north, north, south => rfl
        | north, south, north => by simp_all only [MyCoordChange', Fin.isValue,
                                                   ↓reduceIte, neg_neg, ite_self];
        | north, south, south => rfl
        | south, north, north => rfl
        | south, north, south => by simp_all [MyCoordChange']
        | south, south, north => rfl
        | south, south, south => rfl
    exact h

open Set

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

lemma OverlapNorthSouth :
    (φN φₙ).source ∩ (φN φₛ).source = { x | x.point.val 0 ≠ 0 } := by
  ext x
  simp only [mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro ⟨hₙ, hₛ⟩
    by_contra h
    have h4 : φₙ.source = { x | x ≠ -north_pt } := hφₙ.source
    have h4a : φₙ.source = { x | x ≠ south_pt } := by
      rw [<-bar'] at h4
      exact h4
    have h5 : φₛ.source = { x | x ≠ -south_pt } := hφₛ.source
    have h5a : φₛ.source = { x | x ≠ north_pt } := by
      rw [<-bar] at h5
      exact h5
    have h6 : { point := x.point } ∈ (φN φₙ).source ↔ x.point ∈ φₙ.source := liftedPts x.point φₙ
    have h7 : x.point ∈ φₙ.source := h6.mp hₙ
    have h8 : x.point ∈ { x | x ≠ south_pt } := by rw [h4a] at h7; exact h7
    have h6a : { point := x.point } ∈ (φN φₛ).source ↔ x.point ∈ φₛ.source := liftedPts x.point φₛ
    have h7a : x.point ∈ φₛ.source := h6a.mp hₛ
    have h8a : x.point ∈ { x | x ≠ north_pt } := by rw [h5a] at h7a; exact h7a
    have ha : x.point.val 0 ^ 2  + x.point.val 1 ^ 2 = 1 := sumOfSquares x.point
    have hb : x.point.val 1 ^ 2 = 1 := by
      rw [h] at ha
      simpa using ha
    have hc : x.point.val 1 = 1 ∨ x.point.val 1 = -1 := by
      exact sq_eq_one_iff.mp (by exact hb : (x.point.val 1) ^ 2 = 1)
    cases hc with
    | inl hp1 => have hc2 : x.point.val = !₂[0, 1] := by
                   ext i
                   fin_cases i
                   · exact h
                   · exact hp1
                 have hc4 : north_pt.val = !₂[0, 1] := rfl
                 have hc3 : x.point.val ≠ !₂[0, 1] := by
                  rw [←hc4] at hc2
                  have : x.point = north_pt := Subtype.ext hc2
                  contradiction
                 exact hc3 hc2
    | inr hn1 => have hc1 : x.point.val 1 = -1 := hn1
                 have hc2 : x.point.val = !₂[0, -1] := by
                   ext i
                   fin_cases i
                   · exact h
                   · exact hn1
                 have hc4 : south_pt.val = !₂[0, -1] := rfl
                 have hc3 : x.point.val ≠ !₂[0, -1] := by
                  rw [←hc4] at hc2
                  have : x.point = south_pt := Subtype.ext hc2
                  contradiction
                 exact hc3 hc2
  · intro hx
    constructor
    · have hb : -north_pt.val 0 = -0 := rfl
      have hc : (0 : ℝ) = -0 := zero_eq_neg.mpr rfl
      have hd : -north_pt.val 0 = 0 := by rw [<-hc] at hb; exact hb
      have h8 : x.point ≠ -north_pt := by
        intro h_eq
        have : x.point.val 0 = -north_pt.val 0 := congrArg (fun p => p.val 0) h_eq
        have : x.point.val 0 = 0 := by rw [hd] at this; exact this
        exact hx this
      have h6 : x ∈ (φN φₙ).source := fooN' (x.point) h8
      exact h6
    · have hb : -south_pt.val 0 = -0 := rfl
      have hc : (0 : ℝ) = -0 := zero_eq_neg.mpr rfl
      have hd : -south_pt.val 0 = 0 := by rw [<-hc] at hb; exact hb
      have h8 : x.point ≠ -south_pt := by
        intro h_eq
        have : x.point.val 0 = -south_pt.val 0 := congrArg (fun p => p.val 0) h_eq
        have : x.point.val 0 = 0 := by rw [hd] at this; exact this
        exact hx this
      have h6 : x ∈ (φN φₛ).source := fooS' (x.point) h8
      exact h6

#check PartialHomeomorph

noncomputable
def Mobius' : FiberBundleCore Pole S1 (EuclideanSpace ℝ (Fin 1)) where
  baseSet i := if i = north then (φN φₙ).source else (φN φₛ).source
  isOpen_baseSet i := by
    split
    · exact (φN φₙ).open_source
    · exact (φN φₛ).open_source
  indexAt x := if x.point = north_pt then north else south
  mem_baseSet_at := sob
  coordChange := MyCoordChange'
  coordChange_self := MyCoordChange_self'
  continuousOn_coordChange := sorry
  coordChange_comp := MyCoordChange_comp'

#synth ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

example : φ₀ = @chartAt (EuclideanSpace ℝ (Fin 1)) _ _ _ (instChartedSpaceEuclideanSpaceRealFinElemHAddNatOfNatSphere 1)
    (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))) := rfl

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
  ⟨(finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)⟩

lemma hU.source : φ₀.source = { x | x ≠ -xh } :=
  calc φ₀.source = (chartAt (EuclideanSpace ℝ (Fin 1)) xh).source := rfl
    _ = (stereographic' 1 (-xh)).source := rfl
    _ = {-xh}ᶜ := stereographic'_source (-xh)
    _ = { x | x ≠ -xh } := rfl

lemma hU.target : φ₀.target = univ := by
  calc φ₀.target = (chartAt (EuclideanSpace ℝ (Fin 1)) xh).target := rfl
    _ = (stereographic' 1 (-xh)).target := rfl
    _ = univ := stereographic'_target (-xh)

lemma hV.source : φ₁.source = { x | x ≠ -ug} :=
  calc φ₁.source = (chartAt (EuclideanSpace ℝ (Fin 1)) ug).source := rfl
    _ = (stereographic' 1 (-ug)).source := rfl
    _ = {-ug}ᶜ := stereographic'_source (-ug)
    _ = { x | x ≠ -ug } := rfl

lemma ChartChangeSmoothOn
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

lemma UVSmoothOn :
  ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (φ₁ ∘ φ₀.symm) (φ₀.target ∩ φ₀.symm ⁻¹' φ₁.source) :=
    have h1 : φ₀ ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      chart_mem_maximalAtlas xh
    have h2 : φ₁ ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      chart_mem_maximalAtlas ug
    ChartChangeSmoothOn h1 h2

lemma VUSmoothOn :
  ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (φ₀ ∘ φ₁.symm) (φ₁.target ∩ φ₁.symm ⁻¹' φ₀.source) :=
    have h1 : φ₀ ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      chart_mem_maximalAtlas xh
    have h2 : φ₁ ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      chart_mem_maximalAtlas ug
    ChartChangeSmoothOn h2 h1

noncomputable
def MyCoordChange : Fin 2 → Fin 2 →
                    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → EuclideanSpace ℝ (Fin 1) →
                    EuclideanSpace ℝ (Fin 1)
  | 0, 0, _, α => α
  | 0, 1, x, α => if (x.val 1) > 0 then α else -α
  | 1, 0, x, α => if (x.val 1) > 0 then α else -α
  | 1, 1, _, α => α

theorem MyCoordChange_self : ∀ (i : Fin 2),
    ∀ x ∈ (fun i => if i = 0 then φ₀.source else φ₁.source) i,
    ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChange i i x v = v := by
    intro i x h v
    have h : MyCoordChange i i x v = v :=
      match i with
        | 0 => rfl
        | 1 => rfl
    exact h

theorem t1001 (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) (v : EuclideanSpace ℝ (Fin 1)) :
    MyCoordChange 1 0 x (MyCoordChange 0 1 x v) = v := by
  simp_all only [MyCoordChange, Fin.isValue, ↓reduceIte, neg_neg, ite_self]

theorem t0110 (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) (v : EuclideanSpace ℝ (Fin 1)) :
    MyCoordChange 0 1 x (MyCoordChange 1 0 x v) = v := by
  simp_all [MyCoordChange]

theorem MyCoordChange_comp : ∀ (i j k : Fin 2),
  ∀ x ∈ (fun i => if i = 0 then φ₀.source else φ₁.source) i ∩
        (fun i => if i = 0 then φ₀.source else φ₁.source) j ∩
        (fun i => if i = 0 then φ₀.source else φ₁.source) k,
    ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChange j k x (MyCoordChange i j x v) = MyCoordChange i k x v := by
    intro i j k x h v
    have h : MyCoordChange j k x (MyCoordChange i j x v) = MyCoordChange i k x v :=
      match i, j, k with
        | 0, 0, 0 => rfl
        | 0, 0, 1 => rfl
        | 0, 1, 0 => t1001 x v
        | 0, 1, 1 => rfl
        | 1, 0, 0 => rfl
        | 1, 0, 1 => t0110 x v
        | 1, 1, 0 => rfl
        | 1, 1, 1 => rfl
    exact h

lemma sphere_equator_points : { x | x.val 1 = 0 } = { -xh, -ug } := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  let A := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  let B := { x : EuclideanSpace ℝ (Fin 2) | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2}
  have h1 : A = B := by
    exact EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
  have h2 : y.val ∈ A := y.prop
  have h3 : y.val ∈ B := by
    rw [h1] at h2
    exact h2
  have h4 : ∑ i : Fin 2, y.val i ^ 2 = 1 ^ 2 := by
    simp at h3
    exact h3
  have h5 : (y.val 0) ^ 2 + (y.val 1) ^ 2 = 1 := by
    rwa [Fin.sum_univ_two, one_pow] at h4

  have hf1 (h : y.val 1 ^ 2 + 1 - 1 = 0) : y.val 1 ^ 2 = 0 := by
    have h1 : (y.val 1 ^ 2 + 1) + (- 1) = 0 := h
    have h2 : y.val 1 ^ 2 + (1 - 1) = (y.val 1 ^ 2 + 1) + (- 1) := by rw [add_assoc, sub_eq_add_neg]
    have h3 : y.val 1 ^ 2 + (1 - 1) = y.val 1 ^ 2 := by rw [sub_self, add_zero]
    have h4 : y.val 1 ^ 2 = 0 := by
      calc y.val 1 ^ 2 = y.val 1 ^ 2 + (1 - 1) := by rw [h3]
                   _ = (y.val 1 ^ 2 + 1) + (- 1) := by rw [h2]
                   _ = 0 := by rw [h1]
    exact h4

  have h6 : y.val 1 = 0 ↔ y.val 0 = 1 ∨ y.val 0 = -1 :=
    ⟨ fun h => by
      have gg : (y.val 0) ^ 2 = 1 ↔ y.val 0 = 1 ∨ y.val 0 = -1 := sq_eq_one_iff
      rw [h, zero_pow two_ne_zero, add_zero] at h5
      rwa [gg] at h5,

    fun h => by
      cases h with
      | inl pos1 =>
        rw [pos1, one_pow, ←sub_eq_zero, add_comm] at h5
        exact sq_eq_zero_iff.mp (hf1 h5)
      | inr neg1 =>
        rw [neg1, neg_one_sq, ←sub_eq_zero, add_comm] at h5
        exact sq_eq_zero_iff.mp (hf1 h5)⟩

  have h7a : y.val 1 = 0 -> y.val = xh.val ∨ y.val = ug.val := by
    intro hy1
    have h1 : y.val 0 = 1 ∨ y.val 0 = -1 := h6.mp hy1
    cases h1 with
    | inl hpos => have h5 : y.val = xh.val := by
                    ext i
                    fin_cases i
                    · simp [hpos]; rfl
                    · simp [hy1]; rfl
                  exact Or.inl h5
    | inr hneg => have h5 : y.val = ug.val := by
                    ext i
                    fin_cases i
                    · simp [hneg]; rfl
                    · simp [hy1]; rfl
                  exact Or.inr h5

  have h7b : y.val = xh.val ∨ y.val = ug.val -> y.val 1 = 0 := by
    intro h
    cases h with
    | inl left =>
      rw [left]; rfl
    | inr right =>
      rw [right]; rfl

  have h8 : y.val 1 = 0 <-> y.val = xh.val ∨ y.val = ug.val := ⟨h7a, h7b⟩
  have h9 : y.val = (xh).val -> y = xh := Subtype.eq
  have ha : y.val = (ug).val -> y = ug := Subtype.eq
  have hb : y = xh -> y.val = (xh).val := by intro h; rw[h]
  have hc : y = ug -> y.val = (ug).val := by intro h; rw [h]
  have hd : -!₂[(1 : ℝ), 0] = !₂[-1, 0] := by rw [myNeg 1 0]; simp
  have he : -xh.val = ug.val := by exact hd
  have hf : -xh = ug := Subtype.eq he
  have hg : xh = -ug := by rw [<-hf]; simp
  have hh : y.val 1 = 0 ↔ y = xh ∨ y = ug := by
    rw [h8]
    constructor
    · intro h
      cases h with
      | inl hxh => left; exact h9 hxh
      | inr hug => right; exact ha hug
    · intro h
      cases h with
      | inl hxh => left; rw [← hb hxh]
      | inr hug => right; rw [← hc hug]

  have hi : y.val 1 = 0 ↔ y = -xh ∨ y = -ug := by
    rw [hh]
    constructor
    · intro h
      have chit : y = -ug ∨ y = -xh := by cases h with
      | inl hxh => left; rw [hg] at hxh; exact hxh
      | inr hug => right; rw [<-hf] at hug; exact hug
      exact or_comm.mp chit
    · intro h
      cases h with
      | inl hxh_neg => right; rw [hf] at hxh_neg; exact hxh_neg
      | inr hug_neg => left; rw [← hf, neg_neg] at hug_neg; exact hug_neg
  exact hi

theorem SulSource : φ₀.source ∩ φ₁.source = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := by
  ext y

  have h1 : { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } = { x | x.val 1 = 0 }ᶜ := by
    ext y
    simp
    exact not_congr eq_comm

  have h2 : { x | x ≠ -xh } ∩ { x | x ≠ -ug } = { -xh, -ug }ᶜ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact not_or.symm

  have ha : φ₀.source ∩ φ₁.source = { x | x ≠ -xh } ∩ { x | x ≠ -ug } := by rw [hU.source, hV.source]

  have hq : φ₀.source ∩ φ₁.source = { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := by
    calc φ₀.source ∩ φ₁.source = { x | x ≠ -xh } ∩ { x | x ≠ -ug } := ha
         _ = { -xh, -ug }ᶜ := h2
         _ = { x | x.val 1 = 0 }ᶜ := by rw [← sphere_equator_points]
         _ =  { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := h1.symm
  simp [hq]

def s1 : Set ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) := { x | 0 < x.1.val 1 }

lemma fooo : {(x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) | x.val 1 > 0} ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))) ⊆ { x | 0 < x.1.val 1 } := by
  intro x hx
  exact hx.1

lemma barr : { x | 0 < x.1.val 1 } ⊆ {(x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) | x.val 1 > 0} ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))) := by
  intro x hx
  exact ⟨hx, trivial⟩

theorem tOpen : IsOpen { x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 > 0 } :=
  isOpen_induced_iff.mpr ⟨{ x : EuclideanSpace ℝ (Fin 2) | x 1 > 0 },
    isOpen_lt continuous_const (continuous_apply 1), rfl⟩

lemma s1_is_open : IsOpen s1 := by
  have h2 : IsOpen ({ x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 > 0 }×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := tOpen.prod isOpen_univ
  rw [HasSubset.Subset.antisymm fooo barr] at h2
  exact h2

def s2 : Set ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) := { x | 0 > x.1.val 1 }

lemma foo' : {(x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) | x.val 1 < 0} ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))) ⊆ { x | 0 > x.1.val 1 } := by
  intro x hx
  exact hx.1

lemma bar' : { x | 0 > x.1.val 1 } ⊆ {(x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) | x.val 1 < 0} ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))) := by
  intro x hx
  exact ⟨hx, trivial⟩

theorem tOpen' : IsOpen { x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 < 0 } := by
  have h2 (i : Fin 2) : Continuous fun (x : EuclideanSpace ℝ (Fin 2)) => x i := continuous_apply i
  exact isOpen_induced_iff.mpr ⟨{ x : EuclideanSpace ℝ (Fin 2) | x 1 < 0 },
    isOpen_lt (h2 1) continuous_const, rfl⟩

lemma s2_is_open : IsOpen s2 := by
  have h2 : IsOpen ({ x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 < 0 }×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := tOpen'.prod isOpen_univ
  rw [HasSubset.Subset.antisymm foo' bar'] at h2
  exact h2

theorem t00 : ContinuousOn (fun p => MyCoordChange 0 0 p.1 p.2) (φ₀.source ×ˢ univ) := continuousOn_snd

theorem t01 : ContinuousOn (fun p => MyCoordChange 0 1 p.1 p.2) ((φ₀.source ∩ φ₁.source) ×ˢ univ) := by
  have h1 : (φ₀.source ∩ φ₁.source) = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := SulSource
  let f : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
  | (x, α) =>if (x.val 1) > 0 then α else -α
  let s1 : Set ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) := { x | 0 < x.1.val 1 }
  let s2 : Set ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) := { x | 0 > x.1.val 1 }
  have h6 : (s1 ∪ s2) = (({x | x.val 1 > 0} ∪ {x | x.val 1 < 0}) ×ˢ univ) := by
    ext ⟨p, v⟩
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, Set.mem_setOf_eq]
    exact Iff.rfl

  have hz1 : ContinuousOn f s1 := by
    apply continuous_snd.continuousOn.congr
    intro x hx
    dsimp [f, s1] at hx ⊢
    rw [if_pos hx]
  have hz2 : ContinuousOn f s2 := by
    apply continuous_snd.neg.continuousOn.congr
    intro x hx
    dsimp [f, s2] at hx ⊢
    rw [if_neg (not_lt_of_gt hx)]
  rw [h1, ← h6]
  exact ContinuousOn.union_of_isOpen hz1 hz2 s1_is_open s2_is_open

theorem t10 : ContinuousOn (fun p => MyCoordChange 1 0 p.1 p.2) ((φ₁.source ∩ φ₀.source) ×ˢ univ) := by
  have h1 : MyCoordChange 1 0 = MyCoordChange 0 1 := rfl
  have h2 : (fun (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) => MyCoordChange 1 0 p.1 p.2) = (fun p => MyCoordChange 0 1 p.1 p.2) :=
    funext (fun x => by rw [h1])
  rw [h2, inter_comm]
  exact t01

theorem t11 : ContinuousOn (fun p => MyCoordChange 0 0 p.1 p.2) (φ₁.source ×ˢ univ) := by
  have h1 : (fun (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) =>
    MyCoordChange 0 0 p.fst p.snd) = (fun p => p.snd) := by rfl
  rw [h1]
  exact continuousOn_snd

theorem MyContinuousOn_coordChange : ∀ (i j : Fin 2), ContinuousOn (fun p => MyCoordChange i j p.1 p.2)
  (((fun i => if i = 0 then φ₀.source else φ₁.source) i ∩
      (fun i => if i = 0 then φ₀.source else φ₁.source) j) ×ˢ
    univ) := by
    intro i j
    fin_cases i
    · fin_cases j
      · simp [t00]
      · exact t01
    · fin_cases j
      · exact t10
      · simp; exact t11

theorem my_mem_baseSet_at : ∀ (x : ↑(Metric.sphere 0 1)),
  x ∈ (fun (i : Fin 2) ↦ if i = 0 then φ₀.source else φ₁.source) ((fun x ↦ if x.val 0 > 0 then 0 else 1) x):= by
  intro x
  by_cases h : (x.val 0) > 0
  case pos =>
    have h5 : xh.val 0 = 1 := rfl
    have h7 : x ≠ -xh := by
      intro h_eq
      have h_contra : x.val 0 = -xh.val 0 := congrFun (congrArg Subtype.val h_eq) 0
      rw [h5] at h_contra
      linarith
    have h2 : (fun x ↦ if x.val 0 > 0 then (0 : Fin 2) else 1) x = 0 := if_pos h
    have h3 :
      (fun (i : Fin 2) ↦ if i = 0 then φ₀.source else φ₁.source) ((fun x ↦ if x.val 0 > 0 then 0 else 1) x) = φ₀.source := by
        rw [h2]
        exact if_pos rfl
    rw [h3, hU.source]
    exact h7
  case neg =>
    have h1 : ug.val 0 = -1 := rfl
    have h7 : x ≠ -ug := by
      intro h_eq
      have h_val_eq : x.val = -ug.val := congrArg Subtype.val h_eq
      have h_contra : x.val 0 = -ug.val 0 := congrFun h_val_eq 0
      rw [h1] at h_contra
      linarith
    have h2 : (fun x ↦ if x.val 0 > 0 then (0 : Fin 2) else 1) x = 1 := if_neg h
    have h3 : (fun (i : Fin 2) ↦ if i = 0 then φ₀.source else φ₁.source) ((fun x ↦ if x.val 0 > 0 then 0 else 1) x) =
              φ₁.source := by
                rw [h2]
                exact if_neg (by exact one_ne_zero)
    rw [h3, hV.source]
    exact h7

open Bundle

noncomputable
def Mobius : FiberBundleCore (Fin 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) where
  baseSet i := if i = 0 then φ₀.source else φ₁.source
  isOpen_baseSet i := by
    split
    · exact φ₀.open_source
    · exact φ₁.open_source
  indexAt x := if (x.val 0) > 0 then 0 else 1
  mem_baseSet_at := my_mem_baseSet_at
  coordChange := MyCoordChange
  coordChange_self := MyCoordChange_self
  continuousOn_coordChange := MyContinuousOn_coordChange
  coordChange_comp := MyCoordChange_comp

noncomputable
def ψ₀ :=(Mobius.localTriv 0).toPartialHomeomorph ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
noncomputable
def ψ₁ :=(Mobius.localTriv 1).toPartialHomeomorph ≫ₕ (φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

def totalAtlas : Set (PartialHomeomorph Mobius.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :=
  { ψ₀, ψ₁ }

#synth ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))

#synth ChartedSpace ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))

noncomputable
instance (m n : ℕ) : ChartedSpace ((EuclideanSpace ℝ (Fin (n + m)))) (EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin m))) := by
  have h1 : EuclideanSpace ℝ (Fin (n + m)) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) := EuclideanSpace.finAddEquivProd
  have h2 : EuclideanSpace ℝ (Fin (n + m)) ≃ₜ EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=  ContinuousLinearEquiv.toHomeomorph h1
  let x := (EuclideanSpace.finAddEquivProd : EuclideanSpace ℝ (Fin (n + m)) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
  let y := ContinuousLinearEquiv.toHomeomorph x
  let z := Homeomorph.toPartialHomeomorph y
  have hz : z.symm.source = univ := rfl
  exact PartialHomeomorph.singletonChartedSpace z.symm hz

#synth IsManifold (𝓡 1) 0 (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

noncomputable
def baseChartAt := (fun (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ) => if x.val 0 > 0 then φ₀ else φ₁)

noncomputable instance Mobius.chartedSpaceBase : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
{ atlas := baseAtlas,
  chartAt := baseChartAt,
  mem_chart_source := by
    intro x
    dsimp [baseChartAt]
    split_ifs with h
    · have h1 : x.val 0 > 0 := h
      have h2 : φ₀.source = { x | x ≠ -xh } := hU.source
      rw [h2]
      intro contra
      have h3 : x.val = (-xh).val := congr_arg Subtype.val contra
      have h4 : x.val 0 = -1 := by calc
        x.val 0 = (-xh).val 0 := by rw [<-h3]
        _ = -1 := rfl
      have h5 : x.val 0 < 0 := by rw [h4]; exact neg_one_lt_zero
      have h6 : ¬ x.val 0 > 0 := not_lt_of_gt h5
      exact absurd h1 h6
    · have h1 : ¬ x.val 0 > 0 := h
      have h2 : φ₁.source = { x | x ≠ -ug } := hV.source
      rw [h2]
      intro contra
      have h3 : x.val = (-ug).val := congr_arg Subtype.val contra
      have h4 : x.val 0 = 1 := by calc
        x.val 0 = (-ug).val 0 := by rw [<-h3]
        _ = -(-1) := rfl
        _ = 1 := by rw [neg_eq_iff_eq_neg]
      have h5 : x.val 0 > 0 := by rw [h4]; exact Real.zero_lt_one
      exact absurd h5 h1
  chart_mem_atlas := by
    intro x
    dsimp [baseChartAt, baseAtlas]
    split_ifs with h
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _) }

lemma SmoothInnerPre : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (↑φ₁ ∘ ↑φ₀.symm)  (φ₀ '' ({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 })) := by
  have h1 : (φ₀.target ∩ ↑φ₀.symm ⁻¹' φ₁.source) = φ₀ '' (φ₀.source ∩ φ₁.source) := by
    exact Eq.symm (PartialHomeomorph.image_source_inter_eq' φ₀ φ₁.source)
  have h2 : φ₀.source ∩ φ₁.source = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := SulSource
  rw [<-h2]
  rw [<-h1]
  exact UVSmoothOn

lemma SmoothInnerPre' : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (↑φ₀ ∘ ↑φ₁.symm)  (φ₁ '' ({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 })) := by
  have h1 : (φ₁.target ∩ ↑φ₁.symm ⁻¹' φ₀.source) = φ₁ '' (φ₁.source ∩ φ₀.source) := by
    exact Eq.symm (PartialHomeomorph.image_source_inter_eq' φ₁ φ₀.source)
  have h2 : φ₀.source ∩ φ₁.source = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := SulSource
  have h3 :  (φ₀.source ∩ φ₁.source)= (φ₁.source ∩ φ₀.source) := inter_comm φ₀.source φ₁.source
  rw [<-h3] at h1
  rw [<-h2]
  rw [<-h1]
  exact VUSmoothOn

lemma SmoothInnerPreOn : (φ₀ '' ({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 }))  = (φ₀.symm ≫ₕ φ₁).source := by
  have ha : φ₀ '' (φ₀.source ∩ φ₁.source) = φ₀.target ∩ ↑φ₀.symm ⁻¹' φ₁.source := PartialHomeomorph.image_source_inter_eq' φ₀ φ₁.source
  have h0 : ((φ₀.symm ≫ₕ φ₁).source) =  φ₀.target ∩ ↑φ₀.symm ⁻¹' φ₁.source := by
    exact rfl
  have h2 :  ((φ₀.symm ≫ₕ φ₁).source) = φ₀ '' (φ₀.source ∩ φ₁.source) := by
    rw [h0, ha]
  have h1 : (({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 })) = φ₀.source ∩ φ₁.source := by
    rw [<-SulSource]
  have h3 : φ₀ '' ({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 }) = φ₀ '' (φ₀.source ∩ φ₁.source) := by
    rw [h1]
  rw [h2, h3]

lemma SmoothInnerPreOn' : (φ₁ '' ({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 }))  = (φ₁.symm ≫ₕ φ₀).source := by
  have ha : φ₁ '' (φ₁.source ∩ φ₀.source) = φ₁.target ∩ ↑φ₁.symm ⁻¹' φ₀.source := PartialHomeomorph.image_source_inter_eq' φ₁ φ₀.source
  have h0 : ((φ₁.symm ≫ₕ φ₀).source) =  φ₁.target ∩ ↑φ₁.symm ⁻¹' φ₀.source := by
    exact rfl
  have hb :  (φ₀.source ∩ φ₁.source)= (φ₁.source ∩ φ₀.source) := inter_comm φ₀.source φ₁.source
  have h2 :  ((φ₁.symm ≫ₕ φ₀).source) = φ₁ '' (φ₀.source ∩ φ₁.source) := by
    rw [h0, hb, ha]
  have h1 : (({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 })) = φ₀.source ∩ φ₁.source := by
    rw [<-SulSource]
  have h3 : φ₁ '' ({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 }) = φ₁ '' (φ₀.source ∩ φ₁.source) := by
    rw [h1]
  rw [h2, h3]

lemma SmoothInner01 : ContDiffOn ℝ ⊤ (↑(φ₀.symm ≫ₕ φ₁)) ((φ₀.symm ≫ₕ φ₁).source) := by
  rw [<-SmoothInnerPreOn]
  exact contMDiffOn_iff_contDiffOn.mp SmoothInnerPre

lemma SmoothInner10 : ContDiffOn ℝ ⊤ (↑(φ₁.symm ≫ₕ φ₀)) ((φ₁.symm ≫ₕ φ₀).source) := by
  rw [<-SmoothInnerPreOn']
  exact contMDiffOn_iff_contDiffOn.mp SmoothInnerPre'

lemma SmoothInner00 : ∀ φ₀ ∈ baseAtlas, ContDiffOn ℝ ⊤ (↑(φ₀.symm ≫ₕ φ₀)) (φ₀.symm ≫ₕ φ₀).source := by
  intro φ₀ hφ₀ x hx
  have h4 : EqOn (↑(φ₀.symm ≫ₕ φ₀) : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) id ((φ₀.symm ≫ₕ φ₀)).source := by
    intro y hy
    have h5 : y ∈ φ₀.target := by exact mem_of_mem_inter_left hy
    have h6 : φ₀ (φ₀.symm y) = y := PartialHomeomorph.right_inv φ₀ h5
    exact h6
  have h5 :ContDiffOn ℝ ⊤ id (φ₀.symm ≫ₕ φ₀).source  := by
    exact contDiffOn_id
  have h6 : ContDiffOn ℝ ⊤ (↑(φ₀.symm ≫ₕ φ₀)) (φ₀.symm ≫ₕ φ₀).source := by exact ContDiffOn.congr contDiffOn_id h4
  exact h6 x hx

lemma simpleSmooth : ∀ (e e' : PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1))),
    e ∈ baseAtlas →
    e' ∈ baseAtlas →
    ContDiffOn ℝ ⊤ (↑(e.symm ≫ₕ e')) ((e.symm ≫ₕ e').source) := by
  intros e e' he he'
  simp only [baseAtlas, Set.mem_insert_iff, Set.mem_singleton_iff] at he he'
  rcases he with (rfl | rfl)
  · rcases he' with (rfl | rfl)
    · exact SmoothInner00 φ₀ (by rw [baseAtlas]; simp)
    · exact SmoothInner01
  · rcases he' with (rfl | rfl)
    · exact SmoothInner10
    · exact SmoothInner00 φ₁ (by rw [baseAtlas]; simp)

lemma atlas_eq : @atlas (EuclideanSpace ℝ (Fin 1)) _ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _ Mobius.chartedSpaceBase =
  baseAtlas := rfl

lemma wrappedSmooth : ∀ (e e' : PartialHomeomorph ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) (EuclideanSpace ℝ (Fin 1))),
    e ∈ atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)  →
      e' ∈ atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)  →
        ContDiffOn ℝ ⊤ (↑(𝓡 1) ∘ ↑(e.symm ≫ₕ e') ∘ ↑(𝓡 1).symm)
          (↑(𝓡 1).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range ↑(𝓡 1)) := by
  intro e e' he he'
  have h1 : e ∈ baseAtlas := by
    rw [atlas_eq] at he
    exact he
  have h2 : e' ∈ baseAtlas := by
    rw [atlas_eq] at he'
    exact he'
  have h3 : ContDiffOn ℝ ⊤ (↑(e.symm ≫ₕ e')) (e.symm ≫ₕ e').source := simpleSmooth e e' h1 h2
  have h4 : ContDiffOn ℝ ⊤ (↑(𝓡 1)) (range ↑(𝓡 1)) := by
    exact contDiffOn_id
  have h5 : ContDiffOn ℝ ⊤ (↑(𝓡 1).symm) (range ↑(𝓡 1).symm) := by
    exact contDiffOn_id

  have h6 : ContDiffOn ℝ ⊤ ((↑(𝓡 1) ∘ ↑(e.symm ≫ₕ e')) ∘ ↑(𝓡 1).symm)
    (range ↑(𝓡 1).symm ∩ ↑(𝓡 1).symm ⁻¹' ((e.symm ≫ₕ e').source ∩ ↑(e.symm ≫ₕ e') ⁻¹' range ↑(𝓡 1))) :=
     ContDiffOn.comp_inter (ContDiffOn.comp_inter h4 h3) h5

  have h7 : (↑(𝓡 1).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range ↑(𝓡 1)) =
            (range ↑(𝓡 1).symm ∩ ↑(𝓡 1).symm ⁻¹' ((e.symm ≫ₕ e').source ∩ ↑(e.symm ≫ₕ e') ⁻¹' range ↑(𝓡 1))) := by
    simp

  rw [<-h7] at h6
  exact h6

#synth IsManifold (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
#synth @IsManifold ℝ _ _ _ _ _ _ (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _ Mobius.chartedSpaceBase

instance Circle.Smooth : @IsManifold ℝ _ _ _ _ _ _ (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _ Mobius.chartedSpaceBase := by
  apply isManifold_of_contDiffOn
  exact wrappedSmooth

#synth IsManifold (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
#synth @IsManifold ℝ _ _ _ _ _ _ (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _ Mobius.chartedSpaceBase

noncomputable
instance : ChartedSpace ((EuclideanSpace ℝ (Fin 1)) × (EuclideanSpace ℝ (Fin 1)))
                       (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
 := ChartedSpace.comp
  (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))
  (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)

noncomputable
instance (m n : ℕ) : ChartedSpace ((EuclideanSpace ℝ (Fin (n + m)))) (EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin m))) := by
  have h1 : EuclideanSpace ℝ (Fin (n + m)) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) := EuclideanSpace.finAddEquivProd
  have h2 : EuclideanSpace ℝ (Fin (n + m)) ≃ₜ EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=  ContinuousLinearEquiv.toHomeomorph h1
  let x := (EuclideanSpace.finAddEquivProd : EuclideanSpace ℝ (Fin (n + m)) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
  let y := ContinuousLinearEquiv.toHomeomorph x
  let z := Homeomorph.toPartialHomeomorph y
  have hz : z.symm.source = univ := rfl
  exact PartialHomeomorph.singletonChartedSpace z.symm hz

noncomputable
instance : ChartedSpace (EuclideanSpace ℝ (Fin (1 + 1))) (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) := by
  exact ChartedSpace.comp
    (EuclideanSpace ℝ (Fin (1 + 1)))
    ((EuclideanSpace ℝ (Fin 1)) × (EuclideanSpace ℝ (Fin 1)))
    (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)

#synth IsManifold (𝓡 2) 0 (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
#synth IsManifold (𝓡 2) ⊤ (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)

noncomputable
def totalChartAt : Mobius.TotalSpace → PartialHomeomorph Mobius.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) :=
  fun x ↦
    let _ := Mobius.chartedSpaceBase
    let φ := chartAt (EuclideanSpace ℝ (Fin 1)) x.proj
    let i := Mobius.indexAt x.proj
    (Mobius.localTriv i).toPartialHomeomorph ≫ₕ (φ.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

noncomputable instance Mobius.chartedSpaceTotal :
  ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) Mobius.TotalSpace :=
  { atlas := totalAtlas
    chartAt := totalChartAt
    mem_chart_source := by
      intro x
      dsimp [totalChartAt]
      let φ := chartAt (EuclideanSpace ℝ (Fin 1)) x.proj
      let i := Mobius.indexAt x.proj
      apply And.intro
      · exact (FiberBundleCore.mem_localTrivAt_source Mobius x x.proj).mpr
              (FiberBundle.mem_baseSet_trivializationAt' x.proj)
      · refine mem_preimage.mpr ?_
        apply Set.mem_prod.mpr
        constructor
        · have : (Mobius.localTrivAt x.proj x).1 = x.proj := rfl
          rw [this]
          exact @mem_chart_source _ _ _ _ Mobius.chartedSpaceBase x.proj
        · exact Set.mem_univ _
    chart_mem_atlas := by
      rintro ⟨x, ξ⟩
      let _ := Mobius.chartedSpaceBase
      dsimp [totalChartAt, totalAtlas]
      let φ := chartAt (EuclideanSpace ℝ (Fin 1)) x
      let i := Mobius.indexAt x
      have h8 : Mobius.localTrivAt x =  Mobius.localTriv (if (x.val 0) > 0 then 0 else 1) := rfl

      cases (Classical.em ((x.val 0) > 0)) with
      | inl hx => have h1 : (if (x.val 0) > 0 then φ₀ else φ₁) = φ₀ := if_pos hx
                  have h3 : Mobius.localTriv (if (x.val 0) > 0 then 0 else 1) = Mobius.localTriv 0 := by
                   congr
                   exact if_pos hx
                  have h5 : Mobius.localTrivAt x = Mobius.localTriv 0 := by
                    rw [h8, h3]
                  have h6 : (Mobius.localTriv 0).toPartialHomeomorph ≫ₕ
                            φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) ∈ totalAtlas := by simp [totalAtlas]
                                                                                                           exact Or.symm (Or.inr rfl)
                  have h7 : (Mobius.localTrivAt x).toPartialHomeomorph ≫ₕ
                            (chartAt (EuclideanSpace ℝ (Fin 1)) x).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) ∈ totalAtlas := by
                    rw [h5]
                    exact mem_of_eq_of_mem (congrArg (Mobius.localTriv 0).trans
                      (congrFun (congrArg PartialHomeomorph.prod h1) (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))) h6
                  exact h7
      | inr hx => have h1 : (if (x.val 0) > 0 then φ₀ else φ₁) = φ₁ := if_neg hx
                  have h3 : Mobius.localTriv (if (x.val 0) > 0 then 0 else 1) = Mobius.localTriv 1 := by
                    congr
                    exact if_neg hx
                  have h5 : Mobius.localTrivAt x = Mobius.localTriv 1 := by
                    rw [h8, h3]
                  have h6 : (Mobius.localTriv 1).toPartialHomeomorph ≫ₕ
                            φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) ∈ totalAtlas := by simp [totalAtlas]
                                                                                                           exact Or.symm (Or.inl (by exact rfl))
                  have h7 : (Mobius.localTrivAt x).toPartialHomeomorph ≫ₕ
                            (chartAt (EuclideanSpace ℝ (Fin 1)) x).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) ∈ totalAtlas := by
                    rw [h5]
                    exact mem_of_eq_of_mem (congrArg (Mobius.localTriv 1).trans
                      (congrFun (congrArg PartialHomeomorph.prod h1) (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))) h6
                  exact h7
   }

lemma SmoothInnerTot00 : ∀ ψ₀ ∈ totalAtlas, ContDiffOn ℝ ⊤ (↑(ψ₀.symm ≫ₕ ψ₀)) (ψ₀.symm ≫ₕ ψ₀).source := by
  intro ψ₀ hψ₀ x hx
  have h4 : EqOn (↑(ψ₀.symm ≫ₕ ψ₀)) id ((ψ₀.symm ≫ₕ ψ₀)).source := by
    intro y hy
    have h5 : y ∈ ψ₀.target := by exact mem_of_mem_inter_left hy
    have h6 : ψ₀ (ψ₀.symm y) = y := PartialHomeomorph.right_inv ψ₀ h5
    exact h6
  have h5 :ContDiffOn ℝ ⊤ id (ψ₀.symm ≫ₕ ψ₀).source  := by
    exact contDiffOn_id
  have h6 : ContDiffOn ℝ ⊤ (↑(ψ₀.symm ≫ₕ ψ₀)) (ψ₀.symm ≫ₕ ψ₀).source := by exact ContDiffOn.congr contDiffOn_id h4
  exact h6 x hx

lemma localTrivTransition_eq_coordChange (i j : Fin 2)
  {x : Mobius.Base} {v : (EuclideanSpace ℝ (Fin 1))} (hx : x ∈ Mobius.baseSet i ∩ Mobius.baseSet j) :
  ((Mobius.localTriv i).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv j).toPartialHomeomorph) (x, v) =
    (x, Mobius.coordChange i j x v) := by
  simp
  have ha : x ∈ Mobius.baseSet (Mobius.indexAt x) := Mobius.mem_baseSet_at x
  have hd : x ∈ (Mobius.baseSet i ∩ Mobius.baseSet (Mobius.indexAt x)) ∩ Mobius.baseSet j :=
  ⟨⟨hx.1, ha⟩, hx.2⟩
  have h2 : Mobius.coordChange (Mobius.indexAt x) j x (Mobius.coordChange i (Mobius.indexAt x) x v) =
            Mobius.coordChange i j x v :=  Mobius.coordChange_comp i (Mobius.indexAt x) j x hd v
  exact h2

lemma upperInclusion : ∀ (x : Mobius.Base) (v : EuclideanSpace ℝ (Fin 1)),
    (x.val 1) > 0 →
    ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v)
      = (x, v) := by
    intros x v ha
    have hx : x ∈ { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := Or.inl ha
    have hx' : x ∈ φ₀.source ∩ φ₁.source := SulSource.symm ▸ hx
    have h1 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) =
              (x, Mobius.coordChange 0 1 x v) := localTrivTransition_eq_coordChange 0 1 hx'
    have h2 : Mobius.coordChange 0 1 x v = if (x.val 1) > 0 then v else -v := rfl
    have h3 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) =
    (x, if (x.val 1) > 0 then v else -v) := by
      rw [h2] at h1
      exact h1
    have h4 : (x.val 1) > 0 → (if (x.val 1) > 0 then v else -v) = v := by
      intro h41
      rw [if_pos h41]
    rw [h3, h4]
    exact ha

lemma upperContMDiff : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
      ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph)
      {x : ↑(Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1) | (x.1.val 1) > 0} := by
      apply ContMDiffOn.congr
      · exact contMDiffOn_id
      · intro y hy
        obtain ⟨x, v⟩ := y
        dsimp at hy
        exact upperInclusion x v hy

lemma lowerInclusion : ∀ (x : Mobius.Base) (v : EuclideanSpace ℝ (Fin 1)),
    (x.val 1) < 0 →
    ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v)
      = (x, -v) := by
    intros x v ha
    have hx : x ∈ { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := Or.inr ha
    have hx' : x ∈ φ₀.source ∩ φ₁.source := SulSource.symm ▸ hx
    have h1 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) =
              (x, Mobius.coordChange 0 1 x v) := localTrivTransition_eq_coordChange 0 1 hx'
    have h2 : Mobius.coordChange 0 1 x v = if (x.val 1) > 0 then v else -v := rfl
    have h3 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) =
    (x, if (x.val 1) > 0 then v else -v) := by
      rw [h2] at h1
      exact h1
    have h4 : ¬ (x.val 1) > 0 → (if (x.val 1) > 0 then v else -v) = -v := by
      intro h41
      rw [if_neg h41]
    rw [h3, h4]
    exact not_lt_of_gt ha

lemma lowerContMDiff : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
      ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph)
      {x : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) | (x.1.val 1) < 0} := by

      have h1a : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (fun x ↦ -id x) (univ : Set (EuclideanSpace ℝ (Fin 1))) := contMDiffOn_id.neg
      have hz : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ id {x : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | (x.val 1) < 0} := contMDiffOn_id

      let f1 : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) → ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) :=
        Prod.map id fun x ↦ -id x
      let f2 : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) → ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) :=
        fun x ↦ match x with
        | (x, v) => (x, -v)

      have h2 : f1 = f2 := by
        exact rfl

      have h2c : ∀ y ∈ {x | x.val 1 < 0} ×ˢ univ, f1 y = Prod.map id (fun x ↦ -id x) y := by
            intro y hy
            dsimp at hy
            exact rfl

      have h1b : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤ (Prod.map id fun x ↦ -id x)
       ({x : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | (x.val 1) < 0} ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := hz.prodMap h1a

      have h3 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤ f1 ({x | x.val 1 < 0} ×ˢ univ) := ContMDiffOn.congr h1b h2c

      have h1 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
        (fun (x, v) => (x, -v)) {x : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) | (x.1.val 1) < 0} := by
          rw [h2] at h3
          have h1z :  ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤ f2 ({x | x.val 1 < 0} ×ˢ univ) := h3

          have h1y : ContMDiffOn _ _ ⊤ f2 {x | x.1.val 1 < 0} :=
           h1z.mono (by
            intro x hx
            exact ⟨hx, Set.mem_univ x.2⟩)
          exact h1y

      apply ContMDiffOn.congr
      · exact h1
      · intro y hy
        obtain ⟨x, v⟩ := y
        dsimp at hy
        exact lowerInclusion x v hy

#check ContMDiffOn.union_of_isOpen

open Set

lemma bothContMDiff : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
      ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph)
      {x : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) | (x.1.val 1) > 0 ∨ (x.1.val 1) < 0} := by
  let U := {x : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) | x.1.val 1 > 0}
  let V := {x : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) | x.1.val 1 < 0}
  let f := ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph)
  have h1 : ContMDiffOn _ _ ⊤ f (U ∪ V) :=
    ContMDiffOn.union_of_isOpen upperContMDiff lowerContMDiff s1_is_open s2_is_open
  exact h1

def s' := (↑(φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' {x | x.1.val 1 > 0 ∨ (x.1.val 1) < 0})

#check PartialHomeomorph.trans_source
#check PartialHomeomorph.image_source_eq_target
#check PartialHomeomorph.image_source_inter_eq'
#check PartialHomeomorph.prod_source
#check PartialHomeomorph.symm_source
#check PartialHomeomorph.trans_target
#check PartialHomeomorph.image_eq_target_inter_inv_preimage

noncomputable
def ζ₀ := (Mobius.localTriv 0).toPartialHomeomorph
noncomputable
def ξ₀ := φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))
noncomputable
def ζ₁ := (Mobius.localTriv 1).toPartialHomeomorph
noncomputable
def ξ₁:= φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))

#check ξ₀.target
#check (ζ₀ ≫ₕ ξ₀).target
#check ξ₀.symm ⁻¹' ζ₀.target

example : (ψ₀.symm ≫ₕ ψ₁).source = ψ₀.symm.source ∩ ψ₀.symm ⁻¹' ψ₁.source := by
  exact PartialHomeomorph.trans_source ψ₀.symm ψ₁

example : (ζ₀ ≫ₕ ξ₀).target =
          ξ₀.target ∩
          ξ₀.symm ⁻¹' ζ₀.target :=
           PartialHomeomorph.trans_target ζ₀ ξ₀

example : ξ₀.target =
          φ₀.target ×ˢ (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))).target := by
  exact PartialHomeomorph.prod_target φ₀ (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))

example : ξ₀.target =
          φ₀.target ×ˢ univ := by
  exact PartialHomeomorph.prod_target φ₀ (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))

example : ξ₀ '' ζ₀.target =
 ξ₀.target ∩
  ξ₀.symm ⁻¹' ζ₀.target := by
  have h1 : ζ₀.target ⊆ ξ₀.source := by
    unfold ζ₀ ξ₀
    intro p hp
    simp only [PartialHomeomorph.prod_toPartialEquiv, PartialHomeomorph.refl_partialEquiv,
               PartialEquiv.prod_source, PartialEquiv.refl_source, mem_prod, mem_univ, and_true]
    exact hp.1
  exact PartialHomeomorph.image_eq_target_inter_inv_preimage ξ₀ h1

#check (Mobius.localTriv 0).toPartialHomeomorph.target
#check (Mobius.localTriv 0).target
#check (Mobius.localTriv 0).baseSet
#check (Mobius.localTriv 0).open_source

example : (Mobius.localTriv 0).target = {p | p.1 ∈ φ₀.source} := by
  ext p
  simp only [FiberBundleCore.proj, Fin.isValue, FiberBundleCore.mem_localTriv_target, mem_setOf_eq]
  rfl

example : ζ₀.target = {p | p.1 ∈ φ₀.source} := by
  unfold ζ₀
  ext p
  simp
  exact MapsTo.mem_iff (fun ⦃x⦄ a ↦ a) fun ⦃x⦄ a ↦ a

example : ζ₀.target ⊆ ξ₀.source := by
  unfold ζ₀ ξ₀
  intro p hp
  simp only [PartialHomeomorph.prod_toPartialEquiv, PartialHomeomorph.refl_partialEquiv,
             PartialEquiv.prod_source, PartialEquiv.refl_source, mem_prod, mem_univ, and_true]
  exact hp.1

example : ψ₁.source = { z : Mobius.TotalSpace | z.1 ∈ φ₁.source } := by
  unfold ψ₁
  ext z
  simp
  exact fun a ↦ a

example : (ζ₀ ≫ₕ ξ₀).symm = ξ₀.symm ≫ₕ ζ₀.symm := by
  unfold ζ₀ ξ₀
  exact rfl

example : ψ₀.symm ⁻¹' ψ₁.source = (ζ₀ ≫ₕ ξ₀).symm ⁻¹' ψ₁.source := by
  rfl

example : ψ₀ '' (ψ₀.source ∩ ψ₁.source) = ψ₀.target ∩ ψ₀.symm ⁻¹' ψ₁.source := by
  exact PartialHomeomorph.image_source_inter_eq' ψ₀ ψ₁.source

example : (ψ₀.symm ≫ₕ ψ₁).source = ψ₀.symm.source ∩ ψ₀.symm ⁻¹' ψ₁.source := by
  exact PartialHomeomorph.trans_source ψ₀.symm ψ₁

example : ψ₀ '' { z : Mobius.TotalSpace | z.1 ∈ φ₀.source ∧ z.1 ∈ φ₁.source } = ψ₀.target ∩ ψ₀.symm ⁻¹' ψ₁.source := by
  have h1 :  ψ₀ '' (ψ₀.source ∩ ψ₁.source) = ψ₀.target ∩ ψ₀.symm ⁻¹' ψ₁.source := by
    exact PartialHomeomorph.image_source_inter_eq' ψ₀ ψ₁.source
  have h2 : ψ₀.source = { z : Mobius.TotalSpace | z.1 ∈ φ₀.source } := by
    unfold ψ₀
    ext z
    simp
    exact fun a ↦ a

  have h3 : ψ₁.source = { z : Mobius.TotalSpace | z.1 ∈ φ₁.source } := by
    unfold ψ₁
    ext z
    simp
    exact fun a ↦ a
  rw [h2, h3] at h1

  have h5 : ({z : Mobius.TotalSpace | z.proj ∈ φ₀.source} ∩ {z : Mobius.TotalSpace | z.proj ∈ φ₁.source}) =
            {z : Mobius.TotalSpace | z.proj ∈ φ₀.source ∧ z.proj ∈ φ₁.source} := by
    ext z
    simp only [mem_inter_iff, mem_setOf_eq]
  rw [h5, <-h3] at h1
  exact h1

example : (ψ₀.symm ≫ₕ ψ₁).source = s' := by
  have h1 : φ₀.source ∩ φ₁.source = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := SulSource
  have h2 : ψ₀ =(Mobius.localTriv 0).toPartialHomeomorph ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) := rfl
  have h4 :  ψ₀.symm.source = ψ₀.target := PartialHomeomorph.symm_source ψ₀
  have h8c :(φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).source =
              φ₀.source ×ˢ (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))).source :=
                PartialHomeomorph.prod_source φ₀ (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))
  have h3 : ψ₀.source = { z : Mobius.TotalSpace | z.1 ∈ φ₀.source } := by
    exact sorry

  exact sorry

noncomputable def φ₁' := chartAt (EuclideanSpace ℝ (Fin 1))
  (⟨u, g⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

noncomputable def φ₀' := chartAt (EuclideanSpace ℝ (Fin 1))
  (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

example : φ₀ = @chartAt (EuclideanSpace ℝ (Fin 1)) _ _ _ (instChartedSpaceEuclideanSpaceRealFinElemHAddNatOfNatSphere 1)
    (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))) := rfl

example : φ₀' = @chartAt (EuclideanSpace ℝ (Fin 1)) _ _ _ Mobius.chartedSpaceBase
    (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))) := rfl

example : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ φ₀' φ₀'.source := by
  exact contMDiffOn_chart

#check  contMDiffOn_chart

lemma phiEqualsPhi : φ₀ = φ₀' := by
  have h3 : (fun (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ) => if x.val 0 > 0 then φ₀ else φ₁)
           (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))) = φ₀ := by
    have h32 : (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))).val 0 = 1 := rfl
    have h33 : (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))).val 0 > 0 := by
      rw [h32]
      exact Real.zero_lt_one
    exact if_pos h33
  exact id (Eq.symm h3)

example : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ φ₀ φ₀.source := by
  rw [phiEqualsPhi]
  exact contMDiffOn_chart

example : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤ ξ₁ (φ₀.source ×ˢ univ) := by
  have h1 : ξ₁ = φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) := rfl
  exact sorry

lemma SmoothInnerTot01 : ContDiffOn ℝ ⊤ (↑(ψ₀.symm ≫ₕ ψ₁)) (ψ₀.symm ≫ₕ ψ₁).source := by
  intro x hx
  have h1 : ψ₀.symm ≫ₕ ψ₁ = (ζ₀ ≫ₕ ξ₀).symm ≫ₕ (ζ₁ ≫ₕ ξ₁) := by
    unfold ψ₀ ψ₁
    exact rfl
  have h2 : (ζ₀ ≫ₕ ξ₀).symm = ξ₀.symm ≫ₕ ζ₀.symm := by
    exact rfl
  have h3 : ψ₀.symm ≫ₕ ψ₁ = (ξ₀.symm ≫ₕ ζ₀.symm) ≫ₕ (ζ₁ ≫ₕ ξ₁) := by
    rw [h1, h2]
  have h4 : (ξ₀.symm ≫ₕ ζ₀.symm) ≫ₕ (ζ₁ ≫ₕ ξ₁) = ξ₀.symm ≫ₕ (ζ₀.symm ≫ₕ ζ₁) ≫ₕ ξ₁ := by
    rw [←PartialHomeomorph.trans_assoc, ←PartialHomeomorph.trans_assoc, ←PartialHomeomorph.trans_assoc]
  have h5 : ψ₀.symm ≫ₕ ψ₁ = ξ₀.symm ≫ₕ (ζ₀.symm ≫ₕ ζ₁) ≫ₕ ξ₁ := by
    rw [h3, h4]
  have h6 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
            (ζ₀.symm ≫ₕ ζ₁)
            {x : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) | (x.1.val 1) > 0 ∨ (x.1.val 1) < 0} := by
    exact bothContMDiff
  exact sorry

lemma simpleSmoothTot : ∀ (e e' : PartialHomeomorph Mobius.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))),
    e ∈ totalAtlas →
    e' ∈ totalAtlas →
    ContDiffOn ℝ ⊤ (↑(e.symm ≫ₕ e')) ((e.symm ≫ₕ e').source) := by
  intros e e' he he'
  simp only [totalAtlas, Set.mem_insert_iff, Set.mem_singleton_iff] at he he'
  rcases he with (rfl | rfl)
  · rcases he' with (rfl | rfl)
    · exact SmoothInnerTot00 ψ₀ (by rw [totalAtlas]; simp)
    · exact sorry -- SmoothInner01
  · rcases he' with (rfl | rfl)
    · exact sorry -- SmoothInner10
    · exact SmoothInnerTot00 ψ₁ (by rw [totalAtlas]; simp)
