/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/
import Mathlib
import Mathlib.Topology.FiberBundle.Instances.S1

set_option linter.style.longLine false

open Function Set
open IsManifold Manifold
open Bundle
open Pole

-- Ensure Pole is a Fintype
deriving instance Fintype for Pole

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

lemma stereographic'_symm_zero
  {n : ℕ} {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = n + 1)]
  (v : Metric.sphere (0 : E) 1) :
  (stereographic' n v).symm (0 : EuclideanSpace ℝ (Fin n)) = -v.val := by
  simpa using stereographic'_symm_apply (n := n) v (0 : EuclideanSpace ℝ (Fin n))

lemma φₛ_symm_zero :
  φₛ.symm (0 : EuclideanSpace ℝ (Fin 1)) = -north_pt := by
  rw [φₛ]
  rw [chartAt]
  have h1 : ((stereographic' 1 north_pt).symm 0) = -north_pt :=
    SetCoe.ext (stereographic'_symm_zero (n := 1) north_pt)
  have h3 : chartAt (EuclideanSpace ℝ (Fin 1)) south_pt = stereographic' 1 (-south_pt) := rfl
  have h4 : chartAt (EuclideanSpace ℝ (Fin 1)) south_pt = stereographic' 1 (north_pt) := by
    rw [<-bar] at h3
    exact h3
  have h5 : (chartAt (EuclideanSpace ℝ (Fin 1)) south_pt).symm 0 = -north_pt := by
    rw [<-h4] at h1
    exact h1
  have h6 : φₛ.symm 0 = -north_pt := by
    rw [<-φₛ] at h5
    exact h5
  exact h6

lemma φₙ_symm_zero :
  φₙ.symm (0 : EuclideanSpace ℝ (Fin 1)) = -south_pt := by
  rw [φₙ]
  rw [chartAt]
  have h1 : ((stereographic' 1 south_pt).symm 0) = -south_pt :=
    SetCoe.ext (stereographic'_symm_zero (n := 1) south_pt)
  have h3 : chartAt (EuclideanSpace ℝ (Fin 1)) north_pt = stereographic' 1 (-north_pt) := rfl
  have h4 : chartAt (EuclideanSpace ℝ (Fin 1)) north_pt = stereographic' 1 (south_pt) := by
    rw [<-bar'] at h3
    exact h3
  have h5 : (chartAt (EuclideanSpace ℝ (Fin 1)) north_pt).symm 0 = -south_pt := by
    rw [<-h4] at h1
    exact h1
  have h6 : φₙ.symm 0 = -south_pt := by
    rw [<-φₙ] at h5
    exact h5
  exact h6

lemma hhh4 : φₛ.symm ⁻¹' φₙ.source = {x | x ≠ 0} := by
  ext x
  simp only [Set.mem_preimage, hφₙ.source]
  constructor
  · intro h
    by_contra hx
    have h0 : x ∉ {x | x ≠ 0} := hx
    have h1 : x = 0 := by simp only [Set.mem_setOf, not_not] at hx; exact hx
    have h2 : φₛ.symm (0 : EuclideanSpace ℝ (Fin 1)) = -north_pt := φₛ_symm_zero
    rw [<-h1] at h2
    exact h h2
  · intro h
    intro hx
    have h0 : φₛ.symm.source = univ := hφₛ.target
    have ha : 0 ∈ univ := trivial
    have hb : x ∈ univ := trivial
    have hc : 0 ∈ φₛ.symm.source := h0 ▸ ha
    have hd : x ∈ φₛ.symm.source := h0 ▸ hb
    have h1 : φₛ (φₛ.symm 0) = 0 := PartialHomeomorph.left_inv φₛ.symm hc
    have h2 : φₛ (φₛ.symm x) = x := PartialHomeomorph.left_inv φₛ.symm hd
    rw [<-φₛ_symm_zero] at hx
    have h3 : φₛ.symm x = φₛ.symm 0 := hx
    have h4 : φₛ (φₛ.symm x) = φₛ (φₛ.symm 0) := congrArg (↑φₛ) hx
    have h5 : x = 0 := by
      rw [h1, h2] at h4
      exact h4
    exact h h5

theorem SulSource' : (φN φₙ).source ∩ (φN φₛ).source = { x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 } := by
  have h1 : { x : S1 | x.point.val 0 ≠ 0 } ⊆ { x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 } := by
    intro x hx
    let y := x.point.val 0
    have h1 : y ≠ 0 := hx
    have h2 : (y < 0) ∨ (y = 0) ∨ (0 < y) := lt_trichotomy y 0
    have h3 : (y < 0) ∨ (0 < y) := by
      cases h2 with
      | inl hlt => left; exact hlt
      | inr hrest =>
        cases hrest with
        | inl heq => exfalso; exact hx heq
        | inr hgt => right; exact hgt
    exact id (Or.symm h3)
  have h2 : { x | x.point.val 0 > 0 } ⊆ { x : S1 | x.point.val 0 ≠ 0 } := by
    intro x hx
    let y := x.point.val 0
    have h1 : y > 0 := hx
    have h4 : y ≠ 0 := Ne.symm (ne_of_lt hx)
    exact h4
  have h3 : { x | x.point.val 0 < 0 } ⊆ { x : S1 | x.point.val 0 ≠ 0 } := by
    intro x hx
    let y := x.point.val 0
    have h1 : y < 0 := hx
    have h4 : y ≠ 0 := Ne.symm (ne_of_gt hx)
    exact h4
  have h4 : (φN φₙ).source ∩ (φN φₛ).source = { x | x.point.val 0 ≠ 0 } := OverlapNorthSouth
  have h5 : { x : S1 | x.point.val 0 ≠ 0 } = { x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 } := by
    exact Set.Subset.antisymm h1 (Set.union_subset h2 h3)
  have h6 : (φN φₙ).source ∩ (φN φₛ).source = { x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 } := by
    rw [h5] at h4
    exact h4
  exact h6


def s1' : Set (S1 × EuclideanSpace ℝ (Fin 1)) := { x | 0 < x.1.point.val 0 }

lemma s1_is_open' : IsOpen s1' := by
  have h1 : Continuous (fun x : S1 × EuclideanSpace ℝ (Fin 1) => (↑x.1.point : EuclideanSpace ℝ (Fin 2))) :=
    continuous_induced_dom.comp (continuous_induced_dom.comp continuous_fst)
  have h2 : Continuous (fun u : EuclideanSpace ℝ (Fin 2) => u 0) :=
    continuous_apply 0
  have h : Continuous (fun x : S1 × EuclideanSpace ℝ (Fin 1) => (↑x.1.point : EuclideanSpace ℝ (Fin 2)) 0) :=
    h2.comp h1
  exact isOpen_Ioi.preimage h

def s2' : Set (S1 × EuclideanSpace ℝ (Fin 1)) := { x | 0 > x.1.point.val 0 }

lemma s2_is_open' : IsOpen s2' := by
  have h1 : Continuous (fun x : S1 × EuclideanSpace ℝ (Fin 1) => (↑x.1.point : EuclideanSpace ℝ (Fin 2))) :=
    continuous_induced_dom.comp (continuous_induced_dom.comp continuous_fst)
  have h2 : Continuous (fun u : EuclideanSpace ℝ (Fin 2) => u 0) :=
    continuous_apply 0
  have h : Continuous (fun x : S1 × EuclideanSpace ℝ (Fin 1) => (↑x.1.point : EuclideanSpace ℝ (Fin 2)) 0) :=
    h2.comp h1
  exact isOpen_Iio.preimage h

lemma contNS : ContinuousOn (fun p ↦ MyCoordChange' north south p.1 p.2) (((φN φₙ).source ∩ (φN φₛ).source) ×ˢ univ) := by
  have h0 : (φN φₙ).source ∩ (φN φₛ).source = { x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 } := SulSource'
  have hc :
  ContinuousOn (fun (p : S1 × EuclideanSpace ℝ (Fin 1)) ↦
                  MyCoordChange' north south p.1 p.2)
               ({x | x.point.val 0 > 0} ×ˢ univ) :=
  ContinuousOn.congr continuous_snd.continuousOn (by
    rintro ⟨x, y⟩ ⟨hx, _⟩
    exact if_pos hx)

  have hd :
  ContinuousOn (fun (p : S1 × EuclideanSpace ℝ (Fin 1)) ↦
                  MyCoordChange' north south p.1 p.2)
               ({x | x.point.val 0 < 0} ×ˢ univ) :=
  ContinuousOn.congr (continuous_snd.neg.continuousOn) (by
    rintro ⟨x, y⟩ ⟨hx, _⟩
    have hn : ¬(x.point.val 0 > 0) := not_lt_of_gt hx
    exact if_neg hn)

  have hg : (({x : S1 | x.point.val 0 > 0} ×ˢ univ) ∪ ({x | x.point.val 0 < 0} ×ˢ univ)) =
            ((({x | x.point.val 0 > 0} ∪ {x | x.point.val 0 < 0}) ×ˢ univ) : Set (S1 × EuclideanSpace ℝ (Fin 1)))
    := Eq.symm union_prod

  have he : ContinuousOn (fun p ↦ MyCoordChange' north south p.1 p.2)
            (({x | x.point.val 0 > 0} ×ˢ univ) ∪ ({x | x.point.val 0 < 0} ×ˢ univ)) :=

    have s1_open_prod : IsOpen ({x | x.point.val 0 > 0} ×ˢ univ : Set (S1 × EuclideanSpace ℝ (Fin 1))) := by
      have h0 : IsOpen s1' := s1_is_open'
      have h1 : s1' = { x | 0 < x.1.point.val 0 } := rfl
      have h2 : IsOpen { x : S1 × EuclideanSpace ℝ (Fin 1) | 0 < x.1.point.val 0 } := by
        rw [h1] at h0
        exact h0
      have h3 : { x : S1 × EuclideanSpace ℝ (Fin 1) | 0 < x.1.point.val 0 } =
                {x | x.point.val 0 > 0} ×ˢ univ := by
        ext ⟨a, b⟩
        simp
      rw [h3] at h2
      exact h2

    have s2_open_prod : IsOpen ({x | x.point.val 0 < 0} ×ˢ univ : Set (S1 × EuclideanSpace ℝ (Fin 1))) := by
      have h0 : IsOpen s2' := s2_is_open'
      have h1 : s2' = { x | 0 > x.1.point.val 0 } := rfl
      have h2 : IsOpen { x : S1 × EuclideanSpace ℝ (Fin 1) | 0 > x.1.point.val 0 } := by
        rw [h1] at h0
        exact h0
      have h3 : { x : S1 × EuclideanSpace ℝ (Fin 1) | 0 > x.1.point.val 0 } =
                {x | x.point.val 0 < 0} ×ˢ univ := by
        ext ⟨a, b⟩
        simp
      rw [h3] at h2
      exact h2

    ContinuousOn.union_of_isOpen hc hd s1_open_prod s2_open_prod

  rw [h0, <-hg]
  exact he

lemma contSN : ContinuousOn (fun p ↦ MyCoordChange' south north p.1 p.2) (((φN φₛ).source ∩ (φN φₙ).source) ×ˢ univ) := by
  have h0 : (φN φₙ).source ∩ (φN φₛ).source = { x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 } := SulSource'
  have h1 : (φN φₛ).source ∩ (φN φₙ).source = { x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 } := by
    rw [Set.inter_comm] at h0
    exact h0
  have hc :
  ContinuousOn (fun (p : S1 × EuclideanSpace ℝ (Fin 1)) ↦
                  MyCoordChange' south north p.1 p.2)
               ({x | x.point.val 0 > 0} ×ˢ univ) :=
  ContinuousOn.congr continuous_snd.continuousOn (by
    rintro ⟨x, y⟩ ⟨hx, _⟩
    exact if_pos hx)

  have hd :
  ContinuousOn (fun (p : S1 × EuclideanSpace ℝ (Fin 1)) ↦
                  MyCoordChange' south north p.1 p.2)
               ({x | x.point.val 0 < 0} ×ˢ univ) :=
  ContinuousOn.congr (continuous_snd.neg.continuousOn) (by
    rintro ⟨x, y⟩ ⟨hx, _⟩
    have hn : ¬(x.point.val 0 > 0) := not_lt_of_gt hx
    exact if_neg hn)

  have hg : (({x : S1 | x.point.val 0 > 0} ×ˢ univ) ∪ ({x | x.point.val 0 < 0} ×ˢ univ)) =
            ((({x | x.point.val 0 > 0} ∪ {x | x.point.val 0 < 0}) ×ˢ univ) : Set (S1 × EuclideanSpace ℝ (Fin 1)))
    := Eq.symm union_prod

  have he : ContinuousOn (fun p ↦ MyCoordChange' south north p.1 p.2)
            (({x | x.point.val 0 > 0} ×ˢ univ) ∪ ({x | x.point.val 0 < 0} ×ˢ univ)) :=

    have s1_open_prod : IsOpen ({x | x.point.val 0 > 0} ×ˢ univ : Set (S1 × EuclideanSpace ℝ (Fin 1))) := by
      have h0 : IsOpen s1' := s1_is_open'
      have h1 : s1' = { x | 0 < x.1.point.val 0 } := rfl
      have h2 : IsOpen { x : S1 × EuclideanSpace ℝ (Fin 1) | 0 < x.1.point.val 0 } := by
        rw [h1] at h0
        exact h0
      have h3 : { x : S1 × EuclideanSpace ℝ (Fin 1) | 0 < x.1.point.val 0 } =
                {x | x.point.val 0 > 0} ×ˢ univ := by
        ext ⟨a, b⟩
        simp
      rw [h3] at h2
      exact h2

    have s2_open_prod : IsOpen ({x | x.point.val 0 < 0} ×ˢ univ : Set (S1 × EuclideanSpace ℝ (Fin 1))) := by
      have h0 : IsOpen s2' := s2_is_open'
      have h1 : s2' = { x | 0 > x.1.point.val 0 } := rfl
      have h2 : IsOpen { x : S1 × EuclideanSpace ℝ (Fin 1) | 0 > x.1.point.val 0 } := by
        rw [h1] at h0
        exact h0
      have h3 : { x : S1 × EuclideanSpace ℝ (Fin 1) | 0 > x.1.point.val 0 } =
                {x | x.point.val 0 < 0} ×ˢ univ := by
        ext ⟨a, b⟩
        simp
      rw [h3] at h2
      exact h2

    ContinuousOn.union_of_isOpen hc hd s1_open_prod s2_open_prod

  rw [h1, <-hg]
  exact he

def MyContinuousOn_coordChange' : ∀ (i j : Pole),
  ContinuousOn (fun p => MyCoordChange' i j p.1 p.2)
    (((if i = north then (φN φₙ).source else (φN φₛ).source) ∩ if j = north then (φN φₙ).source else (φN φₛ).source) ×ˢ
      univ) := by
      intro i j
      cases i
      · cases j
        · simp
          exact continuousOn_snd
        · simp
          exact contNS
      · cases j
        · simp
          exact contSN
        · simp
          exact continuousOn_snd

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
  continuousOn_coordChange := MyContinuousOn_coordChange'
  coordChange_comp := MyCoordChange_comp'

noncomputable
instance (m n : ℕ) : ChartedSpace ((EuclideanSpace ℝ (Fin (n + m)))) (EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin m))) := by
  have h1 : EuclideanSpace ℝ (Fin (n + m)) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) := EuclideanSpace.finAddEquivProd
  have h2 : EuclideanSpace ℝ (Fin (n + m)) ≃ₜ EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=  ContinuousLinearEquiv.toHomeomorph h1
  let x := (EuclideanSpace.finAddEquivProd : EuclideanSpace ℝ (Fin (n + m)) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
  let y := ContinuousLinearEquiv.toHomeomorph x
  let z := Homeomorph.toPartialHomeomorph y
  have hz : z.symm.source = univ := rfl
  exact PartialHomeomorph.singletonChartedSpace z.symm hz

#synth ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
                    (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius'.Fiber)

#synth @IsManifold ℝ _ _ _ _ _ _ ((𝓡 1).prod (𝓡 1)) 0 (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius'.Fiber) _ _

#synth IsManifold ((𝓡 1).prod (𝓡 1)) 0 (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius'.Fiber)

#synth IsManifold ((𝓡 1).prod (𝓡 1)) ⊤ (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius'.Fiber)

instance : ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
                        (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) := by
  exact chartedSpaceSelf (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))

noncomputable
instance : ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
                        (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius'.Fiber) :=
  ChartedSpace.comp (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
                    (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
                    (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius'.Fiber)

#synth IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) 0 (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius'.Fiber)

noncomputable
def τₙ := Mobius'.localTriv north
noncomputable
def τₛ := Mobius'.localTriv south

noncomputable
def χₙ := τₙ.toPartialHomeomorph
noncomputable
def χₛ := τₛ.toPartialHomeomorph

noncomputable
def ψₙ := χₙ ≫ₕ ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
noncomputable
def ψₛ := χₛ ≫ₕ ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

def totalAtlas' : Set (PartialHomeomorph Mobius'.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :=
  { ψₙ, ψₛ }

lemma jjj (ψ : PartialHomeomorph Mobius'.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :
  ContDiffOn ℝ ⊤ (↑ψ ∘ ↑ψ.symm) (ψ.target ∩ ↑ψ.symm ⁻¹' ψ.source) := by
  apply ContDiffOn.congr contDiffOn_id
  intro (y : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) hy
  have h0 : y ∈ ψ.target := mem_of_mem_inter_left hy
  have h1 : ψ (ψ.symm y) = y := PartialHomeomorph.left_inv ψ.symm h0
  exact h1

lemma localTrivTransition_eq_coordChange' (i j : Pole)
  {x : Mobius'.Base} {v : (EuclideanSpace ℝ (Fin 1))} (hx : x ∈ Mobius'.baseSet i ∩ Mobius'.baseSet j) :
  ((Mobius'.localTriv i).toPartialHomeomorph.symm ≫ₕ (Mobius'.localTriv j).toPartialHomeomorph) (x, v) =
    (x, Mobius'.coordChange i j x v) := by
  simp
  have ha : x ∈ Mobius'.baseSet (Mobius'.indexAt x) := Mobius'.mem_baseSet_at x
  have hd : x ∈ (Mobius'.baseSet i ∩ Mobius'.baseSet (Mobius'.indexAt x)) ∩ Mobius'.baseSet j :=
  ⟨⟨hx.1, ha⟩, hx.2⟩
  have h2 : Mobius'.coordChange (Mobius'.indexAt x) j x (Mobius'.coordChange i (Mobius'.indexAt x) x v) =
            Mobius'.coordChange i j x v :=  Mobius'.coordChange_comp i (Mobius'.indexAt x) j x hd v
  exact h2

lemma upperInclusionNS : ∀ (x : Mobius'.Base) (v : EuclideanSpace ℝ (Fin 1)),
    (x.point.val 0) > 0 →
    (χₙ.symm ≫ₕ χₛ) (x, v)
      = (x, v) := by
    intros x v ha
    have hx : x ∈ { x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 } := Or.inl ha
    have hx' : x ∈ (φN φₙ).source ∩ (φN φₛ).source := SulSource'.symm ▸ hx
    have h1 : (χₙ.symm ≫ₕ χₛ) (x, v) =
              (x, Mobius'.coordChange north south x v) := localTrivTransition_eq_coordChange' north south hx'
    have h2 : Mobius'.coordChange north south x v = if (x.point.val 0) > 0 then v else -v := rfl
    have h3 : (χₙ.symm ≫ₕ χₛ) (x, v) =
    (x, if (x.point.val 0) > 0 then v else -v) := by
      rw [h2] at h1
      exact h1
    have h4 : (x.point.val 0) > 0 → (if (x.point.val 0) > 0 then v else -v) = v := by
      intro h41
      rw [if_pos h41]
    rw [h3, h4]
    exact ha

lemma xNe0 : ∀ (x : S1) (_ : x.point.val 0 > 0), x.point ≠ north_pt := by
  have h1 : north_pt.val 0 = 0 := rfl
  intros x hx h_eq
  rw [h_eq] at hx
  rw [h1] at hx
  exact lt_irrefl 0 hx

lemma xInSource : ∀ (x : Mobius'.Base) (v : EuclideanSpace ℝ (Fin 1)),
  (x.point.val 0) > 0 → (x, v) ∈ (χₛ.symm ≫ₕ χₙ).source := by
  have h0 : (χₛ.symm ≫ₕ χₙ).source = χₛ '' (χₛ.source ∩ χₙ.source) := PartialHomeomorph.trans_source'' χₛ.symm χₙ
  have h1 : χₛ '' χₛ.source = χₛ.target := PartialHomeomorph.image_source_eq_target χₛ
  have h4  : τₙ.baseSet = (φN φₙ).source := rfl
  have h4' : τₛ.baseSet = (φN φₛ).source := rfl
  have h5 : (φN φₙ).source ∩ (φN φₛ).source = { x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 } := SulSource'
  have h6 : χₛ.source ∩ χₙ.source = Mobius'.proj ⁻¹' ({ x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 }) := by
     have h6a : χₛ.source ∩ χₙ.source =
                              Mobius'.proj ⁻¹' (τₙ.baseSet ∩ τₛ.baseSet) := by
                rw [Set.preimage_inter]
                exact inter_comm (Mobius'.proj ⁻¹' τₛ.baseSet)
                                 (Mobius'.proj ⁻¹' τₙ.baseSet)
     rw [h6a, h4, h4', h5]
  intro x v h
  have h8' : ∃ y ∈ Mobius'.proj ⁻¹' ({x | x.point.val 0 > 0} ∪ {x | x.point.val 0 < 0}),
    Mobius'.proj y = x ∧ y.2 = v := by
    use ⟨x, v⟩
    constructor
    · exact Or.inl h
    · exact Prod.mk_inj.mp rfl
  have h9 : ∃ y ∈ χₛ.source ∩ χₙ.source, Mobius'.proj y = x  ∧ y.2 = v := by
    rw [<-h6] at h8'
    rcases h8' with ⟨y, hy, hy_proj, hy_snd⟩
    exact ⟨y, hy, ⟨hy_proj, hy_snd⟩⟩
  have h2 : (x, v) ∈ χₛ '' (χₛ.source ∩ χₙ.source) := by
    rcases h9 with ⟨y, hy, hyproj, hv⟩
    have h2c : χₛ y ∈ χₛ '' (χₛ.source ∩ χₙ.source) := mem_image_of_mem (↑χₛ) hy
    have h2g : Prod.snd (τₛ y) =  Mobius'.coordChange (Mobius'.indexAt y.proj) south y.proj v := by
      exact Eq.symm
            (PiLp.ext (congrFun (congrArg (Mobius'.coordChange (Mobius'.indexAt y.proj) south y.proj) (id (Eq.symm hv)))))
    have h2z : y.proj = x := hyproj
    have h2y : x.point ≠ north_pt := xNe0 x h
    have h2i : y.proj.point ≠ north_pt := by rw [<-h2z] at h2y; exact h2y
    have h2j : Mobius'.indexAt y.proj = south := if_neg h2i
    have h2k : Prod.snd (τₛ y) =  Mobius'.coordChange south south y.proj v := by
      rw [h2j] at h2g
      exact h2g
    have h2n : Mobius'.proj y = y.proj := rfl
    have h2o : Mobius'.coordChange south south y.proj v = v := rfl
    have h2q : τₛ y = ⟨Mobius'.proj y, v⟩ := Prod.ext rfl h2k
    have h2s : χₛ y = ⟨x, v⟩ := by
      rw [hyproj] at h2q
      exact h2q
    have h2t : ⟨x, v⟩ ∈ χₛ '' (χₛ.source ∩ χₙ.source) := by
      rw [h2s] at h2c
      exact h2c
    exact h2t
  rw [h0]
  exact h2

lemma xInTarget : ∀ (x : Mobius'.Base) (v : EuclideanSpace ℝ (Fin 1)),
  (x.point.val 0) > 0 → (x, v) ∈ (χₛ.symm ≫ₕ χₙ).target := by
  have h1 : (χₛ.symm ≫ₕ χₙ).target = χₙ '' (χₙ.source ∩ χₛ.symm.target) := PartialHomeomorph.trans_target'' χₛ.symm χₙ
  have h2 : χₛ.symm.target = χₛ.source := rfl
  have h3 : (χₛ.symm ≫ₕ χₙ).target = χₙ '' (χₙ.source ∩ χₛ.source) := by rw [h2] at h1; exact h1
  have h4  : τₙ.baseSet = (φN φₙ).source := rfl
  have h4' : τₛ.baseSet = (φN φₛ).source := rfl
  have h5 : (φN φₙ).source ∩ (φN φₛ).source = { x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 } := SulSource'
  have h6 : χₛ.source ∩ χₙ.source = Mobius'.proj ⁻¹' ({ x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 }) := by
     have h6a : χₛ.source ∩ χₙ.source =
                              Mobius'.proj ⁻¹' (τₙ.baseSet ∩ τₛ.baseSet) := by
                rw [Set.preimage_inter]
                exact inter_comm (Mobius'.proj ⁻¹' τₛ.baseSet)
                                 (Mobius'.proj ⁻¹' τₙ.baseSet)
     rw [h6a, h4, h4', h5]
  intro x v h
  have h8' : ∃ y ∈ Mobius'.proj ⁻¹' ({x | x.point.val 0 > 0} ∪ {x | x.point.val 0 < 0}),
    Mobius'.proj y = x ∧ y.2 = v := by
    use ⟨x, v⟩
    constructor
    · exact Or.inl h
    · exact Prod.mk_inj.mp rfl
  have h9 : ∃ y ∈ χₛ.source ∩ χₙ.source, Mobius'.proj y = x  ∧ y.2 = v := by
    rw [<-h6] at h8'
    rcases h8' with ⟨y, hy, hy_proj, hy_snd⟩
    exact ⟨y, hy, ⟨hy_proj, hy_snd⟩⟩
  rw [h3]
  have hz : (x, v) ∈ ↑χₙ '' (χₙ.source ∩ χₛ.source) := by
    rcases h9 with ⟨y, hy, hyproj, hv⟩
    have h2c : χₙ y ∈ χₙ '' (χₙ.source ∩ χₛ.source) := mem_image_of_mem (↑χₙ) (And.comm.mp hy)
    have h2g : Prod.snd (τₙ y) =  Mobius'.coordChange (Mobius'.indexAt y.proj) north y.proj v := by
      exact Eq.symm
            (PiLp.ext (congrFun (congrArg (Mobius'.coordChange (Mobius'.indexAt y.proj) north y.proj) (id (Eq.symm hv)))))
    have h2z : y.proj = x := hyproj
    have h2y : x.point ≠ north_pt := xNe0 x h
    have h2i : y.proj.point ≠ north_pt := by rw [<-h2z] at h2y; exact h2y
    have h2j : Mobius'.indexAt y.proj = south := if_neg h2i
    have h2k : Prod.snd (τₙ y) =  Mobius'.coordChange south north y.proj v := by
      rw [h2j] at h2g
      exact h2g
    have h2n : Mobius'.proj y = y.proj := rfl
    have h2o : Mobius'.coordChange south north y.proj v = MyCoordChange' south north y.proj v := rfl
    have h22 : MyCoordChange' south north y.proj v = if y.proj.point.val 0 > 0 then v else -v := rfl
    have h23 : y.proj.point.val 0 > 0 := by
      rw [h2z]
      exact h
    have h24 : (if y.proj.point.val 0 > 0 then v else -v : EuclideanSpace ℝ (Fin 1)) = v := if_pos h23
    rw [h2o, h22, h24] at h2k
    have h2q : τₙ y = ⟨Mobius'.proj y, v⟩ := Prod.ext rfl h2k
    have h2s : χₙ y = ⟨x, v⟩ := by
      rw [hyproj] at h2q
      exact h2q
    have h2t : ⟨x, v⟩ ∈ χₙ '' (χₙ.source ∩ χₛ.source) := by
      rw [h2s] at h2c
      exact h2c
    exact h2t
  exact hz

lemma upperInclusionSN : ∀ (x : Mobius'.Base) (v : EuclideanSpace ℝ (Fin 1)),
    (x.point.val 0) > 0 →
    (χₛ.symm ≫ₕ χₙ) (x, v)
      = (x, v) := by
  intro x v h
  have hs : (x, v) ∈ (χₛ.symm ≫ₕ χₙ).source := xInSource x v h
  have ht : (x, v) ∈ (χₛ.symm ≫ₕ χₙ).target := xInTarget x v h
  have h0 : (χₙ.symm ≫ₕ χₛ).symm = χₛ.symm ≫ₕ χₙ := PartialHomeomorph.trans_symm_eq_symm_trans_symm χₙ.symm χₛ
  have h1 : (χₛ.symm ≫ₕ χₙ).symm = χₙ.symm ≫ₕ χₛ := PartialHomeomorph.trans_symm_eq_symm_trans_symm χₛ.symm χₙ
  have h2 : (χₙ.symm ≫ₕ χₛ) (x, v) = (x, v) := upperInclusionNS x v h
  have h3 : (χₛ.symm ≫ₕ χₙ).symm (x, v) = (x, v) := by rw [<-h1] at h2; exact h2
  have h4 : (x, v) = (χₛ.symm ≫ₕ χₙ).symm (x, v) ↔ (χₛ.symm ≫ₕ χₙ) (x, v) = (x, v):= PartialHomeomorph.eq_symm_apply (χₛ.symm ≫ₕ χₙ) hs ht
  exact (PartialHomeomorph.eq_symm_apply (χₛ.symm ≫ₕ χₙ) hs ht).mp (id (Eq.symm h2))

lemma upperContMDiffSN : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
      (χₛ.symm ≫ₕ χₙ)
      {x : S1 × EuclideanSpace ℝ (Fin 1) | (x.1.point.val 0) > 0} := by
      apply ContMDiffOn.congr
      · exact contMDiffOn_id
      · intro y hy
        obtain ⟨x, v⟩ := y
        dsimp at hy
        exact upperInclusionSN x v hy

lemma upperContMDiffNS : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
      (χₙ.symm ≫ₕ χₛ)
      {x : S1 × EuclideanSpace ℝ (Fin 1) | (x.1.point.val 0) > 0} := by
      apply ContMDiffOn.congr
      · exact contMDiffOn_id
      · intro y hy
        obtain ⟨x, v⟩ := y
        dsimp at hy
        exact upperInclusionNS x v hy

lemma lowerInclusionSN : ∀ (x : Mobius'.Base) (v : EuclideanSpace ℝ (Fin 1)),
    (x.point.val 0) < 0 → (χₛ.symm ≫ₕ χₙ) (x, v) = (x, -v) := by
  intros x v ha
  have hx : x ∈ { x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 } := Or.inr ha
  have hx'  : x ∈ (φN φₙ).source ∩ (φN φₛ).source := SulSource'.symm ▸ hx
  have hx'' : x ∈ (φN φₛ).source ∩ (φN φₙ).source := by rwa [inter_comm] at hx'
  have h1 : (χₛ.symm ≫ₕ χₙ) (x, v) = (x, Mobius'.coordChange south north x v) :=
    localTrivTransition_eq_coordChange' south north hx''
  have h2 : Mobius'.coordChange south north x v = if (x.point.val 0) > 0 then v else -v := rfl
  have h3 : (χₛ.symm ≫ₕ χₙ) (x, v) = (x, if (x.point.val 0) > 0 then v else -v) := by
      rw [h2] at h1
      exact h1
  have h4 : ¬ (x.point.val 0) > 0 → (if (x.point.val 0) > 0 then v else -v) = -v := by
    intro h41
    rw [if_neg h41]
  rw [h3, h4]
  exact not_lt_of_gt ha

lemma lowerInclusionNS : ∀ (x : Mobius'.Base) (v : EuclideanSpace ℝ (Fin 1)),
    (x.point.val 0) < 0 → (χₙ.symm ≫ₕ χₛ) (x, v) = (x, -v) := by
  intros x v ha
  have hx : x ∈ { x | x.point.val 0 > 0 } ∪ { x | x.point.val 0 < 0 } := Or.inr ha
  have hx'  : x ∈ (φN φₙ).source ∩ (φN φₛ).source := SulSource'.symm ▸ hx
  have h1 : (χₙ.symm ≫ₕ χₛ) (x, v) = (x, Mobius'.coordChange north south x v) :=
    localTrivTransition_eq_coordChange' north south hx'
  have h2 : Mobius'.coordChange north south x v = if (x.point.val 0) > 0 then v else -v := rfl
  have h3 : (χₙ.symm ≫ₕ χₛ) (x, v) = (x, if (x.point.val 0) > 0 then v else -v) := by
      rw [h2] at h1
      exact h1
  have h4 : ¬ (x.point.val 0) > 0 → (if (x.point.val 0) > 0 then v else -v) = -v := by
    intro h41
    rw [if_neg h41]
  rw [h3, h4]
  exact not_lt_of_gt ha

lemma lowerContMDiffSN : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
  (χₛ.symm ≫ₕ χₙ) {x : S1 × EuclideanSpace ℝ (Fin 1) | (x.1.point.val 0) < 0} := by
  have h1a : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (fun x ↦ -id x) (univ : Set (EuclideanSpace ℝ (Fin 1))) := contMDiffOn_id.neg
  have hz : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ id {x : S1 | (x.point.val 0) < 0} := contMDiffOn_id

  let f1 : S1 × EuclideanSpace ℝ (Fin 1) → S1 × EuclideanSpace ℝ (Fin 1) :=
    Prod.map id fun x ↦ -id x
  let f2 : S1 × EuclideanSpace ℝ (Fin 1) → S1 × EuclideanSpace ℝ (Fin 1) :=
        fun x ↦ match x with
        | (x, v) => (x, -v)
  have h2 : f1 = f2 := by
    exact rfl
  have h2c : ∀ y ∈ {x | x.point.val 0 < 0} ×ˢ univ, f1 y = Prod.map id (fun x ↦ -id x) y := by
    intro y hy
    dsimp at hy
    exact rfl
  have h3 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
    f1 ({x | x.point.val 0 < 0} ×ˢ univ) := ContMDiffOn.congr (hz.prodMap h1a) h2c
  have h1 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
    (fun (x, v) => (x, -v)) {x : S1 × EuclideanSpace ℝ (Fin 1) | (x.1.point.val 0) < 0} := by
      rw [h2] at h3
      have h1z :  ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤ f2 ({x | x.point.val 0 < 0} ×ˢ univ) := h3
      have h1y : ContMDiffOn _ _ ⊤ f2 {x | x.1.point.val 0 < 0} :=
        h1z.mono (by
          intro x hx
          exact ⟨hx, Set.mem_univ x.2⟩)
      exact h1y
  apply ContMDiffOn.congr
  · exact h1
  · intro y hy
    obtain ⟨x, v⟩ := y
    dsimp at hy
    exact lowerInclusionSN x v hy

lemma lowerContMDiffNS : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
  (χₙ.symm ≫ₕ χₛ) {x : S1 × EuclideanSpace ℝ (Fin 1) | (x.1.point.val 0) < 0} := by
  have h1a : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (fun x ↦ -id x) (univ : Set (EuclideanSpace ℝ (Fin 1))) := contMDiffOn_id.neg
  have hz : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ id {x : S1 | (x.point.val 0) < 0} := contMDiffOn_id

  let f1 : S1 × EuclideanSpace ℝ (Fin 1) → S1 × EuclideanSpace ℝ (Fin 1) :=
    Prod.map id fun x ↦ -id x
  let f2 : S1 × EuclideanSpace ℝ (Fin 1) → S1 × EuclideanSpace ℝ (Fin 1) :=
        fun x ↦ match x with
        | (x, v) => (x, -v)
  have h2 : f1 = f2 := by
    exact rfl
  have h2c : ∀ y ∈ {x | x.point.val 0 < 0} ×ˢ univ, f1 y = Prod.map id (fun x ↦ -id x) y := by
    intro y hy
    dsimp at hy
    exact rfl
  have h3 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
    f1 ({x | x.point.val 0 < 0} ×ˢ univ) := ContMDiffOn.congr (hz.prodMap h1a) h2c
  have h1 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
    (fun (x, v) => (x, -v)) {x : S1 × EuclideanSpace ℝ (Fin 1) | (x.1.point.val 0) < 0} := by
      rw [h2] at h3
      have h1z :  ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤ f2 ({x | x.point.val 0 < 0} ×ˢ univ) := h3
      have h1y : ContMDiffOn _ _ ⊤ f2 {x | x.1.point.val 0 < 0} :=
        h1z.mono (by
          intro x hx
          exact ⟨hx, Set.mem_univ x.2⟩)
      exact h1y
  apply ContMDiffOn.congr
  · exact h1
  · intro y hy
    obtain ⟨x, v⟩ := y
    dsimp at hy
    exact lowerInclusionNS x v hy

lemma bothContMDiffSN : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
 (χₛ.symm ≫ₕ χₙ)
 {x : S1 × EuclideanSpace ℝ (Fin 1) | (x.1.point.val 0) > 0 ∨ (x.1.point.val 0) < 0} := by
exact ContMDiffOn.union_of_isOpen upperContMDiffSN lowerContMDiffSN s1_is_open' s2_is_open'

lemma bothContMDiffNS : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
 (χₙ.symm ≫ₕ χₛ)
 {x : S1 × EuclideanSpace ℝ (Fin 1) | (x.1.point.val 0) > 0 ∨ (x.1.point.val 0) < 0} := by
exact ContMDiffOn.union_of_isOpen upperContMDiffNS lowerContMDiffNS s1_is_open' s2_is_open'

lemma φNφₙisChart : φN φₙ = chartAt (EuclideanSpace ℝ (Fin 1)) { point := north_pt }:= by
  have h1a : (chartAt (EuclideanSpace ℝ (Fin 1)) : S1 → PartialHomeomorph S1 (EuclideanSpace ℝ (Fin 1)))
         = fun (x : S1) => if x.point = north_pt then φN φₙ else φN φₛ := rfl
  rw [h1a]
  simp

lemma φNφₛisChart : φN φₛ = chartAt (EuclideanSpace ℝ (Fin 1)) { point := south_pt }:= by
  have h1a : (chartAt (EuclideanSpace ℝ (Fin 1)) : S1 → PartialHomeomorph S1 (EuclideanSpace ℝ (Fin 1)))
         = fun (x : S1) => if x.point = north_pt then φN φₙ else φN φₛ := rfl
  rw [h1a]
  simp
  exact fun a ↦ congrArg φN (congrArg (chartAt (EuclideanSpace ℝ (Fin 1))) a)

lemma φNφₙ_smooth : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (⇑(φN φₙ)) (φN φₙ).source := by
  rw [φNφₙisChart]
  exact contMDiffOn_chart

lemma φNφₛ_symm_smooth : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (⇑((φN φₛ)).symm) (φN φₛ).target := by
  rw [φNφₛisChart]
  exact contMDiffOn_chart_symm

lemma side1 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
    ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
    ((φN φₙ).source ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by
  have h3 : (φN φₙ).source ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))) ⊆ Prod.fst ⁻¹' (φN φₙ).source :=
    by
      rintro ⟨a, b⟩ ⟨ha, _⟩
      exact ha
  have h2 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) (𝓡 1) ⊤ ((φN φₙ) ∘ Prod.fst)
    ((φN φₙ).source ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by
      exact ContMDiffOn.comp φNφₙ_smooth contMDiffOn_fst h3
  apply (contMDiffOn_prod_iff _).mpr
  exact ⟨h2, by exact contMDiffOn_snd⟩

lemma side2 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
    ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm
    ((φN φₛ).target ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by
  have h4 : (φN φₛ).target ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))) ⊆ Prod.fst ⁻¹' (φN φₛ).target :=
    by
      rintro ⟨a, b⟩ ⟨ha, _⟩
      exact ha
  have h2 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) (𝓡 1) ⊤ (↑(φN φₛ).symm ∘ Prod.fst)
    ((φN φₛ).target ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by
      exact ContMDiffOn.comp φNφₛ_symm_smooth contMDiffOn_fst h4
  apply (contMDiffOn_prod_iff _).mpr
  exact ⟨h2, by exact contMDiffOn_snd⟩

lemma changeModelSpace
  (f : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) →
       EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
  (s : Set (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :
  ContMDiffOn ((𝓡 1).prod (𝓡 1))
              ((𝓡 1).prod (𝓡 1))
              ⊤ f
              s
  ↔ ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
                𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
                ⊤ f
                s := by
  have ha2b : ContMDiff
    𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
    ((𝓡 1).prod (𝓡 1))
    ⊤
    (id : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) →
          EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) := by
    rw [contMDiff_iff]
    constructor
    · exact continuous_id
    · intro x y
      exact contDiffOn_id

  have hb2a : ContMDiff
    ((𝓡 1).prod (𝓡 1))
    𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
    ⊤
    (id : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) →
          EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) := by
    rw [contMDiff_iff]
    constructor
    · exact continuous_id
    · intro x y
      exact contDiffOn_id
  constructor
  · intro h
    have h0 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤ f
              s := h
    have h1 : ContMDiffOn
              𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
              ((𝓡 1).prod (𝓡 1)) ⊤ (f ∘ id)
              s :=
               ContMDiffOn.comp h0
                (ContMDiffOn.mono (contMDiffOn_univ.mpr ha2b) (Set.subset_univ _)) (fun ⦃a⦄ a ↦ a)
    have h2 : ContMDiffOn
              𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
              𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ⊤ (id ∘ f ∘ id)
              s :=
      ContMDiffOn.comp (contMDiffOn_univ.mpr hb2a) h1 (Set.subset_univ _)
    exact h2
  · intro h
    have h0 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
                          𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ⊤ f
              s := h
    have h1 : ContMDiffOn
              ((𝓡 1).prod (𝓡 1))
              𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
              ⊤ (f ∘ id)
              s :=
               ContMDiffOn.comp h0
                (ContMDiffOn.mono (contMDiffOn_univ.mpr hb2a) (Set.subset_univ _)) (fun ⦃a⦄ a ↦ a)
    have h2 : ContMDiffOn
              ((𝓡 1).prod (𝓡 1))
              ((𝓡 1).prod (𝓡 1))
               ⊤ (id ∘ f ∘ id)
              s :=
      ContMDiffOn.comp (contMDiffOn_univ.mpr ha2b) h1 (Set.subset_univ _)
    exact h2

open Bundle

lemma mobius_preimage_fst (s : Set S1) :
  (χₛ.symm ≫ₕ χₙ) ⁻¹' (Prod.fst ⁻¹' s) = s ×ˢ univ := by
  rw [χₛ, χₙ, τₙ, τₛ]
  apply Set.ext
  intro x
  simp

lemma polePoints :
  ∀ (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1),
    x.val 0 = 0 ↔ x = north_pt ∨ x = south_pt := by
  intro x
  have hsum := sumOfSquares x
  have h5 : (x.val 0) ^ 2 + (x.val 1) ^ 2 = 1 := sumOfSquares x
  constructor
  · intro hx
    have h2 : (x.val 0) ^ 2 = 0 := sq_eq_zero_iff.mpr hx
    rw [h2, AddZeroClass.zero_add (x.val 1 ^ 2)] at h5
    have h3 : x.val 1 ^ 2 = 1 := h5
    have hcoords : x.val 1 = 1 ∨ x.val 1 = -1 :=
      sq_eq_one_iff.mp h3
    rw [Subtype.ext_iff]
    cases hcoords with
    | inl pos =>
      left
      ext i
      fin_cases i
      · simp
        exact hx
      · simp
        exact pos
    | inr neg =>
      right
      ext i
      fin_cases i
      · exact hx
      · exact neg
  · intro hx
    rcases hx with rfl | rfl
    · exact rfl
    · exact rfl

lemma stereographic'_neg [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1)]
 (v : Metric.sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1) :
    stereographic' 1 (-v) v = 0 := by
  dsimp [stereographic']
  simp only [EmbeddingLike.map_eq_zero_iff]
  apply stereographic_neg_apply

lemma southIsNotNorth_general (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
  p ≠ -p := by
  intro h_eq
  have : p.val 0 = -p.val 0 := congrArg (fun (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) => p.val 0) h_eq
  have ha : p.val 0 = 0 := eq_zero_of_neg_eq (id (Eq.symm this))
  have : p.val 1 = -p.val 1 := congrArg (fun (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) => p.val 1) h_eq
  have hb : p.val 1 = 0 := eq_zero_of_neg_eq (id (Eq.symm this))
  have : p.val ∈ Metric.sphere 0 1 := p.prop
  have sphere_eq : ‖p.val‖ ^ 2 = 1 := by
        simp
  have sphere_ne : (p.val 0) ^ 2 + (p.val 1) ^ 2 = 0 := by
    have h1 : (p.val 0) ^ 2 = 0 := sq_eq_zero_iff.mpr ha
    have h2 : (p.val 1) ^ 2 = 0 := sq_eq_zero_iff.mpr hb
    have h3 : (p.val 0) ^ 2 + (p.val 1) ^ 2 = 0 := by
      rw [h1, h2]
      have :(0 : ℝ) + 0 = 0 := add_zero 0
      exact this
    exact h3
  have norm_expand : ‖p.val‖ ^ 2 = (p.val 0) ^ 2 + (p.val 1) ^ 2 := by
    simp
    exact Eq.symm (sumOfSquares p)
  have sphere_nn : ‖p.val‖ ^ 2 = 0 := by
    rw [norm_expand, sphere_ne]
  have : (0 : ℝ) = 1 := by
    rw [<-sphere_eq, <-sphere_nn]
  exact (by norm_num : (0 : ℝ) ≠ 1) this

instance (n) : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) :=
  ⟨(finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)⟩

lemma hf (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : (stereographic' 1 p).symm 0 = -p := by
  have h1 : (stereographic' 1 p).source = {p}ᶜ := stereographic'_source (p)
  have hsrc : -p ∈ (stereographic' 1 p).source := by
    rw [h1]
    have : p ≠ -p := southIsNotNorth_general p
    exact id (Ne.symm this)
  have he :  (stereographic' 1 p).symm ((stereographic' 1 p) (-p)) = -p :=
   (stereographic' 1 p).left_inv hsrc
  have : (stereographic' 1 p) (-p) = 0 := by
    convert stereographic'_neg (-p)
    simp
  have hc : (stereographic' 1 p).symm ((stereographic' 1 p) (-p)) =
            (stereographic' 1 p).symm 0 := congrArg ((stereographic' 1 p).symm) this
  rw [hc] at he
  exact he

lemma zerosAlignN (x : EuclideanSpace ℝ (Fin 1)) :
  ((stereographic' 1 north_pt).symm x).val 0 = 0 ↔ x 0 = 0 := by
  have h1 : (stereographic' 1 north_pt).source = {north_pt}ᶜ := stereographic'_source (north_pt)
  have h2 : (stereographic' 1 north_pt).symm.target = {north_pt}ᶜ := h1
  have h4 : (stereographic' 1 north_pt).symm.source = (stereographic' 1 north_pt).target := rfl
  have h5 : (stereographic' 1 north_pt).target = univ := stereographic'_target north_pt
  have h6 : x ∈ (stereographic' 1 north_pt).symm.source := by
    rw [h4, h5]
    exact trivial
  have h3 : (stereographic' 1 north_pt).symm x ∈ (stereographic' 1 north_pt).symm.target :=
    PartialHomeomorph.map_source (stereographic' 1 north_pt).symm h6
  have h7 : (stereographic' 1 north_pt).symm x ∈ ({north_pt} : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))ᶜ := by
    rw [h2] at h3
    exact h3
  have h9 : ((stereographic' 1 north_pt).symm x).val 0 = 0 ↔
            ((stereographic' 1 north_pt).symm x) = north_pt ∨
            ((stereographic' 1 north_pt).symm x) = south_pt := polePoints ((stereographic' 1 north_pt).symm x)

  have h41 : (stereographic' 1 north_pt).symm 0 = -north_pt := hf north_pt
  have h44 : (stereographic' 1 north_pt).symm 0 = south_pt := by rw [bar'.symm] at h41; exact h41

  constructor
  · intro hx
    have h2 : (stereographic' 1 north_pt).symm x = north_pt ∨
              (stereographic' 1 north_pt).symm x = south_pt := h9.mp hx
    have h3 : (stereographic' 1 north_pt).symm x = south_pt := by
      cases h2
      · exfalso
        (expose_names; exact h7 h)
      · (expose_names; exact h)

    have h4 : (stereographic' 1 north_pt).symm 0 = (stereographic' 1 north_pt).symm x := by
      rw [<-h44] at h3
      exact id (Eq.symm h3)
    have h5 : (stereographic' 1 north_pt) ((stereographic' 1 north_pt).symm 0) =
              (stereographic' 1 north_pt) ((stereographic' 1 north_pt).symm x) := by
      exact congrArg (↑(stereographic' 1 north_pt)) h4
    have h7 : 0 ∈ (stereographic' 1 north_pt).target := by trivial
    have h6 : (stereographic' 1 north_pt) ((stereographic' 1 north_pt).symm 0) = 0 :=
      PartialHomeomorph.right_inv (stereographic' 1 north_pt) h7
    have h8 : (stereographic' 1 north_pt) ((stereographic' 1 north_pt).symm x) = x :=
      PartialHomeomorph.right_inv (stereographic' 1 north_pt) h7
    have h9 : x = 0 := by
      rw [h6, h8] at h5
      exact id (Eq.symm h5)
    exact congrFun h9 0
  · intro hx
    have h3 : ((stereographic' 1 north_pt).symm x) = ((stereographic' 1 north_pt).symm 0) := by
      have : x = 0 := by
        ext i
        fin_cases i
        · exact hx
      rw [this]
    have h4 : (stereographic' 1 north_pt).symm 0 = south_pt := h44
    have h5 : (stereographic' 1 north_pt).symm x = south_pt := by
      rw [<-h3] at h4
      exact h4
    have h2 : ((stereographic' 1 north_pt).symm x).val 0 = south_pt.val 0 :=
      congrFun (congrArg Subtype.val h5) 0
    exact h2

lemma ltn1 : τₙ.source
       = Mobius'.proj ⁻¹' (S1.mk '' { x | x ≠ -north_pt }) := by
  have : φₙ.source = { x | x ≠ -north_pt } := hφₙ.source
  have : S1.mk '' φₙ.source = S1.mk '' { x | x ≠ -north_pt } := congrArg (image S1.mk) this
  have :  Mobius'.proj ⁻¹' (S1.mk '' φₙ.source) =  Mobius'.proj ⁻¹' (S1.mk '' { x | x ≠ -north_pt }) :=
    congrArg (preimage Mobius'.proj) this
  rw [<-this]
  exact rfl

lemma lt2 (pt : { x // x ∈ Metric.sphere 0 1 }) : Mobius'.proj ⁻¹' (S1.mk '' {x | x ≠ -pt})
        = {p | p.1.point ≠ -pt} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ne_of_eq_of_ne (congrArg S1.point (id (Eq.symm hy))) hx
  · intro hp
    refine ⟨p.1.point, hp, ?_⟩
    simp

lemma northTriv_source : τₙ.source = {p | p.1.point ≠ -north_pt} := by
  rw [ltn1, lt2 north_pt]

lemma lts1 : τₛ.source
       = Mobius'.proj ⁻¹' (S1.mk '' { x | x ≠ -south_pt }) := by
  have : φₛ.source = { x | x ≠ -south_pt } := hφₛ.source
  have : S1.mk '' φₛ.source = S1.mk '' { x | x ≠ -south_pt } := congrArg (image S1.mk) this
  have :  Mobius'.proj ⁻¹' (S1.mk '' φₛ.source) =  Mobius'.proj ⁻¹' (S1.mk '' { x | x ≠ -south_pt }) :=
    congrArg (preimage Mobius'.proj) this
  rw [<-this]
  exact rfl

lemma southTriv_source : τₛ.source = {p | p.1.point ≠ -south_pt} := by
    rw [lts1, lt2 south_pt]

lemma ltt_north :
  χₙ.target
    = (S1.mk '' { x | x ≠ -north_pt }) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 1))) := by
  have hdef : χₙ.target =
              (S1.mk '' φₙ.source) ×ˢ Set.univ := rfl
  have : φₙ.source = { x | x ≠ -north_pt } := hφₙ.source
  rw [this] at hdef
  exact hdef

lemma ltt_south :
  χₛ.target
    = (S1.mk '' { x | x ≠ -south_pt }) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 1))) := by
  have hdef : χₛ.target =
              (S1.mk '' φₛ.source) ×ˢ Set.univ := rfl
  have : φₛ.source = { x | x ≠ -south_pt } := hφₛ.source
  rw [this] at hdef
  exact hdef

lemma ltt2 (pt : { x // x ∈ Metric.sphere 0 1 }) :
  (S1.mk '' { x | x ≠ -pt }) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 1)))
    = { p | p.point ≠ -pt } ×ˢ Set.univ := by
  ext p
  simp
  constructor
  · rintro ⟨x, hx, hy⟩
    have h3 : ⟨x, hx⟩ = p.1.point :=
      Eq.symm ((fun x y ↦ (S1MobiusBase x y).mp) p.1 ⟨x, hx⟩ (id (Eq.symm hy.2)))
    exact ne_of_eq_of_ne (id (Eq.symm h3)) hy.1
  · intro hp
    have h2 : { point := ⟨p.1.point, p.1.point.property⟩ } = p.1 := rfl
    refine ⟨p.1.point, p.1.point.property,  And.symm ((fun {a b} ↦ Classical.not_imp.mp) fun a ↦ hp (a h2))⟩

lemma hχₙ.target : χₙ.target = { p | p.point ≠ -north_pt } ×ˢ Set.univ := by
  rw [ltt_north, ltt2 north_pt]

lemma hχₛ.target : χₛ.target = { p | p.point ≠ -south_pt } ×ˢ Set.univ := by
  rw [ltt_south, ltt2 south_pt]

lemma ψₙ_source : ψₙ.source = τₙ.source := by
  have h4 : τₙ.source ⊆ τₙ ⁻¹' τₙ.target := PartialHomeomorph.source_preimage_target χₙ
  have h5 : τₙ.source ∩ χₙ ⁻¹' τₙ.target = τₙ.source := Set.inter_eq_left.mpr h4
  exact h5

lemma ψₛ_source : ψₛ.source = τₛ.source := by
  have h4 : τₛ.source ⊆ τₛ ⁻¹' τₛ.target := PartialHomeomorph.source_preimage_target χₛ
  have h5 : τₛ.source ∩ χₛ ⁻¹' τₛ.target = τₛ.source := Set.inter_eq_left.mpr h4
  exact h5

lemma hNφₙ.target : (φN φₙ).target = univ := hφₙ.target
lemma hNφₛ.target : (φN φₛ).target = univ := hφₛ.target

lemma exχₙA : ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).target = univ := by
  rw [PartialHomeomorph.prod_target, hNφₙ.target]
  simp

lemma exχₙB : (((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' χₙ.target) = univ := by
    have h1 : (χₙ ≫ₕ ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))).target =
    ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).target ∩
    (((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' χₙ.target) :=
    PartialHomeomorph.trans_target χₙ ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
    have h9 : ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm.source ⊆
      ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
        ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm.target :=
          PartialHomeomorph.source_preimage_target
           ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm
    have ha : ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm.source = univ := exχₙA
    have hb : univ ⊆
          ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
        ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm.target := by
      rw [ha] at h9
      exact h9
    have hd :
      ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' χₙ.target =
      univ := eq_univ_of_univ_subset hb
    exact hd

lemma exΧₙ :
  (χₙ ≫ₕ ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))).target = univ := by
    have h1 : (χₙ ≫ₕ ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))).target =
    ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).target ∩
    (((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' χₙ.target) :=
    PartialHomeomorph.trans_target χₙ ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
    have hc : ((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).target ∩
      (((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' χₙ.target) =
      univ := by
        rw [exχₙA, exχₙB, univ_inter univ] at h1
        exact h1
    exact hc

lemma exχₛA : ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).target = univ := by
  rw [PartialHomeomorph.prod_target, hNφₛ.target]
  simp

lemma exχₛB : (((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' χₛ.target) = univ := by
    have h1 : (χₛ ≫ₕ ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))).target =
    ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).target ∩
    (((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' χₛ.target) :=
    PartialHomeomorph.trans_target χₛ ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
    have h9 : ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm.source ⊆
      ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
        ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm.target :=
          PartialHomeomorph.source_preimage_target
           ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm
    have ha : ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm.source = univ := exχₛA
    have hb : univ ⊆
          ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
        ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm.target := by
      rw [ha] at h9
      exact h9
    have hd :
      ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' χₛ.target =
      univ := eq_univ_of_univ_subset hb
    exact hd

lemma exΧₛ :
  (χₛ ≫ₕ ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))).target = univ := by
    have h1 : (χₛ ≫ₕ ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))).target =
    ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).target ∩
    (((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' χₛ.target) :=
    PartialHomeomorph.trans_target χₛ ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
    have hc : ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).target ∩
      (((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' χₛ.target) =
      univ := by
        rw [exχₛA, exχₛB, univ_inter univ] at h1
        exact h1
    exact hc

lemma preimage_point_param
    (φₙ : PartialHomeomorph ↑MobiusBase (EuclideanSpace ℝ (Fin 1))) (a : MobiusBase) :
    (φN φₙ).symm ⁻¹' {x : S1 | x.point ≠ a} =
      φₙ.symm ⁻¹' {x : MobiusBase | x ≠ a} := by
  ext s
  simp [φN]

open Function

lemma φs_symm_maps_neg_north_pt_eq_zero : ∀ p, φₛ.symm p = -north_pt ↔ p = 0 := by
  intro p
  have h7 : ((stereographic' 1 (-south_pt)).symm p).val 0 = 0 ↔ p 0 = 0 := by
    rw [<-bar]
    exact zerosAlignN p
  have h8 : (φₛ.symm p).val 0 = 0 ↔ p 0 = 0 := h7
  have h9 : (φₛ.symm p).val 0 = 0 ↔ (φₛ.symm p) = north_pt ∨ (φₛ.symm p) = south_pt :=
    polePoints (φₛ.symm p)
  have ha : φₛ.source = {x | x ≠ north_pt} := by
    rw [bar]
    exact hφₛ.source
  have hb : φₛ.target = univ := hφₛ.target
  have : p ∈ φₛ.target := by
    have hb1 : p ∈ univ := trivial
    rw [<-hb] at hb1
    exact hb1
  have hc : (φₛ.symm p) ∈ φₛ.source := φₛ.map_target this
  have hd : (φₛ.symm p) ∈ {x | x ≠ north_pt} := by
    rw [ha] at hc
    exact hc
  have he : (φₛ.symm p) ≠ north_pt := hd
  have hf : (φₛ.symm p = north_pt ∨ φₛ.symm p = south_pt) ↔ (φₛ.symm p = south_pt) := by
    apply or_iff_right_of_imp
    intro h
    exact (he h).elim
  have hg : p 0 = 0 ↔ (φₛ.symm p = south_pt) := by
    have : (φₛ.symm p).val 0 = 0 ↔ φₛ.symm p = south_pt := Iff.trans h9 hf
    have :  p 0 = 0 ↔ φₛ.symm p = south_pt := Iff.trans h8.symm this
    exact this
  have hh : (φₛ.symm p = -north_pt) ↔ p 0 = 0 := by
    rw [bar]
    rw [InvolutiveNeg.neg_neg south_pt]
    exact hg.symm

  have hi : (p : EuclideanSpace ℝ (Fin 1)) 0 = 0 ↔ p = 0 := by
    constructor
    · intro h
      funext i
      fin_cases i
      exact h
    · intro h
      rw [h]
      exact rfl

  exact Iff.symm (Iff.trans (id (Iff.symm hi)) (id (Iff.symm hh)))

lemma φₛ_preimage_ne_zero :
    φₛ.symm ⁻¹' {x | x.val 0 ≠ 0} = {x | x ≠ 0} := by
  ext x
  have hg : φₛ.symm x = -north_pt ↔ x = 0 := φs_symm_maps_neg_north_pt_eq_zero x
  have ha : (φₛ.symm x).val 0 = 0 ↔ φₛ.symm x = north_pt ∨ φₛ.symm x = south_pt := polePoints (φₛ.symm x)
  have he : (φₛ.symm x).val 0 ≠ 0 ↔ ¬(φₛ.symm x = north_pt ∨ φₛ.symm x = south_pt) := not_iff_not.mpr ha
  have hf : ¬(φₛ.symm x = north_pt ∨ φₛ.symm x = south_pt) ↔
            (φₛ.symm x ≠ north_pt) ∧ (φₛ.symm x ≠ south_pt) := not_or
  have hd : (φₛ.symm x).val 0 ≠ 0 ↔ φₛ.symm x ≠ north_pt ∧ φₛ.symm x ≠ south_pt :=
    Iff.symm (Iff.trans (id (Iff.symm hf)) (id (Iff.symm he)))
  have hc : φₛ.symm.target = {x | x ≠ -south_pt} := hφₛ.source
  constructor
  · intro hx
    have h7 : φₛ.symm x ≠ north_pt ∧ φₛ.symm x ≠ south_pt := hd.mp hx
    have h9 : φₛ.symm x ≠ south_pt := h7.2
    have hu : φₛ.symm x ≠ -north_pt := by rw [bar'] at h9; exact h9
    have hy : x ≠ 0 := by
      intro h0
      rw [hg.mpr h0] at hu
      exact hu rfl
    exact hy
  · intro hx
    have h1 : x ≠ 0 := hx
    have h2 : φₛ.symm x ≠ -north_pt := by
      intro h0
      rw [hg.mp h0] at h1
      exact h1 rfl
    have h3 : φₛ.symm x ≠ south_pt := by rw [<-bar'] at h2; exact h2
    have h6 : φₛ.symm.source = univ:= hφₛ.target
    have h7 : x ∈ univ := trivial
    have h5 : φₛ.symm x ∈ φₛ.symm.target := φₛ.symm.mapsTo (h6 ▸ h7)
    have h9 : φₛ.symm x ≠ -south_pt := mem_of_mem_inter_left h5
    have ha : φₛ.symm x ≠ north_pt := by rw [<-bar] at h9; exact h9
    have h4 :(φₛ.symm x ≠ north_pt) ∧ (φₛ.symm x ≠ south_pt) := And.intro ha h3
    have hb :  (φₛ.symm x).val 0 ≠ 0 := hd.mpr h4
    exact hb

lemma ll1 : φₛ.symm ⁻¹' {x | x.val 0 ≠ 0} = {p | φₛ.symm p ≠ -north_pt} := by
  have h8 : ∀ (p : EuclideanSpace ℝ (Fin 1)), φₛ.symm p = -north_pt ↔ p = 0 := φs_symm_maps_neg_north_pt_eq_zero
  have h7 : φₛ.symm ⁻¹' {x | x.val 0 ≠ 0} = {x | x ≠ 0} := φₛ_preimage_ne_zero

  have : φₛ.symm ⁻¹' {x | x.val 0 ≠ 0} = {p | φₛ.symm p ≠ -north_pt} := by
    rw [h7]
    ext x
    constructor
    · intro hx
      have : x ≠ 0 := hx
      have : φₛ.symm x ≠ -north_pt := by (expose_names; exact (Iff.ne (h8 x)).mpr hx)
      exact this
    · intro hx
      have : φₛ.symm x ≠ -north_pt := hx
      have :  x ≠ 0 := by (expose_names; exact (Iff.ne (h8 x)).mp hx)
      exact this
  exact this

lemma ll2 (h : φₛ.symm ⁻¹' {x | x.val 0 ≠ 0} = {p | φₛ.symm p ≠ -north_pt}) :
    (φN φₛ).symm ⁻¹' {x | x.point.val 0 ≠ 0} = {p | (φN φₛ).symm p ≠ S1.mk (-north_pt)} := by
  ext p
  constructor
  · intro hx
    have h1 : p ∈ {p | φₛ.symm p ≠ -north_pt} := h ▸ hx
    have h2 : φₛ.symm p ≠ -north_pt := h1
    have h3 : p ∈ {p | S1.mk (φₛ.symm p) ≠ S1.mk (-north_pt)} :=
      (not_congr ((S1.mk_inj (φₛ.symm p) (-north_pt)))).mpr h2
    exact h3
  · intro hx
    have h7 : p ∈  φₛ.symm ⁻¹' {x | x.val 0 ≠ 0} ↔ p ∈ {p | φₛ.symm p ≠ -north_pt} :=
      Eq.to_iff (congrFun h p)
    have h6 : (φN φₛ).symm p ≠ S1.mk (-north_pt) ↔ φₛ.symm p ≠ -north_pt :=
      not_congr (S1.ext_iff ((φN φₛ).symm p) (S1.mk (-north_pt)))
    have h9 : (φN φₛ).symm p ≠ S1.mk (-north_pt) ↔ p ∈  φₛ.symm ⁻¹' {x | x.val 0 ≠ 0} :=
      Iff.symm (Iff.trans h7 (id (Iff.symm h6)))
    have ha :  p ∈ ↑φₛ.symm ⁻¹' {x | x.val 0 ≠ 0}  := h9.mp hx
    exact ha

lemma ll3 (h : (φN φₛ).symm ⁻¹' {x | x.point.val 0 ≠ 0} = {p | (φN φₛ).symm p ≠ S1.mk (-north_pt)}) :
    ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' {x | x.1.point.val 0 ≠ 0} =
    { p | (φN φₛ).symm p.1 ≠ S1.mk (-north_pt)} := by
    ext p
    constructor
    · intro hx
      have : p.1 ∈ {p | (φN φₛ).symm p ≠ S1.mk (-north_pt)} := by rwa [← h]
      exact this
    · intro hx
      have : p.1 ∈ (φN φₛ).symm ⁻¹' {x | x.point.val 0 ≠ 0} := by rwa [h]
      exact this

lemma totalAtlasTarget
  (e : PartialHomeomorph Mobius'.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
  (he : e ∈ totalAtlas') : e.target = univ := by
  rcases he with (rfl | rfl)
  · exact exΧₙ
  · exact exΧₛ

lemma h9pre' : ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source =
    ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
      {x | x.1.point.val 0 > 0 ∨ x.1.point.val 0 < 0} := by
  have h0 : (ψₛ.symm) ⁻¹' ψₙ.source =
    ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' (
      ((χₛ).symm ⁻¹' τₙ.source)) := by
    exact congrArg (preimage ↑ψₛ.symm) ψₙ_source

  have h1 :
  ((χₛ).symm ⁻¹' τₙ.source) =
    { q | ((χₛ).symm q).1.point ≠ -north_pt } := by
      ext q
      simp [northTriv_source, Set.mem_setOf_eq]

  have h2 :
  ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
    { q | ((χₛ).symm q).1.point ≠ -north_pt }
  =
  { p | ((φN φₛ).symm p.1).point ≠ -north_pt } := by
    ext p
    cases p with
    | mk x y =>
    simp [Set.mem_setOf_eq]
    exact Eq.to_iff rfl

  have h3 :
  (ψₛ.symm) ⁻¹' ψₙ.source
  =
  { p | ((φN φₛ).symm p.1).point ≠ -north_pt } := by
    rw [h0, h1, <-h2]

  have h4 : ψₛ.target = univ := totalAtlasTarget ψₛ (Or.inr rfl)

  have h5 : ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source =
            { p | ((φN φₛ).symm p.1).point ≠ -north_pt } := by
    rw [h4, h3, Set.inter_comm, Set.inter_univ]

  have h8 : ∀ (p : EuclideanSpace ℝ (Fin 1)), φₛ.symm p = -north_pt ↔ p = 0 := φs_symm_maps_neg_north_pt_eq_zero
  have h7 : φₛ.symm ⁻¹' {x | x.val 0 ≠ 0} = {x | x ≠ 0} := φₛ_preimage_ne_zero

  have : φₛ.symm ⁻¹' {x | x.val 0 ≠ 0} = {p | φₛ.symm p ≠ -north_pt} := by
    rw [h7]
    ext x
    constructor
    · intro hx
      have : x ≠ 0 := hx
      have : φₛ.symm x ≠ -north_pt := by (expose_names; exact (Iff.ne (h8 x)).mpr hx)
      exact this
    · intro hx
      have : φₛ.symm x ≠ -north_pt := hx
      have :  x ≠ 0 := by (expose_names; exact (Iff.ne (h8 x)).mp hx)
      exact this

  have h9 : ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
           {x | x.1.point.val 0 ≠ 0} =
          {p | (φN φₛ).symm p.1 ≠ { point := -north_pt}} := ll3 (ll2 ll1)

  have hb : {p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) |
          (φN φₛ).symm p.1 ≠ { point := -north_pt}} =
       {p | ((φN φₛ).symm p.1).point ≠ -north_pt} := by
    ext p
    simp [S1.ext_iff]

  have ha : ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
              {x | x.1.point.val 0 ≠ 0 } =
            {p | ((φN φₛ).symm p.1).point ≠ -north_pt} := by
    rw [<-hb]
    exact h9

  have hc : ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source =
   ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'{x | x.1.point.val 0 ≠ 0 } := by
    calc ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source
      = { p | ((φN φₛ).symm p.1).point ≠ -north_pt } := h5
    _ = ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
          {x | x.1.point.val 0 ≠ 0 } := ha.symm

  have : {x : S1 × EuclideanSpace ℝ (Fin 1) | x.1.point.val 0 > 0 ∨ x.1.point.val 0 < 0} =
         {x | x.1.point.val 0 ≠ 0 } := by
    ext x
    simp
    exact ne_comm

  rw [<-this] at hc

  have hd :   ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source =
    ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
      {x | x.1.point.val 0 > 0 ∨ x.1.point.val 0 < 0}  := hc

  exact hd

open Metric

lemma hh41 (h : φₛ.symm ⁻¹' φₙ.source = {x | x ≠ 0}) :
  (φN φₛ).symm ⁻¹' (φN φₙ).source = {x | x ≠ 0} := by
    ext p
    have h6 : S1.mk (φₛ.symm p) ∈ (φN φₙ).source ↔ (φₛ.symm p) ∈ φₙ.source := liftedPts (φₛ.symm p) φₙ
    constructor
    · intro hx
      exact h ▸ (h6.mp hx)
    · intro hx
      have h2 : p ∈ φₛ.symm ⁻¹' φₙ.source := h ▸ hx
      exact (h6.mpr h2)

lemma hh42 (h : (φN φₛ).symm ⁻¹' (φN φₙ).source = {x | x ≠ 0}) :
((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' (φN φₙ).source ×ˢ univ =
  { x | x.1 ≠ 0 } := by
  ext p
  constructor
  · intro hx
    have : p.1 ∈ {x | x ≠ 0} := by rw [← h]; exact hx.1
    exact this
  · intro hx
    have hx1 : p.1 ∈ (φN φₛ).symm ⁻¹' (φN φₙ).source := h ▸ hx
    have : p ∈ ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
               (φN φₙ).source ×ˢ univ := And.intro hx1 trivial
    exact this

lemma kk1 : φₛ.symm ⁻¹' {x | x.val 0 ≠ 0} = {x | x ≠ 0} := φₛ_preimage_ne_zero

lemma kk2 (h : φₛ.symm ⁻¹' {x | x.val 0 ≠ 0} = {x | x ≠ 0}) :
  (φN φₛ).symm ⁻¹' {x | x.point.val 0 ≠ 0} = {x | x ≠ 0} := by
  ext p
  have h6 : S1.mk (φₛ.symm p) ∈  {x | x.point.val 0 ≠ 0} ↔ (φₛ.symm p) ∈ {x | x.val 0 ≠ 0} :=
    MapsTo.mem_iff (fun ⦃x⦄ a ↦ a) fun ⦃x⦄ a ↦ a
  constructor
  · intro hx
    exact h ▸ (h6.mp hx)
  · intro hx
    have h2 : p ∈ φₛ.symm ⁻¹' {x | x.val 0 ≠ 0} := h ▸ hx
    exact (h6.mpr h2)

lemma kk3 (h : (φN φₛ).symm ⁻¹' {x | x.point.val 0 ≠ 0} = {x | x ≠ 0}) :
((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
        {x | x.1.point.val 0 ≠ 0} = {x | x.1 ≠ 0} := by
  ext ⟨a, b⟩
  simp
  have : (a ∈ (φN φₛ).symm ⁻¹' {x | x.point.val 0 ≠ 0}) = (a ∈ {x | x ≠ 0}) :=
    (congrArg (fun s => a ∈ s) h)
  have : ((φN φₛ).symm a).point.val 0 ≠ 0 ↔ a ≠ 0 := Eq.to_iff this
  exact this

lemma h9pre'' : ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source =
  (↑(χₛ.symm ≫ₕ χₙ) ∘
      (↑((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm)) ⁻¹'
    (φN φₙ).source ×ˢ univ := by

  have h1 : (χₛ.symm ≫ₕ χₙ ∘
    ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm) ⁻¹'
      ((φN φₙ).source ×ˢ univ) =
  (((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm) ⁻¹'
    ((χₛ.symm ≫ₕ χₙ) ⁻¹'
      ((φN φₙ).source ×ˢ univ)) := rfl
  have h2 : (χₛ.symm ≫ₕ χₙ) ⁻¹'
    ((φN φₙ).source ×ˢ univ) =
    (φN φₙ).source ×ˢ univ := by
      rw [← mobius_preimage_fst (φN φₙ).source]
      rfl
  have h3 : ↑(χₛ.symm ≫ₕ χₙ) ∘
        ↑((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
      (φN φₙ).source ×ˢ univ =
    ↑((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' (φN φₙ).source ×ˢ univ := by rw [h2] at h1; exact h1
  have h4 : (χₛ.symm ≫ₕ χₙ) ∘
        ↑((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
      (φN φₙ).source ×ˢ univ = {x | x.1 ≠ 0} := hh42 (hh41  hhh4)

  have h5 : ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source =
    ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
      {x | x.1.point.val 0 > 0 ∨ x.1.point.val 0 < 0} := h9pre'

  have : {x : S1 × EuclideanSpace ℝ (Fin 1) | x.1.point.val 0 > 0 ∨ x.1.point.val 0 < 0} =
    {x | x.1.point.val 0 ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [or_comm, ← ne_iff_lt_or_gt]

  have h7 : ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source =
      ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
        {x | x.1.point.val 0 ≠ 0} := by rw [this] at h5; exact h5

  have h8 : ↑((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' {x | x.1.point.val 0 ≠ 0} =
    {x | x.1 ≠ 0} := kk3 (kk2 kk1)

  have h9 :  ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source =  {x | x.1 ≠ 0} := by
    rw [h7, h8]

  have h6 : ↑((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
    (φN φₙ).source ×ˢ univ = {x | x.1 ≠ 0} := hh42 (hh41  hhh4)

  have hw :  ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source =
   ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹'
    (φN φₙ).source ×ˢ univ := by
    rw [h9, <-h6]

  exact hw

lemma bothContMDiff'' : ContDiffOn ℝ ⊤ (ψₙ ∘ ψₛ.symm) (ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source):= by

  let f := ((((φN φₙ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) ∘
    (χₛ.symm ≫ₕ χₙ) ∘
    ((φN φₛ).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm))

  have h9pre : (ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source) ⊆ (φN φₛ).target ×ˢ univ := by
    have hf : (φN φₛ).target = univ := hφₛ.target
    have hg : (φN φₛ).target ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 1))) = Set.univ := by
      rw [hf, Set.univ_prod_univ]
    have hi : (ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source) ⊆ (φN φₛ).target ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 1))) := by
      rw [hg]
      exact Set.subset_univ ((ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source))
    exact hi

  have h9 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
    f
    (ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source) :=
      ContMDiffOn.comp side1
        (ContMDiffOn.comp bothContMDiffSN
          (ContMDiffOn.mono side2 h9pre)
          (by rw [h9pre']))
        (by rw [h9pre''])

  have h93 : ContMDiffOn
   𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
   𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
   ⊤ (ψₙ ∘ ψₛ.symm) (ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source) :=
     (changeModelSpace f (ψₛ.target ∩ ↑ψₛ.symm ⁻¹' ψₙ.source)).mp h9

  exact contMDiffOn_iff_contDiffOn.mp h93

lemma preKkk'
  (ψₙ : PartialHomeomorph Mobius'.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
  (ψₛ : PartialHomeomorph Mobius'.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
  (h1 : ContDiffOn ℝ ⊤ (ψₙ ∘ ψₛ.symm) (ψₛ.target ∩ ψₛ.symm ⁻¹' ψₙ.source))
  (h6 : ψₛ.target = univ) (h6' : ψₙ.target = univ) :
  ContDiffOn ℝ ⊤ ((ψₛ.symm ≫ₕ ψₙ)) ((ψₛ.symm ≫ₕ ψₙ).source ∩ ψₙ.target) := by
  have h0 : (ψₙ ∘ ψₛ.symm) = (ψₛ.symm ≫ₕ ψₙ) := rfl
  have h4 : (ψₛ.symm ≫ₕ ψₙ).source = ψₛ.symm.source ∩ ↑ψₛ.symm ⁻¹' ψₙ.source :=
    PartialHomeomorph.trans_source ψₛ.symm ψₙ
  have h5 : ψₛ.symm.source = ψₛ.target := rfl
  have h8 : univ ∩ ψₛ.symm ⁻¹' ψₙ.source = ψₛ.symm ⁻¹' ψₙ.source :=
    univ_inter (ψₛ.symm ⁻¹' ψₙ.source)
  have h7 : (ψₛ.symm ≫ₕ ψₙ).source = ψₛ.symm ⁻¹' ψₙ.source := by
    rw [h5, h6, h8] at h4
    exact h4
  have ha : (ψₛ.target ∩ ψₛ.symm ⁻¹' ψₙ.source) = (ψₛ.symm ⁻¹' ψₙ.source ∩ ψₛ.target) :=
    inter_comm ψₛ.target (ψₛ.symm ⁻¹' ψₙ.source)
  have h2 : ContDiffOn ℝ ⊤ ((ψₛ.symm ≫ₕ ψₙ)) ((ψₛ.symm ≫ₕ ψₙ).source ∩ ψₛ.target) := by
    rw [h7, <-h0, <-ha]
    exact h1
  have h9 : ψₙ.target = ψₛ.target := by
    calc ψₙ.target = univ := h6'
      _ = ψₛ.target := h6.symm
  rw [<-h9] at h2
  exact h2

lemma kkk'' :
  ∀ (e e' : PartialHomeomorph Mobius'.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))),
    e ∈ totalAtlas' →
    e' ∈ totalAtlas' →
      ContDiffOn ℝ ⊤ (e.symm ≫ₕ e') ((e.symm ≫ₕ e').source ∩ e'.target) := by
  have h6  : ψₛ.target = univ := totalAtlasTarget ψₛ (Or.inr rfl)
  have h6' : ψₙ.target = univ := totalAtlasTarget ψₙ (Or.inl rfl)
  intros e e' he he'
  rcases he with (rfl | rfl)
  · rcases he' with (rfl | rfl)
    · have h1 : ContDiffOn ℝ ⊤ (ψₙ ∘ ψₙ.symm) (ψₙ.target ∩ ψₙ.symm ⁻¹' ψₙ.source) := jjj ψₙ
      exact preKkk' ψₙ ψₙ h1 h6' h6'
    · have hb : ContDiffOn ℝ ⊤ (ψₛ ∘ ψₙ.symm) (ψₙ.target ∩ ψₙ.symm ⁻¹' ψₛ.source) := sorry
      exact preKkk' ψₛ ψₙ hb h6' h6
  · rcases he' with (rfl | rfl)
    · have h1 : ContDiffOn ℝ ⊤ (ψₙ ∘ ψₛ.symm) (ψₛ.target ∩ ψₛ.symm ⁻¹' ψₙ.source) := bothContMDiff''
      exact preKkk' ψₙ ψₛ h1 h6 h6'
    · have h1 : ContDiffOn ℝ ⊤ (ψₛ ∘ ψₛ.symm) (ψₛ.target ∩ ψₛ.symm ⁻¹' ψₛ.source) := jjj ψₛ
      exact preKkk' ψₛ ψₛ h1 h6 h6

lemma ContDiffOn.conjugate_same_space
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → E} {s : Set E}
  {φ : E ≃ₜ E}
  (hf : ContDiffOn ℝ ⊤ f s)
  (hφ : ContDiff ℝ ⊤ (⇑φ))
  (hφ_inv : ContDiff ℝ ⊤ (⇑φ.symm)) :
  ContDiffOn ℝ ⊤ (⇑φ ∘ f ∘ ⇑φ.symm) (⇑φ.symm ⁻¹' s ∩ Set.range (⇑φ)) := by
  let t : Set E := ⇑φ.symm ⁻¹' s ∩ Set.range (⇑φ)
  have h_phi_symm_on_t : ContDiffOn ℝ ⊤ (⇑φ.symm) t := by
    exact hφ_inv.contDiffOn.mono Set.inter_subset_left
  have h_f_on_s : ContDiffOn ℝ ⊤ f s := hf
  have maps_phi_symm_t_s : MapsTo (⇑φ.symm) t s := by
    intro x hx
    exact hx.1
  have h_f_comp_phi_symm_on_t : ContDiffOn ℝ ⊤ (f ∘ ⇑φ.symm) t := by
    exact ContDiffOn.comp h_f_on_s h_phi_symm_on_t maps_phi_symm_t_s
  let im : Set E := Set.image (f ∘ ⇑φ.symm) t
  have h_phi_on_im : ContDiffOn ℝ ⊤ (⇑φ) im := by
    exact hφ.contDiffOn.mono (Set.subset_univ im)
  have maps_h_to_im : MapsTo (f ∘ ⇑φ.symm) t im := by
    intro x hx
    exact Set.mem_image_of_mem (f ∘ ⇑φ.symm) hx
  have h_conjugate_on_t : ContDiffOn ℝ ⊤ (⇑φ ∘ f ∘ ⇑φ.symm) t := by
    exact ContDiffOn.comp h_phi_on_im h_f_comp_phi_symm_on_t maps_h_to_im
  exact h_conjugate_on_t

noncomputable
def I := (𝓡 1).prod (𝓡 1)

lemma kkk'
  (e e' : PartialHomeomorph Mobius'.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
  (he : e ∈ totalAtlas')
  (he' : e' ∈ totalAtlas') :
  ContDiffOn ℝ ⊤
    (↑I ∘ ↑(e.symm ≫ₕ e') ∘ ↑I.symm)
    (↑I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range ↑I) := by
  have h3 : e.target = univ := totalAtlasTarget e he
  have h4 : e'.target = univ := totalAtlasTarget e' he'
  simpa [I, ModelWithCorners.toPartialEquiv, Function.comp, h3, h4] using kkk'' e e' he he'

lemma my_mem_chart_source'' : ∀ (x : Mobius'.TotalSpace), x ∈ (if x.1.point = north_pt then ψₙ else ψₛ).source := by
  intro x
  by_cases h : x.1.point = north_pt
  case pos => have h1 : x.proj.point = north_pt := h
              rw [if_pos h]
              have h1 : ψₙ.source = {p | p.proj.point ≠ -north_pt} := calc
                ψₙ.source = τₙ.source := ψₙ_source
                _ = {p | p.proj.point ≠ -north_pt} := northTriv_source
              have h2 : north_pt ≠ -north_pt := southIsNotNorth_general north_pt
              have h3 : x.proj.point ≠ -north_pt := ne_of_eq_of_ne h h2
              have h5 : x ∈ ψₙ.source := h1 ▸ h3
              exact h5
  case neg => rw [if_neg h]
              have h1 : ψₛ.source = {p | p.proj.point ≠ -south_pt} := calc
                ψₛ.source = τₛ.source := ψₛ_source
                _ = {p | p.proj.point ≠ -south_pt} := southTriv_source
              have h3 : ψₛ.source = {p | p.proj.point ≠ north_pt} := by rw [<-bar] at h1; exact h1
              have h5 : x ∈ {p | p.proj.point ≠ north_pt} := h
              have h6 : x ∈ ψₛ.source := by rw [<-h3] at h5; exact h5
              exact h6

noncomputable
instance Mobius'.ChartedSpace :
  ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) Mobius'.TotalSpace :=
  { atlas := totalAtlas'
  , chartAt x := if x.1.point = north_pt then ψₙ else ψₛ
  , mem_chart_source := my_mem_chart_source''
  , chart_mem_atlas := by
      intro x
      dsimp
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
  }

noncomputable
instance : @IsManifold ℝ _ _ _ _ _ _  ((𝓡 1).prod (𝓡 1)) ⊤ Mobius'.TotalSpace _  Mobius'.ChartedSpace :=
  isManifold_of_contDiffOn ((𝓡 1).prod (𝓡 1)) ⊤ Mobius'.TotalSpace kkk'

#synth IsManifold ((𝓡 1).prod (𝓡 1)) ⊤ (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius'.Fiber)
