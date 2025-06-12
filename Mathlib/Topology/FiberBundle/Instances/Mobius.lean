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
-- import Mathlib.Topology.FiberBundle.Instances.SmoothFiberBundle

set_option linter.style.longLine false

open Function Set

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
noncomputable def V := chartAt (EuclideanSpace ℝ (Fin 1))
  (⟨u, g⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

/-- The constructed chart at x in the standard unit sphere S¹. -/
noncomputable def U := chartAt (EuclideanSpace ℝ (Fin 1))
  (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
  ⟨(finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)⟩

lemma hU.source : U.source = { x | x ≠ -xh } :=
  calc U.source = (chartAt (EuclideanSpace ℝ (Fin 1)) xh).source := rfl
    _ = (stereographic' 1 (-xh)).source := rfl
    _ = {-xh}ᶜ := stereographic'_source (-xh)
    _ = { x | x ≠ -xh } := rfl

lemma hV.source : V.source = { x | x ≠ -ug} :=
  calc V.source = (chartAt (EuclideanSpace ℝ (Fin 1)) ug).source := rfl
    _ = (stereographic' 1 (-ug)).source := rfl
    _ = {-ug}ᶜ := stereographic'_source (-ug)
    _ = { x | x ≠ -ug } := rfl

noncomputable
def MyCoordChange : Fin 2 → Fin 2 →
                    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → EuclideanSpace ℝ (Fin 1) →
                    EuclideanSpace ℝ (Fin 1)
  | 0, 0, _, α => α
  | 0, 1, x, α => if (x.val 1) > 0 then α else -α
  | 1, 0, x, α => if (x.val 1) > 0 then α else -α
  | 1, 1, _, α => α

theorem MyCoordChange_self : ∀ (i : Fin 2),
    ∀ x ∈ (fun i => if i = 0 then U.source else V.source) i,
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
  ∀ x ∈ (fun i => if i = 0 then U.source else V.source) i ∩
        (fun i => if i = 0 then U.source else V.source) j ∩
        (fun i => if i = 0 then U.source else V.source) k,
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

lemma myNeg (a b : ℝ) : -!₂[a, b] = !₂[-a, -b] := by
  let x := ![a, b]
  let y := ![-a, -b]
  have h1 : -(![a, b]) = ![-a, -b] := by simp
  have h2 : -x = y := by rw [h1]
  have h3 : (WithLp.equiv 2 (Fin 2 → ℝ)) (-x) = -(WithLp.equiv 2 (Fin 2 → ℝ)) x := WithLp.equiv_neg 2 x
  rw [h2] at h3
  exact h3.symm

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
    simp [Set.mem_setOf_eq] at h3
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

theorem SulSource : U.source ∩ V.source = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := by
  ext y

  have h1 : { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } = { x | x.val 1 = 0 }ᶜ := by
    ext y
    simp
    exact not_congr eq_comm

  have h2 : { x | x ≠ -xh } ∩ { x | x ≠ -ug } = { -xh, -ug }ᶜ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact not_or.symm

  have ha : U.source ∩ V.source = { x | x ≠ -xh } ∩ { x | x ≠ -ug } := by rw [hU.source, hV.source]

  have hq : U.source ∩ V.source = { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := by
    calc U.source ∩ V.source = { x | x ≠ -xh } ∩ { x | x ≠ -ug } := ha
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

theorem t00 : ContinuousOn (fun p => MyCoordChange 0 0 p.1 p.2) (U.source ×ˢ univ) := continuousOn_snd

theorem t01 : ContinuousOn (fun p => MyCoordChange 0 1 p.1 p.2) ((U.source ∩ V.source) ×ˢ univ) := by
  have h1 : (U.source ∩ V.source) = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := SulSource
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

 theorem t10 : ContinuousOn (fun p => MyCoordChange 1 0 p.1 p.2) ((V.source ∩ U.source) ×ˢ univ) := by
  have h1 : MyCoordChange 1 0 = MyCoordChange 0 1 := rfl
  have h2 : (fun (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) => MyCoordChange 1 0 p.1 p.2) = (fun p => MyCoordChange 0 1 p.1 p.2) :=
    funext (fun x => by rw [h1])
  rw [h2, inter_comm]
  exact t01

theorem t11 : ContinuousOn (fun p => MyCoordChange 0 0 p.1 p.2) (V.source ×ˢ univ) := by
  have h1 : (fun (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) =>
    MyCoordChange 0 0 p.fst p.snd) = (fun p => p.snd) := by rfl
  rw [h1]
  exact continuousOn_snd

theorem MyContinuousOn_coordChange : ∀ (i j : Fin 2), ContinuousOn (fun p => MyCoordChange i j p.1 p.2)
  (((fun i => if i = 0 then U.source else V.source) i ∩
      (fun i => if i = 0 then U.source else V.source) j) ×ˢ
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
  x ∈ (fun (i : Fin 2) ↦ if i = 0 then U.source else V.source) ((fun x ↦ if x.val 0 > 0 then 0 else 1) x):= by
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
      (fun (i : Fin 2) ↦ if i = 0 then U.source else V.source) ((fun x ↦ if x.val 0 > 0 then 0 else 1) x) = U.source := by
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
    have h3 : (fun (i : Fin 2) ↦ if i = 0 then U.source else V.source) ((fun x ↦ if x.val 0 > 0 then 0 else 1) x) =
              V.source := by
                rw [h2]
                exact if_neg (by exact one_ne_zero)
    rw [h3, hV.source]
    exact h7

noncomputable
def Mobius : FiberBundleCore (Fin 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) where
  baseSet i := if i = 0 then U.source else V.source
  isOpen_baseSet i := by
    split
    · exact U.open_source
    · exact V.open_source
  indexAt x := if (x.val 0) > 0 then 0 else 1
  mem_baseSet_at := my_mem_baseSet_at
  coordChange := MyCoordChange
  coordChange_self := MyCoordChange_self
  continuousOn_coordChange := MyContinuousOn_coordChange
  coordChange_comp := MyCoordChange_comp

open scoped Manifold
open Bundle

noncomputable
instance : ChartedSpace ((EuclideanSpace ℝ (Fin 1)) × (EuclideanSpace ℝ (Fin 1)))
                       (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
 := ChartedSpace.comp
  (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))
  (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)

#synth ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))

#synth ChartedSpace ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))

def EuclideanSpace.sumEquivProd (𝕜 : Type*) [RCLike 𝕜] (ι κ : Type*) [Fintype ι] [Fintype κ] :
    EuclideanSpace 𝕜 (ι ⊕ κ) ≃L[𝕜] EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ :=
  (PiLp.sumPiLpEquivProdLpPiLp 2 _).toContinuousLinearEquiv.trans <|
    WithLp.prodContinuousLinearEquiv _ _ _ _

def EuclideanSpace.finAddEquivProd {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} :
    EuclideanSpace 𝕜 (Fin (n + m)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finSumFinEquiv.symm).toContinuousLinearEquiv.trans <|
    sumEquivProd 𝕜 _ _

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

#synth IsManifold ((𝓡 1).prod (𝓡 1)) 0 (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)

#synth IsManifold (𝓡 1) 0 (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

#synth ChartedSpace (EuclideanSpace ℝ (Fin 1)) { x // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}

#check (𝓡 1)
#check (EuclideanSpace ℝ (Fin 1))
#check ModelWithCorners ℝ
#check ((𝓡 1).prod (𝓡 1))

#synth ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
  ({ x // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} × EuclideanSpace ℝ (Fin 1))

#check IsManifold ((𝓡 1).prod (𝓡 1)) 0
  ({ x // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} × EuclideanSpace ℝ (Fin 1))

#synth ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))

open Bundle Manifold Trivialization VectorBundleCore Topology

noncomputable
def ef := Mobius.localTriv 0

noncomputable
def ef' := Mobius.localTriv 1



#check U

#check ef'.coordChange

#check FiberBundle

#check Mobius.fiberBundle
#synth FiberBundle (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber
#check FiberBundleCore.Fiber Mobius

#synth FiberBundle (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber
#synth TopologicalSpace (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)


#check PartialHomeomorph
#check (Mobius.localTriv 0).toFun
#check (Mobius.localTriv 0).continuousOn_toFun

#check ContMDiff (𝓡 2) ((𝓡 1).prod (𝓡 1)) ⊤ (Mobius.localTriv 0).toFun

#check (Mobius.localTriv 0).toPartialEquiv
#check ↑(Mobius.localTriv 0).toPartialEquiv

#check (fun (p : { x // x ∈ Metric.sphere 0 1 } × EuclideanSpace ℝ (Fin 1)) => MyCoordChange 0 1 p.1 p.2)

theorem MySmoothOn_coordChange :
  ∀ (i j : Fin 2),
  ContMDiffOn ((𝓡 1).prod (𝓡 1)) (𝓡 1) 0
    (fun (p : { x // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} × EuclideanSpace ℝ (Fin 1)) =>
      MyCoordChange i j p.1 p.2)
    (((if i = 0 then U.source else V.source) ∩
      (if j = 0 then U.source else V.source)) ×ˢ univ) := by
  intro i j
  apply contMDiffOn_zero_iff.mpr
  exact MyContinuousOn_coordChange i j

theorem ts00 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) (𝓡 1) ⊤
  (fun p => MyCoordChange 0 0 p.1 p.2) (U.source ×ˢ univ) := contMDiffOn_snd

theorem MySmoothOn_coordChange' :
  ∀ (i j : Fin 2),
  ContMDiffOn ((𝓡 1).prod (𝓡 1)) (𝓡 1) ⊤
    (fun (p : { x // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} × EuclideanSpace ℝ (Fin 1)) =>
      MyCoordChange i j p.1 p.2)
    (((if i = 0 then U.source else V.source) ∩
      (if j = 0 then U.source else V.source)) ×ˢ univ) := by
      intro i j
      fin_cases i
      · fin_cases j
        · simp [ts00]
        · exact sorry
      · fin_cases j
        · exact sorry
        · exact sorry

#synth ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)

#check isManifold_of_contDiffOn ((𝓡 1).prod (𝓡 1)) ⊤ (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)

#check PartialHomeomorph (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))

#check (sorry : (∀ (e e' : PartialHomeomorph (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))),
      e ∈ atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) →
        e' ∈ atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) →
          ContDiffOn ℝ ⊤ (↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e') ∘ ↑((𝓡 1).prod (𝓡 1)).symm)
            (↑((𝓡 1).prod (𝓡 1)).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range ↑((𝓡 1).prod (𝓡 1)))))

example (h : ∀ (e e' : PartialHomeomorph
                    (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
                    (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))),
            e ∈ atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
                      (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) →
            e' ∈ atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
                       (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) →
            ContDiffOn ℝ ⊤
              (↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e') ∘ ↑((𝓡 1).prod (𝓡 1)).symm)
              (↑((𝓡 1).prod (𝓡 1)).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range ↑((𝓡 1).prod (𝓡 1)))) :
IsManifold ((𝓡 1).prod (𝓡 1)) ⊤ (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) :=
  isManifold_of_contDiffOn ((𝓡 1).prod (𝓡 1)) ⊤ (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) h

#check Trivialization (EuclideanSpace ℝ (Fin 1)) Mobius.proj
#check Mobius.proj

noncomputable
def φ₀ : PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) := U

noncomputable
def φ₁ : PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) := V

noncomputable
def baseAtlas : Set (PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1))) :=
  {φ₀, φ₁}

lemma he : -xh = ug := sorry
lemma hg : xh = -ug := sorry
lemma hh : xh ≠ -xh := sorry
lemma hi : ug ≠ -ug := sorry

lemma U_source_union_V_source_eq_univ :
    U.source ∪ V.source = Set.univ := by
  have eq_pts := sphere_equator_points
  rw [Set.eq_univ_iff_forall]
  intro (x : Metric.sphere ((0 : EuclideanSpace ℝ (Fin 2))) 1)
  by_cases h : x.val 1 = (0 : ℝ)
  · have h1 : {y | y.val 1 = (0 : ℝ)} = {-xh, -ug} := sphere_equator_points
    have hc : x ∈ {y | y.val 1 = (0 : ℝ)} := h
    have hf : x ∈ ({-xh, -ug} : Set (Metric.sphere ((0 : EuclideanSpace ℝ (Fin 2))) 1)) := by
      rw [←h1]
      exact hc
    rcases (Set.mem_insert_iff.mp hf) with hx | hy
    · have ha : V.source = {x | x ≠ -ug} := hV.source
      have hb : V.source = {x | x ≠ xh} := by rw [hg]; exact ha
      have h1 : x = -xh := hx
      have h2 : (-xh) ∈ V.source := by
        rw [hb]
        simp only [Set.mem_setOf_eq]
        intro contra
        rw [←h1] at contra
        have foo : x = xh := contra
        have baz : x ≠ -xh := by rw [foo]; exact hh
        exact absurd h1 baz
      have h3 : x ∈ U.source ∪ V.source := by
        apply Set.mem_union_right
        have h4 : x ∈ V.source := by rw [h1]; exact h2
        exact h4
      exact h3
    · have h0 : x ∈ {-ug} := hy
      rw [Set.mem_singleton_iff] at h0
      have h1 : x = -ug := h0
      have ha : U.source = {x | x ≠ -xh} := hU.source
      have hb : U.source = {x | x ≠ ug} := by
        rw [ha, he]
      have h2 : (-ug) ∈ U.source := by
        rw [hb]
        simp only [Set.mem_setOf_eq]
        intro contra
        rw [←h1] at contra
        have foo : x = ug := contra
        have baz : x ≠ -ug := by rw [foo]; exact hi
        exact absurd h1 baz
      have h3 : x ∈ U.source ∪ V.source := by
        apply Set.mem_union_left
        have h4 : x ∈ U.source := by rw [h1]; exact h2
        exact h4
      exact h3
  · have h1 : x ∈ { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } :=
      by
        simp only [Set.mem_union, Set.mem_setOf_eq]
        have := ne_iff_lt_or_gt.mp h
        exact Or.elim this (fun hlt => Or.inr hlt) (fun hgt => Or.inl hgt)
    rw [←SulSource] at h1
    exact Set.mem_union_left _ h1.1

noncomputable def ef_chart := ef.toPartialHomeomorph ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
noncomputable def ef'_chart := ef'.toPartialHomeomorph ≫ₕ (φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

#check atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
                      (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)

lemma Mobius.localTriv_mem_trivializationAtlas (i : Fin 2) :
    Mobius.localTriv i ∈ FiberBundle.trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber := by
  rw [FiberBundle.trivializationAtlas]
  exact Set.mem_range_self i

example : ef_chart ∈ atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
                      (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) := by
  dsimp [ChartedSpace.atlas, FiberBundle.chartedSpace]

  apply Set.mem_image2_of_mem

  -- Step 1: ef ∈ trivializationAtlas image under toPartialHomeomorph
  · exact Set.mem_image_of_mem Trivialization.toPartialHomeomorph
      (Mobius.localTriv_mem_trivializationAtlas 0)

  -- Step 2: φ₀ × id ∈ base × fiber chart atlas
  · exact chart_mem_atlas _ (xh, 0)

#check (ChartedSpace.atlas : Set (PartialHomeomorph (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
                                 (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))))

#check Set.range ChartedSpace.chartAt

#check my_mem_baseSet_at
#check mem_chart_source
#check FiberBundleCore.mem_baseSet_at Mobius

#check ChartedSpace.mk baseAtlas (fun x => if x.val 0 > 0 then φ₀ else φ₁)

#check (fun x => (Mobius.localTriv (Mobius.indexAt x)).baseSet)

#check mem_source

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

#check φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))

#check fun x ↦ (Mobius.localTriv (Mobius.indexAt x)).toPartialHomeomorph ≫ₕ
 ((baseChartAt x).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

#check ChartedSpace.chartAt (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)

#check FiberBundleCore.fiberBundle

#synth ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

#check ChartedSpace.atlas
#check FiberBundle.chartedSpace

#print ChartedSpace.atlas
#print FiberBundle.chartedSpace

variable (inst : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
def hhh := inst.1  -- the atlas set

#check (FiberBundle (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)

#check (atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)).image

#check Set.image (fun e ↦ e.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
                 (atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : Set _)

def foo := Set.image (fun e ↦ e.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
                 (atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : Set _)

#check foo Mobius.chartedSpaceBase

noncomputable def baseAtlas' : Set (PartialHomeomorph
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1))
  (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :=
  (atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)).image
    (λ e ↦ e.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

def fiberAtlas := (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber).image toPartialHomeomorph

#check image2 (· ≫ₕ ·) fiberAtlas (baseAtlas' Mobius.chartedSpaceBase)

#check FiberBundleCore.fiberBundle
#check Mobius.chartedSpaceBase
#print FiberBundleCore.fiberBundle

#check (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph)

lemma trivialization_mem_iff_f (e : Trivialization _ _) :
    MemTrivializationAtlas e ↔
    e = Mobius.localTriv 0 ∨ e = Mobius.localTriv 1 := by
  dsimp [MemTrivializationAtlas, Mobius]
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

lemma Mobius_totalSpace_atlas_eq :
  atlas (↑(Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1)) (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =
  (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph) '' (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) :=
  rfl

#synth ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))

#synth ChartedSpace ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))

lemma Mobius_totalSpace_atlas_eq' :
  atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =
  (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph) '' (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) :=
  rfl

#synth MemTrivializationAtlas (trivializationAt (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber _)
#check MemTrivializationAtlas.out

#check (trivializationAt (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber _)

#check MemTrivializationAtlas

lemma totalAtlas_in_image_baseAtlas :
  atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
        (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) ⊆
  { (Mobius.localTriv 0).toPartialHomeomorph ≫ₕ φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))),
    (Mobius.localTriv 1).toPartialHomeomorph ≫ₕ φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))
       } := by

  intro e he
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]

  have h5 : e ∈ atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
                      (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) := he

  let ee : PartialHomeomorph (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
                             ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1))) := sorry

  have h6 : ee ∈ atlas ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))
                      (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) := sorry

  have h7 : ee ∈ (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph) '' (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) := by
    exact h6

  let eee1 : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) :=
    (trivializationAt (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber xh)

  have h2 : eee1 ∈ (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) := MemTrivializationAtlas.out

  have h4 : MemTrivializationAtlas eee1 := by exact instMemTrivializationAtlasTrivializationAt xh

  have h3 :  MemTrivializationAtlas eee1 ↔
             eee1 = Mobius.localTriv 0 ∨ eee1 = Mobius.localTriv 1 := trivialization_mem_iff_f eee1

  have h_atlas_def : atlas _ _ = image2 (· ≫ₕ ·) fiberAtlas (baseAtlas' Mobius.chartedSpaceBase) := by
    exact sorry

  have h1 : e = (Mobius.localTriv 0).toPartialHomeomorph ≫ₕ φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) ∨
            e = (Mobius.localTriv 1).toPartialHomeomorph ≫ₕ φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) := by
    exact sorry

  exact sorry

example : ∀ (e e' : PartialHomeomorph
                    (Bundle.TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
                    (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))),
            e ∈ atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
                      (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) →
            e' ∈ atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
                       (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) →
            ContDiffOn ℝ ⊤
              (↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e') ∘ ↑((𝓡 1).prod (𝓡 1)).symm)
              (↑((𝓡 1).prod (𝓡 1)).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range ↑((𝓡 1).prod (𝓡 1))) := by
  exact  sorry

#check ef.toPartialHomeomorph.symm ≫ₕ ef'.toPartialHomeomorph

example : ContMDiffOn (𝓡 2) ((𝓡 1).prod (𝓡 1)) 0 ↑(Mobius.localTriv 0).toFun (Mobius.localTriv 0).source := by
  sorry

#check ContMDiffOn (𝓡 2) ((𝓡 1).prod (𝓡 1)) 0 (Mobius.localTriv 0).toFun  (Mobius.localTriv 0).source
