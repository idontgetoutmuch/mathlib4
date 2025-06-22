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

#synth ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
  ({ x // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} × EuclideanSpace ℝ (Fin 1))

#synth ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))

open Bundle Manifold Trivialization VectorBundleCore Topology

noncomputable
def ef := Mobius.localTriv 0

noncomputable
def ef' := Mobius.localTriv 1

noncomputable
def φ₀ : PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) := U

noncomputable
def φ₁ : PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) := V

noncomputable
def baseAtlas : Set (PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1))) :=
  {φ₀, φ₁}

noncomputable def ef_chart := ef.toPartialHomeomorph ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
noncomputable def ef'_chart := ef'.toPartialHomeomorph ≫ₕ (φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

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

variable (inst : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))

noncomputable def baseAtlas' : Set (PartialHomeomorph
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1))
  (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :=
  (atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)).image
    (fun e ↦ e.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

def fiberAtlas := (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber).image toPartialHomeomorph

def atlas_def := image2 (· ≫ₕ ·) fiberAtlas (baseAtlas' Mobius.chartedSpaceBase)

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

#check Mobius.localTriv
#check Mobius.coordChange
#check FiberBundleCore.localTriv_apply
#check FiberBundleCore.localTriv_symm_apply
#check extChartAt

variable (x t : ℝ) (hx : x > 0)

-- Abbreviations for clarity
noncomputable def chart := (𝓡 1).prod (𝓡 1)
noncomputable def chart_symm := ((𝓡 1).prod (𝓡 1)).symm
noncomputable def e := Mobius.localTriv 0
noncomputable def e' := Mobius.localTriv 1

#check PartialHomeomorph.symm
#check Trivialization

#check (e.toPartialHomeomorph.symm ≫ₕ e'.toPartialHomeomorph)
#check (↑((𝓡 1).prod (𝓡 1)))
#check ModelWithCorners

example :  ∀ (p : Mobius.TotalSpace),
    (Mobius.localTriv 0) p = (p.proj, Mobius.coordChange (Mobius.indexAt p.proj) 0 p.proj p.snd) := by
  exact FiberBundleCore.localTriv_apply Mobius 0

noncomputable
def totalChartAt : Mobius.TotalSpace → PartialHomeomorph Mobius.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) :=
  fun x ↦
    let _ := Mobius.chartedSpaceBase
    let φ := chartAt (EuclideanSpace ℝ (Fin 1)) x.proj
    let i := Mobius.indexAt x.proj
    (Mobius.localTriv i).toPartialHomeomorph ≫ₕ (φ.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

def totalAtlas := { f | ∃ (i : Fin 2) (φ : _),
  φ ∈ baseAtlas ∧
  f = (Mobius.localTriv i).toPartialHomeomorph ≫ₕ (φ.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) }

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
     use i
     use φ
     have : chartAt (EuclideanSpace ℝ (Fin 1)) x ∈ baseAtlas := chart_mem_atlas (EuclideanSpace ℝ (Fin 1)) x
     exact And.intro this rfl
   }

#check @atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) _
                   Mobius.TotalSpace _ (Mobius.chartedSpaceTotal Mobius.chartedSpaceBase)

noncomputable
def totalChartAt' : Mobius.TotalSpace → PartialHomeomorph Mobius.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) :=
  fun x ↦
    let _ := Mobius.chartedSpaceBase
    let φ := chartAt (EuclideanSpace ℝ (Fin 1)) x.proj
    let i := Mobius.indexAt x.proj
    (Mobius.localTriv i).toPartialHomeomorph ≫ₕ (φ.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

def totalAtlas'  : Set (PartialHomeomorph Mobius.TotalSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :=
  { (Mobius.localTriv 0).toPartialHomeomorph ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))),
    (Mobius.localTriv 1).toPartialHomeomorph ≫ₕ (φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) }

noncomputable instance Mobius.chartedSpaceTotal' :
  ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) Mobius.TotalSpace :=
  { atlas := totalAtlas'
    chartAt := totalChartAt'
    mem_chart_source := by
      intro x
      dsimp [totalChartAt']
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
      dsimp [totalChartAt', totalAtlas']
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
                            φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) ∈ totalAtlas' := by simp [totalAtlas']
                  have h7 : (Mobius.localTrivAt x).toPartialHomeomorph ≫ₕ
                            (chartAt (EuclideanSpace ℝ (Fin 1)) x).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) ∈ totalAtlas' := by
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
                            φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) ∈ totalAtlas' := by simp [totalAtlas']
                  have h7 : (Mobius.localTrivAt x).toPartialHomeomorph ≫ₕ
                            (chartAt (EuclideanSpace ℝ (Fin 1)) x).prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) ∈ totalAtlas' := by
                    rw [h5]
                    exact mem_of_eq_of_mem (congrArg (Mobius.localTriv 1).trans
                      (congrFun (congrArg PartialHomeomorph.prod h1) (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))) h6
                  exact h7
   }

lemma hz1
  (x t : EuclideanSpace ℝ (Fin 1))
  (e : PartialHomeomorph Mobius.TotalSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))))
  (h : (x, t) ∈ (↑((𝓡 1).prod (𝓡 1)).symm ⁻¹' (e.symm ≫ₕ e).source ∩ range ↑((𝓡 1).prod (𝓡 1)))) :
  (x, t) ∈ ((𝓡 1).prod (𝓡 1)).symm.source := by
  rcases h with ⟨_h₁, h₂⟩
  have h1 : range ((𝓡 1).prod (𝓡 1)) = (((𝓡 1).prod (𝓡 1))).target :=
    Eq.symm (ModelWithCorners.target_eq ((𝓡 1).prod (𝓡 1)))
  have h2 : (((𝓡 1).prod (𝓡 1))).target = ((𝓡 1).prod (𝓡 1)).symm.source := rfl
  rw [h1, h2] at h₂
  exact h₂

lemma hz2
  (x t : EuclideanSpace ℝ (Fin 1))
  (e : PartialHomeomorph Mobius.TotalSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))))
  (h : (x, t) ∈ (↑((𝓡 1).prod (𝓡 1)).symm ⁻¹' (e.symm ≫ₕ e).source ∩ range ↑((𝓡 1).prod (𝓡 1)))) :
  ((𝓡 1).prod (𝓡 1)).symm (x, t) ∈ e.target := by
  rcases h with ⟨h₁, _h₂⟩
  have h1 : ((𝓡 1).prod (𝓡 1)).symm (x, t) ∈ (e.symm ≫ₕ e).source := h₁
  have h2 : (e.symm ≫ₕ e).source ⊆ e.target := by
    rw [PartialHomeomorph.trans_source, e.symm_source, ←e.image_source_eq_target]
    simp
  have h3 : ((𝓡 1).prod (𝓡 1)).symm (x, t) ∈ e.target := by
    exact h2 h₁
  exact h3

noncomputable
def conj :=
  (φ₀.prod (PartialHomeomorph.refl _)).symm ≫ₕ
  ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ
   (Mobius.localTriv 1).toPartialHomeomorph) ≫ₕ
  (φ₀.prod (PartialHomeomorph.refl _))

def A : Set ((↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) × EuclideanSpace ℝ (Fin 1)) :=
  {p | p.1.val 1 > 0}

def B := Prod.map φ₀ id '' A
def C := (φ₀.prod (PartialHomeomorph.refl _)) '' A

/- FIXME -/
example : ContDiffOn ℝ ⊤ (ee00.symm ≫ₕ ee10) C := by
  have h0 : ee10 = (Mobius.localTriv 1).toPartialHomeomorph ≫ₕ φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) := rfl

  have h6 : (ee00.symm ≫ₕ ee10) =
  ((φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ≫ₕ ((Mobius.localTriv 0).toPartialHomeomorph).symm) ≫ₕ
  ((Mobius.localTriv 1).toPartialHomeomorph ≫ₕ φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) := by
    exact rfl

  have h7 : ((φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ≫ₕ ((Mobius.localTriv 0).toPartialHomeomorph).symm) ≫ₕ
  ((Mobius.localTriv 1).toPartialHomeomorph ≫ₕ φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))  =
  (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ≫ₕ ((((Mobius.localTriv 0).toPartialHomeomorph).symm) ≫ₕ
  (Mobius.localTriv 1).toPartialHomeomorph) ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) := by
    rw [PartialHomeomorph.trans_assoc, PartialHomeomorph.trans_assoc]

  have h8 : (ee00.symm ≫ₕ ee10) =
    (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ≫ₕ ((((Mobius.localTriv 0).toPartialHomeomorph).symm) ≫ₕ
    (Mobius.localTriv 1).toPartialHomeomorph) ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) := by
    rw [h6, h7]

  have h9 : (ee00.symm ≫ₕ ee10) = conj := by
    rw [h8]
    exact rfl

  have h5 : ∀ (x : Mobius.Base) (v : EuclideanSpace ℝ (Fin 1)),
    (x.val 1) > 0 →
    ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v)
      = (x, v) := by
    intros x v ha
    have hx : x ∈ { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := Or.inl ha
    have hx' : x ∈ U.source ∩ V.source := SulSource.symm ▸ hx
    have h1 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) =
              (x, Mobius.coordChange 0 1 x v) := localTrivTransition_eq_coordChange 0 1 hx'
    have h2 : Mobius.coordChange 0 1 x v = if (x.val 1) > 0 then v else -v := rfl
    have h3 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) =
    (x, if (x.val 1) > 0 then v else -v) := by
      rw [h2] at h1
      exact h1
    have h4 : (x.val 1) > 0 → (if (x.val 1) > 0 then v else -v) = v := by
      intro h4
      rw [if_pos h4]
    rw [h3, h4]
    exact ha

  have ha : ∀ z ∈ C, conj z = z := by
    rintro z ⟨⟨x, v⟩, hx, rfl⟩
    dsimp only [PartialHomeomorph.prod_apply, PartialHomeomorph.refl_apply, id_eq]
    have ha1 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) =
               (x, v) := h5 x v hx
    have ha2 : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) (x, v) = (φ₀ x, v) := rfl

    have hu : xh.val 1 = 0 := rfl
    have hs : (-xh).val 1 = 0 := by simp [hu]
    have hv : (x.val 1) > 0 := hx
    have hw : x.val 1 ≠ xh.val 1 := Ne.symm (ne_of_lt hx)
    have ht : φ₀.source = { x | x ≠ -xh } := hU.source
    have hne : x ≠ -xh := by
      intro h_eq
      have : x.val = (-xh).val := congr_arg Subtype.val h_eq
      rw [← Bool.coe_false]
      rw [this] at hv
      linarith

    have hx_in_src : x ∈ φ₀.source := by
      rw [ht]
      exact hne

    have ha3 : (φ₀.prod (PartialHomeomorph.refl _)).symm (φ₀ x, v) = (x, v) := by
      have ha3a : φ₀.symm (φ₀ x) = x := PartialHomeomorph.left_inv φ₀ hx_in_src
      exact Prod.ext ha3a rfl

    have ha4 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) = (x, v) := h5 x v hv


    have ha5 : conj (φ₀ x, v) = (φ₀ x, v) := by
      calc
        conj (φ₀ x, v)
          = ((φ₀.prod (PartialHomeomorph.refl _)).symm ≫ₕ
            ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ
            (Mobius.localTriv 1).toPartialHomeomorph) ≫ₕ
            (φ₀.prod (PartialHomeomorph.refl _))) (φ₀ x, v) := rfl
        _ = (((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ
            (Mobius.localTriv 1).toPartialHomeomorph) ≫ₕ
            (φ₀.prod (PartialHomeomorph.refl _))) ((φ₀.prod (PartialHomeomorph.refl _)).symm (φ₀ x, v)) := by
          rw [PartialHomeomorph.trans_apply]
        _ = (((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ
            (Mobius.localTriv 1).toPartialHomeomorph) ≫ₕ
            (φ₀.prod (PartialHomeomorph.refl _))) (x, v) := by rw [ha3]
        _ = (φ₀.prod (PartialHomeomorph.refl _)) (((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ
            (Mobius.localTriv 1).toPartialHomeomorph) (x, v)) := by rw  [PartialHomeomorph.trans_apply]
        _ = (φ₀.prod (PartialHomeomorph.refl _)) (x, v) := by rw [ha4]
        _ = (φ₀ x, v) := rfl

    exact ha5

  have h6 : ∀ z ∈ (φ₀.prod (PartialHomeomorph.refl _)) '' A, (ee00.symm ≫ₕ ee10) z = z := by
    exact fun z a ↦ ha z a

  have h7 : ContDiffOn ℝ ⊤ (ee00.symm ≫ₕ ee10) B := by
    apply ContDiffOn.congr
    exact contDiffOn_id
    intro y hy
    obtain ⟨x, v⟩ := y
    exact h6 (x, v) hy

  exact h7

example
  (x t : EuclideanSpace ℝ (Fin 1))
  (e e' : PartialHomeomorph Mobius.TotalSpace
                            (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))))
  (he : e ∈ @atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) _
                   Mobius.TotalSpace _ (Mobius.chartedSpaceTotal' Mobius.chartedSpaceBase))
  (he' : e' ∈ @atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) _
                    Mobius.TotalSpace _ (Mobius.chartedSpaceTotal' Mobius.chartedSpaceBase))
   : ContDiffOn ℝ ⊤
      (↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e') ∘ ↑((𝓡 1).prod (𝓡 1)).symm)
      (↑((𝓡 1).prod (𝓡 1)).symm ⁻¹' (e.symm ≫ₕ e').source ∩ (range ↑((𝓡 1).prod (𝓡 1)))) := by

  have h5 :  ∀ (p : Mobius.TotalSpace),
    (Mobius.localTriv 0) p = (p.proj, Mobius.coordChange (Mobius.indexAt p.proj) 0 p.proj p.snd) := by
      exact FiberBundleCore.localTriv_apply Mobius 0

  cases (Classical.em (e = (Mobius.localTriv 0).toPartialHomeomorph ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))))) with
  | inl heq =>  cases (Classical.em (e' = (Mobius.localTriv 0).toPartialHomeomorph ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))))) with
                | inl heq' => have h1 : e = e' := by rw [heq, heq']
                              exact sorry
                | inr hne' => exact sorry
  | inr hne => exact sorry

example
  (x t : EuclideanSpace ℝ (Fin 1))
  (e e' : PartialHomeomorph Mobius.TotalSpace
                            (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))))
  (he : e ∈ @atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) _
                   Mobius.TotalSpace _ (Mobius.chartedSpaceTotal Mobius.chartedSpaceBase))
  (he' : e' ∈ @atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) _
                    Mobius.TotalSpace _ (Mobius.chartedSpaceTotal Mobius.chartedSpaceBase))
   : ContDiffOn ℝ ⊤
      (↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e') ∘ ↑((𝓡 1).prod (𝓡 1)).symm)
      (↑((𝓡 1).prod (𝓡 1)).symm ⁻¹' (e.symm ≫ₕ e').source ∩ (range ↑((𝓡 1).prod (𝓡 1)))) := by
  obtain ⟨i, w, hw⟩ := he
  have h1 : w ∈ baseAtlas := hw.1
  have h2 : e = (Mobius.localTriv i).toPartialHomeomorph ≫ₕ
                 w.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) := hw.2
  obtain ⟨j, u, hu⟩ := he'
  have h3 : u ∈ baseAtlas := hu.1
  have h4 : e' = (Mobius.localTriv j).toPartialHomeomorph ≫ₕ
                 u.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) := hu.2

  have h5 :  ∀ (p : Mobius.TotalSpace),
    (Mobius.localTriv 0) p = (p.proj, Mobius.coordChange (Mobius.indexAt p.proj) 0 p.proj p.snd) := by
      exact FiberBundleCore.localTriv_apply Mobius 0

  fin_cases i
  · fin_cases j
    · cases (Classical.em (w = φ₀)) with
      | inl hw =>
        have ha1 : e = (Mobius.localTriv 0).toPartialHomeomorph ≫ₕ
                                   φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) := by
                      rw [hw] at h2
                      exact h2
        cases (Classical.em (u = φ₀)) with
        | inl hu => have ha2 : e' = (Mobius.localTriv 0).toPartialHomeomorph ≫ₕ
                                   φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) := by
                      rw [hu] at h4
                      exact h4
                    have ha3 : e = e' :=
                      calc e = (Mobius.localTriv 0).toPartialHomeomorph ≫ₕ
                                   φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) := ha1
                           _ = e' := ha2.symm
                    have ha4 : (e.symm ≫ₕ e') = (e.symm ≫ₕ e) := congrArg e.symm.trans (id (Eq.symm ha3))
                    have ha5 :  e.symm ≫ₕ e ≈ PartialHomeomorph.ofSet e.target e.open_target := by
                      exact PartialHomeomorph.symm_trans_self e
                    have ha8 : ∀ x ∈ e.target, (e.symm ≫ₕ e) x = x :=
                      fun x hx => by
                      rw [PartialHomeomorph.trans_apply]
                      exact e.right_inv hx
                    have ha9 : ∀ x t, (x, t) ∈ ((𝓡 1).prod (𝓡 1)).symm.source ∧
                               ((𝓡 1).prod (𝓡 1)).symm (x, t) ∈ e.target →
                      ((↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e) ∘ ↑((𝓡 1).prod (𝓡 1)).symm) (x, t)) = (x, t) := by
                      intro x t h
                      have h1 : (↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e) ∘ ↑((𝓡 1).prod (𝓡 1)).symm) (x, t) =
                                (((𝓡 1).prod (𝓡 1)).toFun) (((e.symm ≫ₕ e).toFun) ((((𝓡 1).prod (𝓡 1)).symm.toFun) (x, t))) := by rfl
                      have h2 : (((𝓡 1).prod (𝓡 1)).toFun) (((e.symm ≫ₕ e).toFun) ((((𝓡 1).prod (𝓡 1)).symm.toFun) (x, t))) =
                        (((𝓡 1).prod (𝓡 1)).toFun) (((((𝓡 1).prod (𝓡 1)).symm.toFun) (x, t))) := by
                          apply ha8
                          exact h.2
                      have h3 : ((𝓡 1).prod (𝓡 1)).toFun (((𝓡 1).prod (𝓡 1)).symm.toFun (x, t)) = (x, t) := rfl
                      rw [h1, h2, h3]
                    have haa :  ∀ x t, (x, t) ∈ (↑((𝓡 1).prod (𝓡 1)).symm ⁻¹' (e.symm ≫ₕ e).source ∩ (range ↑((𝓡 1).prod (𝓡 1)))) →
                                ((↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e) ∘ ↑((𝓡 1).prod (𝓡 1)).symm) (x, t)) = (x, t) := by
                      intro x t h
                      exact ha9 x t (And.intro (hz1 x t e h) (hz2 x t e h))
                    rw [ha3] at *
                    have haa' : ∀ z ∈ ↑((𝓡 1).prod (𝓡 1)).symm ⁻¹' (e'.symm ≫ₕ e').source ∩ range ↑((𝓡 1).prod (𝓡 1)),
                                (↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e'.symm ≫ₕ e') ∘ ↑((𝓡 1).prod (𝓡 1)).symm) z = z := by
                      intro z hz
                      exact haa z.1 z.2 hz
                    exact contDiffOn_id.congr haa'
        | inr hu => have h1 : ¬u = φ₀ := hu
                    have hu_cases : u = φ₀ ∨ u = φ₁ := h3
                    cases hu_cases with
                      | inl h₁ => contradiction
                      | inr h₂ => have hu1 : u = φ₁ := h₂
                                  have ha2 : e' = (Mobius.localTriv 0).toPartialHomeomorph ≫ₕ
                                   φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) := by
                                    rw [hu1] at h4
                                    exact h4
                                  have ha3 : (Mobius.localTrivAsPartialEquiv 0).symm.trans (Mobius.localTrivAsPartialEquiv 0) ≈
                                             (Mobius.trivChange 0 0).toPartialEquiv :=
                                              FiberBundleCore.localTrivAsPartialEquiv_trans Mobius 0 0
                                  have ha5 : ↑(e.symm ≫ₕ e') =
                                    (fun (x : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) => ((φ₀.symm ≫ₕ φ₁) x.1, x.2)) := by
                                      rw [ha1, ha2]
                                      rw [PartialHomeomorph.trans_symm_eq_symm_trans_symm]
                                      simp
                                      exact sorry
                                  exact sorry
      | inr hw => exact sorry
    · have ha3 : (Mobius.localTrivAsPartialEquiv 1).symm.trans (Mobius.localTrivAsPartialEquiv 0) ≈
                 (Mobius.trivChange 1 0).toPartialEquiv := FiberBundleCore.localTrivAsPartialEquiv_trans Mobius 1 0
      cases (Classical.em (w = φ₀)) with
        | inl hw => cases (Classical.em (u = φ₀)) with
          | inl hu => have ha1 : e = (Mobius.localTriv 0).toPartialHomeomorph ≫ₕ
                                   φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) := by
                        rw [hw] at h2
                        exact h2
                      have ha2 : e' = (Mobius.localTriv 1).toPartialHomeomorph ≫ₕ
                                   φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) := by
                        rw [hu] at h4
                        exact h4
                      have ha9 : ∀ x t, (x, t) ∈ ((𝓡 1).prod (𝓡 1)).symm.source ∧
                               ((𝓡 1).prod (𝓡 1)).symm (x, t) ∈ e.target →
                      ((↑((𝓡 1).prod (𝓡 1)) ∘ (↑(e.symm ≫ₕ e') : PartialHomeomorph (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
    (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))) ∘ ↑((𝓡 1).prod (𝓡 1)).symm) (x, t)) =
                       ((↑((𝓡 1).prod (𝓡 1)) ∘ (↑((Mobius.trivChange 1 0)) : PartialHomeomorph (↑(Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1))
    (↑(Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1))) ∘ ↑((𝓡 1).prod (𝓡 1)).symm) (x, t)) := by
                        exact sorry
                      exact sorry
          | inr hu => exact sorry
        | inr hw => exact sorry
  · fin_cases j
    · exact sorry
    · exact sorry

#check (Mobius.localTriv 0).toPartialHomeomorph
#check (Mobius.localTriv 1).toPartialHomeomorph.symm
#check Mobius.trivChange
#check Mobius.localTriv


#check Mobius.TotalSpace

#check ((𝓡 1).prod (𝓡 1)).toFun

#check (((𝓡 1).prod (𝓡 1)) : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))

#check PartialHomeomorph.self_trans_symm
#check PartialHomeomorph.symm_trans_self
#check (↑((𝓡 1).prod (𝓡 1)) ∘ ↑((𝓡 1).prod (𝓡 1)).symm)

  -- obtain ⟨p, rfl⟩ := hw
  -- obtain ⟨q, rfl⟩ := hu

  -- calc
  --   (↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e') ∘ ↑((𝓡 1).prod (𝓡 1)).symm) (x, t)
  --     = (↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e')) ((((𝓡 1).prod (𝓡 1)).symm (x, t))) := by exact rfl
  --   _ = (↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e')) ((((𝓡 1).prod (𝓡 1)).symm ((x, t).1, (x, t).2))) := by exact rfl
  --   _ = (x, t) := sorry

#synth IsManifold (𝓡 2) 0 Mobius.TotalSpace

#synth @IsManifold _ _ _ _ _ _ _ ((𝓡 1).prod (𝓡 1)) 0 Mobius.TotalSpace _
                  (Mobius.chartedSpaceTotal Mobius.chartedSpaceBase)

lemma flurg
  (e e' : PartialHomeomorph Mobius.TotalSpace
                            (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))))
  (he : e ∈ atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
                   Mobius.TotalSpace)
  (he' : e' ∈ atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
                    Mobius.TotalSpace) :
  ContDiffOn ℝ ⊤
      (↑((𝓡 1).prod (𝓡 1)) ∘ ↑(e.symm ≫ₕ e') ∘ ↑((𝓡 1).prod (𝓡 1)).symm)
    (↑((𝓡 1).prod (𝓡 1)).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range ↑((𝓡 1).prod (𝓡 1))) := by
  exact sorry

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


#synth ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))

#synth ChartedSpace ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))

#synth MemTrivializationAtlas (trivializationAt (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber _)
#check MemTrivializationAtlas.out

#check (trivializationAt (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber _)

#check MemTrivializationAtlas


lemma disjunction_of_image {X  Y : Type*} (y : Y) (a b : X) (f : X -> Y) (h1 : ∃ x, f x = y) (h2 : ∀ y, y = a ∨ y = b) : y = f a ∨ y = f b := by
  obtain ⟨x, hx⟩ := h1
  have hy' := h2 x
  rcases hy' with rfl | rfl
  · exact Or.inl hx.symm
  · exact Or.inr hx.symm

lemma disjunction_of_image_subtype {X Y : Type*} {S : Set X}
  (e : Y) (a b : X) (f : X → Y)
  (h1 : ∃ x ∈ S, f x = e)
  (h2 : ∀ y ∈ S, y = a ∨ y = b) : e = f a ∨ e = f b := by
  obtain ⟨x, hxS, hx⟩ := h1
  specialize h2 x hxS
  cases h2 with
  | inl h_eq =>
    rw [h_eq] at hx
    exact Or.inl hx.symm
  | inr h_eq =>
    rw [h_eq] at hx
    exact Or.inr hx.symm

lemma Mobius_totalSpace_atlas_eq :
  atlas (↑(Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1)) (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =
  (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph) '' (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) := by
  let H' := (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)
  let M := TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber
  let Aₜ := trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber
  let foo := (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph)

  -- Fun facts
  have h0 : atlas H' M = atlas H' M := rfl
  have h1 : atlas H' M = toPartialHomeomorph '' Aₜ := rfl
  have h3 : ∀ c, c ∈ atlas H' M ↔ c ∈ toPartialHomeomorph '' Aₜ := by
    exact fun c ↦ mem_def
  rfl

#check ChartedSpace.comp
#check atlas

lemma mem_atlas_comp_right_iff
  {H H' M : Type*}
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace M]
  [ChartedSpace H' M] [ChartedSpace H H'] :
  ∀ {c : PartialHomeomorph M H} {e : PartialHomeomorph H' H},
    e ∈ atlas H H' →
    c ∈ (ChartedSpace.comp H H' M).atlas ↔ c ≫ₕ e.symm ∈ atlas H' M := by
    letI : ChartedSpace H M := ChartedSpace.comp H H' M
    have h1 : atlas H M = Set.image2 (· ≫ₕ ·) (atlas H' M) (atlas H H') := rfl
    intro c e
    exact sorry

noncomputable
def e₀ : PartialHomeomorph ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))
                             ((EuclideanSpace ℝ (Fin 1)) × (EuclideanSpace ℝ (Fin 1))) :=
  φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))

noncomputable
def e₁ : PartialHomeomorph ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))
                             ((EuclideanSpace ℝ (Fin 1)) × (EuclideanSpace ℝ (Fin 1))) :=
  φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))

#check baseAtlas' Mobius.chartedSpaceBase
#check {e₀, e₁}
#check ({e₀, e₁} :
    Set (PartialHomeomorph
      ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × EuclideanSpace ℝ (Fin 1)))
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))))

lemma baseAtlas'_eq : baseAtlas' Mobius.chartedSpaceBase =
  ({e₀, e₁} :
    Set (PartialHomeomorph
      ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × EuclideanSpace ℝ (Fin 1)))
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))) := by
  rw [baseAtlas']
  have h : atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere 0 1) = {φ₀, φ₁} := rfl
  rw [h]
  exact image_pair (fun e ↦ e.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) φ₀ φ₁

#check atlas
#check (atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
 Set (PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1))))
#check (baseAtlas' Mobius.chartedSpaceBase :
  Set
    (PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × EuclideanSpace ℝ (Fin 1))
                       (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))))

#check (atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)).image
      (fun e ↦ e.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

#check @atlas (EuclideanSpace ℝ (Fin 1)) _ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _ Mobius.chartedSpaceBase

lemma atlas_eq : @atlas (EuclideanSpace ℝ (Fin 1)) _ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _ Mobius.chartedSpaceBase =
  baseAtlas := rfl

lemma atlas_eq_baseAtlas' :
  baseAtlas' Mobius.chartedSpaceBase =
    (@atlas (EuclideanSpace ℝ (Fin 1)) _ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _ Mobius.chartedSpaceBase).image
      (fun e ↦ e.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) := by
  have h0 : @atlas (EuclideanSpace ℝ (Fin 1)) _ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _
   Mobius.chartedSpaceBase = {φ₀, φ₁} := rfl
  have h1 :  baseAtlas' Mobius.chartedSpaceBase = {e₀, e₁} := baseAtlas'_eq
  rw [h1]
  rw [h0]
  exact id (Eq.symm h1)

#check atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
             ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))

#check (@atlas (EuclideanSpace ℝ (Fin 1)) _ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _ Mobius.chartedSpaceBase).image
      (fun e ↦ e.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

#check atlas -- (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
#check ChartedSpace.atlas --  (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)


lemma Mobius_totalSpace_atlas_es :
  atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =
  (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))) ''
    (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
    ∪
  (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph ≫ₕ (φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))) ''
    (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) := by
  let H  := ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))
  let H' := (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1))
  let M  := TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber
  let Aₜ := trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber

  letI : ChartedSpace H M := ChartedSpace.comp H H' M

  have h0 : atlas H M = Set.image2 (· ≫ₕ ·) (atlas H' M) (atlas H H') := rfl
  have ha : atlas H' M = toPartialHomeomorph '' Aₜ := rfl

  have he : atlas H H' = {e₀, e₁} := by
    sorry

  calc
    atlas H M
      = Set.image2 (· ≫ₕ ·) (toPartialHomeomorph '' Aₜ) {e₀, e₁} := by rw [h0, ha, he]; exact rfl
    _ = ⋃ e ∈ ({e₀, e₁} : Set (PartialHomeomorph H' H)), (toPartialHomeomorph '' Aₜ).image (· ≫ₕ e) := by
      exact Eq.symm (iUnion_image_right PartialHomeomorph.trans)
    _ = (fun x ↦ x ≫ₕ e₀) '' (toPartialHomeomorph '' Aₜ) ∪ (fun x ↦ x ≫ₕ e₁) '' (toPartialHomeomorph '' Aₜ) := by
        simp only [mem_insert_iff, mem_singleton_iff, iUnion_iUnion_eq_or_left, iUnion_iUnion_eq_left]
        exact rfl

  have hz0 : (fun x ↦ x ≫ₕ e₀) '' (toPartialHomeomorph '' Aₜ) =
             (fun e ↦ e.toPartialHomeomorph ≫ₕ e₀) '' Aₜ := by
    exact image_image (fun x ↦ x ≫ₕ e₀) toPartialHomeomorph Aₜ

  have hz1 : (fun x ↦ x ≫ₕ e₁) '' (toPartialHomeomorph '' Aₜ) =
             (fun e ↦ e.toPartialHomeomorph ≫ₕ e₁) '' Aₜ := by
    exact image_image (fun x ↦ x ≫ₕ e₁) toPartialHomeomorph Aₜ

  rw [hz0, hz1]

  exact rfl


#check (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph)

def gg : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) ->
         PartialHomeomorph (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
                           ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) :=
  (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph)

lemma Mobius_totalSpace_atlas_ep :
  atlas (↑(Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1)) (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =
    gg '' (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) := rfl

def rr : PartialHomeomorph (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
  (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) := sorry

def ff : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) ->
        PartialHomeomorph (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
                          (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) :=
  sorry


#synth ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))

#check φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))

#check (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    (toPartialHomeomorph e)≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))))

noncomputable
def nf : PartialHomeomorph ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1))
                           (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) :=
  φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))

noncomputable
def fg : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) ->
        PartialHomeomorph (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
                          (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) :=
  (fun e => gg e ≫ₕ nf)

noncomputable
def fh : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) ->
        PartialHomeomorph (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
                          (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) :=
  (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))))

lemma Mobius_totalSpace_atlas_eq' :
  atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =
  (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) => fh e) ''
    (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) :=
  sorry

lemma totalAtlas_in_image_baseAtlas' :
  atlas ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × (EuclideanSpace ℝ (Fin 1)))
        (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)
  ⊆
  {
    (Mobius.localTriv 0).toPartialHomeomorph,
    (Mobius.localTriv 1).toPartialHomeomorph
  } := by
  intro e he
  have h7 : e ∈ (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph) '' (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) := by
    exact he

  have h8 : e ∈ (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph) '' (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) ↔
    ∃ x ∈ (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber), (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph) x = e := Set.mem_image (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph) (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) e

  have hb : ∃ x ∈ (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber), (fun e : Trivialization (EuclideanSpace ℝ (Fin 1)) (π (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber) =>
    e.toPartialHomeomorph) x = e := by exact h8.mp h7

  have hy : ∀ x ∈ (trivializationAtlas (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber),
    x = Mobius.localTriv 0 ∨ x = Mobius.localTriv 1 := by
    intro x hx
    have h9: MemTrivializationAtlas x := { out := hx }
    have h3 : MemTrivializationAtlas x ↔
              x = Mobius.localTriv 0 ∨ x = Mobius.localTriv 1 := trivialization_mem_iff_f x
    have ha : x = Mobius.localTriv 0 ∨ x = Mobius.localTriv 1 := by
      exact h3.mp h9
    exact ha

  have h1 : e = (Mobius.localTriv 0).toPartialHomeomorph ∨ e = (Mobius.localTriv 1).toPartialHomeomorph :=
    disjunction_of_image_subtype e (Mobius.localTriv 0) (Mobius.localTriv 1)
                                (fun e ↦ e.toPartialHomeomorph) hb hy

  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact h1

#synth ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) (TotalSpace (EuclideanSpace ℝ (Fin 1)) Mobius.Fiber)

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

example : Mobius.baseSet 0 = { x | x ≠ -xh } := hU.source
example : Mobius.baseSet 1 = { x | x ≠ -ug } := hV.source

example : ∀ (x : Mobius.Base) (hx : x ∈ { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 }),
 ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
    (((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph))
    ({x | x.1.val 1 < 0} ∪ {x | x.1.val 1 < 0}) := by

  have h5 : ∀ (x : Mobius.Base) (v : EuclideanSpace ℝ (Fin 1)),
    (x.val 1) > 0 →
    ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v)
      = (x, v) := by
    intros x v ha
    have hx : x ∈ { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := Or.inl ha
    have hx' : x ∈ U.source ∩ V.source := SulSource.symm ▸ hx
    have h1 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) =
              (x, Mobius.coordChange 0 1 x v) := localTrivTransition_eq_coordChange 0 1 hx'
    have h2 : Mobius.coordChange 0 1 x v = if (x.val 1) > 0 then v else -v := rfl
    have h3 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) =
    (x, if (x.val 1) > 0 then v else -v) := by
      rw [h2] at h1
      exact h1
    have h4 : (x.val 1) > 0 → (if (x.val 1) > 0 then v else -v) = v := by
      intro h4
      rw [if_pos h4]
    rw [h3, h4]
    exact ha

  have h6 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
      ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph)
      {x : ↑(Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1) | (x.1.val 1) > 0} := by
      apply ContMDiffOn.congr
      · exact contMDiffOn_id
      · intro y hy
        obtain ⟨x, v⟩ := y
        dsimp at hy
        exact h5 x v hy

  have h7 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
      ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph)
      {x : ↑(Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1) | (x.1.val 1) < 0} := sorry

  have h8 : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
      ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph)
      ({x : ↑(Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1) | (x.1.val 1) < 0} ∪
       {x : ↑(Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1) | (x.1.val 1) < 0}) := sorry

  exact fun x hx ↦ h8

noncomputable
def pre : PartialHomeomorph (↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1))
                            (↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) :=
 (((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph))

noncomputable
def ee00 :=  (Mobius.localTriv 0).toPartialHomeomorph ≫ₕ φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))

noncomputable
def ee10 := (Mobius.localTriv 1).toPartialHomeomorph ≫ₕ φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))

#check (↑(ee00.symm ≫ₕ ee10) : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) →
  EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))

noncomputable
def conj :=
  (φ₀.prod (PartialHomeomorph.refl _)).symm ≫ₕ
  ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ
   (Mobius.localTriv 1).toPartialHomeomorph) ≫ₕ
  (φ₀.prod (PartialHomeomorph.refl _))

def A : Set ((↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) × EuclideanSpace ℝ (Fin 1)) :=
  {p | p.1.val 1 > 0}

def B := Prod.map φ₀ id '' A
def C := (φ₀.prod (PartialHomeomorph.refl _)) '' A

example : ContDiffOn ℝ ⊤ (ee00.symm ≫ₕ ee10) C := by
  have h0 : ee10 = (Mobius.localTriv 1).toPartialHomeomorph ≫ₕ φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))) := rfl

  have h6 : (ee00.symm ≫ₕ ee10) =
  ((φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ≫ₕ ((Mobius.localTriv 0).toPartialHomeomorph).symm) ≫ₕ
  ((Mobius.localTriv 1).toPartialHomeomorph ≫ₕ φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) := by
    exact rfl

  have h7 : ((φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ≫ₕ ((Mobius.localTriv 0).toPartialHomeomorph).symm) ≫ₕ
  ((Mobius.localTriv 1).toPartialHomeomorph ≫ₕ φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))  =
  (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ≫ₕ ((((Mobius.localTriv 0).toPartialHomeomorph).symm) ≫ₕ
  (Mobius.localTriv 1).toPartialHomeomorph) ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) := by
    rw [PartialHomeomorph.trans_assoc, PartialHomeomorph.trans_assoc]

  have h8 : (ee00.symm ≫ₕ ee10) =
    (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ≫ₕ ((((Mobius.localTriv 0).toPartialHomeomorph).symm) ≫ₕ
    (Mobius.localTriv 1).toPartialHomeomorph) ≫ₕ (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) := by
    rw [h6, h7]

  have h9 : (ee00.symm ≫ₕ ee10) = conj := by
    rw [h8]
    exact rfl

  have h5 : ∀ (x : Mobius.Base) (v : EuclideanSpace ℝ (Fin 1)),
    (x.val 1) > 0 →
    ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v)
      = (x, v) := by
    intros x v ha
    have hx : x ∈ { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := Or.inl ha
    have hx' : x ∈ U.source ∩ V.source := SulSource.symm ▸ hx
    have h1 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) =
              (x, Mobius.coordChange 0 1 x v) := localTrivTransition_eq_coordChange 0 1 hx'
    have h2 : Mobius.coordChange 0 1 x v = if (x.val 1) > 0 then v else -v := rfl
    have h3 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) =
    (x, if (x.val 1) > 0 then v else -v) := by
      rw [h2] at h1
      exact h1
    have h4 : (x.val 1) > 0 → (if (x.val 1) > 0 then v else -v) = v := by
      intro h4
      rw [if_pos h4]
    rw [h3, h4]
    exact ha

  have ha : ∀ z ∈ C, conj z = z := by
    rintro z ⟨⟨x, v⟩, hx, rfl⟩
    dsimp only [PartialHomeomorph.prod_apply, PartialHomeomorph.refl_apply, id_eq]
    have ha1 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) =
               (x, v) := h5 x v hx
    have ha2 : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) (x, v) = (φ₀ x, v) := rfl

    have hu : xh.val 1 = 0 := rfl
    have hs : (-xh).val 1 = 0 := by simp [hu]
    have hv : (x.val 1) > 0 := hx
    have hw : x.val 1 ≠ xh.val 1 := Ne.symm (ne_of_lt hx)
    have ht : φ₀.source = { x | x ≠ -xh } := hU.source
    have hne : x ≠ -xh := by
      intro h_eq
      have : x.val = (-xh).val := congr_arg Subtype.val h_eq
      rw [← Bool.coe_false]
      rw [this] at hv
      linarith

    have hx_in_src : x ∈ φ₀.source := by
      rw [ht]
      exact hne

    have ha3 : (φ₀.prod (PartialHomeomorph.refl _)).symm (φ₀ x, v) = (x, v) := by
      have ha3a : φ₀.symm (φ₀ x) = x := PartialHomeomorph.left_inv φ₀ hx_in_src
      exact Prod.ext ha3a rfl

    have ha4 : ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ (Mobius.localTriv 1).toPartialHomeomorph) (x, v) = (x, v) := h5 x v hv


    have ha5 : conj (φ₀ x, v) = (φ₀ x, v) := by
      calc
        conj (φ₀ x, v)
          = ((φ₀.prod (PartialHomeomorph.refl _)).symm ≫ₕ
            ((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ
            (Mobius.localTriv 1).toPartialHomeomorph) ≫ₕ
            (φ₀.prod (PartialHomeomorph.refl _))) (φ₀ x, v) := rfl
        _ = (((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ
            (Mobius.localTriv 1).toPartialHomeomorph) ≫ₕ
            (φ₀.prod (PartialHomeomorph.refl _))) ((φ₀.prod (PartialHomeomorph.refl _)).symm (φ₀ x, v)) := by
          rw [PartialHomeomorph.trans_apply]
        _ = (((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ
            (Mobius.localTriv 1).toPartialHomeomorph) ≫ₕ
            (φ₀.prod (PartialHomeomorph.refl _))) (x, v) := by rw [ha3]
        _ = (φ₀.prod (PartialHomeomorph.refl _)) (((Mobius.localTriv 0).toPartialHomeomorph.symm ≫ₕ
            (Mobius.localTriv 1).toPartialHomeomorph) (x, v)) := by rw  [PartialHomeomorph.trans_apply]
        _ = (φ₀.prod (PartialHomeomorph.refl _)) (x, v) := by rw [ha4]
        _ = (φ₀ x, v) := rfl

    exact ha5

  have h6 : ∀ z ∈ (φ₀.prod (PartialHomeomorph.refl _)) '' A, (ee00.symm ≫ₕ ee10) z = z := by
    exact fun z a ↦ ha z a

  have h7 : ContDiffOn ℝ ⊤ (ee00.symm ≫ₕ ee10) B := by
    apply ContDiffOn.congr
    exact contDiffOn_id
    intro y hy
    obtain ⟨x, v⟩ := y
    exact h6 (x, v) hy

  exact h7

#check PartialHomeomorph.trans_apply
