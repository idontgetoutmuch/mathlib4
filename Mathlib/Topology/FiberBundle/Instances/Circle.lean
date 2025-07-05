/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/
import Mathlib

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

lemma hU.target : U.target = univ := by
  calc U.target = (chartAt (EuclideanSpace ℝ (Fin 1)) xh).target := rfl
    _ = (stereographic' 1 (-xh)).target := rfl
    _ = univ := stereographic'_target (-xh)

lemma hV.source : V.source = { x | x ≠ -ug} :=
  calc V.source = (chartAt (EuclideanSpace ℝ (Fin 1)) ug).source := rfl
    _ = (stereographic' 1 (-ug)).source := rfl
    _ = {-ug}ᶜ := stereographic'_source (-ug)
    _ = { x | x ≠ -ug } := rfl

open IsManifold Manifold

example : chartAt (EuclideanSpace ℝ (Fin 1)) (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))) ∈
  IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
   chart_mem_maximalAtlas (⟨x, h⟩ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

example : U ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
   chart_mem_maximalAtlas (⟨x, h⟩ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

lemma UVSmoothOn :
  ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (V ∘ U.symm) (U.target ∩ U.symm ⁻¹' V.source) :=
    have h1 : U ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      chart_mem_maximalAtlas xh
    have h2 : V ∈ IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      chart_mem_maximalAtlas ug
    have h3 : U.target ∩ ↑U.symm ⁻¹' V.source ⊆ U.target := by
      intro x hx
      have h5 : x ∈ U.target := hx.1
      exact h5
    have h4 : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (↑U.symm) (U.target ∩ U.symm ⁻¹' V.source) :=
      (contMDiffOn_symm_of_mem_maximalAtlas h1).mono h3
    have h5 : U.target ∩ ↑U.symm ⁻¹' V.source ⊆ ↑U.symm ⁻¹' V.source := by
      intro x hx
      have h5 : x ∈ U.symm ⁻¹' V.source := hx.2
      exact h5
    (contMDiffOn_of_mem_maximalAtlas h2).comp h4 h5

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

open scoped Manifold
open Bundle

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

#synth IsManifold (𝓡 1) 0 (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

open Bundle Manifold Trivialization VectorBundleCore Topology

noncomputable
def φ₀ : PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) := U

noncomputable
def φ₁ : PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) := V

noncomputable
def baseAtlas : Set (PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1))) :=
  {φ₀, φ₁}

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

example : @atlas (EuclideanSpace ℝ (Fin 1)) _ _ _ Mobius.chartedSpaceBase = baseAtlas := by
      unfold atlas
      exact rfl

noncomputable def baseAtlas' : Set (PartialHomeomorph
  ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1))
  (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :=
  (atlas (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)).image
    (fun e ↦ e.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

lemma SmoothInnerPre : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (↑φ₁ ∘ ↑φ₀.symm)  (φ₀ '' ({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 })) := by
  have h1 : (φ₀.target ∩ ↑φ₀.symm ⁻¹' φ₁.source) = φ₀ '' (φ₀.source ∩ φ₁.source) := by
    exact Eq.symm (PartialHomeomorph.image_source_inter_eq' φ₀ φ₁.source)
  have h2 : φ₀.source ∩ φ₁.source = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := SulSource
  rw [<-h2]
  rw [<-h1]
  exact UVSmoothOn

lemma SmoothInnerPreOn : (φ₀ '' ({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 }))  = (φ₀.symm ≫ₕ φ₁).source := by
  have ha : φ₀ '' (φ₀.source ∩ φ₁.source) = φ₀.target ∩ ↑φ₀.symm ⁻¹' φ₁.source := PartialHomeomorph.image_source_inter_eq' φ₀ φ₁.source
  have h0 : ((φ₀.symm ≫ₕ φ₁).source) =  φ₀.target ∩ ↑φ₀.symm ⁻¹' φ₁.source := by
    exact rfl
  have h2 :  ((φ₀.symm ≫ₕ φ₁).source) = φ₀ '' (φ₀.source ∩ φ₁.source) := by
    rw [h0, ha]
  have h1 : (({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 })) = φ₀.source ∩ φ₁.source := by
    rw [<-SulSource]
    exact rfl
  have h3 : φ₀ '' ({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 }) = φ₀ '' (φ₀.source ∩ φ₁.source) := by
    rw [h1]
  rw [h2, h3]

lemma SmoothInnerPrh : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (↑(φ₀.symm ≫ₕ φ₁)) (φ₀.symm ≫ₕ φ₁).source := by
  rw [<-SmoothInnerPreOn]
  exact SmoothInnerPre

#check contMDiffOn_iff_contDiffOn.mp SmoothInnerPrh

lemma SmoothInnerPri : ContDiffOn ℝ ⊤ (↑(φ₀.symm ≫ₕ φ₁)) ((φ₀.symm ≫ₕ φ₁).source) := by
  exact contMDiffOn_iff_contDiffOn.mp SmoothInnerPrh

#check EqOn

-- (↑(φ₀.symm ≫ₕ φ₀) : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))

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
  intro e e' he he'
  cases (Classical.em (e = φ₀)) with
    | inl heq => rw [heq]
                 cases (Classical.em (e' = φ₀)) with
                  | inl heq' => rw [heq']
                                rw [heq'] at he'
                                exact SmoothInner00 φ₀ he'
                  | inr hne' => have h1 : e' = φ₁ := sorry
                                rw [h1]
                                exact SmoothInnerPri
    | inr hne => cases (Classical.em (e' = φ₀)) with
                  | inl heq' => exact sorry
                  | inr hne' => exact sorry

lemma atlas_eq : @atlas (EuclideanSpace ℝ (Fin 1)) _ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _ Mobius.chartedSpaceBase =
  baseAtlas := rfl

lemma simpleSmooti : ∀ (e e' : PartialHomeomorph ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) (EuclideanSpace ℝ (Fin 1))),
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
  exact simpleSmooti

#synth IsManifold (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
#synth @IsManifold ℝ _ _ _ _ _ _ (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _ Mobius.chartedSpaceBase


#check @chart_mem_maximalAtlas ℝ _ _ _ _ _ _ (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _ Mobius.chartedSpaceBase _ xh

noncomputable def UU := chartAt (EuclideanSpace ℝ (Fin 1))
  (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

noncomputable def VV := chartAt (EuclideanSpace ℝ (Fin 1))
  (⟨u, g⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

lemma SmoothFrom : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (φ₀.symm) (φ₀.target) := by

  have hc : baseChartAt (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))) = φ₀ := by
    unfold baseChartAt
    have hc1 : (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))).val 0  = 1 := rfl
    have hc2 : (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))).val 0 > 0 := by
      rw [hc1]
      exact Real.zero_lt_one

    exact if_pos hc2

  have h2 : UU = φ₀ := by
    exact hc

  have h1 : UU ∈
    IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      chart_mem_maximalAtlas (⟨x, h⟩ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

  have h3 : φ₀ ∈  IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    rw [h2] at h1
    exact h1

  have h4 : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (φ₀.symm) (φ₀.target) :=
    (contMDiffOn_symm_of_mem_maximalAtlas h3)
  exact h4

lemma smoothChartUpper : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
  (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm (φ₀.target ×ˢ univ) := by
    exact ContMDiffOn.prodMap SmoothFrom contMDiffOn_id


def s := (↑(φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm ⁻¹' {x | x.1.val 1 > 0})

noncomputable
def e := (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).symm

lemma ggg : ∀ x, x.val 1 > 0 → x ≠ -ug := by
  intro x hx
  have h1 : ug.val 0 = -1 := rfl
  have h2 : ug.val 1 = 0 := rfl
  have h3 : x.val 1 > 0 := hx
  have h7 : x ≠ -ug := by
    intro h_eq
    have h_val_eq : x.val = -ug.val := congrArg Subtype.val h_eq
    have h_contra : x.val 1 = -ug.val 1 := congrFun h_val_eq 1
    rw [h2] at h_contra
    linarith
  exact h7

lemma hhh : ∀ x, x.val 1 > 0 → x ≠ -xh := by
  intro x hx
  have h1 : xh.val 0 = 1 := rfl
  have h2 : xh.val 1 = 0 := rfl
  have h3 : x.val 1 > 0 := hx
  have h7 : x ≠ -xh := by
    intro h_eq
    have h_val_eq : x.val = -xh.val := congrArg Subtype.val h_eq
    have h_contra : x.val 1 = -xh.val 1 := congrFun h_val_eq 1
    rw [h2] at h_contra
    linarith
  exact h7

example : e.symm '' (e.target ∩ {x | x.1.val 1 > 0}) = e.source ∩ ↑e ⁻¹' (e.target ∩ {x | x.1.val 1 > 0})  := by
  have h1 : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).target =
            φ₀.target ×ˢ univ := rfl
  have h2 : φ₀.target = univ := hU.target
  have h5 : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).target = univ ×ˢ univ := by
    rw [h1, h2]
  have h7 : e.symm.target = e.source := PartialHomeomorph.symm_target e
  have h7 : e.target = (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).source :=
   PartialHomeomorph.symm_target (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
  have h8a : φ₀.source = { x | x ≠ -xh } := hU.source
  have h8b : (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))).source = univ := rfl
  have h8c : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).source =
              φ₀.source ×ˢ (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))).source :=
                PartialHomeomorph.prod_source φ₀ (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))
  have h8d : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).source =
      { x | x ≠ -xh } ×ˢ univ := by
      rw [h8a, h8b] at h8c
      exact h8c
  have h9 : e.target = { x | x ≠ -xh } ×ˢ univ := by
    rw [h7, h8d]
  have ha :  e.target ∩ {x | x.1.val 1 > 0} = ({ x | x ≠ -xh } ×ˢ univ)  ∩ {x | x.1.val 1 > 0} := by
    rw [h9]

  have hb : {x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) | x.1.val 1 > 0} ⊆
   { x : (Metric.sphere 0 1) | x ≠ -xh } ×ˢ univ := by
    intro x hx
    have h1 : x.1 ≠ -xh := hhh x.1 hx
    exact Set.mem_prod.mpr ⟨h1, Set.mem_univ _⟩

  have hc : ({ x | x ≠ -xh } ×ˢ univ) ∩
            {x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) | x.1.val 1 > 0} =
           {x | x.1.val 1 > 0} := by
    exact inter_eq_self_of_subset_right hb

  have hd : e.target ∩ {x | x.1.val 1 > 0} = {x | x.1.val 1 > 0} := by
    rw [ha, hc]

  have h3 : e.symm '' (e.target ∩ {x | x.1.val 1 > 0}) = e.source ∩ e ⁻¹' (e.target ∩ {x | x.1.val 1 > 0}) := PartialHomeomorph.symm_image_target_inter_eq e {x | x.1.val 1 > 0}

  have he : e.symm '' ({x | x.1.val 1 > 0}) = e.source ∩ e ⁻¹' ({x | x.1.val 1 > 0}) := by
    rw [hd] at h3
    exact h3

  have hf : e.symm = (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) :=
    PartialHomeomorph.symm_symm (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

  have hg : e.source = univ ×ˢ univ := by
    exact h5

  have hi : e.symm '' ({x | x.1.val 1 > 0}) = e ⁻¹' ({x | x.1.val 1 > 0}) := by
    rw [hf]
    rw [hg] at he
    have h1 :  e.symm '' {x | x.1.val 1 > 0} = univ ×ˢ univ ∩ e ⁻¹' {x | x.1.val 1 > 0} := he
    have h2 : univ ×ˢ univ ∩ e ⁻¹' {x | x.1.val 1 > 0} = e ⁻¹' {x | x.1.val 1 > 0} := by
      rw [Set.univ_prod_univ, Set.inter_comm]
      exact Set.inter_univ  _
    rw [h2] at h1
    exact h1

  have hj : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) '' {x | x.1.val 1 > 0} =
    e ⁻¹' {x | x.1.val 1 > 0} := by
    rw [hf] at hi
    exact hi

  exact h3

lemma sRewrite : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) '' {x | x.1.val 1 > 0} = s := by
  have h1 : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).target =
            φ₀.target ×ˢ univ := rfl
  have h2 : φ₀.target = univ := hU.target
  have h5 : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).target = univ ×ˢ univ := by
    rw [h1, h2]
  have h7 : e.symm.target = e.source := PartialHomeomorph.symm_target e
  have h7 : e.target = (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).source :=
   PartialHomeomorph.symm_target (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))
  have h8a : φ₀.source = { x | x ≠ -xh } := hU.source
  have h8b : (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))).source = univ := rfl
  have h8c : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).source =
              φ₀.source ×ˢ (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))).source :=
                PartialHomeomorph.prod_source φ₀ (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))
  have h8d : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))).source =
      { x | x ≠ -xh } ×ˢ univ := by
      rw [h8a, h8b] at h8c
      exact h8c
  have h9 : e.target = { x | x ≠ -xh } ×ˢ univ := by
    rw [h7, h8d]
  have ha :  e.target ∩ {x | x.1.val 1 > 0} = ({ x | x ≠ -xh } ×ˢ univ)  ∩ {x | x.1.val 1 > 0} := by
    rw [h9]

  have hb : {x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) | x.1.val 1 > 0} ⊆
   { x : (Metric.sphere 0 1) | x ≠ -xh } ×ˢ univ := by
    intro x hx
    have h1 : x.1 ≠ -xh := hhh x.1 hx
    exact Set.mem_prod.mpr ⟨h1, Set.mem_univ _⟩

  have hc : ({ x | x ≠ -xh } ×ˢ univ) ∩
            {x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) | x.1.val 1 > 0} =
           {x | x.1.val 1 > 0} := by
    exact inter_eq_self_of_subset_right hb

  have hd : e.target ∩ {x | x.1.val 1 > 0} = {x | x.1.val 1 > 0} := by
    rw [ha, hc]

  have h3 : e.symm '' (e.target ∩ {x | x.1.val 1 > 0}) = e.source ∩ e ⁻¹' (e.target ∩ {x | x.1.val 1 > 0}) := PartialHomeomorph.symm_image_target_inter_eq e {x | x.1.val 1 > 0}

  have he : e.symm '' ({x | x.1.val 1 > 0}) = e.source ∩ e ⁻¹' ({x | x.1.val 1 > 0}) := by
    rw [hd] at h3
    exact h3

  have hf : e.symm = (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) :=
    PartialHomeomorph.symm_symm (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1))))

  have hg : e.source = univ ×ˢ univ := by
    exact h5

  have hi : e.symm '' ({x | x.1.val 1 > 0}) = e ⁻¹' ({x | x.1.val 1 > 0}) := by
    rw [hf]
    rw [hg] at he
    have h1 :  e.symm '' {x | x.1.val 1 > 0} = univ ×ˢ univ ∩ e ⁻¹' {x | x.1.val 1 > 0} := he
    have h2 : univ ×ˢ univ ∩ e ⁻¹' {x | x.1.val 1 > 0} = e ⁻¹' {x | x.1.val 1 > 0} := by
      rw [Set.univ_prod_univ, Set.inter_comm]
      exact Set.inter_univ  _
    rw [h2] at h1
    exact h1

  have hj : (φ₀.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) '' {x | x.1.val 1 > 0} =
    e ⁻¹' {x | x.1.val 1 > 0} := by
    rw [hf] at hi
    exact hi

  exact hj

lemma SmoothTo : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ φ₁ φ₁.source := by
  have hc : baseChartAt (⟨u, g⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))) = φ₁ := by
    unfold baseChartAt
    have hc1 : (⟨u, g⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))).val 0  = -1 := rfl
    have hc2 : (⟨u, g⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))).val 0 < 0 := by
      rw [hc1]
      exact neg_one_lt_zero
    have hc3 :  ¬(⟨u, g⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))).val 0 > 0 := neg_one_lt_zero.not_lt
    exact if_neg hc3

  have h2 : VV = φ₁ := by
    exact hc

  have h1 : VV ∈
    IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      chart_mem_maximalAtlas (⟨u, g⟩ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

  have h3 : φ₁ ∈  IsManifold.maximalAtlas (𝓡 1) ⊤ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    rw [h2] at h1
    exact h1

  have h4 : ContMDiffOn (𝓡 1) (𝓡 1) ⊤ (φ₁) (φ₁.source) :=
    (contMDiffOn_of_mem_maximalAtlas h3)

  exact h4

lemma smoothChartUpperSymm : ContMDiffOn ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ⊤
  (φ₁.prod (PartialHomeomorph.refl (EuclideanSpace ℝ (Fin 1)))) (φ₁.source ×ˢ univ) := by
    exact ContMDiffOn.prodMap SmoothTo contMDiffOn_id

#check @ContMDiffOn ℝ _ _ _ _ _ _ ((𝓡 1).prod (𝓡 1)) _ _ _ _ _ _ _ _ ((𝓡 1).prod (𝓡 1)) _ _ _ ⊤ (((𝓡 1).prod (𝓡 1)).toFun) univ

#check contMDiffOn_fst

example : @ContMDiffOn ℝ _ _ _ _ _ _ ((𝓡 1).prod (𝓡 1)) _ _ _ _ _ _ _ _ ((𝓡 1).prod (𝓡 1)) _ _ _ ⊤ (((𝓡 1).prod (𝓡 1)).toFun) univ := by
  apply ContMDiffOn.prodMk
  · exact sorry --  contMDiffOn_id
  · exact sorry -- contMDiffOn_id

example : @ContMDiffOn ℝ _ _ _ _ _ _ ((𝓡 1).prod (𝓡 1)) _ _ _ _ _ _ _ _ (𝓡 1) _ _ _ ⊤ (fun x : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)  => x.1) univ := by
  exact contMDiffOn_fst

example : @ContMDiffOn ℝ _ _ _ _  _ ((𝓡 1).prod (𝓡 1)) _ _ _ _ _ _ _ _ (𝓡 1) _ _ _ ⊤ (fun x : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)  => x.1) univ := by
  exact contMDiffOn_fst

example : @ContMDiffOn ℝ _ _ _ _ _ _ ((𝓡 1).prod (𝓡 1)) _ _ _ _ _ _ _ _ ((𝓡 1).prod (𝓡 1)) _ _ _ ⊤ (((𝓡 1).prod (𝓡 1)).toFun) univ := by
  have h1 : @ContMDiffOn ℝ _ _ _ _ _ _ ((𝓡 1).prod (𝓡 1)) _ _ _ _ _ _ _ _ (𝓡 1) _ _ _ ⊤ (fun x : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) => x.1) univ := by
    exact contMDiffOn_fst
  have h1 : @ContMDiffOn ℝ _ _ _ _ _ _ ((𝓡 1).prod (𝓡 1)) _ _ _ _ _ _ _ _ (𝓡 1) _ _ _ ⊤ (fun x : (𝓡 1).prod (𝓡 1) => ↑(𝓡 1) x.1) univ := by
    exact contMDiffOn_fst

  apply ContMDiffOn.prodMk
  · exact h1
  · exact sorry

#check contMDiff_iff_contDiff
#check contMDiffOn_iff
#check contMDiffOn_iff_contDiffOn

example :  𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) = (𝓡 1).prod (𝓡 1) := by
  exact modelWithCornersSelf_prod

example : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
  𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ⊤ (((𝓡 1).prod (𝓡 1)) ∘ ((𝓡 1).prod (𝓡 1)).symm)
  (((𝓡 1).prod (𝓡 1)).symm ⁻¹' ((𝓡 1).prod (𝓡 1)).source ∩ range ((𝓡 1).prod (𝓡 1))) := by
  sorry

open TopologicalSpace Manifold ModelWithCorners

#check ContMDiffOn 𝓘(ℝ,  EuclideanSpace ℝ (Fin 1)) (𝓡 1) ⊤ (𝓡 1).toFun Set.univ
#check ContMDiffOn 𝓘(ℝ,  EuclideanSpace ℝ (Fin 1))
 (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
 ⊤ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))).toFun Set.univ

#check (contMDiff_model : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ⊤ _)

lemma foo : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ⊤ ((𝓡 1).prod (𝓡 1)) := by
  exact contMDiff_model

noncomputable
def 𝓘 := ((𝓡 1).prod (𝓡 1))
noncomputable
def 𝓙 := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))

lemma bar : ContMDiff 𝓘 𝓙 ⊤ 𝓘 := by
  exact contMDiff_model

#check (inferInstance : ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))

#synth ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))

example : @atlas (EuclideanSpace ℝ (Fin 1)) _ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) _
  Mobius.chartedSpaceBase = {φ₀, φ₁} := rfl

#synth ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
