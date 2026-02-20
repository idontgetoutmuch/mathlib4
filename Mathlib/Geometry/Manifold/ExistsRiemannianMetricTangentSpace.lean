/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Dominic Steinitz
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! ## Existence of a Riemannian bundle metric

Using a partition of unity, we prove the existence of a smooth Riemannian metric.

-/

open Set Bundle ContDiff Manifold Trivialization SmoothPartitionOfUnity

variable
{B : Type*}
{E : B → Type*} [∀ x, NormedAddCommGroup (E x)]

section tangentSpaceEquiv

variable
  [∀ x, NormedSpace ℝ (E x)]

structure VectorSpaceAux
  (x : B) (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) where
  val : E x

lemma VectorSpaceAux.ext_iff {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    (u v : VectorSpaceAux x φ hpos hsymm hdef) :
  u = v ↔ u.val = (v.val : E x) := by
  cases u; cases v; simp

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Zero (VectorSpaceAux x φ hpos hsymm hdef) where
  zero := ⟨0⟩

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Add (VectorSpaceAux x φ hpos hsymm hdef) where
  add u v := ⟨u.val + v.val⟩

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Neg (VectorSpaceAux x φ hpos hsymm hdef) where
  neg u := ⟨-u.val⟩

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Sub (VectorSpaceAux x φ hpos hsymm hdef) where
  sub u v := ⟨u.val - v.val⟩

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  SMul ℝ (VectorSpaceAux x φ hpos hsymm hdef) where
  smul a u := ⟨a • u.val⟩

noncomputable def seminormOfBilinearForm {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ)
    (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  Seminorm ℝ (E x) where
  toFun v := Real.sqrt (φ v v)
  map_zero' := by simp
  add_le' r s := by
    rw [@Real.sqrt_le_iff]
    · have h0 : ((φ r) s) * ((φ s) r) ≤ ((φ r) r) * ((φ s) s) :=
        LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le φ.toLinearMap₁₂ hpos r s
      have h1 : φ (r + s) (r + s) ≤ (Real.sqrt ((φ r) r) + Real.sqrt ((φ s) s)) ^ 2 := by
        calc φ (r + s) (r + s)
          = (φ r) r + (φ r) s + (φ s) r + (φ s) s := by grind
        _ = (φ r) r + 2 * (φ r) s + (φ s) s := by
              rw [hsymm r s]
              ring
        _ ≤ (φ r) r + 2 * √((φ r) r * (φ s) s) + (φ s) s := by
              gcongr
              have h1 :  (φ r) s * (φ s) r ≤ (φ r) r * (φ s) s :=
                LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le φ.toLinearMap₁₂ hpos r s
              have h2 :  ((φ r) s) ^ 2 ≤ ((φ r) r * (φ s) s) := by
                rw [sq, hsymm r s]
                exact le_of_eq_of_le (congrFun (congrArg HMul.hMul (hsymm s r)) ((φ s) r)) h0
              exact Real.le_sqrt_of_sq_le h2
        _ = (√((φ r) r) + √((φ s) s)) ^ 2 := by
                rw [add_sq, Real.sq_sqrt (hpos r), Real.sq_sqrt (hpos s),
                    Real.sqrt_mul (hpos r) ((φ s) s)]
                ring
      exact ⟨by positivity, h1⟩
  neg' r := by simp
  smul' a v := by simp [← mul_assoc, ← Real.sqrt_mul_self_eq_abs, Real.sqrt_mul (mul_self_nonneg a)]

noncomputable instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Norm (VectorSpaceAux x φ hpos hsymm hdef) where
  norm v := seminormOfBilinearForm φ hpos hsymm v.val

lemma seminormOfBilinearForm_sub_self {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    (v : VectorSpaceAux x φ hpos hsymm hdef) :
  seminormOfBilinearForm φ hpos hsymm (v.val - v.val) = 0 := by
  unfold seminormOfBilinearForm
  simp

lemma seminormOfBilinearForm_sub_comm {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
    (u v : VectorSpaceAux x φ hpos hsymm hdef) :
  seminormOfBilinearForm φ hpos hsymm (u.val - v.val) =
  seminormOfBilinearForm φ hpos hsymm (v.val - u.val) := by
  unfold seminormOfBilinearForm
  have : √((φ (u.val - v.val)) (u.val - v.val)) =  √((φ (v.val - u.val)) (v.val - u.val)) := by
    grind
  exact this

lemma my_eq_of_dist_eq_zero {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  ∀ {u v: VectorSpaceAux x φ hpos hsymm hdef},
    (seminormOfBilinearForm φ hpos hsymm) (u.val - v.val) = 0 → u = v := by
    intro u v h
    rw [seminormOfBilinearForm] at h
    have h1 : u.val - v.val = 0 := (hdef (u.val - v.val))
      ((Real.sqrt_eq_zero (hpos (u.val - v.val))).mp h)
    apply (VectorSpaceAux.ext_iff φ hpos hsymm hdef u v).mpr
    exact sub_eq_zero.mp h1

lemma my_dist_triangle {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  ∀ (x_1 y z : VectorSpaceAux x φ hpos hsymm hdef),
    (seminormOfBilinearForm φ hpos hsymm) (x_1.val - z.val) ≤
      (seminormOfBilinearForm φ hpos hsymm) (x_1.val - y.val) +
      (seminormOfBilinearForm φ hpos hsymm) (y.val - z.val) := by
  intro u v w
  have h1 : seminormOfBilinearForm φ hpos hsymm ((u.val - v.val) + (v.val - w.val)) ≤
    seminormOfBilinearForm φ hpos hsymm (u.val - v.val) +
    seminormOfBilinearForm φ hpos hsymm (v.val - w.val)
    := (seminormOfBilinearForm φ hpos hsymm).add_le' (u.val - v.val) (v.val - w.val)
  have h2 : (u.val - v.val) + (v.val - w.val) = u.val - w.val :=
    sub_add_sub_cancel u.val v.val w.val
  exact h2 ▸ h1

noncomputable instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  NormedAddCommGroup (VectorSpaceAux x φ hpos hsymm hdef) where
  norm := fun v => seminormOfBilinearForm φ hpos hsymm v.val
  dist_eq := by intros; rfl
  add_assoc := fun u v w => VectorSpaceAux.ext_iff _ _ _ _ _ _|>.mpr (add_assoc u.val v.val w.val)
  zero_add := fun u => VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (zero_add u.val)
  add_zero := fun u => VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (add_zero u.val)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := fun u => VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (neg_add_cancel u.val)
  add_comm := fun u v => VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (add_comm u.val v.val)
  sub_eq_add_neg :=
    fun u v => VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (sub_eq_add_neg u.val v.val)
  dist_self := seminormOfBilinearForm_sub_self φ hpos hsymm hdef
  dist_comm := seminormOfBilinearForm_sub_comm φ hpos hsymm hdef
  dist_triangle := my_dist_triangle φ hpos hsymm hdef
  eq_of_dist_eq_zero := my_eq_of_dist_eq_zero φ hpos hsymm hdef

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  Module ℝ (VectorSpaceAux x φ hpos hsymm hdef) where
  one_smul u := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (one_smul ℝ u.val)
  mul_smul a b u := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (mul_smul a b u.val)
  smul_add a u v := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (smul_add a u.val v.val)
  smul_zero a := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (smul_zero a)
  zero_smul u := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (zero_smul ℝ u.val)
  add_smul a b u := VectorSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (add_smul a b u.val)

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  NormedSpace ℝ (VectorSpaceAux x φ hpos hsymm hdef) where
  norm_smul_le := by
    intro a u
    have h1 : (φ (a • u.val)) (a • u.val) = a * (φ u.val) (a • u.val) := by
      rw [φ.map_smul a u.val]
      rfl
    have h2 : (φ u.val) (a • u.val) = a * (φ u.val u.val) :=
      (φ u.val).map_smul a u.val
    have h3 : φ (a • u.val) (a • u.val) = a * a * φ u.val u.val := by grind
    have h4 : norm (a • u) = Real.sqrt ( a * a * φ u.val u.val) :=
      Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (congrArg Real.sqrt (id (Eq.symm h3)))))
    have h5 : norm (a • u) = |a| * Real.sqrt (φ u.val u.val) := by
      rw [h4, Real.sqrt_mul' (a * a) (hpos u.val), Real.sqrt_mul_self_eq_abs a]
    exact le_of_eq h5

def tangentSpaceEquiv {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ φ v v)
    (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  E x ≃ₗ[ℝ] VectorSpaceAux x φ hpos hsymm hdef where
  toFun v := ⟨v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun u := u.val
  left_inv _ := rfl
  right_inv _ := rfl

end tangentSpaceEquiv

variable
{EB : Type*} [NormedAddCommGroup EB]
{HB : Type*}
{F : Type*} [NormedAddCommGroup F] [TopologicalSpace (TotalSpace F E)]

noncomputable section section1

variable
  [InnerProductSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [TopologicalSpace B] [ChartedSpace HB B]
  [InnerProductSpace ℝ F]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB ω B] [ContMDiffVectorBundle ω F E IB]
  [FiniteDimensional ℝ EB]

def g_bilin_1 (i b : B) :
 (TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
             (fun (x : B) ↦ E x →L[ℝ] E x →L[ℝ] ℝ)) :=
  ⟨b, by
    letI ψ := trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
        (fun (x : B) ↦ E x →L[ℝ] E x →L[ℝ] ℝ) i
    by_cases h : (b, (fun (x : B) ↦ innerSL ℝ) b) ∈ ψ.target
    · exact (ψ.invFun (b, (fun (x : B) ↦ innerSL ℝ) b)).snd
    · exact 0⟩

open scoped Classical in
def g_bilin_2 (i p : B) : E p →L[ℝ] (E p →L[ℝ] ℝ) :=
  letI χ := trivializationAt F E i
  if p ∈ χ.baseSet then
    (innerSL ℝ).comp (χ.continuousLinearMapAt ℝ p) |>.flip.comp (χ.continuousLinearMapAt ℝ p)
  else
    0

lemma g_nonneg (j b : B) (v : E b) :
    0 ≤ ((g_bilin_2 (F := F) j b).toFun v).toFun v := by
  unfold g_bilin_2
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
  split_ifs with h
  · exact (inner_self_nonneg (𝕜 := ℝ))
  · simp

lemma g_pos (i b : B)
    (hb : b ∈ (trivializationAt F E i).baseSet ∩ (chartAt HB i).source)
    (v : E b) (hv : v ≠ 0) :
    0 < ((g_bilin_2 (F := F) i b).toFun v).toFun v := by
  unfold g_bilin_2
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
  split_ifs with hh1
  · letI χ := (trivializationAt F E i)
    have h1 : ((continuousLinearMapAt ℝ χ b) v ≠ 0 ↔ v ≠ 0) := by
      rw [←coe_continuousLinearEquivAt_eq χ hh1]
      exact AddEquivClass.map_ne_zero_iff
    have h2 : innerSL ℝ ((continuousLinearMapAt ℝ χ b) v)
                       ((continuousLinearMapAt ℝ χ b) v) ≠ 0 := inner_self_ne_zero.mpr (h1.mpr hv)
    exact Std.lt_of_le_of_ne (inner_self_nonneg (𝕜 := ℝ)) h2.symm
  · exfalso
    exact hh1 hb.1

def aux {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  SeminormFamily ℝ (E x) (Fin 1) := fun _ ↦ seminormOfBilinearForm φ hpos hsymm

instance {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0)
  [FiniteDimensional ℝ (E x)] :
    FiniteDimensional ℝ (VectorSpaceAux x φ hpos hsymm hdef) := by
      exact LinearEquiv.finiteDimensional (tangentSpaceEquiv φ hpos hsymm hdef)

end section1

section section2

variable
  [NormedAddCommGroup EB] [InnerProductSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedSpace ℝ (E x)]

lemma withSeminormsOfBilinearForm {x : B}
  (φ : E x →L[ℝ] E x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0)
  [FiniteDimensional ℝ (E x)] :
  WithSeminorms (aux φ hpos hsymm) := by
    apply WithSeminorms.congr (norm_withSeminorms ℝ (E x))
    · have h1 : IsBoundedLinearMap ℝ (tangentSpaceEquiv φ hpos hsymm hdef).toLinearMap := by
        rw [← IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap]
        exact ⟨LinearMap.isLinear _, LinearMap.continuous_of_finiteDimensional _⟩
      obtain ⟨C, hC⟩ := h1.bound
      intro i
      use {0}, ⟨max C 1, by positivity⟩
      intro v
      simp only [Seminorm.comp_id, Fin.isValue, Finset.sup_singleton, Seminorm.smul_apply,
                 coe_normSeminorm]
      calc
        seminormOfBilinearForm φ hpos hsymm v =
        ‖tangentSpaceEquiv φ hpos hsymm hdef v‖ := rfl
        _ ≤ C * ‖v‖ := hC.2 v
        _ ≤ max C 1 * ‖v‖ := by gcongr; exact le_max_left C 1
    · have h1 : IsBoundedLinearMap ℝ (tangentSpaceEquiv φ hpos hsymm hdef).symm.toLinearMap := by
        rw [← IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap]
        exact ⟨LinearMap.isLinear _, LinearMap.continuous_of_finiteDimensional _⟩
      obtain ⟨C, hC⟩ := h1.bound
      intro j
      use {0}, ⟨max C 1, by positivity⟩
      intro v
      simp only [Seminorm.comp_id, Fin.isValue, Finset.sup_singleton, Seminorm.smul_apply,
                 coe_normSeminorm, ]
      calc ‖v‖ ≤ C * seminormOfBilinearForm φ hpos hsymm v := hC.2 ⟨v⟩
        _ ≤ max C 1 * seminormOfBilinearForm φ hpos hsymm v := by
          gcongr; exact le_max_left C 1
        _ = max C 1 * aux φ hpos hsymm j v := rfl

lemma aux_tvs {x : B} (φ : E x →L[ℝ] E x →L[ℝ] ℝ)
   (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
   [FiniteDimensional ℝ (E x)] :
    Bornology.IsVonNBounded ℝ {v | (φ v) v < 1} := by
  rw [WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded
        (p := aux φ hpos hsymm) (withSeminormsOfBilinearForm φ hpos hsymm hdef)]
  intro I
  letI J : Finset (Fin 1) := {1}
  suffices ∃ r > 0, ∀ x ∈ {v | (φ v) v < 1}, (J.sup (aux φ hpos hsymm)) x < r by
    obtain (rfl | h) : I = ∅ ∨ I = {default} := by
      by_cases h : I = ∅
      · simp only [Fin.default_eq_zero, Fin.isValue]
        exact Or.symm (Or.inr h)
      · rw [Finset.eq_singleton_iff_nonempty_unique_mem]
        refine Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr h, fun x hx ↦ Unique.uniq _ _⟩
    · use 1; simp
    · convert this
  simp only [Set.mem_setOf_eq, Finset.sup_singleton, J]
  refine ⟨1, by norm_num, fun x h ↦ ?_⟩
  simp only [aux, seminormOfBilinearForm]
  change Real.sqrt (φ x x) < 1
  rw [Real.sqrt_lt' (by norm_num)]
  simp [h]

end section2

noncomputable section section3

variable
  [InnerProductSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [TopologicalSpace B] [ChartedSpace HB B]
  [InnerProductSpace ℝ F]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

theorem g_bilin_symm_2 (i p : B) (v w : E p) :
    ((g_bilin_2 (F := F) i p).toFun v).toFun w =
    ((g_bilin_2 (F := F) i p).toFun w).toFun v := by
  unfold g_bilin_2
  split_ifs with h
  · simp [real_inner_comm]
  · simp

def g_global_bilin_2 (f : SmoothPartitionOfUnity B IB B) (p : B) :
    E p →L[ℝ] (E p →L[ℝ] ℝ) :=
  ∑ᶠ (j : B), (f j) p • g_bilin_2 (F := F) j p

lemma finsum_image_eq_sum {B E F : Type*} [AddCommMonoid E] [AddCommMonoid F]
  (φ : E →+ F) {f : B → E} {h_fin : Finset B}
  (h1 : Function.support f ⊆ h_fin) :
  ∑ᶠ j, φ (f j) = ∑ j ∈ h_fin, φ (f j) := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    have hf : f j ≠ 0 := by
      contrapose! hj
      simpa using (map_zero φ).symm ▸ congrArg φ hj
    exact h1 hf

def evalAt (b : B) (v w : E b) :
    (E b →L[ℝ] (E b →L[ℝ] ℝ)) →+ ℝ where
    toFun := fun f => (f.toFun v).toFun w
    map_zero' := by simp
    map_add' := by intro f g; exact rfl

lemma riemannian_metric_symm_2 (f : SmoothPartitionOfUnity B IB B) (b : B)
  (v w : E b) :
  ((g_global_bilin_2 (F := F) f b).toFun v).toFun w
   =
  ((g_global_bilin_2 (F := F) f b).toFun w).toFun v := by
  unfold g_global_bilin_2
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
  have h1 : (Function.support fun j ↦ ((f j) b • (g_bilin_2 (F := F) j b) :
    E b →L[ℝ] E b →L[ℝ] ℝ)).Finite := by
    apply (f.locallyFinite'.point_finite b).subset
    intro i hi
    simp only [Function.mem_support, ne_eq, smul_eq_zero, not_or] at hi
    exact hi.1
  rw [finsum_eq_sum _ h1]
  letI h : (j : B) → (E b →L[ℝ] (E b →L[ℝ] ℝ)) := fun j ↦ (f j) b • g_bilin_2 (F := F) j b
  have h2 : (Function.support h) ⊆ h1.toFinset := Finite.toFinset_subset.mp fun ⦃a⦄ a ↦ a
  have h3 : ∀ (u v : E b),
      ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_2 (F := F) j b).toFun u).toFun v =
      ((∑ j ∈ h1.toFinset, (f j) b • g_bilin_2 (F := F) j b).toFun u).toFun v := by
    intros u v
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  calc ((∑ j ∈ h1.toFinset, (f j) b • g_bilin_2 (F := F) j b).toFun v).toFun w
      = ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_2 (F := F) j b).toFun v).toFun w := (h3 v w).symm
    _ = ∑ᶠ (j : B), (((f j) b • g_bilin_2 j b).toFun v).toFun w :=
          (finsum_image_eq_sum (evalAt b v w) (f := h) (h_fin := h1.toFinset) h2).symm
    _ = ∑ᶠ (j : B), (((f j) b • g_bilin_2 j b).toFun w).toFun v :=
          finsum_congr (fun j ↦ congrArg (HMul.hMul ((f j) b)) (g_bilin_symm_2 j b v w))
    _ = ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_2 j b).toFun w).toFun v :=
          finsum_image_eq_sum (evalAt b w v) (f := h) (h_fin := h1.toFinset) h2
    _ = ((∑ j ∈ h1.toFinset, (f j) b • g_bilin_2 j b).toFun w).toFun v := h3 w v

lemma riemannian_metric_pos_def_2 (f : SmoothPartitionOfUnity B IB B)
  (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
  (b : B) (v : E b) (hv : v ≠ 0) :
  0 < g_global_bilin_2 (F := F) f b v v := by
  unfold g_global_bilin_2
  have h1 : (Function.support fun j ↦ ((f j) b • (g_bilin_2 (F := F) j b) :
    E b →L[ℝ] E b →L[ℝ] ℝ)).Finite := by
    apply (f.locallyFinite'.point_finite b).subset
    intro i hi
    simp only [Function.mem_support, ne_eq, smul_eq_zero, not_or] at hi
    exact hi.1
  rw [finsum_eq_sum _ h1]
  have h2 : ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_2 (F := F) j b).toFun v).toFun v =
            ((∑ j ∈ h1.toFinset, (f j) b • g_bilin_2 (F := F) j b).toFun v).toFun v := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  letI h : (j : B) → (E b →L[ℝ] (E b →L[ℝ] ℝ)) := fun j ↦ (f j) b • g_bilin_2 (F := F) j b
  letI h' x := f x b * ((g_bilin_2 (F := F) x b).toFun v).toFun v
  have h3 : (Function.support h) ⊆ h1.toFinset := Set.Finite.toFinset_subset.mp fun ⦃a⦄ a ↦ a
  have h4 : ∀ i, 0 ≤ f.toFun i b := fun i => f.nonneg' i b
  have ⟨i, h5⟩ : ∃ i, 0 < f i b := by
    by_contra hneg
    push_neg at hneg
    have : ∀ (x : B), f x b = 0 := fun x => le_antisymm (hneg x) (h4 x)
    exact absurd ((finsum_eq_zero_of_forall_eq_zero this).symm.trans (f.sum_eq_one' b trivial))
      one_ne_zero.symm
  have h6 : b ∈ (trivializationAt F E i).baseSet ∩ (chartAt HB i).source :=
    hf i (subset_closure (Function.mem_support.mpr h5.ne'))
  have h7 : ∀ j, 0 ≤ h' j := fun j => mul_nonneg (h4 j) (g_nonneg j b v)
  have h8 : ∃ j, 0 < h' j := ⟨i, mul_pos h5 (g_pos i b h6 v hv)⟩
  have h9 : (Function.support h').Finite := by
    apply (f.locallyFinite'.point_finite b).subset
    intro x hx
    simp only [Function.support_mul, Set.mem_inter_iff, Function.mem_support, ne_eq, h'] at hx
    exact mul_ne_zero_iff.mp (mul_ne_zero_iff.mpr hx) |>.1
  have ha : 0 < ∑ᶠ i, h' i := finsum_pos h7 h8 h9
  have hb : ∑ᶠ i, h' i =
            ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_2 (F := F) j b).toFun v).toFun v :=
    (finsum_image_eq_sum (evalAt b v v) (f := h) (h_fin := h1.toFinset) h3) ▸ rfl
  exact lt_of_lt_of_eq ha (hb.trans h2)

lemma riemannian_unit_ball_bounded_2 (f : SmoothPartitionOfUnity B IB B)
  (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
  [∀ x, FiniteDimensional ℝ (E x)] :
  ∀ (b : B), Bornology.IsVonNBounded ℝ
    {v : E b | g_global_bilin_2 (F := F) f b v v < 1} := fun b =>
  aux_tvs (g_global_bilin_2 f b)
    (fun v => by
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · exact le_of_lt (riemannian_metric_pos_def_2 f hf b v hv))
    (fun u v => riemannian_metric_symm_2 f b u v)
    (fun v h => by
      by_contra hv
      exact lt_irrefl 0 (h ▸ riemannian_metric_pos_def_2 f hf b v hv))

end section3

section section4

variable
  [InnerProductSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [TopologicalSpace B] [ChartedSpace HB B]
  [InnerProductSpace ℝ F]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ω F E IB]

lemma g_bilin_1g_smooth_on_chart (i : B) :
  ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
    (g_bilin_1 (F := F) (E := E) i)
    ((trivializationAt F E i).baseSet ∩ (chartAt HB i).source) := by
  unfold g_bilin_1
  simp only [hom_trivializationAt_target, hom_trivializationAt_baseSet,
  Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet, Set.inter_univ,
  Set.inter_self, Set.mem_prod,
  Set.mem_univ, and_true, PartialEquiv.invFun_as_coe, OpenPartialHomeomorph.coe_coe_symm,
  dite_eq_ite]
  intro b hb
  classical
  letI ψ := trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) i
  have heq : ∀ x ∈ (chartAt HB i).source,
    (if (x, ((innerSL ℝ) : (F →L[ℝ] F →L[ℝ] ℝ))) ∈ (chartAt HB i).source ×ˢ Set.univ
      then
        ψ.invFun (x, ((innerSL ℝ) : (F →L[ℝ] F →L[ℝ] ℝ)))
      else
        ⟨x, 0⟩)
    =
    ψ.invFun (x, ((innerSL ℝ) : (F →L[ℝ] F →L[ℝ] ℝ))) := by
    intro x hx
    have : (x, ((innerSL ℝ) : (F →L[ℝ] F →L[ℝ] ℝ))) ∈
      (chartAt HB i).source ×ˢ Set.univ := Set.mk_mem_prod hx trivial
    exact if_pos this
  have h2 : ContMDiffOn (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
    ψ.toPartialEquiv.symm ψ.target := contMDiffOn_symm _
  letI innerAtP : B → F →L[ℝ] F →L[ℝ] ℝ := fun x ↦ innerSL ℝ
  have h4 : ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
    (fun c => (c, innerAtP c)) ((trivializationAt F E i).baseSet ∩ (chartAt HB i).source) := by
      apply ContMDiffOn.prodMk
      · exact contMDiffOn_id
      · exact contMDiffOn_const
  have : (trivializationAt F E i).baseSet ∩ (chartAt HB i).source ⊆
  (fun c ↦ (c, innerAtP c)) ⁻¹' ψ.target := by
    intro c hc
    simp only [Set.mem_preimage]
    rw [ψ.target_eq]
    simp only [Set.mem_prod, Set.mem_univ, and_true]
    have baseSet_eq : (trivializationAt F E i).baseSet =
    (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) i).baseSet := by
      simp only [hom_trivializationAt_baseSet, Trivial.fiberBundle_trivializationAt',
               Trivial.trivialization_baseSet, Set.inter_univ, Set.inter_self]
    rw [←baseSet_eq]
    exact hc.1
  have h5 : ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
    (ψ.toPartialEquiv.symm ∘ fun c ↦ (c, innerAtP c))
     ((trivializationAt F E i).baseSet ∩ (chartAt HB i).source) := h2.comp h4 this
  refine (ContMDiffOn.congr h5 ?_) b hb
  intro y hy
  simp only [Function.comp_apply]
  ext
  · rfl
  · simp only [innerAtP, Set.inter_univ, Set.inter_self, Set.mem_prod, Set.mem_univ, and_true,
               OpenPartialHomeomorph.coe_coe_symm, heq_eq_eq, if_pos hy.1]
    rfl

end section4

noncomputable section section5

variable
  [InnerProductSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [TopologicalSpace B] [ChartedSpace HB B]
  [InnerProductSpace ℝ F]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ω F E IB]

def g_global_bilin_1 (f : SmoothPartitionOfUnity B IB B) (p : B) :
    E p →L[ℝ] (E p →L[ℝ] ℝ) :=
      ∑ᶠ (j : B), (f j) p • (g_bilin_1 (F := F) j p).snd

lemma g_global_bilin_1_smooth (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source)) :
  ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g_global_bilin_1 (F := F) (E := E) f x)) := by
  have h1 := contMDiff_totalSpace_weighted_sum_of_local_sections
    (V := fun b => E b →L[ℝ] (E b →L[ℝ] Trivial B ℝ b))
    (F_fiber := F →L[ℝ] (F →L[ℝ] ℝ))
    (s_loc := fun (i b : B) => (g_bilin_1 (F := F) i b).snd)
    (U := fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source)
    (hU_isOpen := by
      intro i
      simp only
      exact IsOpen.inter (trivializationAt F E i).open_baseSet (chartAt HB i).open_source)
    (hρ_subord := h_sub)
    (h_smooth_s_loc := by
      intro i
      apply ContMDiffOn.congr
      · have : ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞ (g_bilin_1 i)
                ((trivializationAt F E i).baseSet ∩ (chartAt HB i).source) :=
          g_bilin_1g_smooth_on_chart i
        exact this
      · have h1 : ∀ y ∈ (trivializationAt F E i).baseSet ∩ (chartAt HB i).source,
          TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) y ((g_bilin_1 (F := F) (E := E) i y).snd) =
          g_bilin_1 (F := F) i y := by
          unfold g_bilin_1
          simp only [Set.mem_inter_iff, hom_trivializationAt_target, hom_trivializationAt_baseSet,
            Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet, Set.inter_univ,
            Set.inter_self, Set.mem_prod,
            Set.mem_univ, and_true, PartialEquiv.invFun_as_coe,
            OpenPartialHomeomorph.coe_coe_symm, dite_eq_ite, implies_true]
        exact h1)
  exact h1

end section5

section section6

variable
  [InnerProductSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [TopologicalSpace B] [ChartedSpace HB B]
  [InnerProductSpace ℝ F]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

lemma trivializationAt_vectorBundle_bilinearForm_apply
    (x₀ x : B)
    (w : E x →L[ℝ] E x →L[ℝ] ℝ)
    (u v : F)
    (hx : x ∈ (trivializationAt F E x₀).baseSet) :
  (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
                    (fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) x₀).continuousLinearMapAt ℝ x w u v =
    w ((trivializationAt F E x₀).symm x u)
      ((trivializationAt F E x₀).symm x v) := by
  rw [continuousLinearMapAt_apply, @linearMapAt_apply]
  simp only [hom_trivializationAt_baseSet, Trivial.fiberBundle_trivializationAt',
             Trivial.trivialization_baseSet, Set.inter_univ, Set.inter_self]
  rw [hom_trivializationAt_apply]
  have hx' : x ∈ (trivializationAt F E x₀).baseSet ∩
    ((trivializationAt F E x₀).baseSet ∩ Set.univ) := by
    exact ⟨hx, ⟨hx, trivial⟩⟩
  rw [if_pos hx',
      inCoordinates_apply_eq₂ hx hx (by simp : x ∈ (trivializationAt ℝ (fun _ ↦ ℝ) x₀).baseSet)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
             LinearMap.id_coe, id_eq]

lemma g_bilin_eq (i b : B)
  (hb : b ∈ (trivializationAt F E i).baseSet ∩ (chartAt HB i).source)
  (α β : E b) :
  (g_bilin_1 (F := F) i b).snd.toFun α β = (g_bilin_2 (F := F) i b).toFun α β := by
  unfold g_bilin_1 g_bilin_2
  simp only [PartialEquiv.invFun_as_coe, OpenPartialHomeomorph.coe_coe_symm, dite_eq_ite,
    hom_trivializationAt_target, hom_trivializationAt_baseSet,
    Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet,
    Set.inter_univ, Set.inter_self, Set.mem_prod, hb.1, Set.mem_univ, and_self, ↓reduceDIte,
    AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe, if_true]
  letI ψ := FiberBundle.trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
      (fun (x : B) ↦ E x →L[ℝ] E x →L[ℝ] ℝ) i
  letI χ := trivializationAt F E i
  letI w := ψ.symm b (innerSL ℝ)
  have hc : b ∈ ψ.baseSet := by
    rw [hom_trivializationAt_baseSet]
    simp only [hom_trivializationAt_baseSet, Trivial.fiberBundle_trivializationAt',
               Trivial.trivialization_baseSet, inter_univ, inter_self]
    exact hb.1
  have h1 u v :
      (((continuousLinearMapAt ℝ ψ b) (ψ.symmL ℝ b (innerSL ℝ))) u) v =
      innerSL ℝ u v :=
    by rw [continuousLinearMapAt_symmL ψ hc]
  have h2 : ∀ u v, innerSL ℝ u v = w (χ.symm b u) (χ.symm b v) := fun u v => by
    rw [← h1]; exact trivializationAt_vectorBundle_bilinearForm_apply i b w u v hb.1
  have h3 : χ.symm b (χ.continuousLinearMapAt ℝ b α) = α :=
    symmL_continuousLinearMapAt (trivializationAt F E i) hb.1 α
  have h4 : χ.symm b (χ.continuousLinearMapAt ℝ b β) = β :=
    symmL_continuousLinearMapAt (trivializationAt F E i) hb.1 β
  have h5 : (innerSL ℝ) ((continuousLinearMapAt ℝ χ b) α) ((continuousLinearMapAt ℝ χ b) β) =
      w α β := by
    rw [h2 (χ.continuousLinearMapAt ℝ b α) (χ.continuousLinearMapAt ℝ b β), h3, h4]
  have h6 : (ψ.toOpenPartialHomeomorph.symm (b, innerSL ℝ)).snd = ψ.symm b (innerSL ℝ) := by
    rw [symm_apply ψ hc (innerSL ℝ)]
    simp only [cast_eq]
  rw [h6, ← h5]
  exact real_inner_comm _ _

lemma g_global_bilin_eq
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
    (p : B) (α β : E p) :
    g_global_bilin_1 (F := F) (E := E) f p α β =
    g_global_bilin_2 (F := F) f p α β := by
  have : g_global_bilin_1 (F := F) (E := E) f p = g_global_bilin_2 (F := F) f p := by
    unfold g_global_bilin_1 g_global_bilin_2
    congr 1
    ext j
    congr 2
    ext α β
    by_cases h : (f j) p = 0
    · have h1 : (f j) p = 0 := h
      have h2 : (f j) p • (g_bilin_1 (F := F) (E := E) j p).snd = 0 :=
        smul_eq_zero_of_left h (g_bilin_1 j p).snd
      have h3 : (f j) p • g_bilin_2 (F := F) (E := E) j p = 0 :=
        smul_eq_zero_of_left h (g_bilin_2 j p)
      rw [h2, h3]
    · have hp : p ∈ tsupport (f j) := by
        rw [tsupport]
        apply subset_closure
        exact h
      have hsupp : p ∈ (trivializationAt F E j).baseSet ∩ (chartAt HB j).source :=
        hf j hp
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      congr 1
      exact g_bilin_eq j p hsupp α β
  rw [this]

lemma riemannian_metric_symm_1
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
    (b : B) (v w : E b) :
    g_global_bilin_1 (F := F) (E := E) f b v w =
    g_global_bilin_1 (F := F) (E := E) f b w v := by
  rw [g_global_bilin_eq f hf b v w, g_global_bilin_eq f hf b w v]
  exact Real.ext_cauchy (congrArg Real.cauchy (riemannian_metric_symm_2 (F := F) f b v w))

lemma riemannian_metric_pos_def_1
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
    (b : B) (v : E b) (hv : v ≠ 0) :
    0 < g_global_bilin_1 (F := F) (E := E) f b v v := by
  rw [g_global_bilin_eq (F := F) (E := E) f hf b v v]
  exact riemannian_metric_pos_def_2 f hf b v hv

lemma riemannian_unit_ball_bounded_1 (f : SmoothPartitionOfUnity B IB B)
  (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
  [∀ x, FiniteDimensional ℝ (E x)] :
  ∀ (b : B), Bornology.IsVonNBounded ℝ
    {v : E b | g_global_bilin_1 (F := F) (E := E) f b v v < 1} := by
  intro b
  have hy : ∀ v, g_global_bilin_1 (F := F) (E := E) f b v v =
                  g_global_bilin_2 (F := F) f b v v :=
    fun v => g_global_bilin_eq f hf b v v
  simp_rw [hy]
  exact riemannian_unit_ball_bounded_2 f hf b

end section6

section section9

variable
  [InnerProductSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  [TopologicalSpace B] [ChartedSpace HB B]
  [InnerProductSpace ℝ F]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB ω B] [ContMDiffVectorBundle ω F E IB]
  [FiniteDimensional ℝ EB] [SigmaCompactSpace B] [T2Space B]

/--
Existence of a smooth Riemannian metric on a manifold.
-/
public theorem exists_riemannian_metric
  [FiniteDimensional ℝ F]
  [∀ x, FiniteDimensional ℝ (E x)] :
    Nonempty (ContMDiffRiemannianMetric (IB := IB) (n := ∞) (F := F) (E := E)) :=
  let ⟨f, hf⟩ : ∃ (f : SmoothPartitionOfUnity B IB B),
      f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source) := by
    apply SmoothPartitionOfUnity.exists_isSubordinate
    · exact isClosed_univ
    · intro i
      exact IsOpen.inter (trivializationAt F E i).open_baseSet (chartAt HB i).open_source
    · intro b _
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      exact ⟨b, FiberBundle.mem_baseSet_trivializationAt' b, mem_chart_source HB b⟩
  ⟨{ inner := g_global_bilin_1 (F := F) f
     symm := riemannian_metric_symm_1 f hf
     pos := riemannian_metric_pos_def_1 f hf
     isVonNBounded := riemannian_unit_ball_bounded_1 f hf
     contMDiff := g_global_bilin_1_smooth f hf }⟩

end section9
