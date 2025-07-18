import Mathlib

open Set Complex

def HalfN := Set.Ioo 0 Real.pi
def HalfE := Set.Ioo (-Real.pi / 2) (Real.pi / 2)
def HalfS := Set.Ioo Real.pi (2 * Real.pi)
def HalfW := Set.Ioo (Real.pi / 2) (3 * Real.pi / 2)

noncomputable def chartNorthComplex : PartialEquiv Circle ℝ :=
{ toFun z := Complex.re (z : ℂ),
  invFun x := Circle.exp (Real.arccos x),
  source := Circle.exp '' HalfN,
  target := Set.Ioo (-1) 1,

  map_source' := sorry,
  map_target' := sorry,

  left_inv' := sorry,
  right_inv' := sorry }

noncomputable def chartEastComplex : PartialEquiv Circle ℝ :=
{ toFun z := Complex.im (z : ℂ),
  invFun x := Circle.exp (Real.arcsin x),
  source := Circle.exp '' HalfE,
  target := Set.Ioo (-1) 1,

  map_source' := sorry,
  map_target' := sorry,

  left_inv' := sorry,
  right_inv' := sorry }

noncomputable def chartSouthComplex : PartialEquiv Circle ℝ :=
{ toFun z := Complex.re (z : ℂ),
  invFun x := Circle.exp (2 * Real.pi - Real.arccos x),
  source := Circle.exp '' HalfS,
  target := Set.Ioo (-1) 1,

  map_source' := sorry,
  map_target' := sorry,

  left_inv' := sorry,
  right_inv' := sorry }

noncomputable def chartWestComplex : PartialEquiv Circle ℝ :=
{ toFun z := Complex.im (z : ℂ),
  invFun x := Circle.exp (Real.pi - Real.arcsin x),
  source := Circle.exp '' HalfW
  target := Set.Ioo (-1) 1,

  map_source' := sorry,
  map_target' := sorry,

  left_inv' := sorry,
  right_inv' := sorry }

lemma FourSemis : (univ : Set Circle) ⊆
  Circle.exp '' (HalfN ∪ HalfE ∪ HalfS ∪ HalfW) := by
  intro z hz
  by_cases hθ0 : z = 1
  · have h1 : z = 1 := hθ0
    have h2 : 1 ∈ Circle.exp '' HalfE := by
      use (0 : Real)
      simp
      have h21 : 0 < Real.pi / 2 := by
        exact Real.pi_div_two_pos
      have h22 : -(Real.pi / 2)  < 0 := by
        exact neg_neg_iff_pos.mpr Real.pi_div_two_pos
      have h24 : -(Real.pi / 2) = -Real.pi / 2 := neg_div' 2 Real.pi
      have h25 :  -Real.pi / 2 < 0 := lt_of_eq_of_lt (id (Eq.symm h24)) h22
      exact And.symm ⟨h21, h25⟩
    have h3 : z ∈ Circle.exp ''HalfE := mem_of_eq_of_mem hθ0 h2
    have h4 : HalfE ⊆ HalfN ∪ HalfE := subset_union_right
    have h5 : HalfN ∪HalfE ⊆ HalfN ∪ HalfE ∪  HalfS := subset_union_left
    have h6 : HalfN ∪ HalfE ∪ HalfS ⊆ HalfN ∪HalfE ∪ HalfS ∪ HalfW := subset_union_left
    have h7 : HalfE ⊆ (HalfN ∪HalfE ∪ HalfS ∪ HalfW) := by
      exact subset_union_of_subset_left (fun ⦃a⦄ a_1 ↦ h5 (h4 a_1))
                                        (Ioo (Real.pi / 2) (3 * Real.pi / 2))
    have h8 : Circle.exp ''HalfE ⊆ Circle.exp '' (HalfN ∪ HalfE ∪ HalfS ∪ HalfW) := by
      exact image_mono h7
    have h9 : z ∈ Circle.exp '' (HalfN ∪ HalfE ∪ HalfS ∪ HalfW) := by
      exact h8 h3
    exact h8 h3
  · exact sorry

noncomputable
def myChartAt z :=
    let θ := Complex.arg z
    if θ < Real.pi / 2 then chartEastComplex
    else if θ < Real.pi then chartNorthComplex
    else if θ < 3 * Real.pi / 2 then chartWestComplex
    else chartSouthComplex

lemma contOnNE01 : ContDiffOn ℝ ⊤ (chartNorthComplex.symm.trans chartEastComplex)
                         (Set.Ioo 0 1) := by
  intro x hx
  have h1 : ∀ x ∈ (Set.Ioo 0 1), (chartNorthComplex.symm.trans chartEastComplex) x =
          Complex.im (Circle.exp (Real.arccos x)) := by
    intro x hx
    exact rfl
  have h2 : ∀ x ∈ (Set.Ioo 0 1), Complex.im (Circle.exp (Real.arccos x)) = √(1 - x^2) := by
    intro x hx
    simp
    exact Real.sin_arccos x

  have h3 : ContDiffOn ℝ ⊤ (fun x : ℝ ↦ x ^ 2) (Set.Ioo 0 1) := by
    exact ContDiffOn.pow contDiffOn_id 2

  have h4 : ContDiffOn ℝ ⊤ (fun x : ℝ ↦ (1 - x)) (Set.Ioo 0 1) := by
    exact contDiffOn_const.sub contDiffOn_id

  have h6 : ContDiffOn ℝ ⊤ (fun x : ℝ ↦ 1 - x ^ 2) (Set.Ioo 0 1) := by
    have h61 : MapsTo (fun x : ℝ ↦ x ^ 2) (Ioo 0 1) (Ioo 0 1) := by
      intro x hx
      have h0 : 0 < x ∧ x < 1 := hx
      have h1 : 0 < x^2 := pow_pos h0.1 2
      have h2 : x ^ 2 < 1 := by
        have h20 : (0 : ℝ) < 2 := two_pos
        have h21 : (x : ℝ) ^ (2 : ℝ) < 1 := Real.rpow_lt_one (le_of_lt h0.1) h0.2 h20
        exact_mod_cast h21
      exact ⟨h1, h2⟩
    exact ContDiffOn.comp h4 h3 h61

  have ha :  ∀ x ∈ Ioo (0 : ℝ) 1, 1 - x ^ 2 ≠ 0 := by
    intro x hx
    have h0 : 0 < x ∧ x < 1 := hx
    have h1 : 0 < x ^ 2 := pow_pos h0.1 2
    have h2 : x ^ 2 < 1 := by
      have h20 : (0 : ℝ) < 2 := two_pos
      have h21 : (x : ℝ) ^ (2 : ℝ) < 1 := Real.rpow_lt_one (le_of_lt h0.1) h0.2 h20
      exact_mod_cast h21
    exact ne_of_gt (sub_pos_of_lt h2)

  have h5 :  ContDiffOn ℝ ⊤ (fun x ↦ √(1 - x ^ 2)) (Ioo 0 1) := by
    exact ContDiffOn.sqrt h6 ha

  have h8 : ∀ x ∈ (Set.Ioo 0 1), ((chartNorthComplex.symm.trans chartEastComplex)) x =
                 (fun x ↦ √(1 - x ^ 2)) x := by
    intro x hx
    rw [h1 x hx, h2 x hx]

  have h9 :  EqOn (↑(chartNorthComplex.symm.trans chartEastComplex)) (fun x ↦ √(1 - x ^ 2))
                  (Ioo 0 1) := by
    intro x hx
    exact h8 x hx

  have h7 : ContDiffOn ℝ ⊤ (chartNorthComplex.symm.trans chartEastComplex) (Set.Ioo 0 1) := by
    exact ContDiffOn.congr h5 h9

  exact h7 x hx

lemma circleOverlap1 :
    (↑Circle.exp) '' HalfN ∩ (↑Circle.exp) '' HalfE ⊇ (↑Circle.exp) '' (HalfN ∩ HalfE) := by
  exact Set.image_inter_subset _ _ _

lemma circleOverlap2 :
    (↑Circle.exp) '' HalfN ∩ (↑Circle.exp) '' HalfE ⊆ (↑Circle.exp) '' (HalfN ∩ HalfE) := by
  rintro z ⟨⟨θ₁, hθ₁, rfl⟩, ⟨θ₂, hθ₂, heq⟩⟩
  have h1 : ∃ (m : ℤ), θ₂ = θ₁ + ↑m * (2 * Real.pi) := Circle.exp_eq_exp.mp heq
  have h2 : θ₁ ∈ Set.Ioo 0 Real.pi := hθ₁
  have h3 : θ₂ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2) := hθ₂
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp heq
  by_contra h
  push_neg at h
  rcases Int.lt_trichotomy m 0 with mlt | meq | mgt
  · have h0 : m < 0 := mlt
    exact sorry
  · rw [meq, Int.cast_zero, zero_mul, add_zero] at hm
    subst hm
    exact h ⟨θ₂, ⟨mem_inter hθ₁ hθ₂, heq⟩⟩
  · have h0 : 0 < m := mgt
    have h1 : 1 ≤ m := Int.add_one_le_iff.mpr h0
    have h2 : θ₂ = θ₁ + m * (2 * Real.pi) := hm
    have h3 : (1 : ℝ) * (2 * Real.pi) ≤ (m : ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right (Int.cast_one_le_of_pos mgt) (by positivity)
    have hu : (1 : ℝ) * (2 * Real.pi) = 2 * Real.pi := one_mul (2 * Real.pi)
    have hv :  2 * Real.pi ≤ ↑m * (2 * Real.pi) := by rw [hu] at h3; exact h3
    have hz : θ₁ > 0 := hθ₁.1
    have h4 : θ₁ + m * (2 * Real.pi) ≥ 0 + 2 * Real.pi := add_le_add (le_of_lt hz) hv
    have h5 : θ₂ ≥ 0 + 2 * Real.pi := by rw [<-h2] at h4; exact h4
    have h6 : 0 + 2 * Real.pi = 2 * Real.pi := AddZeroClass.zero_add (2 * Real.pi)
    have h7 : θ₂ ≥ 2 * Real.pi := le_of_eq_of_le (id (Eq.symm h6)) h5
    have h8 : θ₂ < Real.pi / 2 := hθ₂.2
    have : (2 * Real.pi : ℝ) > Real.pi / 2 := by
      linarith [Real.pi_pos]
    exact not_lt_of_ge h7 (lt_trans h8 this)

lemma circleOverlap : (↑Circle.exp) '' HalfN ∩ (↑Circle.exp) '' HalfE =
                      (↑Circle.exp) '' (HalfN ∩ HalfE) := by
  have h1 : (↑Circle.exp) '' HalfN ∩ (↑Circle.exp) '' HalfE ⊆
            (↑Circle.exp) '' (HalfN ∩ HalfE) := circleOverlap2
  have h2 : (↑Circle.exp) '' HalfN ∩ (↑Circle.exp) '' HalfE ⊇
            (↑Circle.exp) '' (HalfN ∩ HalfE) := circleOverlap1
  exact Subset.antisymm h1 h2

lemma targetOverlap1 :
  Ioo 0 1 ⊆ Complex.re '' ((fun θ ↦ (Circle.exp θ : ℂ)) '' (Set.Ioo 0 (Real.pi / 2))) := by
  intro x hx
  simp
  let θ := Real.arccos x
  have hu : -1 < x := lt_trans neg_one_lt_zero hx.1
  have h0 : Real.cos θ = x := Real.cos_arccos (le_of_lt hu) (le_of_lt hx.2)
  rcases hx with ⟨hl, hu⟩
  have h1 : 0 < θ := Real.arccos_pos.mpr hu
  have h2 : θ < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hl
  use θ

lemma targetOverlap2 :
  Complex.re '' ((fun θ ↦ (Circle.exp θ : ℂ)) '' (Set.Ioo 0 (Real.pi / 2))) ⊆ Ioo 0 1 := by
  intro x hx
  simp
  rcases hx with ⟨z, ⟨hz, rfl⟩⟩
  rcases hz with ⟨θ, ⟨hθ, rfl⟩⟩
  let y := Complex.re (Circle.exp θ : ℂ)
  have h1 : Complex.re (Circle.exp θ : ℂ) = Real.cos θ := by
    simp
  rw [h1]
  have h4 : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨lt_of_lt_of_le (neg_lt_zero.mpr Real.pi_div_two_pos) (le_of_lt hθ.1), hθ.2⟩
  have h6 : θ ∈ Ioo 0 Real.pi :=
   ⟨hθ.1, lt_trans hθ.2 (div_two_lt_of_pos Real.pi_pos)⟩

  have h3 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo h4
  have h5 : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo h6
  have h7 : Real.cos θ < 1 := by
    have h7z : 0 < Real.sin θ ^ 2 := sq_pos_of_pos h5
    have h7a : Real.cos θ ^ 2 < 1 := by
      rw [← Real.sin_sq_add_cos_sq θ]
      exact lt_add_of_pos_left _ h7z
    have h73 : Real.cos θ < 1 := (sq_lt_one_iff₀ (le_of_lt h3)).mp h7a
    exact h73
  exact ⟨h3, h7⟩

lemma targetOverlap :
  Complex.re '' ((fun θ ↦ (Circle.exp θ : ℂ)) '' (Set.Ioo 0 (Real.pi / 2))) = Ioo 0 1 := by
  exact Subset.antisymm targetOverlap2 targetOverlap1

lemma foo : ((Ioo 0 Real.pi) ∩ (Ioo (-Real.pi / 2) (Real.pi / 2))) = (Ioo 0 (Real.pi / 2)) := by
  have h0 :  Ioo 0 Real.pi ∩ Ioo (-Real.pi / 2) (Real.pi / 2) =
             Ioo (max 0 (-Real.pi / 2)) (min Real.pi (Real.pi / 2)) := Ioo_inter_Ioo
  have hz : (-Real.pi / 2) ≤ 0 := sorry
  have h1 : (max 0 (-Real.pi / 2)) = 0 :=  max_eq_left hz
  have hy :  Real.pi / 2 ≤ Real.pi := sorry
  have h2 : (min Real.pi (Real.pi / 2)) = Real.pi / 2 := min_eq_right hy
  rw [Ioo_inter_Ioo, h1, h2]

lemma arccosOverlap1 : Real.arccos '' (Ioo 0 1) ⊆ Ioo 0 (Real.pi / 2) := by
  intro y hy
  rcases hy with ⟨x, hx_mem, rfl⟩
  apply mem_Ioo.mpr
  constructor
  · exact Real.arccos_pos.mpr hx_mem.2
  · exact Real.arccos_lt_pi_div_two.mpr hx_mem.1

lemma arccosOverlap2 : Ioo 0 (Real.pi / 2) ⊆  Real.arccos '' (Ioo 0 1) := by
  rintro y ⟨hy₀, hy₁⟩
  let x := Real.cos y
  have hx0 : 0 < x := by
    apply Real.cos_pos_of_mem_Ioo ⟨
      show -(Real.pi / 2) < y from
        calc
          -(Real.pi / 2) < 0 := neg_lt_zero.mpr Real.pi_div_two_pos
          _ < y := hy₀,
      hy₁⟩
  have hx4 : y < Real.pi / 2 := hy₁
  have hx5 : Real.pi / 2 < Real.pi := by
    apply div_two_lt_of_pos
    exact Real.pi_pos
  have hx3 : y < Real.pi := lt_of_le_of_lt (le_of_lt hx4) hx5
  have hx2 : Real.cos y < Real.cos 0 :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (le_of_lt hx3) hy₀
  have hx6 : x < 1 := by
    have : x = Real.cos y := rfl
    rw [this]
    have : Real.cos 0 = 1 := Real.cos_zero
    rw [<-this]
    exact hx2
  have hx_mem : x ∈ Ioo 0 1 := ⟨hx0, hx6⟩
  have hx_bar : Real.arccos x = y := Real.arccos_cos (le_of_lt hy₀) (le_of_lt hx3)
  have hx_foo : Real.arccos x ∈ Real.arccos '' (Ioo 0 1) := by
    exact ⟨x, hx_mem, rfl⟩
  have hx_baz : y ∈ Real.arccos '' Ioo 0 1 := mem_of_eq_of_mem (id (Eq.symm hx_bar)) hx_foo
  exact hx_baz

lemma arccosOverlap :
  Ioo 0 (Real.pi / 2) =  Real.arccos '' (Ioo 0 1) := by
  exact Subset.antisymm arccosOverlap2 arccosOverlap1

lemma bar : chartNorthComplex.symm '' (Set.Ioo 0 1) = Circle.exp '' (Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : chartNorthComplex.symm = Circle.exp ∘ Real.arccos := rfl
  have h2 : Real.arccos '' (Set.Ioo 0 1) = Ioo 0 (Real.pi / 2) := arccosOverlap.symm
  have h4 : (Circle.exp ∘ Real.arccos) '' (Ioo 0 1) = Circle.exp '' (Real.arccos '' (Ioo 0 1)) :=
    (Set.image_image  Circle.exp Real.arccos (Ioo 0 1)).symm
  have h3 : (Circle.exp ∘ Real.arccos) '' (Ioo 0 1) = Circle.exp '' (Ioo 0 (Real.pi /2)) := by
    rw [<-h2]
    exact h4
  exact h3

lemma sourceNE01 : (chartNorthComplex.symm.trans chartEastComplex).source = (Set.Ioo 0 1) := by
  have h1 : (chartNorthComplex.symm.trans chartEastComplex).source =
    chartNorthComplex.symm.source ∩
    chartNorthComplex.symm ⁻¹' (chartNorthComplex.symm.target ∩ chartEastComplex.source) := by
    exact PartialEquiv.trans_source' chartNorthComplex.symm chartEastComplex
  have h2 : chartNorthComplex.symm.source = Set.Ioo (-1) 1 := rfl
  have h4 : chartEastComplex.source = Circle.exp '' HalfE := rfl
  have h6 : HalfE = Set.Ioo (-Real.pi / 2) (Real.pi / 2) := rfl
  have h7 : chartNorthComplex.symm.target = Circle.exp '' HalfN := rfl
  have h8 : chartNorthComplex.symm.target ∩ chartEastComplex.source =
            Circle.exp '' (Set.Ioo 0 (Real.pi / 2)) := by
    rw [h7, h4, HalfE, HalfN]
    rw [<-foo]
    exact circleOverlap

  have h9 : chartNorthComplex.symm ⁻¹' (chartNorthComplex.symm.target ∩ chartEastComplex.source) =
            chartNorthComplex.symm ⁻¹' (Circle.exp '' (Set.Ioo 0 (Real.pi / 2))) := by
    rw [h8]

  have hc : InjOn (↑chartNorthComplex.symm) chartNorthComplex.symm.source :=
    PartialEquiv.injOn chartNorthComplex.symm

  have hi : Ioo 0 1 ⊆ chartNorthComplex.symm.source := by
    have h0 : Ioo (0 : ℝ) 1 ⊆ Ioo (-1) 1 :=
      (Ioo_subset_Ioo_iff zero_lt_one).mpr ⟨le_of_lt neg_one_lt_zero, Preorder.le_refl 1⟩
    exact h0

  have ha : chartNorthComplex.symm '' (Set.Ioo 0 1) = Circle.exp '' (Set.Ioo 0 (Real.pi / 2)) :=
    bar

  have he : chartNorthComplex.symm.source ∩
            chartNorthComplex.symm ⁻¹' (chartNorthComplex.symm.target ∩ chartEastComplex.source) =
            chartNorthComplex.symm.source ∩
            chartNorthComplex.symm ⁻¹' (Circle.exp '' (Set.Ioo 0 (Real.pi / 2))) := by
    exact congrArg (Inter.inter chartNorthComplex.symm.source) h9

  have hf : chartNorthComplex.symm.source ∩
            chartNorthComplex.symm ⁻¹' (chartNorthComplex.symm.target ∩ chartEastComplex.source) =
            chartNorthComplex.symm.source ∩
            chartNorthComplex.symm ⁻¹' (chartNorthComplex.symm '' (Set.Ioo 0 1)) := by
    rw [ha]
    exact he

  have hj : chartNorthComplex.symm.source ∩
            chartNorthComplex.symm ⁻¹' (chartNorthComplex.symm '' (Set.Ioo 0 1)) =
            chartNorthComplex.symm ⁻¹' (chartNorthComplex.symm '' (Set.Ioo 0 1)) ∩
            chartNorthComplex.symm.source := by
    exact inter_comm chartNorthComplex.symm.source
          (↑chartNorthComplex.symm ⁻¹' (↑chartNorthComplex.symm '' Ioo 0 1))

  have hg : chartNorthComplex.symm.source ∩
            chartNorthComplex.symm ⁻¹' (chartNorthComplex.symm.target ∩ chartEastComplex.source) =
            chartNorthComplex.symm ⁻¹' (chartNorthComplex.symm '' (Set.Ioo 0 1)) ∩
            chartNorthComplex.symm.source := by
    rw [hj] at hf
    exact hf

  have hh : chartNorthComplex.symm ⁻¹' (chartNorthComplex.symm '' (Set.Ioo 0 1)) ∩
            chartNorthComplex.symm.source = Set.Ioo 0 1 :=  InjOn.preimage_image_inter hc hi
  rw [h1, hg]

  exact hh

lemma contDiffOnNE : ContDiffOn ℝ ⊤ (↑(chartNorthComplex.symm.trans chartEastComplex))
                 (chartNorthComplex.symm.trans chartEastComplex).source := by
  rw [sourceNE01]
  exact contOnNE01

example : ContinuousOn (↑(chartNorthComplex.symm.trans chartEastComplex))
                 (chartNorthComplex.symm.trans chartEastComplex).source := by
  exact ContDiffOn.continuousOn contDiffOnNE

noncomputable
def CircleChartedSpace : ChartedSpaceCore ℝ Circle where
  atlas := {chartNorthComplex, chartEastComplex, chartSouthComplex, chartWestComplex}
  chartAt z :=
    let θ := Complex.arg z
    if θ < Real.pi / 2 then chartEastComplex
    else if θ < Real.pi then chartNorthComplex
    else if θ < 3 * Real.pi / 2 then chartWestComplex
    else chartSouthComplex
  mem_chart_source := fun x ↦ by exact sorry
  chart_mem_atlas := sorry
  open_source := sorry
  continuousOn_toFun := by
    intro e e' he he'
    cases he with
      | inl he1 =>
       cases he' with
        | inl he2' =>
          rw [he1, he2']

          have h2 : EqOn (chartNorthComplex.symm.trans chartNorthComplex)
                         id chartNorthComplex.target :=
            fun z hz ↦ by
              simp at *
              exact PartialEquiv.right_inv chartNorthComplex hz

          have h6 : chartNorthComplex.target ∩ chartNorthComplex.symm ⁻¹' chartNorthComplex.source
                    = chartNorthComplex.target := by
            simp
            exact PartialEquiv.target_subset_preimage_source chartNorthComplex

          have h4 : ContinuousOn (↑chartNorthComplex ∘ ↑chartNorthComplex.symm)
           (chartNorthComplex.target ∩ ↑chartNorthComplex.symm ⁻¹' chartNorthComplex.source) := by
            rw [h6]
            exact ContinuousOn.congr continuousOn_id h2

          exact h4

          | inr he3' => cases he3' with
            | inl he4' => rw [he1, he4']
                          have he41' :
    (chartNorthComplex.symm.trans chartEastComplex).source =
    chartNorthComplex.symm.source ∩
    chartNorthComplex.symm ⁻¹' (chartNorthComplex.symm.target ∩ chartEastComplex.source) :=
     PartialEquiv.trans_source' chartNorthComplex.symm chartEastComplex
                          have he42' : chartNorthComplex.symm.target = Circle.exp '' HalfN := rfl
                          have he43' : chartEastComplex.source = Circle.exp '' HalfE := rfl
                          have he44' : chartNorthComplex.symm.target ∩ chartEastComplex.source =
                                       Circle.exp '' (Set.Ioo 0 (Real.pi / 2)) := sorry
                          exact ContDiffOn.continuousOn contDiffOnNE
            | inr he5' => cases he5' with
                          | inl he6' => exact sorry
                          | inr he7' => exact sorry
      | inr he2 => cases he2 with
                    | inl he3 => sorry
                    | inr he4 => cases he4 with
                      | inl he5 => sorry
                      | inr he6 => sorry
