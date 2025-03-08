/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.GDelta.UniformSpace
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Instances.Rat

/-!
# Borel (measurable) space

## Main definitions

* `borel α` : the least `σ`-algebra that contains all open sets;
* `class BorelSpace` : a space with `TopologicalSpace` and `MeasurableSpace` structures
  such that `‹MeasurableSpace α› = borel α`;
* `class OpensMeasurableSpace` : a space with `TopologicalSpace` and `MeasurableSpace`
  structures such that all open sets are measurable; equivalently, `borel α ≤ ‹MeasurableSpace α›`.
* `BorelSpace` instances on `Empty`, `Unit`, `Bool`, `Nat`, `Int`, `Rat`;
* `MeasurableSpace` and `BorelSpace` instances on `ℝ`, `ℝ≥0`, `ℝ≥0∞`.

## Main statements

* `IsOpen.measurableSet`, `IsClosed.measurableSet`: open and closed sets are measurable;
* `Continuous.measurable` : a continuous function is measurable;
* `Continuous.measurable2` : if `f : α → β` and `g : α → γ` are measurable and `op : β × γ → δ`
  is continuous, then `fun x => op (f x, g y)` is measurable;
* `Measurable.add` etc : dot notation for arithmetic operations on `Measurable` predicates,
  and similarly for `dist` and `edist`;
* `AEMeasurable.add` : similar dot notation for almost everywhere measurable functions;
-/


noncomputable section

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal MeasureTheory

universe u v w x y

variable {α β γ γ₂ δ : Type*} {ι : Sort y} {s t u : Set α}

open MeasurableSpace TopologicalSpace

/-- `MeasurableSpace` structure generated by `TopologicalSpace`. -/
def borel (α : Type u) [TopologicalSpace α] : MeasurableSpace α :=
  generateFrom { s : Set α | IsOpen s }

theorem borel_anti : Antitone (@borel α) := fun _ _ h =>
  MeasurableSpace.generateFrom_le fun _ hs => .basic _ (h _ hs)

theorem borel_eq_top_of_discrete [TopologicalSpace α] [DiscreteTopology α] : borel α = ⊤ :=
  top_le_iff.1 fun s _ => GenerateMeasurable.basic s (isOpen_discrete s)

theorem borel_eq_generateFrom_of_subbasis {s : Set (Set α)} [t : TopologicalSpace α]
    [SecondCountableTopology α] (hs : t = .generateFrom s) : borel α = .generateFrom s :=
  le_antisymm
    (generateFrom_le fun u (hu : t.IsOpen u) => by
      rw [hs] at hu
      induction hu with
      | basic u hu => exact GenerateMeasurable.basic u hu
      | univ => exact @MeasurableSet.univ α (generateFrom s)
      | inter s₁ s₂ _ _ hs₁ hs₂ => exact @MeasurableSet.inter α (generateFrom s) _ _ hs₁ hs₂
      | sUnion f hf ih =>
        rcases isOpen_sUnion_countable f (by rwa [hs]) with ⟨v, hv, vf, vu⟩
        rw [← vu]
        exact @MeasurableSet.sUnion α (generateFrom s) _ hv fun x xv => ih _ (vf xv))
    (generateFrom_le fun u hu =>
      GenerateMeasurable.basic _ <| show t.IsOpen u by rw [hs]; exact GenerateOpen.basic _ hu)

theorem TopologicalSpace.IsTopologicalBasis.borel_eq_generateFrom [TopologicalSpace α]
    [SecondCountableTopology α] {s : Set (Set α)} (hs : IsTopologicalBasis s) :
    borel α = .generateFrom s :=
  borel_eq_generateFrom_of_subbasis hs.eq_generateFrom

theorem isPiSystem_isOpen [TopologicalSpace α] : IsPiSystem ({s : Set α | IsOpen s}) :=
  fun _s hs _t ht _ => IsOpen.inter hs ht

lemma isPiSystem_isClosed [TopologicalSpace α] : IsPiSystem ({s : Set α | IsClosed s}) :=
  fun _s hs _t ht _ ↦ IsClosed.inter hs ht

theorem borel_eq_generateFrom_isClosed [TopologicalSpace α] :
    borel α = .generateFrom { s | IsClosed s } :=
  le_antisymm
    (generateFrom_le fun _t ht =>
      @MeasurableSet.of_compl α _ (generateFrom { s | IsClosed s })
        (GenerateMeasurable.basic _ <| isClosed_compl_iff.2 ht))
    (generateFrom_le fun _t ht =>
      @MeasurableSet.of_compl α _ (borel α) (GenerateMeasurable.basic _ <| isOpen_compl_iff.2 ht))

theorem borel_comap {f : α → β} {t : TopologicalSpace β} :
    @borel α (t.induced f) = (@borel β t).comap f :=
  comap_generateFrom.symm

theorem Continuous.borel_measurable [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
    (hf : Continuous f) : @Measurable α β (borel α) (borel β) f :=
  Measurable.of_le_map <|
    generateFrom_le fun s hs => GenerateMeasurable.basic (f ⁻¹' s) (hs.preimage hf)

/-- A space with `MeasurableSpace` and `TopologicalSpace` structures such that
all open sets are measurable. -/
class OpensMeasurableSpace (α : Type*) [TopologicalSpace α] [h : MeasurableSpace α] : Prop where
  /-- Borel-measurable sets are measurable. -/
  borel_le : borel α ≤ h

/-- A space with `MeasurableSpace` and `TopologicalSpace` structures such that
the `σ`-algebra of measurable sets is exactly the `σ`-algebra generated by open sets. -/
class BorelSpace (α : Type*) [TopologicalSpace α] [MeasurableSpace α] : Prop where
  /-- The measurable sets are exactly the Borel-measurable sets. -/
  measurable_eq : ‹MeasurableSpace α› = borel α

namespace Mathlib.Tactic.Borelize

open Lean Elab Term Tactic Meta

/-- The behaviour of `borelize α` depends on the existing assumptions on `α`.

- if `α` is a topological space with instances `[MeasurableSpace α] [BorelSpace α]`, then
  `borelize α` replaces the former instance by `borel α`;
- otherwise, `borelize α` adds instances `borel α : MeasurableSpace α` and `⟨rfl⟩ : BorelSpace α`.

Finally, `borelize α β γ` runs `borelize α; borelize β; borelize γ`.
-/
syntax "borelize" (ppSpace colGt term:max)* : tactic

/-- Add instances `borel e : MeasurableSpace e` and `⟨rfl⟩ : BorelSpace e`. -/
def addBorelInstance (e : Expr) : TacticM Unit := do
  let t ← Lean.Elab.Term.exprToSyntax e
  evalTactic <| ← `(tactic|
    refine_lift
      letI : MeasurableSpace $t := borel $t
      haveI : BorelSpace $t := ⟨rfl⟩
      ?_)

/-- Given a type `e`, an assumption `i : MeasurableSpace e`, and an instance `[BorelSpace e]`,
replace `i` with `borel e`. -/
def borelToRefl (e : Expr) (i : FVarId) : TacticM Unit := do
  let te ← Lean.Elab.Term.exprToSyntax e
  evalTactic <| ← `(tactic|
    have := @BorelSpace.measurable_eq $te _ _ _)
  try
    liftMetaTactic fun m => return [← subst m i]
  catch _ =>
    let et ← synthInstance (← mkAppOptM ``TopologicalSpace #[e])
    throwError m!"\
      `‹TopologicalSpace {e}› := {et}\n\
      depends on\n\
      {Expr.fvar i} : MeasurableSpace {e}`\n\
      so `borelize` isn't available"
  evalTactic <| ← `(tactic|
    refine_lift
      letI : MeasurableSpace $te := borel $te
      ?_)

/-- Given a type `$t`, if there is an assumption `[i : MeasurableSpace $t]`, then try to prove
`[BorelSpace $t]` and replace `i` with `borel $t`. Otherwise, add instances
`borel $t : MeasurableSpace $t` and `⟨rfl⟩ : BorelSpace $t`. -/
def borelize (t : Term) : TacticM Unit := withMainContext <| do
  let u ← mkFreshLevelMVar
  let e ← withoutRecover <| Tactic.elabTermEnsuringType t (mkSort (mkLevelSucc u))
  let i? ← findLocalDeclWithType? (← mkAppOptM ``MeasurableSpace #[e])
  i?.elim (addBorelInstance e) (borelToRefl e)

elab_rules : tactic
  | `(tactic| borelize $[$t:term]*) => t.forM borelize

end Mathlib.Tactic.Borelize

instance (priority := 100) OrderDual.opensMeasurableSpace {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [h : OpensMeasurableSpace α] : OpensMeasurableSpace αᵒᵈ where
  borel_le := h.borel_le

instance (priority := 100) OrderDual.borelSpace {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [h : BorelSpace α] : BorelSpace αᵒᵈ where
  measurable_eq := h.measurable_eq

/-- In a `BorelSpace` all open sets are measurable. -/
instance (priority := 100) BorelSpace.opensMeasurable {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] : OpensMeasurableSpace α :=
  ⟨ge_of_eq <| BorelSpace.measurable_eq⟩

instance Subtype.borelSpace {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [hα : BorelSpace α] (s : Set α) : BorelSpace s :=
  ⟨by borelize α; symm; apply borel_comap⟩

instance Countable.instBorelSpace [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace α] [DiscreteTopology α] : BorelSpace α := by
  have : ∀ s, @MeasurableSet α inferInstance s := fun s ↦ s.to_countable.measurableSet
  have : ∀ s, @MeasurableSet α (borel α) s := fun s ↦ measurableSet_generateFrom (isOpen_discrete s)
  exact ⟨by aesop⟩

instance Subtype.opensMeasurableSpace {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [h : OpensMeasurableSpace α] (s : Set α) : OpensMeasurableSpace s :=
  ⟨by
    rw [borel_comap]
    exact comap_mono h.1⟩

lemma opensMeasurableSpace_iff_forall_measurableSet
    [TopologicalSpace α] [MeasurableSpace α] :
    OpensMeasurableSpace α ↔  (∀ (s : Set α), IsOpen s → MeasurableSet s) := by
  refine ⟨fun h s hs ↦ ?_, fun h ↦ ⟨generateFrom_le h⟩⟩
  exact OpensMeasurableSpace.borel_le _ <| GenerateMeasurable.basic _ hs

instance (priority := 100) BorelSpace.countablyGenerated {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] : CountablyGenerated α := by
  obtain ⟨b, bct, -, hb⟩ := exists_countable_basis α
  refine ⟨⟨b, bct, ?_⟩⟩
  borelize α
  exact hb.borel_eq_generateFrom

section

variable [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β]
  [MeasurableSpace β] [OpensMeasurableSpace β] [TopologicalSpace γ] [MeasurableSpace γ]
  [BorelSpace γ] [TopologicalSpace γ₂] [MeasurableSpace γ₂] [BorelSpace γ₂] [MeasurableSpace δ]

theorem IsOpen.measurableSet (h : IsOpen s) : MeasurableSet s :=
  OpensMeasurableSpace.borel_le _ <| GenerateMeasurable.basic _ h

theorem IsOpen.nullMeasurableSet {μ} (h : IsOpen s) : NullMeasurableSet s μ :=
  h.measurableSet.nullMeasurableSet

open scoped Function in -- required for scoped `on` notation
@[elab_as_elim]
theorem MeasurableSet.induction_on_open {C : ∀ s : Set γ, MeasurableSet s → Prop}
    (isOpen : ∀ U (hU : IsOpen U), C U hU.measurableSet)
    (compl : ∀ t (ht : MeasurableSet t), C t ht → C tᶜ ht.compl)
    (iUnion : ∀ f : ℕ → Set γ, Pairwise (Disjoint on f) → ∀ (hf : ∀ i, MeasurableSet (f i)),
      (∀ i, C (f i) (hf i)) → C (⋃ i, f i) (.iUnion hf)) :
    ∀ t (ht : MeasurableSet t), C t ht := fun t ht ↦
  MeasurableSpace.induction_on_inter BorelSpace.measurable_eq isPiSystem_isOpen
    (isOpen _ isOpen_empty) isOpen compl iUnion t ht

instance (priority := 1000) {s : Set α} [h : HasCountableSeparatingOn α IsOpen s] :
    CountablySeparated s := by
  rw [CountablySeparated.subtype_iff]
  exact .mono (fun _ ↦ IsOpen.measurableSet) Subset.rfl

@[measurability]
theorem measurableSet_interior : MeasurableSet (interior s) :=
  isOpen_interior.measurableSet

theorem IsGδ.measurableSet (h : IsGδ s) : MeasurableSet s := by
  rcases h with ⟨S, hSo, hSc, rfl⟩
  exact MeasurableSet.sInter hSc fun t ht => (hSo t ht).measurableSet

theorem measurableSet_of_continuousAt {β} [EMetricSpace β] (f : α → β) :
    MeasurableSet { x | ContinuousAt f x } :=
  (IsGδ.setOf_continuousAt f).measurableSet

theorem IsClosed.measurableSet (h : IsClosed s) : MeasurableSet s :=
  h.isOpen_compl.measurableSet.of_compl

theorem IsClosed.nullMeasurableSet {μ} (h : IsClosed s) : NullMeasurableSet s μ :=
  h.measurableSet.nullMeasurableSet

theorem IsCompact.measurableSet [T2Space α] (h : IsCompact s) : MeasurableSet s :=
  h.isClosed.measurableSet

theorem IsCompact.nullMeasurableSet [T2Space α] {μ} (h : IsCompact s) : NullMeasurableSet s μ :=
  h.isClosed.nullMeasurableSet

/-- If two points are topologically inseparable,
then they can't be separated by a Borel measurable set. -/
theorem Inseparable.mem_measurableSet_iff {x y : γ} (h : Inseparable x y) {s : Set γ}
    (hs : MeasurableSet s) : x ∈ s ↔ y ∈ s :=
  MeasurableSet.induction_on_open (fun _ ↦ h.mem_open_iff) (fun _ _ ↦ Iff.not)
    (fun _ _ _ h ↦ by simp [h]) s hs

/-- If `K` is a compact set in an R₁ space and `s ⊇ K` is a Borel measurable superset,
then `s` includes the closure of `K` as well. -/
theorem IsCompact.closure_subset_measurableSet [R1Space γ] {K s : Set γ} (hK : IsCompact K)
    (hs : MeasurableSet s) (hKs : K ⊆ s) : closure K ⊆ s := by
  rw [hK.closure_eq_biUnion_inseparable, iUnion₂_subset_iff]
  exact fun x hx y hy ↦ (hy.mem_measurableSet_iff hs).1 (hKs hx)

/-- In an R₁ topological space with Borel measure `μ`,
the measure of the closure of a compact set `K` is equal to the measure of `K`.

See also `MeasureTheory.Measure.OuterRegular.measure_closure_eq_of_isCompact`
for a version that assumes `μ` to be outer regular
but does not assume the `σ`-algebra to be Borel. -/
theorem IsCompact.measure_closure [R1Space γ] {K : Set γ} (hK : IsCompact K) (μ : Measure γ) :
    μ (closure K) = μ K := by
  refine le_antisymm ?_ (measure_mono subset_closure)
  calc
    μ (closure K) ≤ μ (toMeasurable μ K) := measure_mono <|
      hK.closure_subset_measurableSet (measurableSet_toMeasurable ..) (subset_toMeasurable ..)
    _ = μ K := measure_toMeasurable ..

@[measurability]
theorem measurableSet_closure : MeasurableSet (closure s) :=
  isClosed_closure.measurableSet

theorem measurable_of_isOpen {f : δ → γ} (hf : ∀ s, IsOpen s → MeasurableSet (f ⁻¹' s)) :
    Measurable f := by
  rw [‹BorelSpace γ›.measurable_eq]
  exact measurable_generateFrom hf

theorem measurable_of_isClosed {f : δ → γ} (hf : ∀ s, IsClosed s → MeasurableSet (f ⁻¹' s)) :
    Measurable f := by
  apply measurable_of_isOpen; intro s hs
  rw [← MeasurableSet.compl_iff, ← preimage_compl]; apply hf; rw [isClosed_compl_iff]; exact hs

theorem measurable_of_isClosed' {f : δ → γ}
    (hf : ∀ s, IsClosed s → s.Nonempty → s ≠ univ → MeasurableSet (f ⁻¹' s)) : Measurable f := by
  apply measurable_of_isClosed; intro s hs
  rcases eq_empty_or_nonempty s with h1 | h1
  · simp [h1]
  by_cases h2 : s = univ
  · simp [h2]
  exact hf s hs h1 h2

instance nhds_isMeasurablyGenerated (a : α) : (𝓝 a).IsMeasurablyGenerated := by
  rw [nhds, iInf_subtype']
  refine @Filter.iInf_isMeasurablyGenerated α _ _ _ fun i => ?_
  exact i.2.2.measurableSet.principal_isMeasurablyGenerated

/-- If `s` is a measurable set, then `𝓝[s] a` is a measurably generated filter for
each `a`. This cannot be an `instance` because it depends on a non-instance `hs : MeasurableSet s`.
-/
theorem MeasurableSet.nhdsWithin_isMeasurablyGenerated {s : Set α} (hs : MeasurableSet s) (a : α) :
    (𝓝[s] a).IsMeasurablyGenerated :=
  haveI := hs.principal_isMeasurablyGenerated
  Filter.inf_isMeasurablyGenerated _ _

instance (priority := 100) OpensMeasurableSpace.separatesPoints [T0Space α] :
    SeparatesPoints α := by
  rw [separatesPoints_iff]
  intro x y hxy
  apply Inseparable.eq
  rw [inseparable_iff_forall_isOpen]
  exact fun s hs => hxy _ hs.measurableSet

theorem borel_eq_top_of_countable {α : Type*} [TopologicalSpace α] [T0Space α] [Countable α] :
    borel α = ⊤ := by
  refine top_unique fun s _ ↦ ?_
  borelize α
  exact .of_discrete

-- see Note [lower instance priority]
instance (priority := 100) OpensMeasurableSpace.toMeasurableSingletonClass [T1Space α] :
    MeasurableSingletonClass α :=
  ⟨fun _ => isClosed_singleton.measurableSet⟩

instance Pi.opensMeasurableSpace {ι : Type*} {X : ι → Type*} [Countable ι]
    [t' : ∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, SecondCountableTopology (X i)] [∀ i, OpensMeasurableSpace (X i)] :
    OpensMeasurableSpace (∀ i, X i) := by
  constructor
  have : Pi.topologicalSpace = .generateFrom { t | ∃ (s : ∀ a, Set (X a)) (i : Finset ι),
      (∀ a ∈ i, s a ∈ countableBasis (X a)) ∧ t = pi (↑i) s } := by
    simp only [funext fun a => @eq_generateFrom_countableBasis (X a) _ _, pi_generateFrom_eq]
  rw [borel_eq_generateFrom_of_subbasis this]
  apply generateFrom_le
  rintro _ ⟨s, i, hi, rfl⟩
  refine MeasurableSet.pi i.countable_toSet fun a ha => IsOpen.measurableSet ?_
  rw [eq_generateFrom_countableBasis (X a)]
  exact .basic _ (hi a ha)

/-- The typeclass `SecondCountableTopologyEither α β` registers the fact that at least one of
the two spaces has second countable topology. This is the right assumption to ensure that continuous
maps from `α` to `β` are strongly measurable. -/
class SecondCountableTopologyEither (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] :
  Prop where
  /-- The projection out of `SecondCountableTopologyEither` -/
  out : SecondCountableTopology α ∨ SecondCountableTopology β

instance (priority := 100) secondCountableTopologyEither_of_left (α β : Type*) [TopologicalSpace α]
    [TopologicalSpace β] [SecondCountableTopology α] : SecondCountableTopologyEither α β where
  out := Or.inl (by infer_instance)

instance (priority := 100) secondCountableTopologyEither_of_right (α β : Type*)
    [TopologicalSpace α] [TopologicalSpace β] [SecondCountableTopology β] :
    SecondCountableTopologyEither α β where
  out := Or.inr (by infer_instance)

/-- If either `α` or `β` has second-countable topology, then the open sets in `α × β` belong to the
product sigma-algebra. -/
instance Prod.opensMeasurableSpace [h : SecondCountableTopologyEither α β] :
    OpensMeasurableSpace (α × β) := by
  apply opensMeasurableSpace_iff_forall_measurableSet.2 (fun s hs ↦ ?_)
  rcases h.out with hα|hβ
  · let F : Set α → Set β := fun a ↦ {y | ∃ b, IsOpen b ∧ y ∈ b ∧ a ×ˢ b ⊆ s}
    have A : ∀ a, IsOpen (F a) := by
      intro a
      apply isOpen_iff_forall_mem_open.2
      rintro y ⟨b, b_open, yb, hb⟩
      exact ⟨b, fun z zb ↦ ⟨b, b_open, zb, hb⟩, b_open, yb⟩
    have : s = ⋃ a ∈ countableBasis α, a ×ˢ F a := by
      apply Subset.antisymm
      · rintro ⟨y1, y2⟩ hy
        rcases isOpen_prod_iff.1 hs y1 y2 hy with ⟨u, v, u_open, v_open, yu, yv, huv⟩
        obtain ⟨a, ha, ya, au⟩ : ∃ a ∈ countableBasis α, y1 ∈ a ∧ a ⊆ u :=
          IsTopologicalBasis.exists_subset_of_mem_open (isBasis_countableBasis α) yu u_open
        simp only [mem_iUnion, mem_prod, mem_setOf_eq, exists_and_left, exists_prop]
        exact ⟨a, ya, ha, v, v_open, yv, (Set.prod_mono_left au).trans huv⟩
      · rintro ⟨y1, y2⟩ hy
        simp only [mem_iUnion, mem_prod, mem_setOf_eq, exists_and_left, exists_prop] at hy
        rcases hy with ⟨a, ya, -, b, -, yb, hb⟩
        exact hb (mem_prod.2 ⟨ya, yb⟩)
    rw [this]
    apply MeasurableSet.biUnion (countable_countableBasis α) (fun a ha ↦ ?_)
    exact (isOpen_of_mem_countableBasis ha).measurableSet.prod (A a).measurableSet
  · let F : Set β → Set α := fun a ↦ {y | ∃ b, IsOpen b ∧ y ∈ b ∧ b ×ˢ a ⊆ s}
    have A : ∀ a, IsOpen (F a) := by
      intro a
      apply isOpen_iff_forall_mem_open.2
      rintro y ⟨b, b_open, yb, hb⟩
      exact ⟨b, fun z zb ↦ ⟨b, b_open, zb, hb⟩, b_open, yb⟩
    have : s = ⋃ a ∈ countableBasis β, F a ×ˢ a := by
      apply Subset.antisymm
      · rintro ⟨y1, y2⟩ hy
        rcases isOpen_prod_iff.1 hs y1 y2 hy with ⟨u, v, u_open, v_open, yu, yv, huv⟩
        obtain ⟨a, ha, ya, au⟩ : ∃ a ∈ countableBasis β, y2 ∈ a ∧ a ⊆ v :=
          IsTopologicalBasis.exists_subset_of_mem_open (isBasis_countableBasis β) yv v_open
        simp only [mem_iUnion, mem_prod, mem_setOf_eq, exists_and_left, exists_prop]
        exact ⟨a, ⟨u, u_open, yu, (Set.prod_mono_right au).trans huv⟩, ha, ya⟩
      · rintro ⟨y1, y2⟩ hy
        simp only [mem_iUnion, mem_prod, mem_setOf_eq, exists_and_left, exists_prop] at hy
        rcases hy with ⟨a, ⟨b, -, yb, hb⟩, -, ya⟩
        exact hb (mem_prod.2 ⟨yb, ya⟩)
    rw [this]
    apply MeasurableSet.biUnion (countable_countableBasis β) (fun a ha ↦ ?_)
    exact (A a).measurableSet.prod (isOpen_of_mem_countableBasis ha).measurableSet

variable {α' : Type*} [TopologicalSpace α'] [MeasurableSpace α']

theorem interior_ae_eq_of_null_frontier {μ : Measure α'} {s : Set α'} (h : μ (frontier s) = 0) :
    interior s =ᵐ[μ] s :=
  interior_subset.eventuallyLE.antisymm <| subset_closure.eventuallyLE.trans (ae_le_set.2 h)

theorem measure_interior_of_null_frontier {μ : Measure α'} {s : Set α'} (h : μ (frontier s) = 0) :
    μ (interior s) = μ s :=
  measure_congr (interior_ae_eq_of_null_frontier h)

theorem nullMeasurableSet_of_null_frontier {s : Set α} {μ : Measure α} (h : μ (frontier s) = 0) :
    NullMeasurableSet s μ :=
  ⟨interior s, isOpen_interior.measurableSet, (interior_ae_eq_of_null_frontier h).symm⟩

theorem closure_ae_eq_of_null_frontier {μ : Measure α'} {s : Set α'} (h : μ (frontier s) = 0) :
    closure s =ᵐ[μ] s :=
  ((ae_le_set.2 h).trans interior_subset.eventuallyLE).antisymm <| subset_closure.eventuallyLE

theorem measure_closure_of_null_frontier {μ : Measure α'} {s : Set α'} (h : μ (frontier s) = 0) :
    μ (closure s) = μ s :=
  measure_congr (closure_ae_eq_of_null_frontier h)

instance separatesPointsOfOpensMeasurableSpaceOfT0Space [T0Space α] :
    MeasurableSpace.SeparatesPoints α where
  separates x y := by
    contrapose!
    intro x_ne_y
    obtain ⟨U, U_open, mem_U⟩ := exists_isOpen_xor'_mem x_ne_y
    by_cases x_in_U : x ∈ U
    · refine ⟨U, U_open.measurableSet, x_in_U, ?_⟩
      simp_all only [ne_eq, xor_true, not_false_eq_true]
    · refine ⟨Uᶜ, U_open.isClosed_compl.measurableSet, x_in_U, ?_⟩
      simp_all only [ne_eq, xor_false, id_eq, mem_compl_iff, not_true_eq_false, not_false_eq_true]

/-- A continuous function from an `OpensMeasurableSpace` to a `BorelSpace`
is measurable. -/
@[fun_prop]
theorem Continuous.measurable {f : α → γ} (hf : Continuous f) : Measurable f :=
  hf.borel_measurable.mono OpensMeasurableSpace.borel_le (le_of_eq <| BorelSpace.measurable_eq)

/-- A continuous function from an `OpensMeasurableSpace` to a `BorelSpace`
is ae-measurable. -/
@[fun_prop]
theorem Continuous.aemeasurable {f : α → γ} (h : Continuous f) {μ : Measure α} : AEMeasurable f μ :=
  h.measurable.aemeasurable

theorem IsClosedEmbedding.measurable {f : α → γ} (hf : IsClosedEmbedding f) : Measurable f :=
  hf.continuous.measurable

@[deprecated (since := "2024-10-20")]
alias ClosedEmbedding.measurable := IsClosedEmbedding.measurable

/-- If a function is defined piecewise in terms of functions which are continuous on their
respective pieces, then it is measurable. -/
theorem ContinuousOn.measurable_piecewise {f g : α → γ} {s : Set α} [∀ j : α, Decidable (j ∈ s)]
    (hf : ContinuousOn f s) (hg : ContinuousOn g sᶜ) (hs : MeasurableSet s) :
    Measurable (s.piecewise f g) := by
  refine measurable_of_isOpen fun t ht => ?_
  rw [piecewise_preimage, Set.ite]
  apply MeasurableSet.union
  · rcases _root_.continuousOn_iff'.1 hf t ht with ⟨u, u_open, hu⟩
    rw [hu]
    exact u_open.measurableSet.inter hs
  · rcases _root_.continuousOn_iff'.1 hg t ht with ⟨u, u_open, hu⟩
    rw [diff_eq_compl_inter, inter_comm, hu]
    exact u_open.measurableSet.inter hs.compl

@[to_additive]
instance (priority := 100) ContinuousMul.measurableMul [Mul γ] [ContinuousMul γ] :
    MeasurableMul γ where
  measurable_const_mul _ := (continuous_const.mul continuous_id).measurable
  measurable_mul_const _ := (continuous_id.mul continuous_const).measurable

instance (priority := 100) ContinuousSub.measurableSub [Sub γ] [ContinuousSub γ] :
    MeasurableSub γ where
  measurable_const_sub _ := (continuous_const.sub continuous_id).measurable
  measurable_sub_const _ := (continuous_id.sub continuous_const).measurable

@[to_additive]
instance (priority := 100) ContinuousInv.measurableInv [Inv γ] [ContinuousInv γ] :
    MeasurableInv γ := ⟨continuous_inv.measurable⟩

@[to_additive]
instance (priority := 100) ContinuousSMul.measurableSMul {M α} [TopologicalSpace M]
    [TopologicalSpace α] [MeasurableSpace M] [MeasurableSpace α] [OpensMeasurableSpace M]
    [BorelSpace α] [SMul M α] [ContinuousSMul M α] : MeasurableSMul M α :=
  ⟨fun _ => (continuous_const_smul _).measurable, fun _ =>
    (continuous_id.smul continuous_const).measurable⟩

section Homeomorph

@[measurability]
protected theorem Homeomorph.measurable (h : α ≃ₜ γ) : Measurable h :=
  h.continuous.measurable

/-- A homeomorphism between two Borel spaces is a measurable equivalence. -/
def Homeomorph.toMeasurableEquiv (h : γ ≃ₜ γ₂) : γ ≃ᵐ γ₂ where
  measurable_toFun := h.measurable
  measurable_invFun := h.symm.measurable
  toEquiv := h.toEquiv

lemma Homeomorph.measurableEmbedding (h : γ ≃ₜ γ₂) : MeasurableEmbedding h :=
  h.toMeasurableEquiv.measurableEmbedding

@[simp]
theorem Homeomorph.toMeasurableEquiv_coe (h : γ ≃ₜ γ₂) : (h.toMeasurableEquiv : γ → γ₂) = h :=
  rfl

@[simp]
theorem Homeomorph.toMeasurableEquiv_symm_coe (h : γ ≃ₜ γ₂) :
    (h.toMeasurableEquiv.symm : γ₂ → γ) = h.symm :=
  rfl

end Homeomorph

@[measurability]
theorem ContinuousMap.measurable (f : C(α, γ)) : Measurable f :=
  f.continuous.measurable

@[fun_prop]
theorem measurable_of_continuousOn_compl_singleton [T1Space α] {f : α → γ} (a : α)
    (hf : ContinuousOn f {a}ᶜ) : Measurable f :=
  measurable_of_measurable_on_compl_singleton a
    (continuousOn_iff_continuous_restrict.1 hf).measurable

theorem Continuous.measurable2 [SecondCountableTopologyEither α β] {f : δ → α}
    {g : δ → β} {c : α → β → γ} (h : Continuous fun p : α × β => c p.1 p.2) (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => c (f a) (g a) :=
  h.measurable.comp (hf.prodMk hg)

theorem Continuous.aemeasurable2 [SecondCountableTopologyEither α β]
    {f : δ → α} {g : δ → β} {c : α → β → γ} {μ : Measure δ}
    (h : Continuous fun p : α × β => c p.1 p.2) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => c (f a) (g a)) μ :=
  h.measurable.comp_aemeasurable (hf.prodMk hg)

instance (priority := 100) HasContinuousInv₀.measurableInv [GroupWithZero γ] [T1Space γ]
    [HasContinuousInv₀ γ] : MeasurableInv γ :=
  ⟨measurable_of_continuousOn_compl_singleton 0 continuousOn_inv₀⟩

@[to_additive]
instance (priority := 100) ContinuousMul.measurableMul₂ [SecondCountableTopology γ] [Mul γ]
    [ContinuousMul γ] : MeasurableMul₂ γ :=
  ⟨continuous_mul.measurable⟩

instance (priority := 100) ContinuousSub.measurableSub₂ [SecondCountableTopology γ] [Sub γ]
    [ContinuousSub γ] : MeasurableSub₂ γ :=
  ⟨continuous_sub.measurable⟩

instance (priority := 100) ContinuousSMul.measurableSMul₂ {M α} [TopologicalSpace M]
    [MeasurableSpace M] [OpensMeasurableSpace M] [TopologicalSpace α]
    [SecondCountableTopologyEither M α] [MeasurableSpace α] [BorelSpace α] [SMul M α]
    [ContinuousSMul M α] : MeasurableSMul₂ M α :=
  ⟨continuous_smul.measurable⟩

end

section BorelSpace

variable [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [TopologicalSpace β]
  [MeasurableSpace β] [BorelSpace β] [TopologicalSpace γ] [MeasurableSpace γ] [BorelSpace γ]
  [MeasurableSpace δ]

theorem pi_le_borel_pi {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)] :
      MeasurableSpace.pi ≤ borel (∀ i, X i) := by
  have : ‹∀ i, MeasurableSpace (X i)› = fun i => borel (X i) :=
    funext fun i => BorelSpace.measurable_eq
  rw [this]
  exact iSup_le fun i => comap_le_iff_le_map.2 <| (continuous_apply i).borel_measurable

theorem prod_le_borel_prod : Prod.instMeasurableSpace ≤ borel (α × β) := by
  rw [‹BorelSpace α›.measurable_eq, ‹BorelSpace β›.measurable_eq]
  refine sup_le ?_ ?_
  · exact comap_le_iff_le_map.mpr continuous_fst.borel_measurable
  · exact comap_le_iff_le_map.mpr continuous_snd.borel_measurable

instance Pi.borelSpace {ι : Type*} {X : ι → Type*} [Countable ι] [∀ i, TopologicalSpace (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, SecondCountableTopology (X i)] [∀ i, BorelSpace (X i)] :
    BorelSpace (∀ i, X i) :=
  ⟨le_antisymm pi_le_borel_pi OpensMeasurableSpace.borel_le⟩

instance Prod.borelSpace [SecondCountableTopologyEither α β] :
    BorelSpace (α × β) :=
  ⟨le_antisymm prod_le_borel_prod OpensMeasurableSpace.borel_le⟩

/-- Given a measurable embedding to a Borel space which is also a topological embedding, then the
source space is also a Borel space. -/
lemma MeasurableEmbedding.borelSpace {α β : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [hβ : BorelSpace β] {e : α → β}
    (h'e : MeasurableEmbedding e) (h''e : IsInducing e) :
    BorelSpace α := by
  constructor
  have : MeasurableSpace.comap e (borel β) = ‹_› := by simpa [hβ.measurable_eq] using h'e.comap_eq
  rw [← this, ← borel_comap, h''e.eq_induced]

instance _root_.ULift.instBorelSpace : BorelSpace (ULift α) :=
  MeasurableEquiv.ulift.measurableEmbedding.borelSpace Homeomorph.ulift.isInducing

instance DiscreteMeasurableSpace.toBorelSpace {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] : BorelSpace α := by
  constructor; ext; simp [MeasurableSpace.measurableSet_generateFrom, MeasurableSet.of_discrete]

protected theorem Topology.IsEmbedding.measurableEmbedding {f : α → β} (h₁ : IsEmbedding f)
    (h₂ : MeasurableSet (range f)) : MeasurableEmbedding f :=
  show MeasurableEmbedding
      (((↑) : range f → β) ∘ (Homeomorph.ofIsEmbedding f h₁).toMeasurableEquiv) from
    (MeasurableEmbedding.subtype_coe h₂).comp (MeasurableEquiv.measurableEmbedding _)

@[deprecated (since := "2024-10-26")]
alias Embedding.measurableEmbedding := IsEmbedding.measurableEmbedding

protected theorem Topology.IsClosedEmbedding.measurableEmbedding {f : α → β}
    (h : IsClosedEmbedding f) : MeasurableEmbedding f :=
  h.isEmbedding.measurableEmbedding h.isClosed_range.measurableSet

@[deprecated (since := "2024-10-20")]
alias ClosedEmbedding.measurableEmbedding := IsClosedEmbedding.measurableEmbedding

protected theorem Topology.IsOpenEmbedding.measurableEmbedding {f : α → β} (h : IsOpenEmbedding f) :
    MeasurableEmbedding f :=
  h.isEmbedding.measurableEmbedding h.isOpen_range.measurableSet

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding.measurableEmbedding := IsOpenEmbedding.measurableEmbedding

instance Empty.borelSpace : BorelSpace Empty :=
  ⟨borel_eq_top_of_discrete.symm⟩

instance Unit.borelSpace : BorelSpace Unit :=
  ⟨borel_eq_top_of_discrete.symm⟩

instance Bool.borelSpace : BorelSpace Bool :=
  ⟨borel_eq_top_of_discrete.symm⟩

instance Nat.borelSpace : BorelSpace ℕ :=
  ⟨borel_eq_top_of_discrete.symm⟩

instance Int.borelSpace : BorelSpace ℤ :=
  ⟨borel_eq_top_of_discrete.symm⟩

instance Rat.borelSpace : BorelSpace ℚ :=
  ⟨borel_eq_top_of_countable.symm⟩

/- Instances on `Real` and `Complex` are special cases of `RCLike` but without these instances,
Lean fails to prove `BorelSpace (ι → ℝ)`, so we leave them here. -/
instance Real.measurableSpace : MeasurableSpace ℝ :=
  borel ℝ

instance Real.borelSpace : BorelSpace ℝ :=
  ⟨rfl⟩

instance NNReal.measurableSpace : MeasurableSpace ℝ≥0 :=
  Subtype.instMeasurableSpace

instance NNReal.borelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace _

instance ENNReal.measurableSpace : MeasurableSpace ℝ≥0∞ :=
  borel ℝ≥0∞

instance ENNReal.borelSpace : BorelSpace ℝ≥0∞ :=
  ⟨rfl⟩

instance EReal.measurableSpace : MeasurableSpace EReal :=
  borel EReal

instance EReal.borelSpace : BorelSpace EReal :=
  ⟨rfl⟩

end BorelSpace
