import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.LinearAlgebra.Dual
import Mathlib.MeasureTheory.Integral.Periodic
import Mathlib.Analysis.Calculus.ParametricIntegral
import SphereEversion.ToMathlib.Topology.Periodic
import SphereEversion.ToMathlib.MeasureTheory.BorelSpace
import SphereEversion.Loops.Basic
import SphereEversion.Local.DualPair

/-! # Theillière's corrugation operation

This files introduces the fundamental calculus tool of convex integration. The version of convex
integration that we formalize is Theillière's corrugation-based convex integration.
It improves a map `f : E → F` by adding to it some corrugation map
`λ x, (1/N) • ∫ t in 0..(N*π x), (γ x t - (γ x).average)` where `γ` is a family of loops in
`F` parametrized by `E` and `N` is some (very large) real number.

Under the assumption that `∀ x, (γ x).average = D f x p.v` for some dual pair `p`, this improved
map will have a derivative which is almost a value of `γ x` in direction `p.v` and almost the
derivative of `f` in direction `ker p.π`. More precisely, its derivative will be almost
`p.update (D f x) (γ x (N*p.π x))`. In addition the improved map will be very close to `f`
in C⁰ topology. All those "almost" and "very close" refer to the asymptotic behavior when `N`
is very large.

The main definition is `corrugation`. The main results are:
* `fderiv_corrugated_map` computing the difference between `D (f + corrugation p.π N γ) x` and
    `p.update (D f x) (γ x (N*p.π x)) + corrugation.remainder p.π N γ x`
* `remainder_c0_small_on` saying this difference is very small
* `corrugation.c0_small_on` saying that corrugations are C⁰-small

-/


noncomputable section

open Set Function FiniteDimensional Asymptotics Filter TopologicalSpace Int MeasureTheory
  ContinuousLinearMap

open scoped Topology unitInterval

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type _} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] {G : Type _} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H : Type _} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H] {π : E →L[ℝ] ℝ}
  (N : ℝ) (γ : E → Loop F)

open scoped Borelize

/-- Theillière's corrugations. -/
def corrugation (π : E →L[ℝ] ℝ) (N : ℝ) (γ : E → Loop F) : E → F := fun x =>
  (1 / N) • ∫ t in 0 ..N * π x, γ x t - (γ x).average

local notation "𝒯" => corrugation π

/-- The integral appearing in corrugations is periodic. -/
theorem per_corrugation (γ : Loop F) (hγ : ∀ s t, IntervalIntegrable γ volume s t) :
    OnePeriodic fun s => ∫ t in 0 ..s, γ t - γ.average :=
  by
  have int_avg : ∀ s t, IntervalIntegrable (fun u : ℝ => γ.average) volume s t := fun s t =>
    intervalIntegrable_const
  intro s
  have int₁ : IntervalIntegrable (fun t => γ t - γ.average) volume 0 s := (hγ _ _).sub (int_avg _ _)
  have int₂ : IntervalIntegrable (fun t => γ t - γ.average) volume s (s + 1) :=
    (hγ _ _).sub (int_avg _ _)
  have int₃ : IntervalIntegrable γ volume s (s + 1) := hγ _ _
  have int₄ : IntervalIntegrable (fun t => γ.average) volume s (s + 1) := int_avg _ _
  dsimp only
  /- Rmk: Lean doesn't want to rewrite using `interval_integral.integral_sub` without being
      given the integrability assumptions :-( -/
  rw [← intervalIntegral.integral_add_adjacent_intervals int₁ int₂,
    intervalIntegral.integral_sub int₃ int₄, γ.periodic.interval_integral_add_eq s 0, zero_add,
    Loop.average]
  simp only [add_zero, add_tsub_cancel_left, intervalIntegral.integral_const, one_smul, sub_self]

@[simp]
theorem corrugation_const {x : E} (h : (γ x).IsConst) : 𝒯 N γ x = 0 :=
  by
  unfold corrugation
  rw [Loop.isConst_iff_const_avg] at h
  rw [h]
  simp only [add_zero, intervalIntegral.integral_const, Loop.const_apply, Loop.average_const,
    smul_zero, sub_self]

variable (γ π N)

theorem corrugation.support : support (𝒯 N γ) ⊆ Loop.support γ :=
  by
  intro x x_in
  apply subset_closure
  intro h
  apply x_in
  simp [h]

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » loop.support[loop.support] γ) -/
theorem corrugation_eq_zero (x) (_ : x ∉ Loop.support γ) : corrugation π N γ x = 0 :=
  nmem_support.mp fun hx => H (corrugation.support N γ hx)

theorem corrugation.c0_small_on [FirstCountableTopology E] [LocallyCompactSpace E]
    {γ : ℝ → E → Loop F} {K : Set E} (hK : IsCompact K) (h_le : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x)
    (h_ge : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x) (hγ_cont : Continuous ↿γ) {ε : ℝ} (ε_pos : 0 < ε) :
    ∀ᶠ N in atTop, ∀ x ∈ K, ∀ (t), ‖𝒯 N (γ t) x‖ < ε :=
  by
  have cont' : Continuous ↿fun (q : ℝ × E) t => ∫ t in 0 ..t, (γ q.1 q.2) t - (γ q.1 q.2).average :=
    by
    refine' continuous_parametric_intervalIntegral_of_continuous _ continuous_snd
    refine' (hγ_cont.comp₃ continuous_fst.fst.fst continuous_fst.fst.snd continuous_snd).sub _
    refine' Loop.continuous_average _
    exact hγ_cont.comp₃ continuous_fst.fst.fst.fst continuous_fst.fst.fst.snd continuous_snd
  rcases cont'.bounded_on_compact_of_one_periodic _ ((is_compact_Icc : IsCompact I).prod hK) with
    ⟨C, hC⟩
  · apply (const_mul_one_div_lt ε_pos C).mono
    intro N hN x hx t
    rw [corrugation, norm_smul, mul_comm]
    apply (mul_le_mul_of_nonneg_right _ (norm_nonneg <| 1 / N)).trans_lt hN
    cases' le_or_lt t 0 with ht ht
    · rw [h_le x t ht]
      apply hC (0, x)
      simp [hx]
    · cases' le_or_lt 1 t with ht' ht'
      · rw [h_ge x t ht']
        apply hC (1, x)
        simp [hx]
      · exact hC (t, x) (mk_mem_prod ⟨ht.le, ht'.le⟩ hx) _
  · rintro ⟨t, x⟩
    apply per_corrugation
    intro a b
    exact (hγ_cont.comp₃ continuous_const continuous_const continuous_id).IntervalIntegrable _ _

variable {γ}

theorem corrugation.contDiff' {n : ℕ∞} {γ : G → E → Loop F} (hγ_diff : 𝒞 n ↿γ) {x : H → E}
    (hx : 𝒞 n x) {g : H → G} (hg : 𝒞 n g) : 𝒞 n fun h => 𝒯 N (γ <| g h) <| x h :=
  by
  apply ContDiff.const_smul
  apply contDiff_parametric_primitive_of_contDiff
  · apply ContDiff.sub
    · exact hγ_diff.comp₃ hg.fst' hx.fst' contDiff_snd
    · apply contDiff_average
      exact hγ_diff.comp₃ hg.fst'.fst' hx.fst'.fst' contDiff_snd
  · apply contDiff_const.mul (π.contDiff.comp hx)

theorem corrugation.contDiff [FiniteDimensional ℝ E] {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) : 𝒞 n (𝒯 N γ) :=
  (contDiff_parametric_primitive_of_contDiff (contDiff_sub_average hγ_diff)
        (π.ContDiff.const_smul N) 0).const_smul
    _

notation "∂₁" => partialFDerivFst ℝ

/-- The remainder appearing when differentiating a corrugation.
-/
def corrugation.remainder (π : E → ℝ) (N : ℝ) (γ : E → Loop F) : E → E →L[ℝ] F := fun x =>
  (1 / N) • ∫ t in 0 ..N * π x, ∂₁ (fun x t => (γ x).normalize t) x t

local notation "R" => corrugation.remainder π

variable [FiniteDimensional ℝ E]

theorem remainder_eq (N : ℝ) {γ : E → Loop F} (h : 𝒞 1 ↿γ) :
    R N γ = fun x => (1 / N) • ∫ t in 0 ..N * π x, (Loop.diff γ x).normalize t := by
  simp_rw [Loop.diff_normalize h]; rfl

-- The next lemma is a restatement of the above to emphasize that remainder is a corrugation
-- unused
theorem remainder_eq_corrugation (N : ℝ) {γ : E → Loop F} (h : 𝒞 1 ↿γ) :
    R N γ = 𝒯 N fun x => Loop.diff γ x :=
  remainder_eq _ _ h

@[simp]
theorem remainder_eq_zero (N : ℝ) {γ : E → Loop F} (h : 𝒞 1 ↿γ) {x : E} (hx : x ∉ Loop.support γ) :
    R N γ x = 0 :=
  by
  have hx' : x ∉ Loop.support (Loop.diff γ) := fun h => hx <| Loop.support_diff h
  simp [remainder_eq π N h, Loop.normalize_of_isConst (Loop.isConst_of_not_mem_support hx')]

theorem corrugation.fderiv_eq {N : ℝ} (hN : N ≠ 0) (hγ_diff : 𝒞 1 ↿γ) :
    D (𝒯 N γ) = fun x : E => ((γ x (N * π x) - (γ x).average) ⬝ π) + R N γ x :=
  by
  ext1 x₀
  have hπ_diff := π.contDiff
  have diff := contDiff_sub_average hγ_diff
  have key := (hasFDerivAt_parametric_primitive_of_contDiff' diff (hπ_diff.const_smul N) x₀ 0).2
  erw [fderiv_const_smul key.differentiable_at, key.fderiv, smul_add, add_comm]
  congr 1
  rw [fderiv_const_smul (hπ_diff.differentiable le_rfl).differentiableAt N, π.fderiv]
  simp only [smul_smul, inv_mul_cancel hN, one_div, Algebra.id.smul_eq_mul, one_smul,
    ContinuousLinearMap.comp_smul]

theorem corrugation.fderiv_apply (hN : N ≠ 0) (hγ_diff : 𝒞 1 ↿γ) (x v : E) :
    D (𝒯 N γ) x v = π v • (γ x (N * π x) - (γ x).average) + R N γ x v := by
  simp only [corrugation.fderiv_eq hN hγ_diff, to_span_singleton_apply, add_apply, coe_comp',
    comp_app]

theorem fderiv_corrugated_map (hN : N ≠ 0) (hγ_diff : 𝒞 1 ↿γ) {f : E → F} (hf : 𝒞 1 f)
    (p : DualPair E) {x} (hfγ : (γ x).average = D f x p.V) :
    D (f + corrugation p.π N γ) x =
      p.update (D f x) (γ x (N * p.π x)) + corrugation.remainder p.π N γ x :=
  by
  ext v
  erw [fderiv_add (hf.differentiable le_rfl).differentiableAt
      ((corrugation.contDiff N hγ_diff).differentiable le_rfl).differentiableAt]
  simp_rw [ContinuousLinearMap.add_apply, corrugation.fderiv_apply N hN hγ_diff, hfγ,
    DualPair.update, ContinuousLinearMap.add_apply, p.π.comp_to_span_singleton_apply, add_assoc]

theorem Remainder.smooth {γ : G → E → Loop F} (hγ_diff : 𝒞 ∞ ↿γ) {x : H → E} (hx : 𝒞 ∞ x)
    {g : H → G} (hg : 𝒞 ∞ g) : 𝒞 ∞ fun h => R N (γ <| g h) <| x h :=
  by
  apply ContDiff.const_smul
  apply contDiff_parametric_primitive_of_contDiff
  · let ψ : E → H × ℝ → F := fun x q => (γ (g q.1) x).normalize q.2
    change 𝒞 ⊤ fun q : H × ℝ => ∂₁ ψ (x q.1) (q.1, q.2)
    refine' (ContDiff.contDiff_top_partial_fst _).comp₂ hx.fst' (contDiff_fst.prod contDiff_snd)
    dsimp [ψ, Loop.normalize]
    apply ContDiff.sub
    apply hγ_diff.comp₃ hg.fst'.snd' contDiff_fst contDiff_snd.snd
    apply contDiff_average
    exact hγ_diff.comp₃ hg.fst'.snd'.fst' contDiff_fst.fst' contDiff_snd
  · exact contDiff_const.mul (π.contDiff.comp hx)

theorem remainder_c0_small_on {K : Set E} (hK : IsCompact K) (hγ_diff : 𝒞 1 ↿γ) {ε : ℝ}
    (ε_pos : 0 < ε) : ∀ᶠ N in atTop, ∀ x ∈ K, ‖R N γ x‖ < ε :=
  by
  have : ∀ N : ℝ, R N γ = 𝒯 N (Loop.diff γ) := by
    intro N
    exact remainder_eq π N hγ_diff
  simp_rw [fun N => remainder_eq π N hγ_diff]
  let g : ℝ → E → Loop (E →L[ℝ] F) := fun t => Loop.diff γ
  have g_le : ∀ (x) (t : ℝ), t ≤ 0 → g t x = g 0 x := fun _ _ _ => rfl
  have g_ge : ∀ (x) (t : ℝ), t ≥ 1 → g t x = g 1 x := fun _ _ _ => rfl
  have g_cont : Continuous ↿g := (Loop.continuous_diff hγ_diff).snd'
  apply (corrugation.c0_small_on hK g_le g_ge g_cont ε_pos).mono
  intro N H x x_in
  exact H x x_in 0

