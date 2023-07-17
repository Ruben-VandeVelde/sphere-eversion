import Mathlib.Analysis.Calculus.BumpFunctionInner
import Mathlib.MeasureTheory.Integral.Periodic
import SphereEversion.Loops.Surrounding
import SphereEversion.Loops.DeltaMollifier
import SphereEversion.ToMathlib.ExistsOfConvex
import SphereEversion.ToMathlib.Analysis.ContDiff

/-!
# The reparametrization lemma

This file contains a proof of Gromov's parametric reparametrization lemma. It concerns the behaviour
of the average value of a loop `γ : S¹ → F` when the loop is reparametrized by precomposing with a
diffeomorphism `S¹ → S¹`.

Given a loop `γ : S¹ → F` for some real vector space `F`, one may integrate to obtain its average
`∫ x in 0..1, (γ x)` in `F`. Although this average depends on the loop's parametrization, it
satisfies a contraint that depends only on the image of the loop: the average is contained in the
convex hull of the image of `γ`. The non-parametric version of the reparametrization lemma says that
conversely, given any point `g` in the interior of the convex hull of the image of `γ`, one may find
a reparametrization of `γ` whose average is `g`.

The reparametrization lemma thus allows one to reduce the problem of constructing a loop whose
average is a given point, to the problem of constructing a loop subject to a condition that depends
only on its image.

In fact the reparametrization lemma holds parametrically. Given a smooth family of loops:
`γ : E × S¹ → F`, `(x, t) ↦ γₓ t`, together with a smooth function `g : E → F`, such that `g x` is
contained in the interior of the convex hull of the image of `γₓ` for all `x`, there exists a smooth
family of diffeomorphism `φ : E × S¹ → S¹`, `(x, t) ↦ φₓ t` such that the average of `γₓ ∘ φₓ` is
`g x` for all `x`.

The idea of the proof is simple: since `g x` is contained in the interior of the convex hull of
the image of `γₓ` one may find `t₀, t₁, ..., tₙ` and barycentric coordinates `w₀, w₁, ..., wₙ` such
that `g x = ∑ᵢ wᵢ • γₓ(tᵢ)`. If there were no smoothness requirement on `φₓ` one could define
it to be a step function which spends time `wᵢ` at each `tᵢ`. However because there is a smoothness
condition, one rounds off the corners of the would-be step function by using a "delta mollifier"
(an approximation to a Dirac delta function).

The above construction works locally in the neighbourhood of any `x` in `E` and one uses a partition
of unity to globalise all the local solutions into the required family: `φ : E × S¹ → S¹`.

The key ingredients are theories of calculus, convex hulls, barycentric coordinates,
existence of delta mollifiers, partitions of unity, and the inverse function theorem.
-/


noncomputable section

open Set Function MeasureTheory intervalIntegral Filter

open scoped Topology unitInterval Manifold BigOperators

variable {E F : Type _}

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

variable [MeasurableSpace F] [BorelSpace F]

local notation "ι" => Fin (FiniteDimensional.finrank ℝ F + 1)

section MetricSpace

variable [MetricSpace E] [LocallyCompactSpace E]

theorem Loop.tendsto_mollify_apply (γ : E → Loop F) (h : Continuous ↿γ) (x : E) (t : ℝ) :
    Tendsto (fun z : E × ℕ => (γ z.1).mollify z.2 t) ((𝓝 x).Prod atTop) (𝓝 (γ x t)) :=
  by
  have hγ : ∀ x, Continuous (γ x) := fun x => h.comp <| Continuous.Prod.mk _
  have h2γ : ∀ x, Continuous fun z => γ z x := fun x => h.comp <| Continuous.Prod.mk_left _
  simp_rw [Loop.mollify_eq_convolution _ (hγ _)]
  rw [← add_zero (γ x t)]
  refine' tendsto.add _ _
  · rw [← one_smul ℝ (γ x t)]
    refine' ((tendsto_coe_nat_div_add_atTop 1).comp tendsto_snd).smul _
    refine' ContDiffBump.convolution_tendsto_right _ _ _ tendsto_const_nhds
    · simp_rw [bump]; norm_cast
      exact
        ((tendsto_add_at_top_iff_nat 2).2 (tendsto_const_div_atTop_nhds_0_nat 1)).comp tendsto_snd
    · exact eventually_of_forall fun x => (hγ _).AEStronglyMeasurable
    · have := h.tendsto (x, t)
      rw [nhds_prod_eq] at this 
      exact this.comp ((tendsto_fst.comp tendsto_fst).prod_mk tendsto_snd)
  · rw [← zero_smul ℝ (_ : F)]
    have : Continuous fun z => intervalIntegral (γ z) 0 1 volume :=
      continuous_parametric_intervalIntegral_of_continuous (by apply h) continuous_const
    exact
      (tendsto_one_div_add_at_top_nhds_0_nat.comp tendsto_snd).smul
        ((this.tendsto x).comp tendsto_fst)

end MetricSpace

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Given a smooth function `g : E → F` between normed vector spaces, a smooth surrounding family
is a smooth family of loops `E → loop F`, `x ↦ γₓ` such that `γₓ` surrounds `g x` for all `x`. -/
@[nolint has_nonempty_instance]
structure SmoothSurroundingFamily (g : E → F) where
  smooth_surrounded : 𝒞 ∞ g
  toFun : E → Loop F
  smooth : 𝒞 ∞ ↿to_fun
  Surrounds : ∀ x, (to_fun x).Surrounds <| g x

namespace SmoothSurroundingFamily

variable {g : E → F} (γ : SmoothSurroundingFamily g) (x y : E)

instance : CoeFun (SmoothSurroundingFamily g) fun _ => E → Loop F :=
  ⟨toFun⟩

protected theorem continuous : Continuous (γ x) :=
  by
  apply continuous_uncurry_left x
  exact γ.smooth.continuous

/-- Given `γ : smooth_surrounding_family g` and `x : E`, `γ.surrounding_parameters_at x` are the
`tᵢ : ℝ`, for `i = 0, 1, ..., dim F` such that `γ x tᵢ` surround `g x`. -/
def surroundingParametersAt : ι → ℝ :=
  Classical.choose (γ.Surrounds x)

/-- Given `γ : smooth_surrounding_family g` and `x : E`, `γ.surrounding_points_at x` are the
points `γ x tᵢ` surrounding `g x` for parameters `tᵢ : ℝ`, `i = 0, 1, ..., dim F` (defined
by `γ.surrounding_parameters_at x`). -/
def surroundingPointsAt : ι → F :=
  γ x ∘ γ.surroundingParametersAt x

/-- Given `γ : smooth_surrounding_family g` and `x : E`, `γ.surrounding_weights_at x` are the
barycentric coordinates of `g x` wrt to the points `γ x tᵢ`, for parameters `tᵢ : ℝ`,
`i = 0, 1, ..., dim F` (defined by `γ.surrounding_parameters_at x`). -/
def surroundingWeightsAt : ι → ℝ :=
  Classical.choose (Classical.choose_spec (γ.Surrounds x))

theorem surroundPtsPointsWeightsAt :
    SurroundingPts (g x) (γ.surroundingPointsAt x) (γ.surroundingWeightsAt x) :=
  Classical.choose_spec _

/-- Note that we are mollifying the loop `γ y` at the surrounding parameters for `γ x`. -/
def approxSurroundingPointsAt (n : ℕ) (i : ι) : F :=
  (γ y).mollify n (γ.surroundingParametersAt x i)

theorem approxSurroundingPointsAt_smooth (n : ℕ) : 𝒞 ∞ fun y => γ.approxSurroundingPointsAt x y n :=
  by
  refine' cont_diff_pi.mpr fun i => _
  suffices 𝒞 ∞ fun y => ∫ s in 0 ..1, deltaMollifier n (γ.surrounding_parameters_at x i) s • γ y s
    by simpa [approx_surrounding_points_at, Loop.mollify]
  refine' contDiff_parametric_integral_of_contDiff (ContDiff.smul _ γ.smooth) 0 1
  exact delta_mollifier_smooth.snd'

/-- The key property from which it should be easy to construct `local_centering_density`,
`local_centering_density_nhd` etc below. -/
theorem eventually_exists_surroundingPts_approxSurroundingPointsAt :
    ∀ᶠ z : E × ℕ in (𝓝 x).Prod atTop,
      ∃ w, SurroundingPts (g z.1) (γ.approxSurroundingPointsAt x z.1 z.2) w :=
  by
  let a : ι → E × ℕ → F := fun i z => γ.approx_surrounding_points_at x z.1 z.2 i
  suffices ∀ i, tendsto (a i) ((𝓝 x).Prod at_top) (𝓝 (γ.surrounding_points_at x i))
    by
    have hg : tendsto (fun z : E × ℕ => g z.fst) ((𝓝 x).Prod at_top) (𝓝 (g x)) :=
      tendsto.comp γ.smooth_surrounded.continuous.continuous_at tendsto_fst
    exact
      eventually_surroundingPts_of_tendsto_of_tendsto' ⟨_, γ.surround_pts_points_weights_at x⟩ this
        hg
  intro i
  let t := γ.surrounding_parameters_at x i
  change tendsto (fun z : E × ℕ => (γ z.1).mollify z.2 t) ((𝓝 x).Prod at_top) (𝓝 (γ x t))
  exact Loop.tendsto_mollify_apply γ γ.smooth.continuous x t

/-- This is an auxiliary definition to help construct `centering_density` below.

Given `x : E`, it represents a smooth probability distribution on the circle with the property that:
`∫ s in 0..1, γ.local_centering_density x y s • γ y s = g y`
for all `y` in a neighbourhood of `x` (see `local_centering_density_average` below). -/
def localCenteringDensity [DecidablePred (· ∈ affineBases ι ℝ F)] : E → ℝ → ℝ := fun y =>
  by
  choose n hn₁ hn₂ using
    filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surrounding_pts_approx_surrounding_points_at x)
  choose u hu v hv huv using mem_prod_iff.mp hn₁
  choose m hmv using mem_at_top_sets.mp hv
  exact
    ∑ i,
      evalBarycentricCoords ι ℝ F (g y) (γ.approx_surrounding_points_at x y m) i •
        deltaMollifier m (γ.surrounding_parameters_at x i)

/-- This is an auxiliary definition to help construct `centering_density` below. -/
def localCenteringDensityMp : ℕ :=
  by
  choose n hn₁ hn₂ using
    filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surrounding_pts_approx_surrounding_points_at x)
  choose u hu v hv huv using mem_prod_iff.mp hn₁
  choose m hmv using mem_at_top_sets.mp hv
  exact m

theorem localCenteringDensity_spec [DecidablePred (· ∈ affineBases ι ℝ F)] :
    γ.localCenteringDensity x y =
      ∑ i,
        evalBarycentricCoords ι ℝ F (g y)
            (γ.approxSurroundingPointsAt x y (γ.localCenteringDensityMp x)) i •
          deltaMollifier (γ.localCenteringDensityMp x) (γ.surroundingParametersAt x i) :=
  rfl

/-- This is an auxiliary definition to help construct `centering_density` below. -/
def localCenteringDensityNhd : Set E :=
  by
  choose n hn₁ hn₂ using
    filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surrounding_pts_approx_surrounding_points_at x)
  choose u hu v hv huv using mem_prod_iff.mp hn₁
  exact interior u

theorem localCenteringDensityNhd_isOpen : IsOpen <| γ.localCenteringDensityNhd x :=
  isOpen_interior

theorem localCenteringDensityNhd_self_mem : x ∈ γ.localCenteringDensityNhd x :=
  by
  let h :=
    filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surrounding_pts_approx_surrounding_points_at x)
  exact
    mem_interior_iff_mem_nhds.mpr
      (Classical.choose
        (Classical.choose_spec (mem_prod_iff.mp (Classical.choose (Classical.choose_spec h)))))

-- unused
theorem localCenteringDensityNhd_covers : univ ⊆ ⋃ x, γ.localCenteringDensityNhd x := fun x hx =>
  mem_iUnion.mpr ⟨x, γ.localCenteringDensityNhd_self_mem x⟩

theorem approxSurroundingPointsAt_of_localCenteringDensityNhd
    (hy : y ∈ γ.localCenteringDensityNhd x) :
    ∃ w, SurroundingPts (g y) (γ.approxSurroundingPointsAt x y (γ.localCenteringDensityMp x)) w :=
  by
  let h :=
    filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surrounding_pts_approx_surrounding_points_at x)
  let nn := Classical.choose h
  let hnn := mem_prod_iff.mp (Classical.choose (Classical.choose_spec h))
  let n := Classical.choose hnn
  let hn := Classical.choose_spec hnn
  change y ∈ interior n at hy 
  let v := Classical.choose (Classical.choose_spec hn)
  let hv : v ∈ at_top := Classical.choose (Classical.choose_spec (Classical.choose_spec hn))
  let m := Classical.choose (mem_at_top_sets.mp hv)
  let hm := Classical.choose_spec (mem_at_top_sets.mp hv)
  change ∃ w, SurroundingPts (g y) (γ.approx_surrounding_points_at x y m) w
  suffices (y, m) ∈ nn by exact Classical.choose_spec (Classical.choose_spec h) _ this
  apply Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hn))
  change y ∈ n ∧ m ∈ v
  exact ⟨interior_subset hy, hm _ (le_refl _)⟩

theorem approxSurroundingPointsAt_mem_affineBases (hy : y ∈ γ.localCenteringDensityNhd x) :
    γ.approxSurroundingPointsAt x y (γ.localCenteringDensityMp x) ∈ affineBases ι ℝ F :=
  (Classical.choose_spec
      (γ.approxSurroundingPointsAt_of_localCenteringDensityNhd x y hy)).mem_affineBases

variable [DecidablePred (· ∈ affineBases ι ℝ F)]

@[simp]
theorem localCenteringDensity_pos (hy : y ∈ γ.localCenteringDensityNhd x) (t : ℝ) :
    0 < γ.localCenteringDensity x y t :=
  by
  simp only [γ.local_centering_density_spec x, Fintype.sum_apply, Pi.smul_apply,
    Algebra.id.smul_eq_mul]
  refine' Finset.sum_pos (fun i hi => _) Finset.univ_nonempty
  refine' mul_pos _ (deltaMollifier_pos _)
  obtain ⟨w, hw⟩ := γ.approx_surrounding_points_at_of_local_centering_density_nhd x y hy
  convert hw.w_pos i
  rw [← hw.coord_eq_w]
  simp [evalBarycentricCoords, γ.approx_surrounding_points_at_mem_affine_bases x y hy]

theorem localCenteringDensity_periodic : Periodic (γ.localCenteringDensity x y) 1 :=
  Finset.univ.periodic_sum fun i hi => Periodic.smul deltaMollifier_periodic _

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem localCenteringDensity_smooth_on :
    smooth_on ↿(γ.localCenteringDensity x) <| γ.localCenteringDensityNhd x ×ˢ (univ : Set ℝ) :=
  by
  let h₀ (yt : E × ℝ) (hyt : yt ∈ γ.local_centering_density_nhd x ×ˢ (univ : Set ℝ)) :=
    congr_fun (γ.local_centering_density_spec x yt.fst) yt.snd
  refine' ContDiffOn.congr _ h₀
  simp only [Fintype.sum_apply, Pi.smul_apply, Algebra.id.smul_eq_mul]
  refine' ContDiffOn.sum fun i hi => ContDiffOn.mul _ (ContDiff.contDiffOn _)
  · let w : F × (ι → F) → ℝ := fun z => evalBarycentricCoords ι ℝ F z.1 z.2 i
    let z : E → F × (ι → F) :=
      (Prod.map g fun y => γ.approx_surrounding_points_at x y (γ.local_centering_density_mp x)) ∘
        fun x => (x, x)
    change smooth_on ((w ∘ z) ∘ Prod.fst) (γ.local_centering_density_nhd x ×ˢ univ)
    rw [prod_univ]
    refine' ContDiffOn.comp _ cont_diff_fst.cont_diff_on subset.rfl
    have h₁ := smooth_barycentric ι ℝ F (Fintype.card_fin _)
    have h₂ : 𝒞 ∞ (eval i : (ι → ℝ) → ℝ) := contDiff_apply _ _ i
    refine' (h₂.comp_cont_diff_on h₁).comp _ _
    · have h₃ := (diag_preimage_prod_self (γ.local_centering_density_nhd x)).symm.Subset
      refine' ContDiffOn.comp _ (cont_diff_id.prod contDiff_id).ContDiffOn h₃
      refine' γ.smooth_surrounded.ContDiffOn.Prod_map (ContDiff.contDiffOn _)
      exact γ.approx_surrounding_points_at_smooth x _
    · intro y hy
      simp [z, γ.approx_surrounding_points_at_mem_affine_bases x y hy]
  · exact delta_mollifier_smooth.comp contDiff_snd

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem localCenteringDensity_continuous (hy : y ∈ γ.localCenteringDensityNhd x) :
    Continuous fun t => γ.localCenteringDensity x y t :=
  by
  refine' continuous_iff_continuous_at.mpr fun t => _
  have hyt : γ.local_centering_density_nhd x ×ˢ univ ∈ 𝓝 (y, t) :=
    mem_nhds_prod_iff'.mpr
      ⟨γ.local_centering_density_nhd x, univ, γ.local_centering_density_nhd_is_open x, hy,
        isOpen_univ, mem_univ t, rfl.subset⟩
  exact
    ((γ.local_centering_density_smooth_on x).continuousOn.continuousAt hyt).comp
      (Continuous.Prod.mk y).continuousAt

@[simp]
theorem localCenteringDensity_integral_eq_one (hy : y ∈ γ.localCenteringDensityNhd x) :
    ∫ s in 0 ..1, γ.localCenteringDensity x y s = 1 :=
  by
  let n := γ.local_centering_density_mp x
  simp only [γ.local_centering_density_spec x, Prod.forall, exists_prop, gt_iff_lt,
    Fintype.sum_apply, Pi.smul_apply, Algebra.id.smul_eq_mul, Finset.sum_smul]
  rw [intervalIntegral.integral_finset_sum]
  · have h : γ.approx_surrounding_points_at x y n ∈ affineBases ι ℝ F :=
      γ.approx_surrounding_points_at_mem_affine_bases x y hy
    simp_rw [← smul_eq_mul, intervalIntegral.integral_smul, deltaMollifier_integral_eq_one,
      Algebra.id.smul_eq_mul, mul_one, evalBarycentricCoords_apply_of_mem_bases ι ℝ F (g y) h,
      AffineBasis.coords_apply, AffineBasis.sum_coord_apply_eq_one]
  · simp_rw [← smul_eq_mul]
    refine' fun i hi => (Continuous.const_smul _ _).IntervalIntegrable 0 1
    exact delta_mollifier_smooth.continuous

@[simp]
theorem localCenteringDensity_average (hy : y ∈ γ.localCenteringDensityNhd x) :
    ∫ s in 0 ..1, γ.localCenteringDensity x y s • γ y s = g y :=
  by
  let n := γ.local_centering_density_mp x
  simp only [γ.local_centering_density_spec x, Prod.forall, exists_prop, gt_iff_lt,
    Fintype.sum_apply, Pi.smul_apply, Algebra.id.smul_eq_mul, Finset.sum_smul]
  rw [intervalIntegral.integral_finset_sum]
  · simp_rw [mul_smul, intervalIntegral.integral_smul]
    change ∑ i, _ • γ.approx_surrounding_points_at x y n i = _
    have h : γ.approx_surrounding_points_at x y n ∈ affineBases ι ℝ F :=
      γ.approx_surrounding_points_at_mem_affine_bases x y hy
    erw [evalBarycentricCoords_apply_of_mem_bases ι ℝ F (g y) h]
    simp only [AffineBasis.coords_apply]
    exact AffineBasis.linear_combination_coord_eq_self _ _
  · simp_rw [mul_smul]
    refine' fun i hi => ((Continuous.smul _ (γ.continuous y)).const_smul _).IntervalIntegrable 0 1
    exact delta_mollifier_smooth.continuous

/-- Given `γ : smooth_surrounding_family g`, together with a point `x : E` and a map `f : ℝ → ℝ`,
`γ.is_centering_density x f` is the proposition that `f` is periodic, strictly positive, and
has integral one and that the average of `γₓ` with respect to the measure that `f` defines on
the circle is `g x`.

The continuity assumption is just a legacy convenience and should be dropped. -/
structure IsCenteringDensity (x : E) (f : ℝ → ℝ) : Prop where
  Pos : ∀ t, 0 < f t
  Periodic : Periodic f 1
  integral_one : ∫ s in 0 ..1, f s = 1
  average : ∫ s in 0 ..1, f s • γ x s = g x
  Continuous : Continuous f

-- Can drop if/when have `interval_integrable.smul_continuous_on`
theorem isCenteringDensity_convex (x : E) : Convex ℝ {f | γ.IsCenteringDensity x f} := by
  classical
  rintro f ⟨hf₁, hf₂, hf₃, hf₄, hf₅⟩ k ⟨hk₁, hk₂, hk₃, hk₄, hk₅⟩ a b ha hb hab
  have hf₆ : IntervalIntegrable f volume 0 1 := by apply interval_integrable_of_integral_ne_zero;
    rw [hf₃]; exact one_ne_zero
  have hf₇ : IntervalIntegrable (f • γ x) volume 0 1 :=
    (hf₅.smul (γ.continuous x)).IntervalIntegrable 0 1
  have hk₆ : IntervalIntegrable k volume 0 1 := by apply interval_integrable_of_integral_ne_zero;
    rw [hk₃]; exact one_ne_zero
  have hk₇ : IntervalIntegrable (k • γ x) volume 0 1 :=
    (hk₅.smul (γ.continuous x)).IntervalIntegrable 0 1
  exact
    { Pos := fun t => convex_Ioi (0 : ℝ) (hf₁ t) (hk₁ t) ha hb hab
      Periodic := (hf₂.smul a).add (hk₂.smul b)
      integral_one := by
        simp_rw [Pi.add_apply]
        rw [intervalIntegral.integral_add (hf₆.smul a) (hk₆.smul b)]
        simp [intervalIntegral.integral_smul, hf₃, hk₃, hab]
      average := by
        simp_rw [Pi.add_apply, Pi.smul_apply, add_smul, smul_assoc]
        erw [intervalIntegral.integral_add (hf₇.smul a) (hk₇.smul b)]
        simp [intervalIntegral.integral_smul, ← add_smul, hf₄, hk₄, hab]
      Continuous := Continuous.add (hf₅.const_smul a) (hk₅.const_smul b) }

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem exists_smooth_isCenteringDensity (x : E) :
    ∃ U ∈ 𝓝 x,
      ∃ f : E → ℝ → ℝ,
        smooth_on (uncurry f) (U ×ˢ (univ : Set ℝ)) ∧ ∀ y ∈ U, γ.IsCenteringDensity y (f y) :=
  ⟨γ.localCenteringDensityNhd x,
    mem_nhds_iff.mpr
      ⟨_, Subset.rfl, γ.localCenteringDensityNhd_isOpen x, γ.localCenteringDensityNhd_self_mem x⟩,
    γ.localCenteringDensity x, γ.localCenteringDensity_smooth_on x, fun y hy =>
    ⟨γ.localCenteringDensity_pos x y hy, γ.localCenteringDensity_periodic x y,
      γ.localCenteringDensity_integral_eq_one x y hy, γ.localCenteringDensity_average x y hy,
      γ.localCenteringDensity_continuous x y hy⟩⟩

/-- This the key construction. It represents a smooth probability distribution on the circle with
the property that:
`∫ s in 0..1, γ.centering_density x s • γ x s = g x`
for all `x : E` (see `centering_density_average` below). -/
def centeringDensity : E → ℝ → ℝ :=
  Classical.choose
    (exists_contDiff_of_convex₂ γ.isCenteringDensity_convex γ.exists_smooth_isCenteringDensity)

theorem centeringDensity_smooth : 𝒞 ∞ <| uncurry fun x t => γ.centeringDensity x t :=
  (Classical.choose_spec <|
      exists_contDiff_of_convex₂ γ.isCenteringDensity_convex γ.exists_smooth_isCenteringDensity).1

theorem isCenteringDensityCenteringDensity (x : E) :
    γ.IsCenteringDensity x (γ.centeringDensity x) :=
  (Classical.choose_spec <|
        exists_contDiff_of_convex₂ γ.isCenteringDensity_convex γ.exists_smooth_isCenteringDensity).2
    x

@[simp]
theorem centeringDensity_pos (t : ℝ) : 0 < γ.centeringDensity x t :=
  (γ.isCenteringDensityCenteringDensity x).Pos t

theorem centeringDensity_periodic : Periodic (γ.centeringDensity x) 1 :=
  (γ.isCenteringDensityCenteringDensity x).Periodic

@[simp]
theorem centeringDensity_integral_eq_one : ∫ s in 0 ..1, γ.centeringDensity x s = 1 :=
  (γ.isCenteringDensityCenteringDensity x).integral_one

@[simp]
theorem centeringDensity_average : ∫ s in 0 ..1, γ.centeringDensity x s • γ x s = g x :=
  (γ.isCenteringDensityCenteringDensity x).average

theorem centeringDensity_continuous : Continuous (γ.centeringDensity x) :=
  by
  apply continuous_uncurry_left x
  exact γ.centering_density_smooth.continuous

theorem centeringDensity_intervalIntegrable (t₁ t₂ : ℝ) :
    IntervalIntegrable (γ.centeringDensity x) volume t₁ t₂ :=
  (γ.centeringDensity_continuous x).IntervalIntegrable t₁ t₂

@[simp]
theorem integral_add_one_centeringDensity (t : ℝ) :
    ∫ s in 0 ..t + 1, γ.centeringDensity x s = (∫ s in 0 ..t, γ.centeringDensity x s) + 1 :=
  by
  have h₁ := γ.centering_density_interval_integrable x 0 t
  have h₂ := γ.centering_density_interval_integrable x t (t + 1)
  simp [← integral_add_adjacent_intervals h₁ h₂,
    (γ.centering_density_periodic x).intervalIntegral_add_eq t 0]

theorem deriv_integral_centeringDensity_pos (t : ℝ) :
    0 < deriv (fun t => ∫ s in 0 ..t, γ.centeringDensity x s) t :=
  by
  rw [intervalIntegral.deriv_integral_right (γ.centering_density_interval_integrable _ _ _)
      ((γ.centering_density_continuous x).StronglyMeasurableAtFilter volume (𝓝 t))
      (centering_density_continuous γ x).continuousAt]
  exact centering_density_pos γ x t

theorem strictMono_integral_centeringDensity :
    StrictMono fun t => ∫ s in 0 ..t, γ.centeringDensity x s :=
  strictMono_of_deriv_pos (γ.deriv_integral_centeringDensity_pos x)

theorem surjective_integral_centeringDensity :
    Surjective fun t => ∫ s in 0 ..t, γ.centeringDensity x s :=
  haveI : Continuous fun t => ∫ s in 0 ..t, γ.centering_density x s :=
    continuous_primitive (γ.centering_density_interval_integrable x) 0
  EquivariantMap.surjective
    ⟨fun t => ∫ s in 0 ..t, γ.centering_density x s, γ.integral_add_one_centering_density x⟩ this

/-- Given `γ : smooth_surrounding_family g`, `x ↦ γ.reparametrize x` is a smooth family of
diffeomorphisms of the circle such that reparametrizing `γₓ` by `γ.reparametrize x` gives a loop
with average `g x`.

This is the key construction and the main "output" of the reparametrization lemma. -/
def reparametrize : E → EquivariantEquiv := fun x =>
  ({    toFun := fun t => ∫ s in 0 ..t, γ.centeringDensity x s
        invFun :=
          (StrictMono.orderIsoOfSurjective _ (γ.strictMono_integral_centeringDensity x)
              (γ.surjective_integral_centeringDensity x)).symm
        left_inv := StrictMono.orderIsoOfSurjective_symm_apply_self _ _ _
        right_inv := fun t => StrictMono.orderIsoOfSurjective_self_symm_apply _ _ _ t
        map_zero' := integral_same
        eqv' := γ.integral_add_one_centeringDensity x } : EquivariantEquiv).symm

-- unused
theorem coe_reparametrize_symm :
    ((γ.reparametrize x).symm : ℝ → ℝ) = fun t => ∫ s in 0 ..t, γ.centeringDensity x s :=
  rfl

-- unused
theorem reparametrize_symm_apply (t : ℝ) :
    (γ.reparametrize x).symm t = ∫ s in 0 ..t, γ.centeringDensity x s :=
  rfl

-- unused
@[simp]
theorem integral_reparametrize (t : ℝ) :
    ∫ s in 0 ..γ.reparametrize x t, γ.centeringDensity x s = t := by
  simp [← reparametrize_symm_apply]

theorem hasDerivAt_reparametrize_symm (s : ℝ) :
    HasDerivAt (γ.reparametrize x).symm (γ.centeringDensity x s) s :=
  integral_hasDerivAt_right (γ.centeringDensity_intervalIntegrable x 0 s)
    ((γ.centeringDensity_continuous x).StronglyMeasurableAtFilter _ _)
    (γ.centeringDensity_continuous x).continuousAt

theorem
  reparametrize_smooth :-- 𝒞 ∞ ↿γ.reparametrize :=
        𝒞
        ∞ <|
      uncurry fun x t => γ.reparametrize x t :=
  by
  let f : E → ℝ → ℝ := fun x t => ∫ s in 0 ..t, γ.centering_density x s
  change 𝒞 ⊤ fun p : E × ℝ => (StrictMono.orderIsoOfSurjective (f p.1) _ _).symm p.2
  apply contDiff_parametric_symm_of_deriv_pos
  · exact contDiff_parametric_primitive_of_cont_diff'' γ.centering_density_smooth 0
  · exact fun x => deriv_integral_centering_density_pos γ x

@[simp]
theorem reparametrize_average :
    ((γ x).reparam <| (γ.reparametrize x).EquivariantMap).average = g x :=
  by
  change ∫ s : ℝ in 0 ..1, γ x (γ.reparametrize x s) = g x
  have h₁ :
    ∀ s, s ∈ uIcc 0 (1 : ℝ) → HasDerivAt (γ.reparametrize x).symm (γ.centering_density x s) s :=
    fun s hs => γ.has_deriv_at_reparametrize_symm x s
  have h₂ : ContinuousOn (fun s => γ.centering_density x s) (uIcc 0 1) :=
    (γ.centering_density_continuous x).continuousOn
  have h₃ : Continuous fun s => γ x (γ.reparametrize x s) :=
    (γ.continuous x).comp (continuous_uncurry_left x γ.reparametrize_smooth.continuous)
  rw [← (γ.reparametrize x).symm.map_zero, ← (γ.reparametrize x).symm.map_one, ←
    integral_comp_smul_deriv h₁ h₂ h₃]
  simp

end SmoothSurroundingFamily

