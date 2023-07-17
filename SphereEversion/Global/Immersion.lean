import Mathlib.Geometry.Manifold.Instances.Sphere
import SphereEversion.ToMathlib.LinearAlgebra.FiniteDimensional
import SphereEversion.ToMathlib.Analysis.InnerProductSpace.Rotation
import SphereEversion.Global.Gromov
import SphereEversion.Global.TwistOneJetSec

-- import interactive_expr
-- import interactive_expr
-- set_option trace.filter_inst_type true
-- set_option trace.filter_inst_type true
noncomputable section

open Metric FiniteDimensional Set Function LinearMap Filter ContinuousLinearMap

open scoped Manifold Topology

section General

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type _} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type _} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') {M' : Type _}
  [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M'] {F : Type _}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type _} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) (N : Type _) [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N]

local notation "TM" => TangentSpace I

local notation "TM'" => TangentSpace I'

local notation "HJ" => ModelProd (ModelProd H H') (E →L[ℝ] E')

local notation "ψJ" => chartAt HJ

/-- A map between manifolds is an immersion if it is differentiable and its differential at
any point is injective. Note the formalized definition doesn't require differentiability.
If `f` is not differentiable at `m` then, by definition, `mfderiv I I' f m` is zero, which
is not injective unless the source dimension is zero, which implies differentiability. -/
def Immersion (f : M → M') : Prop :=
  ∀ m, Injective (mfderiv I I' f m)

variable (M M')

/-- The relation of immersions for maps between two manifolds. -/
def immersionRel : RelMfld I M I' M' :=
  {σ | Injective σ.2}

variable {M M'}

@[simp]
theorem mem_immersionRel_iff {σ : OneJetBundle I M I' M'} :
    σ ∈ immersionRel I M I' M' ↔ Injective (σ.2 : TangentSpace I _ →L[ℝ] TangentSpace I' _) :=
  Iff.rfl

/-- A characterisation of the immersion relation in terms of a local chart. -/
theorem mem_immersionRel_iff' {σ σ' : OneJetBundle I M I' M'} (hσ' : σ' ∈ (ψJ σ).source) :
    σ' ∈ immersionRel I M I' M' ↔ Injective (ψJ σ σ').2 :=
  by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps] at hσ' 
  simp_rw [mem_immersionRel_iff]
  rw [oneJetBundle_chartAt_apply, in_coordinates_eq]
  simp_rw [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, EquivLike.comp_injective,
    EquivLike.injective_comp]
  exacts [hσ'.1.1, hσ'.1.2]

theorem chartAt_image_immersionRel_eq {σ : OneJetBundle I M I' M'} :
    ψJ σ '' ((ψJ σ).source ∩ immersionRel I M I' M') = (ψJ σ).target ∩ {q : HJ | Injective q.2} :=
  LocalEquiv.IsImage.image_eq fun σ' hσ' => (mem_immersionRel_iff' I I' hσ').symm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

theorem immersionRel_open : IsOpen (immersionRel I M I' M') :=
  by
  simp_rw [ChartedSpace.isOpen_iff HJ (immersionRel I M I' M'), chartAt_image_immersionRel_eq]
  refine' fun σ => (ψJ σ).open_target.inter _
  convert is_open_univ.prod ContinuousLinearMap.isOpen_injective
  · ext; simp
  · infer_instance
  · infer_instance

@[simp]
theorem immersionRel_slice_eq {m : M} {m' : M'} {p : DualPair <| TangentSpace I m}
    {φ : TangentSpace I m →L[ℝ] TangentSpace I' m'} (hφ : Injective φ) :
    (immersionRel I M I' M').slice ⟨(m, m'), φ⟩ p = (ker p.π).map φᶜ :=
  Set.ext_iff.mpr fun w => p.injective_update_iff hφ

theorem immersionRel_ample (h : finrank ℝ E < finrank ℝ E') : (immersionRel I M I' M').Ample :=
  by
  rw [RelMfld.ample_iff]
  rintro ⟨⟨m, m'⟩, φ : TangentSpace I m →L[ℝ] TangentSpace I' m'⟩ (p : DualPair (TangentSpace I m))
    (hφ : injective φ)
  haveI : FiniteDimensional ℝ (TangentSpace I m) := (by infer_instance : FiniteDimensional ℝ E)
  have hcodim := two_le_rank_of_rank_lt_rank p.ker_pi_ne_top h φ.to_linear_map
  rw [immersionRel_slice_eq I I' hφ]
  exact ample_of_two_le_codim hcodim

/-- This is lemma `lem:open_ample_immersion` from the blueprint. -/
theorem immersionRel_open_ample (h : finrank ℝ E < finrank ℝ E') :
    IsOpen (immersionRel I M I' M') ∧ (immersionRel I M I' M').Ample :=
  ⟨immersionRel_open I I', immersionRel_ample I I' h⟩

end General

section Generalbis

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [ModelWithCorners.Boundaryless I] {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {H' : Type _}
  [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') [ModelWithCorners.Boundaryless I']
  {M' : Type _} [MetricSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M']

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

variable {EP : Type _} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
  {HP : Type _} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  [ModelWithCorners.Boundaryless IP] {P : Type _} [TopologicalSpace P] [ChartedSpace HP P]
  [SmoothManifoldWithCorners IP P] {C : Set (P × M)} {ε : M → ℝ}

variable (I M I' M' IP P)

/-- parametric h-principle for immersions. -/
theorem immersionRel_satisfiesHPrincipleWith [Nonempty P] [T2Space P] [SigmaCompactSpace P]
    [LocallyCompactSpace P] [Nonempty M] [T2Space M] [SigmaCompactSpace M] [LocallyCompactSpace M]
    [Nonempty M'] [T2Space M'] [LocallyCompactSpace M'] [SigmaCompactSpace M']
    (h : finrank ℝ E < finrank ℝ E') (hC : IsClosed C) (hε_pos : ∀ x, 0 < ε x)
    (hε_cont : Continuous ε) : (immersionRel I M I' M').SatisfiesHPrincipleWith IP C ε :=
  (immersionRel_ample I I' h).SatisfiesHPrincipleWith (immersionRel_open I I') hC hε_pos hε_cont

end Generalbis

section sphere_eversion

variable (E : Type _) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 3)]

attribute [local instance] fact_finite_dimensional_of_finrank_eq_succ

local notation "𝕊²" => sphere (0 : E) 1

/- Maybe the next two lemmas won't be used directly, but they should be done first as
sanity checks. -/
theorem immersion_inclusion_sphere : Immersion (𝓡 2) 𝓘(ℝ, E) fun x : 𝕊² => (x : E) :=
  mfderiv_coe_sphere_injective

theorem immersion_antipodal_sphere : Immersion (𝓡 2) 𝓘(ℝ, E) fun x : 𝕊² => -(x : E) :=
  by
  intro x
  change injective (mfderiv (𝓡 2) 𝓘(ℝ, E) (-fun x : 𝕊² => (x : E)) x)
  rw [mfderiv_neg]
  exact neg_injective.comp (mfderiv_coe_sphere_injective x)

-- The relation of immersion of a two-sphere into its ambient Euclidean space.
local notation "𝓡_imm" => immersionRel (𝓡 2) 𝕊² 𝓘(ℝ, E) E

variable (ω : Orientation ℝ E (Fin 3))

theorem smooth_bs :
    Smooth (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E) fun p : ℝ × 𝕊² => ((1 - p.1) • p.2 + p.1 • -p.2 : E) :=
  by
  refine' (ContMDiff.smul _ _).add (cont_mdiff_fst.smul _)
  · exact (cont_diff_const.sub contDiff_id).contMDiff.comp contMDiff_fst
  · exact cont_mdiff_coe_sphere.comp contMDiff_snd
  · exact (cont_diff_neg.cont_mdiff.comp contMDiff_coe_sphere).comp contMDiff_snd

def formalEversionAux : FamilyOneJetSec (𝓡 2) 𝕊² 𝓘(ℝ, E) E 𝓘(ℝ, ℝ) ℝ :=
  familyJoin (smooth_bs E) <|
    familyTwist (drop (oneJetExtSec ⟨(coe : 𝕊² → E), contMDiff_coe_sphere⟩))
      (fun p : ℝ × 𝕊² => ω.rot (p.1, p.2))
      (by
        intro p
        have : SmoothAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E →L[ℝ] E) ω.rot (p.1, p.2) :=
          by
          refine' (ω.cont_diff_rot _).contMDiffAt
          exact ne_zero_of_mem_unit_sphere p.2
        refine' this.comp p (Smooth.smoothAt _)
        exact smooth_fst.prod_mk (cont_mdiff_coe_sphere.comp smooth_snd))

/-- A formal eversion of a two-sphere into its ambient Euclidean space. -/
def formalEversionAux2 : HtpyFormalSol 𝓡_imm :=
  { formalEversionAux E ω with
    is_sol' := fun t x => (ω.isometry_rot t x).Injective.comp (mfderiv_coe_sphere_injective x) }

def formalEversion : HtpyFormalSol 𝓡_imm :=
  (formalEversionAux2 E ω).reindex ⟨smoothStep, contMDiff_iff_contDiff.mpr smoothStep.smooth⟩

@[simp]
theorem formalEversion_bs (t : ℝ) :
    (formalEversion E ω t).bs = fun x : 𝕊² =>
      (1 - smoothStep t : ℝ) • (x : E) + (smoothStep t : ℝ) • (-x : E) :=
  rfl

theorem formalEversion_zero (x : 𝕊²) : (formalEversion E ω 0).bs x = x := by simp

theorem formalEversion_one (x : 𝕊²) : (formalEversion E ω 1).bs x = -x := by simp

theorem formalEversionHolAtZero {t : ℝ} (ht : t < 1 / 4) :
    (formalEversion E ω t).toOneJetSec.IsHolonomic :=
  by
  intro x
  change
    mfderiv (𝓡 2) 𝓘(ℝ, E) (fun y : 𝕊² => ((1 : ℝ) - smoothStep t) • (y : E) + smoothStep t • -y) x =
      (ω.rot (smoothStep t, x)).comp (mfderiv (𝓡 2) 𝓘(ℝ, E) (fun y : 𝕊² => (y : E)) x)
  simp_rw [smoothStep.of_lt ht, ω.rot_zero, ContinuousLinearMap.id_comp]
  congr
  ext y
  simp [smoothStep.of_lt ht]

theorem formalEversionHolAtOne {t : ℝ} (ht : 3 / 4 < t) :
    (formalEversion E ω t).toOneJetSec.IsHolonomic :=
  by
  intro x
  change
    mfderiv (𝓡 2) 𝓘(ℝ, E) (fun y : 𝕊² => ((1 : ℝ) - smoothStep t) • (y : E) + smoothStep t • -y) x =
      (ω.rot (smoothStep t, x)).comp (mfderiv (𝓡 2) 𝓘(ℝ, E) (fun y : 𝕊² => (y : E)) x)
  trans mfderiv (𝓡 2) 𝓘(ℝ, E) (-fun y : 𝕊² => (y : E)) x
  · congr 2
    ext y
    simp [smoothStep.of_gt ht]
  ext v
  simp_rw [mfderiv_neg, ContinuousLinearMap.coe_comp', comp_app, ContinuousLinearMap.neg_apply,
    smoothStep.of_gt ht]
  rw [ω.rot_one]
  rw [← range_mfderiv_coe_sphere x]
  exact LinearMap.mem_range_self _ _

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem formalEversion_hol_near_zero_one :
    ∀ᶠ s : ℝ × 𝕊² near {0, 1} ×ˢ univ, (formalEversion E ω s.1).toOneJetSec.IsHolonomicAt s.2 :=
  by
  have : (Iio (1 / 4 : ℝ) ∪ Ioi (3 / 4)) ×ˢ (univ : Set 𝕊²) ∈ 𝓝ˢ (({0, 1} : Set ℝ) ×ˢ univ) :=
    by
    refine' ((is_open_Iio.union isOpen_Ioi).prod isOpen_univ).mem_nhdsSet.mpr _
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    refine' ⟨_, mem_univ _⟩
    simp_rw [mem_insert_iff, mem_singleton_iff] at hs 
    rcases hs with (rfl | rfl)
    · exact Or.inl (show (0 : ℝ) < 1 / 4 by norm_num)
    · exact Or.inr (show (3 / 4 : ℝ) < 1 by norm_num)
  refine' eventually_of_mem this _
  rintro ⟨t, x⟩ ⟨ht | ht, hx⟩
  · exact formalEversionHolAtZero E ω ht x
  · exact formalEversionHolAtOne E ω ht x

theorem sphere_eversion :
    ∃ f : ℝ → 𝕊² → E,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E) ∞ (uncurry f) ∧
        (f 0 = fun x => x) ∧ (f 1 = fun x => -x) ∧ ∀ t, Immersion (𝓡 2) 𝓘(ℝ, E) (f t) :=
  by
  classical
  let ω : Orientation ℝ E (Fin 3) :=
    ((stdOrthonormalBasis _ _).reindex <|
          finCongr (Fact.out _ : finrank ℝ E = 3)).toBasis.Orientation
  have rankE := Fact.out (finrank ℝ E = 3)
  haveI : FiniteDimensional ℝ E := finite_dimensional_of_finrank_eq_succ rankE
  have ineq_rank : finrank ℝ (EuclideanSpace ℝ (Fin 2)) < finrank ℝ E := by simp [rankE]
  let ε : 𝕊² → ℝ := fun x => 1
  have hε_pos : ∀ x, 0 < ε x := fun x => zero_lt_one
  have hε_cont : Continuous ε := continuous_const
  haveI : Nontrivial E := nontrivial_of_finrank_eq_succ (Fact.out _ : finrank ℝ E = 3)
  haveI : Nonempty ↥(sphere 0 1 : Set E) :=
    (normed_space.sphere_nonempty.mpr zero_le_one).to_subtype
  rcases(immersionRel_satisfiesHPrincipleWith (𝓡 2) 𝕊² 𝓘(ℝ, E) E 𝓘(ℝ, ℝ) ℝ ineq_rank
          ((finite.is_closed (by simp : ({0, 1} : Set ℝ).Finite)).prod isClosed_univ) hε_pos
          hε_cont).bs
      (formalEversion E ω) (formalEversion_hol_near_zero_one E ω) with
    ⟨f, h₁, h₂, -, h₅⟩
  have := h₂.nhds_set_forall_mem
  refine' ⟨f, h₁, _, _, h₅⟩
  · ext x
    rw [this (0, x) (by simp)]
    convert formalEversion_zero E ω x
  · ext x
    rw [this (1, x) (by simp)]
    convert formalEversion_one E ω x

-- The next instance will be used in the main file
instance (n : ℕ) : Fact (finrank ℝ (EuclideanSpace ℝ <| Fin n) = n) :=
  ⟨finrank_euclideanSpace_fin⟩

notation "ℝ^" -- The next notation will be used in the main file
n:arg => EuclideanSpace ℝ (Fin n)

end sphere_eversion

