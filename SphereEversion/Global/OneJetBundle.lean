/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn

! This file was ported from Lean 3 source module global.one_jet_bundle
-/
import SphereEversion.ToMathlib.Geometry.Manifold.VectorBundle.Misc
-- import SphereEversion.InteractiveExpr

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option trace.filter_inst_type -/
set_option trace.filter_inst_type true

/-!
# 1-jet bundles

This file contains the definition of the 1-jet bundle `J¹(M, M')`, also known as
`one_jet_bundle I M I' M'`.

We also define
* `one_jet_ext I I' f : M → J¹(M, M')`: the 1-jet extension `j¹f` of a map `f : M → M'`

We prove
* If `f` is smooth, `j¹f` is smooth.
* If `x ↦ (f₁ x, f₂ x, ϕ₁ x) : N → J¹(M₁, M₂)` and `x ↦ (f₂ x, f₃ x, ϕ₂ x) : N → J¹(M₂, M₃)`
  are smooth, then so is `x ↦ (f₁ x, f₃ x, ϕ₂ x ∘ ϕ₁ x) : N → J¹(M₁, M₃)`.
-/


noncomputable section

open Filter Set Equiv Bundle ContinuousLinearMap

open scoped Manifold Topology Bundle

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _)
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  (I' : ModelWithCorners 𝕜 E' H') (M' : Type _) [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M'] {E'' : Type _} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type _} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type _}
  [TopologicalSpace M''] [ChartedSpace H'' M''] [SmoothManifoldWithCorners I'' M''] {F : Type _}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _} [TopologicalSpace G]
  (J : ModelWithCorners 𝕜 F G) {N : Type _} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N] {F' : Type _} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type _} [TopologicalSpace G'] (J' : ModelWithCorners 𝕜 F' G') {N' : Type _}
  [TopologicalSpace N'] [ChartedSpace G' N'] [SmoothManifoldWithCorners J' N'] {E₂ : Type _}
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] {H₂ : Type _} [TopologicalSpace H₂]
  {I₂ : ModelWithCorners 𝕜 E₂ H₂} {M₂ : Type _} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [SmoothManifoldWithCorners I₂ M₂] {E₃ : Type _} [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  {H₃ : Type _} [TopologicalSpace H₃] {I₃ : ModelWithCorners 𝕜 E₃ H₃} {M₃ : Type _}
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [SmoothManifoldWithCorners I₃ M₃]

variable {M M'}

local notation "σ" => RingHom.id 𝕜

instance deleteme1 :
    ∀ x : M × M',
      Module 𝕜 (((ContMDiffMap.fst : C^∞⟮I.prod I', M × M'; I, M⟯) *ᵖ (TangentSpace I)) x) :=
  by infer_instance

instance deleteme2 :
    ∀ x : M × M',
      Module 𝕜 (((ContMDiffMap.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ (TangentSpace I')) x) :=
  by infer_instance

instance deleteme3 :
    VectorBundle 𝕜 E ((ContMDiffMap.fst : C^∞⟮I.prod I', M × M'; I, M⟯) *ᵖ (TangentSpace I)) := by
  infer_instance

instance deleteme4 :
    VectorBundle 𝕜 E' ((ContMDiffMap.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ (TangentSpace I')) :=
  by infer_instance

instance deleteme5 :
    SmoothVectorBundle E ((ContMDiffMap.fst : C^∞⟮I.prod I', M × M'; I, M⟯) *ᵖ (TangentSpace I))
      (I.prod I') :=
  by infer_instance

instance deleteme6 :
    SmoothVectorBundle E' ((ContMDiffMap.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ (TangentSpace I'))
      (I.prod I') :=
  by infer_instance

/-- The fibers of the one jet-bundle. -/
@[nolint unused_arguments]
def OneJetSpace (p : M × M') : Type _ :=
  Bundle.ContinuousLinearMap σ
    ((ContMDiffMap.fst : C^∞⟮I.prod I', M × M'; I, M⟯) *ᵖ (TangentSpace I))
    ((ContMDiffMap.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ (TangentSpace I')) p
deriving AddCommGroup, TopologicalSpace

variable {I I'}

-- what is better notation for this?
local notation "FJ¹MM'" => (OneJetSpace I I' : M × M' → Type _)

variable (I I')

instance (p : M × M') :
    CoeFun (OneJetSpace I I' p) fun _ => TangentSpace I p.1 → TangentSpace I' p.2 :=
  ⟨fun φ => φ.toFun⟩

variable (M M')

-- is empty if the base manifold is empty
/-- The space of one jets of maps between two smooth manifolds.
Defined in terms of `bundle.total_space` to be able to put a suitable topology on it. -/
@[nolint has_inhabited_instance, reducible]
def OneJetBundle :=
  TotalSpace (E →L[𝕜] E') (OneJetSpace I I' : M × M' → Type _)

variable {I I' M M'}

local notation "J¹MM'" => OneJetBundle I M I' M'

local notation "HJ" => ModelProd (ModelProd H H') (E →L[𝕜] E')

@[ext]
theorem OneJetBundle.ext {x y : J¹MM'} (h : x.1.1 = y.1.1) (h' : x.1.2 = y.1.2) (h'' : x.2 = y.2) :
    x = y := by
  rcases x with ⟨⟨a, b⟩, c⟩
  rcases y with ⟨⟨d, e⟩, f⟩
  dsimp only at h h' h'' 
  rw [h, h', h'']

variable (I I' M M')

section OneJetBundleInstances

section

variable {M} (p : M × M')

instance (x : M × M') : Module 𝕜 (FJ¹MM' x) := by delta_instance one_jet_space

end

variable (M)

instance : TopologicalSpace J¹MM' := by delta_instance one_jet_bundle one_jet_space

instance : FiberBundle (E →L[𝕜] E') FJ¹MM' := by delta_instance one_jet_space

instance : VectorBundle 𝕜 (E →L[𝕜] E') FJ¹MM' := by delta_instance one_jet_space

instance : SmoothVectorBundle (E →L[𝕜] E') (OneJetSpace I I' : M × M' → Type _) (I.prod I') := by
  delta_instance one_jet_space

instance : ChartedSpace HJ J¹MM' := by delta_instance one_jet_bundle one_jet_space

instance : SmoothManifoldWithCorners ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) J¹MM' := by
  apply Bundle.TotalSpace.smoothManifoldWithCorners

end OneJetBundleInstances

variable (M)

/-- The tangent bundle projection on the basis is a continuous map. -/
theorem one_jet_bundle_proj_continuous : Continuous (π (E →L[𝕜] E') FJ¹MM') :=
  continuous_proj (E →L[𝕜] E') FJ¹MM'

variable {I M I' M' J J'}

attribute [simps] ContMDiffMap.fst ContMDiffMap.snd

theorem oneJetBundle_trivializationAt (x₀ x : J¹MM') :
    (trivializationAt (E →L[𝕜] E') (OneJetSpace I I') x₀.proj x).2 =
      inCoordinates E (TangentSpace I) E' (TangentSpace I') x₀.proj.1 x.proj.1 x₀.proj.2 x.proj.2
        x.2 :=
  by
  delta OneJetSpace
  rw [continuousLinearMap_trivializationAt, Trivialization.continuousLinearMap_apply]
  simp_rw [inTangentCoordinates, in_coordinates]
  congr 2
  exact
    Trivialization.pullback_symmL ContMDiffMap.fst (trivialization_at E (TangentSpace I) x₀.1.1)
      x.proj

theorem trivializationAt_one_jet_bundle_source (x₀ : M × M') :
    (trivializationAt (E →L[𝕜] E') FJ¹MM' x₀).source =
      π (E →L[𝕜] E') FJ¹MM' ⁻¹'
        (Prod.fst ⁻¹' (chartAt H x₀.1).source ∩ Prod.snd ⁻¹' (chartAt H' x₀.2).source) :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, mfld_simps]
theorem trivializationAt_one_jet_bundle_target (x₀ : M × M') :
    (trivializationAt (E →L[𝕜] E') FJ¹MM' x₀).target =
      (Prod.fst ⁻¹' (trivializationAt E (TangentSpace I) x₀.1).baseSet ∩
          Prod.snd ⁻¹' (trivializationAt E' (TangentSpace I') x₀.2).baseSet) ×ˢ
        Set.univ :=
  rfl

/-- Computing the value of a chart around `v` at point `v'` in `J¹(M, M')`.
  The last component equals the continuous linear map `v'.2`, composed on both sides by an
  appropriate coordinate change function. -/
theorem oneJetBundle_chartAt_apply (v v' : OneJetBundle I M I' M') :
    chartAt HJ v v' =
      ((chartAt H v.1.1 v'.1.1, chartAt H' v.1.2 v'.1.2),
        inCoordinates E (TangentSpace I) E' (TangentSpace I') v.1.1 v'.1.1 v.1.2 v'.1.2 v'.2) :=
  by
  ext1
  · rfl
  rw [charted_space_chart_at_snd]
  exact oneJetBundle_trivializationAt v v'

/-- In `J¹(M, M')`, the source of a chart has a nice formula -/
theorem oneJetBundle_chart_source (x₀ : J¹MM') :
    (chartAt HJ x₀).source = π (E →L[𝕜] E') FJ¹MM' ⁻¹' (chartAt (ModelProd H H') x₀.proj).source :=
  by
  simp only [FiberBundle.chartedSpace_chartAt, trivializationAt_one_jet_bundle_source, mfld_simps]
  simp_rw [prod_univ, ← preimage_inter, ← Set.prod_eq, preimage_preimage, inter_eq_left_iff_subset,
    subset_def, mem_preimage]
  intro x hx
  rwa [Trivialization.coe_fst]
  rwa [trivializationAt_one_jet_bundle_source, mem_preimage, ← Set.prod_eq]

/-- In `J¹(M, M')`, the target of a chart has a nice formula -/
theorem oneJetBundle_chart_target (x₀ : J¹MM') :
    (chartAt HJ x₀).target = Prod.fst ⁻¹' (chartAt (ModelProd H H') x₀.proj).target :=
  by
  simp only [FiberBundle.chartedSpace_chartAt, trivializationAt_one_jet_bundle_target, mfld_simps]
  simp_rw [prod_univ, preimage_inter, preimage_preimage, inter_eq_left_iff_subset, subset_inter_iff]
  rw [← @preimage_preimage _ _ _ fun x => (chart_at H x₀.proj.1).symm (Prod.fst x)]
  rw [← @preimage_preimage _ _ _ fun x => (chart_at H' x₀.proj.2).symm (Prod.snd x)]
  refine' ⟨preimage_mono _, preimage_mono _⟩
  · rw [← @preimage_preimage _ _ _ (chart_at H x₀.proj.1).symm]
    refine' (prod_subset_preimage_fst _ _).trans (preimage_mono _)
    exact (chart_at H x₀.proj.1).target_subset_preimage_source
  · rw [← @preimage_preimage _ _ _ (chart_at H' x₀.proj.2).symm]
    refine' (prod_subset_preimage_snd _ _).trans (preimage_mono _)
    exact (chart_at H' x₀.proj.2).target_subset_preimage_source

section Maps

theorem smooth_one_jet_bundle_proj :
    Smooth ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (I.prod I') (π (E →L[𝕜] E') FJ¹MM') := by
  apply smooth_proj _

theorem Smooth.oneJetBundle_proj {f : N → J¹MM'}
    (hf : Smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) f) : Smooth J (I.prod I') fun x => (f x).1 :=
  smooth_one_jet_bundle_proj.comp hf

theorem SmoothAt.oneJetBundle_proj {f : N → J¹MM'} {x₀ : N}
    (hf : SmoothAt J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) f x₀) :
    SmoothAt J (I.prod I') (fun x => (f x).1) x₀ :=
  (smooth_one_jet_bundle_proj _).comp x₀ hf

/-- The constructor of one_jet_bundle, in case `sigma.mk` will not give the right type. -/
@[simp]
def OneJetBundle.mk (x : M) (y : M') (f : OneJetSpace I I' (x, y)) : J¹MM' :=
  ⟨(x, y), f⟩

@[simp, mfld_simps]
theorem one_jet_bundle_mk_fst {x : M} {y : M'} {f : OneJetSpace I I' (x, y)} :
    (OneJetBundle.mk x y f).1 = (x, y) :=
  rfl

@[simp, mfld_simps]
theorem one_jet_bundle_mk_snd {x : M} {y : M'} {f : OneJetSpace I I' (x, y)} :
    (OneJetBundle.mk x y f).2 = f :=
  rfl

theorem smoothAt_oneJetBundle {f : N → J¹MM'} {x₀ : N} :
    SmoothAt J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) f x₀ ↔
      SmoothAt J I (fun x => (f x).1.1) x₀ ∧
        SmoothAt J I' (fun x => (f x).1.2) x₀ ∧
          SmoothAt J 𝓘(𝕜, E →L[𝕜] E')
            (inTangentCoordinates I I' (fun x => (f x).1.1) (fun x => (f x).1.2) (fun x => (f x).2)
              x₀)
            x₀ :=
  by
  simp_rw [SmoothAt, cont_mdiff_at_total_space, contMDiffAt_prod_iff, and_assoc',
    oneJetBundle_trivializationAt]
  rfl

theorem smoothAt_oneJetBundle_mk {f : N → M} {g : N → M'} {ϕ : N → E →L[𝕜] E'} {x₀ : N} :
    SmoothAt J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
        (fun x => OneJetBundle.mk (f x) (g x) (ϕ x) : N → J¹MM') x₀ ↔
      SmoothAt J I f x₀ ∧
        SmoothAt J I' g x₀ ∧ SmoothAt J 𝓘(𝕜, E →L[𝕜] E') (inTangentCoordinates I I' f g ϕ x₀) x₀ :=
  smoothAt_oneJetBundle

theorem SmoothAt.oneJetBundle_mk {f : N → M} {g : N → M'} {ϕ : N → E →L[𝕜] E'} {x₀ : N}
    (hf : SmoothAt J I f x₀) (hg : SmoothAt J I' g x₀)
    (hϕ : SmoothAt J 𝓘(𝕜, E →L[𝕜] E') (inTangentCoordinates I I' f g ϕ x₀) x₀) :
    SmoothAt J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
      (fun x => OneJetBundle.mk (f x) (g x) (ϕ x) : N → J¹MM') x₀ :=
  smoothAt_oneJetBundle.mpr ⟨hf, hg, hϕ⟩

variable (I I')

/-- The one-jet extension of a function -/
def oneJetExt (f : M → M') : M → OneJetBundle I M I' M' := fun x =>
  OneJetBundle.mk x (f x) (mfderiv I I' f x)

variable {I I'}

theorem SmoothAt.oneJetExt {f : M → M'} {x : M} (hf : SmoothAt I I' f x) :
    SmoothAt I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (oneJetExt I I' f) x :=
  smoothAt_id.oneJetBundle_mk hf (hf.mfderiv_const le_rfl)

theorem Smooth.oneJetExt {f : M → M'} (hf : Smooth I I' f) :
    Smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (oneJetExt I I' f) := fun x =>
  (hf x).SmoothAt.oneJetExt

theorem ContinuousAt.inTangentCoordinates_comp {f : N → M} {g : N → M'} {h : N → N'}
    {ϕ' : N → E' →L[𝕜] F'} {ϕ : N → E →L[𝕜] E'} {x₀ : N} (hg : ContinuousAt g x₀) :
    inTangentCoordinates I J' f h (fun x => ϕ' x ∘L ϕ x) x₀ =ᶠ[𝓝 x₀] fun x =>
      inTangentCoordinates I' J' g h ϕ' x₀ x ∘L inTangentCoordinates I I' f g ϕ x₀ x :=
  by
  refine'
    eventually_of_mem
      (hg.preimage_mem_nhds <|
        (achart H' (g x₀)).1.open_source.mem_nhds <| mem_achart_source H' (g x₀))
      fun x hx => _
  ext v
  simp_rw [Function.comp_apply, inTangentCoordinates, in_coordinates,
    ContinuousLinearMap.comp_apply]
  rw [Trivialization.symmL_continuousLinearMapAt]
  exact hx

theorem SmoothAt.clm_comp_inTangentCoordinates {f : N → M} {g : N → M'} {h : N → N'}
    {ϕ' : N → E' →L[𝕜] F'} {ϕ : N → E →L[𝕜] E'} {n : N} (hg : ContinuousAt g n)
    (hϕ' : SmoothAt J 𝓘(𝕜, E' →L[𝕜] F') (inTangentCoordinates I' J' g h ϕ' n) n)
    (hϕ : SmoothAt J 𝓘(𝕜, E →L[𝕜] E') (inTangentCoordinates I I' f g ϕ n) n) :
    SmoothAt J 𝓘(𝕜, E →L[𝕜] F') (inTangentCoordinates I J' f h (fun n => ϕ' n ∘L ϕ n) n) n :=
  (hϕ'.clm_comp hϕ).congr_of_eventuallyEq hg.inTangentCoordinates_comp

variable (I')

theorem SmoothAt.one_jet_comp {f1 : N' → M} (f2 : N' → M') {f3 : N' → N} {x₀ : N'}
    {h : ∀ x : N', OneJetSpace I' J (f2 x, f3 x)} {g : ∀ x : N', OneJetSpace I I' (f1 x, f2 x)}
    (hh : SmoothAt J' ((I'.prod J).prod 𝓘(𝕜, E' →L[𝕜] F)) (fun x => OneJetBundle.mk _ _ (h x)) x₀)
    (hg : SmoothAt J' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (fun x => OneJetBundle.mk _ _ (g x)) x₀) :
    SmoothAt J' ((I.prod J).prod 𝓘(𝕜, E →L[𝕜] F))
      (fun x => OneJetBundle.mk (f1 x) (f3 x) (h x ∘L g x) : N' → OneJetBundle I M J N) x₀ :=
  by
  rw [smoothAt_oneJetBundle_mk] at hh hg ⊢
  exact ⟨hg.1, hh.2.1, hh.2.2.clm_comp_inTangentCoordinates hg.2.1.continuousAt hg.2.2⟩

theorem Smooth.one_jet_comp {f1 : N' → M} (f2 : N' → M') {f3 : N' → N}
    {h : ∀ x : N', OneJetSpace I' J (f2 x, f3 x)} {g : ∀ x : N', OneJetSpace I I' (f1 x, f2 x)}
    (hh : Smooth J' ((I'.prod J).prod 𝓘(𝕜, E' →L[𝕜] F)) fun x => OneJetBundle.mk _ _ (h x))
    (hg : Smooth J' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) fun x => OneJetBundle.mk _ _ (g x)) :
    Smooth J' ((I.prod J).prod 𝓘(𝕜, E →L[𝕜] F))
      (fun x => OneJetBundle.mk (f1 x) (f3 x) (h x ∘L g x) : N' → OneJetBundle I M J N) :=
  fun x₀ => hh.SmoothAt.one_jet_comp I' f2 (hg x₀)

variable {I'}

theorem Smooth.one_jet_add {f : N → M} {g : N → M'} {ϕ ϕ' : ∀ x : N, OneJetSpace I I' (f x, g x)}
    (hϕ : Smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) fun x => OneJetBundle.mk _ _ (ϕ x))
    (hϕ' : Smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) fun x => OneJetBundle.mk _ _ (ϕ' x)) :
    Smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) fun x =>
      OneJetBundle.mk (f x) (g x) (ϕ x + ϕ' x) :=
  by
  intro x
  specialize hϕ x
  specialize hϕ' x
  rw [← SmoothAt, smoothAt_oneJetBundle_mk] at hϕ hϕ' ⊢
  simp_rw [inTangentCoordinates, in_coordinates, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_add]
  exact ⟨hϕ.1, hϕ.2.1, hϕ.2.2.add hϕ'.2.2⟩

variable (I' J')

/-- A useful definition to define maps between two one_jet_bundles. -/
protected def OneJetBundle.map (f : M → N) (g : M' → N')
    (Dfinv : ∀ x : M, TangentSpace J (f x) →L[𝕜] TangentSpace I x) :
    OneJetBundle I M I' M' → OneJetBundle J N J' N' := fun p =>
  OneJetBundle.mk (f p.1.1) (g p.1.2) ((mfderiv I' J' g p.1.2 ∘L p.2) ∘L Dfinv p.1.1)

variable {I' J'}

theorem OneJetBundle.map_map {f₂ : N → M₂} {f : M → N} {g₂ : N' → M₃} {g : M' → N'}
    {Dfinv : ∀ x : M, TangentSpace J (f x) →L[𝕜] TangentSpace I x}
    {Df₂inv : ∀ x : N, TangentSpace I₂ (f₂ x) →L[𝕜] TangentSpace J x} {x : J¹MM'}
    (hg₂ : MDifferentiableAt J' I₃ g₂ (g x.1.2)) (hg : MDifferentiableAt I' J' g x.1.2) :
    OneJetBundle.map J' I₃ f₂ g₂ Df₂inv (OneJetBundle.map I' J' f g Dfinv x) =
      OneJetBundle.map I' I₃ (f₂ ∘ f) (g₂ ∘ g) (fun x => Dfinv x ∘L Df₂inv (f x)) x :=
  by
  ext _; · rfl; · rfl
  dsimp only [OneJetBundle.map, OneJetBundle.mk]
  simp_rw [← ContinuousLinearMap.comp_assoc, mfderiv_comp x.1.2 hg₂ hg]

theorem OneJetBundle.map_id (x : J¹MM') :
    OneJetBundle.map I' I' id id (fun x => ContinuousLinearMap.id 𝕜 (TangentSpace I x)) x = x :=
  by
  ext _; · rfl; · rfl
  dsimp only [OneJetBundle.map, OneJetBundle.mk]
  simp_rw [mfderiv_id]
  -- note: rw fails since we have to unfold the type `bundle.pullback`
  erw [ContinuousLinearMap.id_comp]

theorem SmoothAt.oneJetBundle_map {f : M'' → M → N} {g : M'' → M' → N'} {x₀ : M''}
    {Dfinv : ∀ (z : M'') (x : M), TangentSpace J (f z x) →L[𝕜] TangentSpace I x} {k : M'' → J¹MM'}
    (hf : SmoothAt (I''.prod I) J f.uncurry (x₀, (k x₀).1.1))
    (hg : SmoothAt (I''.prod I') J' g.uncurry (x₀, (k x₀).1.2))
    (hDfinv :
      SmoothAt I'' 𝓘(𝕜, F →L[𝕜] E)
        (inTangentCoordinates J I (fun x => f x (k x).1.1) (fun x => (k x).1.1)
          (fun x => Dfinv x (k x).1.1) x₀)
        x₀)
    (hk : SmoothAt I'' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) k x₀) :
    SmoothAt I'' ((J.prod J').prod 𝓘(𝕜, F →L[𝕜] F'))
      (fun z => OneJetBundle.map I' J' (f z) (g z) (Dfinv z) (k z)) x₀ :=
  by
  rw [smoothAt_oneJetBundle] at hk 
  refine' SmoothAt.one_jet_comp _ _ _ _
  refine' SmoothAt.one_jet_comp _ _ _ _
  · refine' hk.2.1.oneJetBundle_mk (hg.comp x₀ (smooth_at_id.prod_mk hk.2.1)) _
    exact ContMDiffAt.mfderiv g (fun x => (k x).1.2) hg hk.2.1 le_rfl
  · exact hk.1.oneJetBundle_mk hk.2.1 hk.2.2
  exact (hf.comp x₀ (smooth_at_id.prod_mk hk.1)).oneJetBundle_mk hk.1 hDfinv

/-- A useful definition to define maps between two one_jet_bundles. -/
def mapLeft (f : M → N) (Dfinv : ∀ x : M, TangentSpace J (f x) →L[𝕜] TangentSpace I x) :
    J¹MM' → OneJetBundle J N I' M' := fun p => OneJetBundle.mk (f p.1.1) p.1.2 (p.2 ∘L Dfinv p.1.1)

theorem mapLeft_eq_map (f : M → N) (Dfinv : ∀ x : M, TangentSpace J (f x) →L[𝕜] TangentSpace I x) :
    mapLeft f Dfinv = OneJetBundle.map I' I' f (id : M' → M') Dfinv :=
  by
  ext x; rfl; rfl; dsimp only [OneJetBundle.map, mapLeft, one_jet_bundle_mk_snd]
  simp_rw [mfderiv_id, ContinuousLinearMap.id_comp]

theorem SmoothAt.mapLeft {f : N' → M → N} {x₀ : N'}
    {Dfinv : ∀ (z : N') (x : M), TangentSpace J (f z x) →L[𝕜] TangentSpace I x} {g : N' → J¹MM'}
    (hf : SmoothAt (J'.prod I) J f.uncurry (x₀, (g x₀).1.1))
    (hDfinv :
      SmoothAt J' 𝓘(𝕜, F →L[𝕜] E)
        (inTangentCoordinates J I (fun x => f x (g x).1.1) (fun x => (g x).1.1)
          (fun x => Dfinv x (g x).1.1) x₀)
        x₀)
    (hg : SmoothAt J' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) g x₀) :
    SmoothAt J' ((J.prod I').prod 𝓘(𝕜, F →L[𝕜] E')) (fun z => mapLeft (f z) (Dfinv z) (g z)) x₀ :=
  by simp_rw [mapLeft_eq_map]; exact hf.one_jet_bundle_map smoothAt_snd hDfinv hg

/-- The projection `J¹(E × P, F) → J¹(E, F)`. Not actually used. -/
def bundleFst : OneJetBundle (J.prod I) (N × M) I' M' → OneJetBundle J N I' M' :=
  mapLeft Prod.fst fun x => ContinuousLinearMap.inl 𝕜 F E

/-- The projection `J¹(P × E, F) → J¹(E, F)`. -/
def bundleSnd : OneJetBundle (J.prod I) (N × M) I' M' → J¹MM' :=
  mapLeft Prod.snd fun x => mfderiv I (J.prod I) (fun y => (x.1, y)) x.2

theorem bundleSnd_eq (x : OneJetBundle (J.prod I) (N × M) I' M') :
    bundleSnd x = mapLeft Prod.snd (fun x => ContinuousLinearMap.inr 𝕜 F E) x := by
  simp_rw [bundleSnd, mfderiv_prod_right]; rfl

theorem smooth_bundleSnd :
    Smooth (((J.prod I).prod I').prod 𝓘(𝕜, F × E →L[𝕜] E')) ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
      (bundleSnd : OneJetBundle (J.prod I) (N × M) I' M' → J¹MM') :=
  by
  intro x₀
  refine' SmoothAt.mapLeft _ _ smoothAt_id
  · exact smooth_at_snd.snd
  have :
    ContMDiffAt (((J.prod I).prod I').prod 𝓘(𝕜, F × E →L[𝕜] E')) 𝓘(𝕜, E →L[𝕜] F × E) ∞
      (inTangentCoordinates I (J.prod I) _ _ _ x₀) x₀ :=
    ContMDiffAt.mfderiv (fun (x : OneJetBundle (J.prod I) (N × M) I' M') (y : M) => (x.1.1.1, y))
      (fun x : OneJetBundle (J.prod I) (N × M) I' M' => x.1.1.2) _ _ le_top
  exact this
  · exact (smooth_one_jet_bundle_proj.fst.fst.prod_map smooth_id).SmoothAt
  -- slow
  · exact smooth_one_jet_bundle_proj.fst.snd.smooth_at

-- slow
end Maps

-- move
theorem localEquiv_eq_equiv {α β} {f : LocalEquiv α β} {e : α ≃ β} (h1 : ∀ x, f x = e x)
    (h2 : f.source = univ) (h3 : f.target = univ) : f = e.toLocalEquiv :=
  by
  refine' LocalEquiv.ext h1 (fun y => _) h2
  conv_rhs => rw [← f.right_inv ((set.ext_iff.mp h3 y).mpr (mem_univ y)), h1]
  exact (e.left_inv _).symm

local notation "𝓜" => ModelProd (ModelProd H H') (E →L[𝕜] E')

/-- In the one_jet bundle to the model space, the charts are just the canonical identification
between a product type and a bundle total space type, a.k.a. ` bundle.total_space.to_prod`. -/
@[simp, mfld_simps]
theorem oneJetBundle_model_space_chartAt (p : OneJetBundle I H I' H') :
    (chartAt 𝓜 p).toLocalEquiv = (Bundle.TotalSpace.toProd (H × H') (E →L[𝕜] E')).toLocalEquiv :=
  by
  apply localEquiv_eq_equiv
  · intro x
    rw [LocalHomeomorph.coe_coe, oneJetBundle_chartAt_apply p x,
      inCoordinates_tangent_bundle_core_model_space]
    ext <;> rfl
  · simp_rw [oneJetBundle_chart_source, prodChartedSpace_chartAt, chartAt_self_eq,
      LocalHomeomorph.refl_prod_refl]
    rfl
  · simp_rw [oneJetBundle_chart_target, prodChartedSpace_chartAt, chartAt_self_eq,
      LocalHomeomorph.refl_prod_refl]
    rfl

@[simp, mfld_simps]
theorem oneJetBundle_model_space_coe_chartAt (p : OneJetBundle I H I' H') :
    ⇑(chartAt 𝓜 p) = Bundle.TotalSpace.toProd (H × H') (E →L[𝕜] E') := by unfold_coes;
  simp only [mfld_simps]

@[simp, mfld_simps]
theorem oneJetBundle_model_space_coe_chartAt_symm (p : OneJetBundle I H I' H') :
    ((chartAt 𝓜 p).symm : 𝓜 → OneJetBundle I H I' H') =
      (Bundle.TotalSpace.toProd (H × H') (E →L[𝕜] E')).symm :=
  by unfold_coes; simp only [mfld_simps]

variable (I I')

-- note: this proof works for all vector bundles where we have proven
-- `∀ p, chart_at _ p = f.to_local_equiv`
/-- The canonical identification between the one_jet bundle to the model space and the product,
as a homeomorphism -/
def oneJetBundleModelSpaceHomeomorph : OneJetBundle I H I' H' ≃ₜ 𝓜 :=
  {
    Bundle.TotalSpace.toProd (H × H')
      (E →L[𝕜]
        E') with
    continuous_toFun :=
      by
      let p : OneJetBundle I H I' H' := ⟨(I.symm (0 : E), I'.symm (0 : E')), 0⟩
      have : Continuous (chart_at 𝓜 p) :=
        by
        rw [continuous_iff_continuousOn_univ]
        convert LocalHomeomorph.continuousOn _
        simp only [mfld_simps]
      simpa only [mfld_simps] using this
    continuous_invFun :=
      by
      let p : OneJetBundle I H I' H' := ⟨(I.symm (0 : E), I'.symm (0 : E')), 0⟩
      have : Continuous (chart_at 𝓜 p).symm :=
        by
        rw [continuous_iff_continuousOn_univ]
        convert LocalHomeomorph.continuousOn _
        simp only [mfld_simps]
      simpa only [mfld_simps] using this }

-- unused
@[simp, mfld_simps]
theorem oneJetBundleModelSpaceHomeomorph_coe :
    (oneJetBundleModelSpaceHomeomorph I I' : OneJetBundle I H I' H' → 𝓜) =
      Bundle.TotalSpace.toProd (H × H') (E →L[𝕜] E') :=
  rfl

-- unused
@[simp, mfld_simps]
theorem oneJetBundleModelSpaceHomeomorph_coe_symm :
    ((oneJetBundleModelSpaceHomeomorph I I').symm : 𝓜 → OneJetBundle I H I' H') =
      (Bundle.TotalSpace.toProd (H × H') (E →L[𝕜] E')).symm :=
  rfl

