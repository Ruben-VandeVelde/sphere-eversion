import analysis.calculus.bump_function_inner
import topology.metric_space.hausdorff_distance

import local.one_jet

/-!
# Local partial differential relations and their formal solutions

This file defines `rel_loc E F`, the type of first order partial differential relations
for maps between two real normed spaces `E` and `F`.

To any `R : rel_loc E F` we associate the type `sol R` of maps `f : E → F` of
solutions of `R`, and its formal counterpart `formal_sol R`.

The h-principle question is whether we can deform any formal solution into a solution.
The type of deformations is `htpy_jet_sec E F` (homotopies of 1-jet sections).
-/

noncomputable theory

open set function real filter
open_locale unit_interval topology

variables (E : Type*) [normed_add_comm_group E] [normed_space ℝ E]
variables (F : Type*) [normed_add_comm_group F] [normed_space ℝ F]
variables (P : Type*) [normed_add_comm_group P] [normed_space ℝ P]

/-- A first order relation for maps between real vector spaces. -/
def rel_loc := set (one_jet E F)

instance : has_mem (E × F × (E →L[ℝ] F)) (rel_loc E F) := set.has_mem


variables {E F}

/-- A predicate stating that a 1-jet section is a formal solution to a first order relation for
maps between vector spaces. -/
def jet_sec.is_formal_sol (𝓕 : jet_sec E F) (R : rel_loc E F) : Prop :=
∀ x, (x, 𝓕.f x, 𝓕.φ x) ∈ R

namespace rel_loc

/-- A formal solution to a local relation `R`. -/
@[ext] structure formal_sol (R : rel_loc E F) extends jet_sec E F :=
(is_sol : ∀ x, (x, f x, φ x) ∈ R)

instance (R : rel_loc E F) : has_coe (formal_sol R) (jet_sec E F):=
⟨formal_sol.to_jet_sec⟩

@[simp] lemma formal_sol.to_jet_sec_eq_coe {R : rel_loc E F} (𝓕 : formal_sol R) :
𝓕.to_jet_sec = (𝓕 : jet_sec E F) := rfl

@[simp] lemma formal_sol.coe_is_formal_sol  {R : rel_loc E F} (𝓕 : formal_sol R) :
  (𝓕 : jet_sec E F).is_formal_sol R := 𝓕.is_sol

/-- Bundling a formal solution from a 1-jet section that is a formal solution. -/
def _root_.jet_sec.is_formal_sol.formal_sol  {𝓕 : jet_sec E F} {R : rel_loc E F}
  (h : 𝓕.is_formal_sol R) : formal_sol R :=
{is_sol := h, ..𝓕}

instance (R : rel_loc E F) : has_coe_to_fun (formal_sol R) (λ S, E → F × (E →L[ℝ] F)) :=
⟨λ 𝓕, λ x, (𝓕.f x, 𝓕.φ x)⟩

@[simp] lemma formal_sol.coe_apply  {R : rel_loc E F} (𝓕 : formal_sol R) (x : E) :
(𝓕 : jet_sec E F) x = 𝓕 x := rfl

variables  {R : rel_loc E F}

lemma formal_sol.eq_iff {𝓕 𝓕' : formal_sol R} {x : E} :
  𝓕 x = 𝓕' x ↔ 𝓕.f x = 𝓕'.f x ∧ 𝓕.φ x = 𝓕'.φ x :=
jet_sec.eq_iff

/-- A formal solution (f, φ) is holonomic at `x` if the differential of `f` at `x` is `φ x`. -/
def formal_sol.is_holonomic_at (𝓕 : formal_sol R) (x : E) : Prop := D 𝓕.f x = 𝓕.φ x

-- TODO: this should come from a lemma about `jet_sec`
lemma formal_sol.is_holonomic_at_congr (𝓕 𝓕' : formal_sol R) {s : set E}
  (h : ∀ᶠ x near s, 𝓕 x = 𝓕' x) : ∀ᶠ x near s, 𝓕.is_holonomic_at x ↔ 𝓕'.is_holonomic_at x :=
begin
  apply h.eventually_nhds_set.mono,
  intros x hx,
  have hf : 𝓕.f =ᶠ[𝓝 x] 𝓕'.f,
  { apply hx.mono,
    simp_rw rel_loc.formal_sol.eq_iff,
    tauto },
  unfold rel_loc.formal_sol.is_holonomic_at,
  rw [hf.fderiv_eq, (rel_loc.formal_sol.eq_iff.mp hx.self_of_nhds).2]
end

variable (P)
/-- A family of formal solutions is a 1-parameter family of formal solutions. -/
@[ext] structure family_formal_sol (R : rel_loc E F) extends family_jet_sec E F P :=
(is_sol : ∀ t x, (x, f t x, φ t x) ∈ R)

/-- A homotopy of formal solutions is a 1-parameter family of formal solutions. -/
@[reducible] def htpy_formal_sol (R : rel_loc E F) := R.family_formal_sol ℝ

def htpy_formal_sol.to_htpy_jet_sec {R : rel_loc E F} (𝓕 : R.htpy_formal_sol) : htpy_jet_sec E F :=
𝓕.to_family_jet_sec

open rel_loc

instance (R : rel_loc E F) : has_coe_to_fun (family_formal_sol P R) (λ S, P → jet_sec E F) :=
⟨λ S t,
 { f := S.f t,
   f_diff := S.f_diff.comp (cont_diff_const.prod cont_diff_id),
   φ := S.φ t,
   φ_diff := S.φ_diff.comp (cont_diff_const.prod cont_diff_id) }⟩

end rel_loc
