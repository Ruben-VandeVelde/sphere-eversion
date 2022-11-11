import geometry.manifold.partition_of_unity
import topology.metric_space.emetric_paracompact

import to_mathlib.topology.nhds_set

open set filter
open_locale manifold topological_space

lemma exists_cont_diff_zero_one {E : Type*} [normed_add_comm_group E]
  [normed_space ℝ E] [finite_dimensional ℝ E] {s t : set E} (hs : is_closed s)
  (ht : is_closed t) (hd : disjoint s t) :
  ∃ f : E → ℝ, cont_diff ℝ ⊤ f ∧ eq_on f 0 s ∧ eq_on f 1 t ∧
    ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
let ⟨f, hfs, hft, hf01⟩ := exists_smooth_zero_one_of_closed 𝓘(ℝ, E) hs ht hd
in ⟨f, f.smooth.cont_diff, hfs, hft, hf01⟩

lemma exists_cont_diff_zero_one_nhds {E : Type*} [normed_add_comm_group E]
  [normed_space ℝ E] [finite_dimensional ℝ E] {s t : set E} (hs : is_closed s)
  (ht : is_closed t) (hd : disjoint s t) :
  ∃ f : E → ℝ, cont_diff ℝ ⊤ f ∧ (∀ᶠ x in 𝓝ˢ s, f x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, f x = 1) ∧
    ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
begin
  rcases normal_exists_closure_subset hs ht.is_open_compl
    (subset_compl_iff_disjoint_left.mpr hd.symm) with ⟨u, u_op, hsu, hut⟩,
  have hcu : is_closed (closure u) := is_closed_closure,
  rcases normal_exists_closure_subset ht hcu.is_open_compl (subset_compl_comm.mp hut) with
    ⟨v, v_op, htv, hvu⟩,
  have hcv : is_closed (closure v) := is_closed_closure,
  rcases exists_cont_diff_zero_one hcu hcv (subset_compl_iff_disjoint_left.mp hvu) with
    ⟨f, hfsmooth, hfu, hfv, hf⟩,
  refine ⟨f, hfsmooth, _, _, hf⟩,
  apply eventually_of_mem (mem_of_superset (u_op.mem_nhds_set.mpr hsu) subset_closure) hfu,
  apply eventually_of_mem (mem_of_superset (v_op.mem_nhds_set.mpr htv) subset_closure) hfv
end

lemma exists_cont_diff_one_nhds_of_interior {E : Type*} [normed_add_comm_group E]
  [normed_space ℝ E] [finite_dimensional ℝ E] {s t : set E} (hs : is_closed s)
  (hd : s ⊆ interior t) :
  ∃ f : E → ℝ, cont_diff ℝ ⊤ f ∧ (∀ᶠ x in 𝓝ˢ s, f x = 1) ∧ (∀ x ∉ t, f x = 0) ∧
    ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
begin
  have : is_closed (interior t)ᶜ,
  exact is_open_interior.is_closed_compl,

  rcases exists_cont_diff_zero_one_nhds this hs _ with ⟨f, hfsmooth, h0, h1, hf⟩,
  { refine ⟨f, hfsmooth, h1, _, hf⟩,
    intros x hx,
    exact h0.on_set _ (λ hx', hx $ interior_subset hx') },
  rwa [← subset_compl_iff_disjoint_left, compl_compl]
end

lemma exists_interpolation_of_interior {E : Type*} [normed_add_comm_group E]
  [normed_space ℝ E] [finite_dimensional ℝ E]
  {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
  {s t : set E} (hs : is_closed s)
  (hd : s ⊆ interior t) {f g : E → F} {n : ℕ∞} (hf : cont_diff ℝ n f) (hg : cont_diff ℝ n g) :
  ∃ h : E → F, cont_diff ℝ n h ∧
               (∀ᶠ x in 𝓝ˢ s, h x = f x) ∧
               (∀ x ∉ t, h x = g x) ∧
               (∀ x, h x ∈ segment ℝ (f x) (g x)) :=
begin
  rcases exists_cont_diff_one_nhds_of_interior hs hd with ⟨ρ, ρ_diff, ρs, ρt, ρ_mem⟩,
  replace ρ_diff : cont_diff ℝ n ρ, from ρ_diff.of_le le_top,
  refine ⟨λ x, ρ x • f x + (1 - ρ x) • g x, _, _, _, _⟩,
  { exact (ρ_diff.smul hf).add ((cont_diff_const.sub ρ_diff).smul hg) },
  { apply ρs.mono,
    intros x hx,
    simp [hx] },
  { intros x hx,
    simp [ρt x hx] },
  { exact λ x, ⟨ρ x, 1 - ρ x, (ρ_mem x).1, by simp [(ρ_mem x).2], by simp, rfl⟩ },
end
