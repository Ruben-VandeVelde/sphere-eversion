import Mathbin.Analysis.Convex.Hull
import Mathbin.Data.Real.Basic
import Mathbin.Topology.Connected
import Mathbin.Topology.PathConnected
import Mathbin.Topology.Algebra.Affine
import Mathbin.LinearAlgebra.Dimension
import Mathbin.LinearAlgebra.AffineSpace.Midpoint
import Mathbin.Data.Matrix.Notation
import Mathbin.Analysis.Convex.Topology
import Project.ToMathlib.Topology.Misc

/-!
# Ample subsets of real vector spaces

In this file we study ample set in real vector spaces. A set is ample if all its connected
component have full convex hull. We then prove this property is invariant under a number of affine
geometric operations.

As trivial examples, the empty set and the univ set are ample. After proving those fact,
the second part of the file proves that a linear subspace with codimension at least 2 has a
ample complement. This is the crucial geometric ingredient which allows to apply convex integration
to the theory of immersions in positive codimension.

All vector spaces in the file (and more generally in this folder) are real vector spaces.

## Implementation notes

The definition of ample subset asks for a vector space structure and a topology on the ambiant type
without any link between those structures, but we will only be using these for finite dimensional
vector spaces with their natural topology.
-/


/-! ## Definition and invariance -/


open Set AffineMap

open scoped Convex Matrix

variable {E F : Type _} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A subset of a topological real vector space is ample if the convex hull of each of its
connected components is the full space. -/
def AmpleSet (s : Set F) : Prop :=
  ∀ x ∈ s, convexHull ℝ (connectedComponentIn s x) = univ

/-- images of ample sets under continuous linear equivalences are ample. -/
theorem AmpleSet.image {s : Set E} (h : AmpleSet s) (L : E ≃L[ℝ] F) : AmpleSet (L '' s) :=
  by
  intro x hx
  rw [L.image_eq_preimage] at hx 
  have : L '' connectedComponentIn s (L.symm x) = connectedComponentIn (L '' s) x :=
    by
    conv_rhs => rw [← L.apply_symm_apply x]
    exact L.to_homeomorph.image_connected_component_in hx
  rw [← this]
  refine' (L.to_linear_equiv.to_linear_map.convex_hull_image _).trans _
  rw [h (L.symm x) hx, image_univ]
  exact L.to_linear_equiv.to_equiv.range_eq_univ

-- unused
/-- preimages of ample sets under continuous linear equivalences are ample. -/
theorem AmpleSet.preimage {s : Set F} (h : AmpleSet s) (L : E ≃L[ℝ] F) : AmpleSet (L ⁻¹' s) := by
  rw [← L.image_symm_eq_preimage]; exact h.image L.symm

open scoped Pointwise

/-- Translating a ample set is ample.
We basically mimic `ample_set.image`. We could prove the common generalization using
continuous affine equivalences -/
theorem AmpleSet.vadd [ContinuousAdd E] {s : Set E} (h : AmpleSet s) {y : E} : AmpleSet (y +ᵥ s) :=
  by
  intro x hx
  simp_rw [mem_vadd_set] at hx 
  obtain ⟨x, hx, rfl⟩ := hx
  have : y +ᵥ connectedComponentIn s x = connectedComponentIn (y +ᵥ s) (y +ᵥ x) :=
    (Homeomorph.addLeft y).image_connectedComponentIn hx
  rw [← this]
  refine' ((AffineEquiv.constVAdd ℝ E y).toAffineMap.image_convexHull _).symm.trans _
  rw [h x hx, image_univ]
  exact (AffineEquiv.toEquiv _).range_eq_univ

/-! ## Trivial examples -/


/-- A whole vector space is ample. -/
theorem ampleSet_univ {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    AmpleSet (univ : Set F) := by
  intro x _
  rw [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ, convexHull_univ]

-- unused
/-- The empty set in a vector space is ample. -/
theorem ampleSet_empty {F : Type _} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] :
    AmpleSet (∅ : Set F) := fun _ h => False.elim h

/-! ## Codimension at least 2 subspaces have ample complement. -/


section Lemma213

local notation "π" => Submodule.linearProjOfIsCompl _ _

attribute [local instance 100] TopologicalAddGroup.pathConnectedSpace

/-- Given two complementary subspaces `p` and `q` in `F`, if the complement of `{0}`
is path connected in `p` then the complement of `q` is path connected in `F`. -/
theorem isPathConnected_compl_of_isPathConnected_compl_zero [TopologicalAddGroup F]
    [ContinuousSMul ℝ F] {p q : Submodule ℝ F} (hpq : IsCompl p q)
    (hpc : IsPathConnected ({0}ᶜ : Set p)) : IsPathConnected (qᶜ : Set F) :=
  by
  rw [isPathConnected_iff] at hpc ⊢
  constructor
  · rcases hpc.1 with ⟨a, ha⟩
    exact ⟨a, mt (Submodule.eq_zero_of_coe_mem_of_disjoint hpq.disjoint) ha⟩
  · intro x hx y hy
    have : π hpq x ≠ 0 ∧ π hpq y ≠ 0 := by
      constructor <;> intro h <;> rw [Submodule.linearProjOfIsCompl_apply_eq_zero_iff hpq] at h  <;>
        [exact hx h; exact hy h]
    rcases hpc.2 (π hpq x) this.1 (π hpq y) this.2 with ⟨γ₁, hγ₁⟩
    let γ₂ := PathConnectedSpace.somePath (π hpq.symm x) (π hpq.symm y)
    let γ₁' : Path (_ : F) _ := γ₁.map continuous_subtype_val
    let γ₂' : Path (_ : F) _ := γ₂.map continuous_subtype_val
    refine'
      ⟨(γ₁'.add γ₂').cast (Submodule.linear_proj_add_linearProjOfIsCompl_eq_self hpq x).symm
          (Submodule.linear_proj_add_linearProjOfIsCompl_eq_self hpq y).symm,
        _⟩
    intro t
    rw [Path.cast_coe, Path.add_apply]
    change (γ₁ t : F) + (γ₂ t : F) ∉ q
    rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hpq, LinearMap.map_add,
      Submodule.linearProjOfIsCompl_apply_right hpq, add_zero,
      Submodule.linearProjOfIsCompl_apply_eq_zero_iff hpq]
    exact mt (Submodule.eq_zero_of_coe_mem_of_disjoint hpq.disjoint) (hγ₁ t)

/-- For `x` and `y` in a real vector space, if `x ≠ 0` and `0` is in the segment from
`x` to `y` then `y` is on the line spanned by `x`.  -/
theorem mem_span_of_zero_mem_segment {F : Type _} [AddCommGroup F] [Module ℝ F] {x y : F}
    (hx : x ≠ 0) (h : (0 : F) ∈ [x -[ℝ] y]) : y ∈ Submodule.span ℝ ({x} : Set F) :=
  by
  rw [segment_eq_image] at h 
  rcases h with ⟨t, ht, htxy⟩
  rw [Submodule.mem_span_singleton]
  dsimp only at htxy 
  use (t - 1) / t
  have : t ≠ 0 := by
    intro h
    rw [h] at htxy 
    refine' hx _
    simpa using htxy
  rw [← smul_eq_zero_iff_eq' (neg_ne_zero.mpr <| inv_ne_zero this), smul_add, smul_smul, smul_smul,
    ← neg_one_mul, mul_assoc, mul_assoc, inv_mul_cancel this, mul_one, neg_one_smul,
    add_neg_eq_zero] at htxy 
  convert htxy
  ring

variable [TopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- For `x` and `y` in a real vector space, if `x ≠ 0` and `y` is not on the line
spanned by `x` then `x` and `y` can be joined by a path in the complement of `{0}`.  -/
theorem joinedIn_compl_zero_of_not_mem_span {x y : F} (hx : x ≠ 0)
    (hy : y ∉ Submodule.span ℝ ({x} : Set F)) : JoinedIn ({0}ᶜ : Set F) x y :=
  by
  refine'
    JoinedIn.ofLine line_map_continuous.continuous_on (line_map_apply_zero _ _)
      (line_map_apply_one _ _) _
  rw [← segment_eq_image_lineMap]
  exact fun t ht (h' : t = 0) => (mt (mem_span_of_zero_mem_segment hx) hy) (h' ▸ ht)

/-- In a vector space whose dimension is at least 2, the complement of
`{0}` is ample. -/
theorem isPathConnected_compl_zero_of_two_le_dim (hdim : 2 ≤ Module.rank ℝ F) :
    IsPathConnected ({0}ᶜ : Set F) :=
  by
  rw [isPathConnected_iff]
  constructor
  · suffices 0 < Module.rank ℝ F by rwa [rank_pos_iff_exists_ne_zero] at this 
    exact lt_of_lt_of_le (by norm_num) hdim
  · intro x hx y hy
    by_cases h : y ∈ Submodule.span ℝ ({x} : Set F)
    · suffices ∃ z, z ∉ Submodule.span ℝ ({x} : Set F)
        by
        rcases this with ⟨z, hzx⟩
        have hzy : z ∉ Submodule.span ℝ ({y} : Set F) := fun h' =>
          hzx (Submodule.mem_span_singleton_trans h' h)
        exact
          (joinedIn_compl_zero_of_not_mem_span hx hzx).trans
            (joinedIn_compl_zero_of_not_mem_span hy hzy).symm
      by_contra h'
      push_neg at h' 
      rw [← Submodule.eq_top_iff'] at h' 
      rw [← rank_top ℝ, ← h'] at hdim 
      suffices : (2 : Cardinal) ≤ 1
      exact not_le_of_lt (by norm_num) this
      have := hdim.trans (rank_span_le _)
      rwa [Cardinal.mk_singleton] at this 
    · exact joinedIn_compl_zero_of_not_mem_span hx h

/-- Let `E` be a linear subspace in a real vector space. If `E` has codimension at
least two then its complement is path-connected. -/
theorem isPathConnected_compl_of_two_le_codim {E : Submodule ℝ F}
    (hcodim : 2 ≤ Module.rank ℝ (F ⧸ E)) : IsPathConnected (Eᶜ : Set F) :=
  by
  rcases E.exists_is_compl with ⟨E', hE'⟩
  refine' isPathConnected_compl_of_isPathConnected_compl_zero hE'.symm _
  refine' isPathConnected_compl_zero_of_two_le_dim _
  rwa [← (E.quotient_equiv_of_is_compl E' hE').rank_eq]

/-- Let `E` be a linear subspace in a real vector space. If `E` has codimension at
least two then its complement is connected. -/
theorem isConnected_compl_of_two_le_codim {E : Submodule ℝ F} (hcodim : 2 ≤ Module.rank ℝ (F ⧸ E)) :
    IsConnected (Eᶜ : Set F) :=
  (isPathConnected_compl_of_two_le_codim hcodim).IsConnected

theorem Submodule.connectedComponentIn_eq_self_of_two_le_codim (E : Submodule ℝ F)
    (hcodim : 2 ≤ Module.rank ℝ (F ⧸ E)) {x : F} (hx : x ∉ E) :
    connectedComponentIn ((E : Set F)ᶜ) x = Eᶜ :=
  IsPreconnected.connectedComponentIn (isConnected_compl_of_two_le_codim hcodim).2 hx

/-- Let `E` be a linear subspace in a real vector space. If `E` has codimension at
least two then its complement is ample. -/
theorem ample_of_two_le_codim {E : Submodule ℝ F} (hcodim : 2 ≤ Module.rank ℝ (F ⧸ E)) :
    AmpleSet (Eᶜ : Set F) := by
  intro x hx
  rw [E.connected_component_in_eq_self_of_two_le_codim hcodim hx, eq_univ_iff_forall]
  intro y
  by_cases h : y ∈ E
  · rcases E.exists_is_compl with ⟨E', hE'⟩
    rw [(E.quotient_equiv_of_is_compl E' hE').rank_eq] at hcodim 
    have hcodim' : 0 < Module.rank ℝ E' := lt_of_lt_of_le (by norm_num) hcodim
    rw [rank_pos_iff_exists_ne_zero] at hcodim' 
    rcases hcodim' with ⟨z, hz⟩
    have : y ∈ [y + -z -[ℝ] y + z] := by
      rw [← sub_eq_add_neg]
      exact mem_segment_sub_add y z
    refine' (convex_convexHull ℝ (Eᶜ : Set F)).segment_subset _ _ this <;>
              refine' subset_convexHull ℝ (Eᶜ : Set F) _ <;>
            change _ ∉ E <;>
          rw [Submodule.add_mem_iff_right _ h] <;>
        try rw [Submodule.neg_mem_iff] <;>
      exact mt (Submodule.eq_zero_of_coe_mem_of_disjoint hE'.symm.disjoint) hz
  · exact subset_convexHull ℝ (Eᶜ : Set F) h

end Lemma213

