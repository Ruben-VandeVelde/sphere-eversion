import SphereEversion.ToMathlib.Data.Set.Prod
import SphereEversion.ToMathlib.Data.Set.Lattice
import SphereEversion.ToMathlib.Topology.Constructions
import SphereEversion.ToMathlib.Topology.Germ
import SphereEversion.ToMathlib.Topology.Misc
import SphereEversion.ToMathlib.Order.Filter.Basic
import SphereEversion.Indexing
import SphereEversion.Notations
-- import SphereEversion.InteractiveExpr
-- import Mathlib.Tactic.Induction

-- set_option trace.filter_inst_type true

open Set Filter Prod TopologicalSpace Function

open scoped Topology unitInterval

/-!
Notes by Patrick:

The goal of this file is to explore how to prove `exists_surrounding_loops` and the local to global
inductive homotopy construction in a way that uncouples the general
topological argument from the things specific to loops or homotopies of jet sections.

First there is a lemma `inductive_construction` which abstracts the locally ultimately constant
arguments, assuming we work with a fixed covering. It builds on
`locally_finite.exists_forall_eventually_of_index_type`.

From `inductive_construction` alone we deduce `inductive_htpy_construction` which builds a homotopy
in a similar context. This is meant to be used to go from Chapter 2 to Chapter 3.

Combining `inductive_construction` with an argument using local existence and exhaustions, we
get `inductive_construction_of_loc` building a function from local existence and patching
assumptions. It also has a version `relative_inductive_construction_of_loc` which does this
relative to a closed set. This is used for `exists_surrounding_loops`.

This file also contains supporting lemmas about `index_type`. A short term goal will be to
get rid of the `indexing` abstraction and do everything in terms of `index_type`, unless
`indexing` makes those supporting lemmas really cleaner to prove.
-/


section inductive_construction

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » V n.succ) -/
theorem LocallyFinite.exists_forall_eventually_of_indexType {α X : Type _} [TopologicalSpace X]
    {N : ℕ} {f : IndexType N → X → α} {V : IndexType N → Set X} (hV : LocallyFinite V)
    (h : ∀ n : IndexType N, ¬IsMax n → ∀ (x) (_ : x ∉ V n.succ), f n.succ x = f n x) :
    ∃ F : X → α, ∀ x : X, ∀ᶠ n in Filter.atTop, f n =ᶠ[𝓝 x] F :=
  by
  choose U hUx hU using hV
  choose i₀ hi₀ using fun x => (hU x).bddAbove
  have key : ∀ {x} {n}, n ≥ i₀ x → ∀ {y}, y ∈ U x → f n y = f (i₀ x) y :=
    by
    intro x
    apply @IndexType.induction_from N fun i => ∀ {y}, y ∈ U x → f i y = f (i₀ x) y
    exact fun _ _ => rfl
    intro i hi h'i ih y hy
    rw [h i h'i, ih hy]
    intro h'y
    replace hi₀ := mem_upper_bounds.mp (hi₀ x) i.succ ⟨y, h'y, hy⟩
    exact lt_irrefl _ (((i.lt_succ h'i).trans_le hi₀).trans_le hi)
  refine' ⟨fun x => f (i₀ x) x, fun x => _⟩
  apply (eventually_ge_atTop (i₀ x)).mono fun n hn => _
  apply mem_of_superset (hUx x) fun y hy => _
  calc
    f n y = f (i₀ x) y := key hn hy
    _ = f (max (i₀ x) (i₀ y)) y := (key (le_max_left _ _) hy).symm
    _ = f (i₀ y) y := key (le_max_right _ _) (mem_of_mem_nhds <| hUx y)

local notation "𝓘" => IndexType

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » U n.succ) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » U i) -/
theorem inductive_construction {X Y : Type _} [TopologicalSpace X] {N : ℕ} {U : IndexType N → Set X}
    (P₀ : ∀ x : X, Germ (𝓝 x) Y → Prop) (P₁ : ∀ i : IndexType N, ∀ x : X, Germ (𝓝 x) Y → Prop)
    (P₂ : IndexType N → (X → Y) → Prop) (U_fin : LocallyFinite U)
    (init : ∃ f : X → Y, (∀ x, P₀ x f) ∧ P₂ 0 f)
    (ind :
      ∀ (i : IndexType N) (f : X → Y),
        (∀ x, P₀ x f) →
          P₂ i f →
            (∀ j < i, ∀ x, P₁ j x f) →
              ∃ f' : X → Y,
                (∀ x, P₀ x f') ∧
                  (¬IsMax i → P₂ i.succ f') ∧
                    (∀ j ≤ i, ∀ x, P₁ j x f') ∧ ∀ (x) (_ : x ∉ U i), f' x = f x) :
    ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ j, ∀ x, P₁ j x f :=
  by
  let P : 𝓘 N → (X → Y) → Prop := fun n f =>
    (∀ x, P₀ x f) ∧ (¬IsMax n → P₂ n.succ f) ∧ ∀ j ≤ n, ∀ x, P₁ j x f
  let Q : 𝓘 N → (X → Y) → (X → Y) → Prop := fun n f f' => ∀ (x) (_ : x ∉ U n.succ), f' x = f x
  obtain ⟨f, hf⟩ : ∃ f : 𝓘 N → X → Y, ∀ n, P n (f n) ∧ (¬IsMax n → Q n (f n) (f n.succ)) :=
    by
    apply IndexType.exists_by_induction
    · rcases init with ⟨f₀, h₀f₀, h₁f₀⟩
      rcases ind 0 f₀ h₀f₀ h₁f₀ (by simp [IndexType.not_lt_zero]) with ⟨f', h₀f', h₂f', h₁f', hf'⟩
      exact ⟨f', h₀f', h₂f', h₁f'⟩
    · rintro n f ⟨h₀f, h₂f, h₁f⟩ hn
      by_cases hn : IsMax n
      · simp only [P, Q, n.succ_eq.mpr hn]
        exact ⟨f, ⟨h₀f, fun hn' => (hn' hn).elim, h₁f⟩, fun _ _ => rfl⟩
      rcases ind _ f h₀f (h₂f hn) fun j hj => h₁f _ <| j.le_of_lt_succ hj with
        ⟨f', h₀f', h₂f', h₁f', hf'⟩
      exact ⟨f', ⟨h₀f', h₂f', h₁f'⟩, hf'⟩
  dsimp only [P, Q] at hf 
  simp only [forall_and] at hf 
  rcases hf with ⟨⟨h₀f, h₂f, h₁f⟩, hfU⟩
  rcases U_fin.exists_forall_eventually_of_index_type hfU with ⟨F, hF⟩
  refine' ⟨F, fun x => _, fun j => _⟩
  · rcases(hF x).exists with ⟨n₀, hn₀⟩
    simp only [germ.coe_eq.mpr hn₀.symm, h₀f n₀ x]
  intro x
  rcases((hF x).And <| eventually_ge_atTop j).exists with ⟨n₀, hn₀, hn₀'⟩
  exact eventually.germ_congr (h₁f _ _ hn₀' x) hn₀.symm

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » U i) -/
/-- We are given a suitably nice extended metric space `X` and three local constraints `P₀`,`P₀'`
and `P₁` on maps from `X` to some type `Y`. All maps entering the discussion are required to
statisfy `P₀` everywhere. The goal is to turn a map `f₀` satisfying `P₁` near a compact set `K` into
one satisfying everywhere without changing `f₀` near `K`. The assumptions are:
* For every `x` in `X` there is a map which satisfies `P₁` near `x`
* One can patch two maps `f₁ f₂` satisfying `P₁` on open sets `U₁` and `U₂` respectively
  and such that `f₁` satisfies `P₀'` everywhere into a map satisfying `P₁` on `K₁ ∪ K₂` for any
  compact sets `Kᵢ ⊆ Uᵢ` and `P₀'` everywhere. -/
theorem inductive_construction_of_loc {X Y : Type _} [EMetricSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (P₀ P₀' P₁ : ∀ x : X, Germ (𝓝 x) Y → Prop) {f₀ : X → Y}
    (hP₀f₀ : ∀ x, P₀ x f₀ ∧ P₀' x f₀)
    (loc : ∀ x, ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ᶠ x' in 𝓝 x, P₁ x' f)
    (ind :
      ∀ {U₁ U₂ K₁ K₂ : Set X} {f₁ f₂ : X → Y},
        IsOpen U₁ →
          IsOpen U₂ →
            IsClosed K₁ →
              IsClosed K₂ →
                K₁ ⊆ U₁ →
                  K₂ ⊆ U₂ →
                    (∀ x, P₀ x f₁ ∧ P₀' x f₁) →
                      (∀ x, P₀ x f₂) →
                        (∀ x ∈ U₁, P₁ x f₁) →
                          (∀ x ∈ U₂, P₁ x f₂) →
                            ∃ f : X → Y,
                              (∀ x, P₀ x f ∧ P₀' x f) ∧
                                (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ ∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x) :
    ∃ f : X → Y, ∀ x, P₀ x f ∧ P₀' x f ∧ P₁ x f :=
  by
  let P : Set X → Prop := fun U => ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ x ∈ U, P₁ x f
  have hP₁ : Antitone P := by
    rintro U V hUV ⟨f, h, h'⟩
    exact ⟨f, h, fun x hx => h' x (hUV hx)⟩
  have hP₂ : P ∅ := ⟨f₀, fun x => (hP₀f₀ x).1, fun x h => h.elim⟩
  have hP₃ : ∀ x : X, x ∈ univ → ∃ (V : Set X) (H : V ∈ 𝓝 x), P V :=
    by
    rintro x -
    rcases loc x with ⟨f, h₀f, h₁f⟩
    exact ⟨_, h₁f, f, h₀f, fun x => id⟩
  rcases exists_locallyFinite_subcover_of_locally isClosed_univ hP₁ hP₂ hP₃ with
    ⟨K, U : IndexType 0 → Set X, K_cpct, U_op, hU, hKU, U_loc, hK⟩
  have ind' :
    ∀ (i : 𝓘 0) (f : X → Y),
      (∀ x, P₀ x f ∧ P₀' x f) →
        (∀ j < i, ∀ x, RestrictGermPredicate P₁ (K j) x ↑f) →
          ∃ f' : X → Y,
            (∀ x : X, P₀ x ↑f' ∧ P₀' x ↑f') ∧
              (∀ j ≤ i, ∀ x, RestrictGermPredicate P₁ (K j) x f') ∧
                ∀ (x) (_ : x ∉ U i), f' x = f x :=
    by
    simp_rw [forall_restrictGermPredicate_iff, ← eventually_nhdsSet_Union₂]
    rintro (i : ℕ) f h₀f h₁f
    have cpct : IsClosed (⋃ j < i, K j) :=
      by
      rw [show (⋃ j < i, K j) = ⋃ j ∈ Finset.range i, K j by simp only [Finset.mem_range]]
      apply (Finset.range i).isClosed_biUnion _ fun j _ => (K_cpct j).isClosed
    rcases hU i with ⟨f', h₀f', h₁f'⟩
    rcases mem_nhds_set_iff_exists.mp h₁f with ⟨V, V_op, hKV, h₁V⟩
    rcases ind V_op (U_op i) cpct (K_cpct i).isClosed hKV (hKU i) h₀f h₀f' h₁V h₁f' with
      ⟨F, h₀F, h₁F, hF⟩
    simp_rw [← bUnion_le] at h₁F 
    exact ⟨F, h₀F, h₁F, fun x hx => hF.on_set x (Or.inr hx)⟩
  have :=
    inductive_construction (fun x φ => P₀ x φ ∧ P₀' x φ)
      (fun j : 𝓘 0 => RestrictGermPredicate P₁ (K j)) (fun _ _ => True) U_loc ⟨f₀, hP₀f₀, trivial⟩
  simp only [IndexType.not_isMax, not_false_iff, forall_true_left, true_and_iff] at this 
  rcases this ind' with ⟨f, h, h'⟩
  refine' ⟨f, fun x => ⟨(h x).1, (h x).2, _⟩⟩
  rcases mem_Union.mp (hK trivial : x ∈ ⋃ j, K j) with ⟨j, hj⟩
  exact (h' j x hj).self_of_nhds

/-- We are given a suitably nice extended metric space `X` and three local constraints `P₀`,`P₀'`
and `P₁` on maps from `X` to some type `Y`. All maps entering the discussion are required to
statisfy `P₀` everywhere. The goal is to turn a map `f₀` satisfying `P₁` near a compact set `K` into
one satisfying everywhere without changing `f₀` near `K`. The assumptions are:
* For every `x` in `X` there is a map which satisfies `P₁` near `x`
* One can patch two maps `f₁ f₂` satisfying `P₁` on open sets `U₁` and `U₂` respectively
  into a map satisfying `P₁` on `K₁ ∪ K₂` for any compact sets `Kᵢ ⊆ Uᵢ`.
This is deduced this version from the version where `K` is empty but adding some `P'₀`, see
`inductive_construction_of_loc`. -/
theorem relative_inductive_construction_of_loc {X Y : Type _} [EMetricSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] (P₀ P₁ : ∀ x : X, Germ (𝓝 x) Y → Prop)
    {K : Set X} (hK : IsClosed K) {f₀ : X → Y} (hP₀f₀ : ∀ x, P₀ x f₀) (hP₁f₀ : ∀ᶠ x near K, P₁ x f₀)
    (loc : ∀ x, ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ᶠ x' in 𝓝 x, P₁ x' f)
    (ind :
      ∀ {U₁ U₂ K₁ K₂ : Set X} {f₁ f₂ : X → Y},
        IsOpen U₁ →
          IsOpen U₂ →
            IsClosed K₁ →
              IsClosed K₂ →
                K₁ ⊆ U₁ →
                  K₂ ⊆ U₂ →
                    (∀ x, P₀ x f₁) →
                      (∀ x, P₀ x f₂) →
                        (∀ x ∈ U₁, P₁ x f₁) →
                          (∀ x ∈ U₂, P₁ x f₂) →
                            ∃ f : X → Y,
                              (∀ x, P₀ x f) ∧
                                (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ ∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x) :
    ∃ f : X → Y, (∀ x, P₀ x f ∧ P₁ x f) ∧ ∀ᶠ x near K, f x = f₀ x :=
  by
  let P₀' : ∀ x : X, germ (𝓝 x) Y → Prop := RestrictGermPredicate (fun x φ => φ.value = f₀ x) K
  have hf₀ : ∀ x, P₀ x f₀ ∧ P₀' x f₀ := fun x =>
    ⟨hP₀f₀ x, fun hx => eventually_of_forall fun x' => rfl⟩
  have ind' :
    ∀ (U₁ U₂ K₁ K₂ : Set X) {f₁ f₂ : X → Y},
      IsOpen U₁ →
        IsOpen U₂ →
          IsClosed K₁ →
            IsClosed K₂ →
              K₁ ⊆ U₁ →
                K₂ ⊆ U₂ →
                  (∀ x, P₀ x f₁ ∧ P₀' x f₁) →
                    (∀ x, P₀ x f₂) →
                      (∀ x ∈ U₁, P₁ x f₁) →
                        (∀ x ∈ U₂, P₁ x f₂) →
                          ∃ f : X → Y,
                            (∀ x, P₀ x f ∧ P₀' x f) ∧
                              (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ ∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x :=
    by
    intro U₁ U₂ K₁ K₂ f₁ f₂ U₁_op U₂_op K₁_cpct K₂_cpct hK₁U₁ hK₂U₂ hf₁ hf₂ hf₁U₁ hf₂U₂
    obtain ⟨h₀f₁, h₀'f₁⟩ := forall_and_distrib.mp hf₁
    rw [forall_restrictGermPredicate_iff] at h₀'f₁ 
    rcases(hasBasis_nhdsSet K).mem_iff.mp (hP₁f₀.germ_congr_set h₀'f₁) with ⟨U, ⟨U_op, hKU⟩, hU⟩
    rcases ind (U_op.union U₁_op) U₂_op (hK.union K₁_cpct) K₂_cpct (union_subset_union hKU hK₁U₁)
        hK₂U₂ h₀f₁ hf₂ (fun x hx => hx.elim (fun hx => hU hx) fun hx => hf₁U₁ x hx) hf₂U₂ with
      ⟨f, h₀f, hf, h'f⟩
    rw [union_assoc, eventually_nhds_set_union] at hf h'f 
    exact ⟨f, fun x => ⟨h₀f x, restrictGermPredicate_congr (hf₁ x).2 h'f.1⟩, hf.2, h'f.2⟩
  rcases inductive_construction_of_loc P₀ P₀' P₁ hf₀ loc ind' with ⟨f, hf⟩
  simp only [forall_and, forall_restrictGermPredicate_iff] at hf ⊢
  exact ⟨f, ⟨hf.1, hf.2.2⟩, hf.2.1⟩

end inductive_construction

section Htpy

private noncomputable def T : ℕ → ℝ := fun n => Nat.rec 0 (fun k x => x + 1 / (2 : ℝ) ^ (k + 1)) n

open scoped BigOperators

-- Note this is more painful than Patrick hoped for. Maybe this should be the definition of T.
private theorem T_eq (n : ℕ) : t n = 1 - (1 / (2 : ℝ)) ^ n :=
  by
  have : T n = ∑ k in Finset.range n, 1 / (2 : ℝ) ^ (k + 1) :=
    by
    induction' n with n hn
    · simp only [T, Finset.range_zero, Finset.sum_empty]
    change T n + _ = _
    rw [hn, Finset.sum_range_succ]
  simp_rw [this, ← one_div_pow, pow_succ, ← Finset.mul_sum,
    geom_sum_eq (by norm_num : 1 / (2 : ℝ) ≠ 1) n]
  field_simp
  norm_num
  apply div_eq_of_eq_mul
  apply neg_ne_zero.mpr
  apply ne_of_gt
  positivity
  ring

private theorem T_lt (n : ℕ) : t n < 1 := by
  rw [T_eq]
  have : (0 : ℝ) < (1 / 2) ^ n := by positivity
  linarith

private theorem T_lt_succ (n : ℕ) : t n < t (n + 1) :=
  lt_add_of_le_of_pos le_rfl (one_div_pos.mpr (pow_pos zero_lt_two _))

private theorem T_le_succ (n : ℕ) : t n ≤ t (n + 1) :=
  (t_lt_succ n).le

private theorem T_succ_sub (n : ℕ) : t (n + 1) - t n = 1 / 2 ^ (n + 1) :=
  by
  change T n + _ - T n = _
  simp

private theorem mul_T_succ_sub (n : ℕ) : 2 ^ (n + 1) * (t (n + 1) - t n) = 1 :=
  by
  rw [T_succ_sub]
  field_simp

private theorem T_one : t 1 = 1 / 2 := by simp [T]

private theorem T_nonneg (n : ℕ) : 0 ≤ t n :=
  by
  rw [T_eq]
  have : (1 / (2 : ℝ)) ^ n ≤ 1
  apply pow_le_one <;> norm_num
  linarith

private theorem not_T_succ_le (n : ℕ) : ¬t (n + 1) ≤ 0 :=
  by
  rw [T_eq, not_le]
  have : (1 / (2 : ℝ)) ^ (n + 1) < 1
  apply pow_lt_one <;> norm_num
  linarith

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (p «expr ∉ » [lower_set.prod/upper_set.prod/finset.product/multiset.product/set.prod/list.product](Ici (T i.to_nat),
  U i)) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » U i) -/
theorem inductive_htpy_construction {X Y : Type _} [TopologicalSpace X] {N : ℕ}
    {U K : IndexType N → Set X} (P₀ P₁ : ∀ x : X, Germ (𝓝 x) Y → Prop)
    (P₂ : ∀ p : ℝ × X, Germ (𝓝 p) Y → Prop)
    (hP₂ :
      ∀ (a b) (p : ℝ × X) (f : ℝ × X → Y),
        P₂ (a * p.1 + b, p.2) f → P₂ p fun p : ℝ × X => f (a * p.1 + b, p.2))
    (U_fin : LocallyFinite U) (K_cover : (⋃ i, K i) = univ) {f₀ : X → Y} (init : ∀ x, P₀ x f₀)
    (init' : ∀ p, P₂ p fun p : ℝ × X => f₀ p.2)
    -- Not in the original version
    (ind :
      ∀ (i : IndexType N) (f : X → Y),
        (∀ x, P₀ x f) →
          (∀ᶠ x near ⋃ j < i, K j, P₁ x f) →
            ∃ F : ℝ → X → Y,
              (∀ t, ∀ x, P₀ x <| F t) ∧
                (∀ᶠ x near ⋃ j ≤ i, K j, P₁ x <| F 1) ∧
                  (∀ p, P₂ p ↿F) ∧
                    (∀ t, ∀ (x) (_ : x ∉ U i), F t x = f x) ∧
                      (∀ᶠ t near Iic 0, F t = f) ∧ ∀ᶠ t near Ici 1, F t = F 1) :
    ∃ F : ℝ → X → Y, F 0 = f₀ ∧ (∀ t x, P₀ x (F t)) ∧ (∀ x, P₁ x (F 1)) ∧ ∀ p, P₂ p ↿F :=
  by
  let PP₀ : ∀ p : ℝ × X, germ (𝓝 p) Y → Prop := fun p φ =>
    P₀ p.2 φ.sliceRight ∧ (p.1 = 0 → φ.value = f₀ p.2) ∧ P₂ p φ
  let PP₁ : ∀ i : IndexType N, ∀ p : ℝ × X, germ (𝓝 p) Y → Prop := fun i p φ =>
    p.1 = 1 → RestrictGermPredicate P₁ (K i) p.2 φ.sliceRight
  let PP₂ : IndexType N → (ℝ × X → Y) → Prop := fun i f =>
    ∀ x, ∀ t ≥ T i.toNat, f (t, x) = f (T i.toNat, x)
  have hPP₀ : ∀ p : ℝ × X, PP₀ p fun p : ℝ × X => f₀ p.2 :=
    by
    rintro ⟨t, x⟩
    exact ⟨init x, fun h => rfl, init' _⟩
  have ind' :
    ∀ (i) (f : ℝ × X → Y),
      (∀ p, PP₀ p f) →
        PP₂ i f →
          (∀ j < i, ∀ p, PP₁ j p f) →
            ∃ f' : ℝ × X → Y,
              (∀ p, PP₀ p f') ∧
                (¬IsMax i → PP₂ i.succ f') ∧
                  (∀ j ≤ i, ∀ p, PP₁ j p f') ∧ ∀ (p) (_ : p ∉ Ici (T i.toNat) ×ˢ U i), f' p = f p :=
    by
    rintro i F h₀F h₂F h₁F
    replace h₁F : ∀ᶠ x : X near ⋃ j < i, K j, P₁ x fun x => F (T i.to_nat, x)
    · rw [eventually_nhdsSet_Union₂]
      intro j hj
      have : ∀ x : X, RestrictGermPredicate P₁ (K j) x fun x' => F (1, x') := fun x =>
        h₁F j hj (1, x) rfl
      apply (forall_restrict_germ_predicate_iff.mp this).germ_congr_set
      apply eventually_of_forall fun x => (_ : F (T i.to_nat, x) = F (1, x))
      rw [h₂F _ _ (T_lt _).le]
    rcases ind i (fun x => F (T i.to_nat, x)) (fun x => (h₀F (_, x)).1) h₁F with
        ⟨F', h₀F', h₁F', h₂F', hUF', hpast_F', hfutur_F'⟩ <;>
      clear ind
    let F'' : ℝ × X → Y := fun p : ℝ × X =>
      if p.1 ≤ T i.to_nat then F p else F' (2 ^ (i.to_nat + 1) * (p.1 - T i.to_nat)) p.2
    have loc₁ : ∀ p : ℝ × X, p.1 ≤ T i.to_nat → (F'' : germ (𝓝 p) Y) = F :=
      by
      dsimp only [PP₂] at h₂F 
      rintro ⟨t, x⟩ (ht : t ≤ _)
      rcases eq_or_lt_of_le ht with (rfl | ht)
      · apply Quotient.sound
        replace hpast_F' : ↿F' =ᶠ[𝓝 (0, x)] fun q : ℝ × X => F (T i.to_nat, q.2)
        · have : 𝓝 (0 : ℝ) ≤ 𝓝ˢ (Iic 0) := nhds_le_nhdsSet right_mem_Iic
          apply mem_of_superset (prod_mem_nhds (hpast_F'.filter_mono this) univ_mem)
          rintro ⟨t', x'⟩ ⟨ht', hx'⟩
          exact (congr_fun ht' x' : _)
        have lim :
          tendsto (fun x : ℝ × X => (2 ^ (i.to_nat + 1) * (x.1 - T i.to_nat), x.2))
            (𝓝 (T i.to_nat, x)) (𝓝 (0, x)) :=
          by
          rw [nhds_prod_eq, nhds_prod_eq]
          have limt :
            tendsto (fun t => 2 ^ (i.to_nat + 1) * (t - T i.to_nat)) (𝓝 <| T i.to_nat) (𝓝 0) :=
            by
            rw [show (0 : ℝ) = 2 ^ (i.to_nat + 1) * (T i.to_nat - T i.to_nat) by simp]
            apply tendsto.const_mul
            exact tendsto_id.sub_const _
          exact limt.prod_map tendsto_id
        apply eventually.mono (hpast_F'.comp_fun limUnder)
        dsimp [F'']
        rintro ⟨t, x⟩ h'
        split_ifs
        · rfl
        · push_neg at h 
          change (↿F') (2 ^ (i.to_nat + 1) * (t - T i.to_nat), x) = _
          rw [h', h₂F x t h.le]
      · have hp : ∀ᶠ p : ℝ × X in 𝓝 (t, x), p.1 ≤ T i.to_nat :=
          by
          convert prod_mem_nhds (Iic_mem_nhds ht) univ_mem using 1
          simp
        apply Quotient.sound
        exact hp.mono fun p hp => if_pos hp
    have loc₂ :
      ∀ p : ℝ × X,
        p.1 > T i.to_nat →
          (F'' : germ (𝓝 p) Y) = fun p : ℝ × X =>
            F' (2 ^ (i.to_nat + 1) * (p.1 - T i.to_nat)) p.2 :=
      by
      rintro ⟨t, x⟩ (ht : t > _)
      apply Quotient.sound
      have hp : ∀ᶠ p : ℝ × X in 𝓝 (t, x), ¬p.1 ≤ T i.to_nat :=
        by
        apply mem_of_superset (prod_mem_nhds (Ioi_mem_nhds ht) univ_mem)
        rintro ⟨t', x'⟩ ⟨ht', hx'⟩
        simpa using ht'
      apply hp.mono fun q hq => _
      exact if_neg hq
    refine' ⟨F'', _, _, _, _⟩
    · rintro p
      by_cases ht : p.1 ≤ T i.to_nat
      · rw [loc₁ _ ht]
        apply h₀F
      · push_neg at ht 
        cases' p with t x
        rw [loc₂ _ ht]
        refine' ⟨h₀F' (2 ^ (i.to_nat + 1) * (t - T i.to_nat)) x, _, _⟩
        · rintro (rfl : t = 0)
          exact (lt_irrefl _ ((T_nonneg i.to_nat).trans_lt ht)).elim
        ·
          simpa only [mul_sub, neg_mul] using
            hP₂ (2 ^ (i.to_nat + 1)) (-2 ^ (i.to_nat + 1) * T i.to_nat) (t, x) (↿F') (h₂F' _)
    · intro hi x t ht
      rw [i.to_nat_succ hi] at ht ⊢
      have h₂t : ¬t ≤ T i.to_nat := by
        push_neg
        exact (T_lt_succ i.to_nat).trans_le ht
      dsimp only [F'']
      rw [if_neg h₂t, if_neg]
      · rw [hfutur_F'.on_set, mul_T_succ_sub]
        conv =>
          rw [mem_Ici]
          congr
          rw [← mul_T_succ_sub i.to_nat]
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht _) (pow_nonneg zero_le_two _)
      · push_neg
        apply T_lt_succ
    · rintro j hj ⟨t, x⟩ (rfl : t = 1)
      replace h₁F' := eventually_nhds_set_Union₂.mp h₁F' j hj
      rw [loc₂ (1, x) (T_lt i.to_nat)]
      revert x
      change
        ∀ x : X,
          RestrictGermPredicate P₁ (K j) x fun x' : X =>
            F' (2 ^ (i.to_nat + 1) * (1 - T i.to_nat)) x'
      rw [forall_restrictGermPredicate_iff]
      apply h₁F'.germ_congr_set
      apply eventually_of_forall _
      apply congr_fun (hfutur_F'.on_set _ _)
      conv =>
        congr
        skip
        rw [← mul_T_succ_sub i.to_nat]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right (T_lt _).le _) (pow_nonneg zero_le_two _)
    · rintro ⟨t, x⟩ htx
      simp only [prod_mk_mem_set_prod_eq, mem_Ici, not_and_or, not_le] at htx 
      cases' htx with ht hx
      · change (↑F'' : germ (𝓝 (t, x)) Y).value = (↑F : germ (𝓝 (t, x)) Y).value
        rw [loc₁ (t, x) ht.le]
      · dsimp only [F'']
        split_ifs with ht ht
        · rfl
        · rw [hUF' _ x hx]
          push_neg at ht 
          rw [h₂F x _ ht.le]
  rcases inductive_construction PP₀ PP₁ PP₂ (U_fin.prod_left fun i => Ici (T i.toNat))
      ⟨fun p => f₀ p.2, hPP₀, fun x t ht => rfl⟩ ind' with
    ⟨F, hF, h'F⟩
  clear ind ind' hPP₀
  refine' ⟨curry F, _, _, _, _⟩
  · exact funext fun x => (hF (0, x)).2.1 rfl
  · exact fun t x => (hF (t, x)).1
  · intro x
    obtain ⟨j, hj⟩ : ∃ j, x ∈ K j := by simpa using (by simp [K_cover] : x ∈ ⋃ j, K j)
    exact (h'F j (1, x) rfl hj).self_of_nhds
  · intro p
    convert (hF p).2.2 using 2
    exact uncurry_curry F

end Htpy

