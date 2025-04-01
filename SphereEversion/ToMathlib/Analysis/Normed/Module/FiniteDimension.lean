import Mathlib.Analysis.Normed.Module.FiniteDimension

-- being affinely independent is an open condition
section
variable (𝕜 E : Type*) {ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜] [Finite ι]

-- https://github.com/leanprover-community/mathlib4/pull/23528
theorem isOpen_affineIndependent : IsOpen {p : ι → E | AffineIndependent 𝕜 p} := by
  classical
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i₀⟩⟩
  · exact isOpen_discrete _
  · simp_rw [affineIndependent_iff_linearIndependent_vsub 𝕜 _ i₀]
    let ι' := { x // x ≠ i₀ }
    cases nonempty_fintype ι
    haveI : Fintype ι' := Subtype.fintype _
    convert_to
      IsOpen ((fun (p : ι → E) (i : ι') ↦ p i -ᵥ p i₀) ⁻¹' {p : ι' → E | LinearIndependent 𝕜 p})
    refine isOpen_setOf_linearIndependent.preimage ?_
    exact continuous_pi fun i' ↦
      (continuous_apply (π := fun _ : ι ↦ E) i'.1).vsub <| continuous_apply i₀

end
