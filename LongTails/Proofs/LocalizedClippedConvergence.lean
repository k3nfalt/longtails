import LongTails.Proofs.LocalizedClippedConfidence

set_option backward.isDefEq.respectTransparency false

open MeasureTheory OracleTemplate
open LongTails.Algorithms.LocalizedClippedSubgradient
open LongTails.Setups.TerminalClippingConvex (Public Query)
open scoped RealInnerProductSpace

namespace LongTails.Proofs.LocalizedClippedSubgradient

open LongTails.Setups.DistanceGrowingSubgradient (spec)

lemma convergence : Convergence spec (fun p _ => 2 * iterations p) := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p ⟨_, hG, hδ, hδ', hR, hε⟩ I O ⟨Ω, m, hadm⟩
  dsimp only [Setups.TerminalClippingConvex.spec, Setups.DistanceGrowingSubgradient.withSamples] at hadm
  rcases hadm with ⟨g, proj, ν, P, hiid, hO,
    hcvx, hclosed, hx0, hf, hfm, ⟨u, hu, hmin, hd⟩, hp, hpX, hpv, hg, hgi, hsub, hmi, hm⟩
  have hO' : O = TerminalClipping.sampleOracle p g proj P := by
    rw [hO]
    unfold TerminalClipping.sampleOracle
    congr 1
    funext k query seed
    rcases query with ⟨i, query⟩
    cases query <;> rfl
  subst hO'
  let y := fun ξ : ℕ → Ω => execute (TerminalClipping.sampleOracle p g proj P)
    (algorithm p) (fun _ => 2 * iterations p) () ξ
  have hy : Measurable y ∧ (∀ ξ, y ξ ∈ I.domain) ∧
      (P : Measure (ℕ → Ω)) {ξ | p.ε < I.f (y ξ) - I.f u} ≤ ENNReal.ofReal p.δ := by
    by_cases hzero : p.G * p.R ≤ p.ε
    · have hN : iterations p = 0 := by simp [iterations, hzero]
      have hx : y = fun _ => p.x0 := by
        funext ξ
        dsimp only [y]
        rw [execute_output]
        simp [output, hN]
      have hg₀ := TerminalClipping.objective_difference_from_moment
        (hgi p.x0 hx0) (hmi p.x0 hx0) hG (by simpa using hm p.x0 hx0) (hsub p.x0 hx0 u hu)
      have hb := (hg₀.trans (mul_le_mul_of_nonneg_left hd hG)).trans hzero
      rw [hx]
      exact ⟨measurable_const, fun _ => hx0, by simp [hb.not_gt]⟩
    · exact confidence p hδ hδ' hR hε (lt_of_not_ge hzero) g proj ν P hiid hclosed.measurableSet
        hf hfm hx0 hp hpX hpv hg hgi hmi hm hu hd (fun x hx => hsub x hx u hu)
  change Measurable (fun s : Unit × (ℕ → Ω) => y s.2) ∧ _ ∧ _
  refine ⟨hy.1.comp measurable_snd, fun s => hy.2.1 s.2, u, hu, hmin, ?_⟩
  have hsnd := measurePreserving_snd (μ := (Measure.dirac () : Measure Unit))
    (ν := (P : Measure (ℕ → Ω)))
  exact (hsnd.measure_preimage_le {ξ | p.ε < I.f (y ξ) - I.f u}).trans hy.2.2

end LongTails.Proofs.LocalizedClippedSubgradient
