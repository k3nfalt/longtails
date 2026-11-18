import LongTails.Proofs.SublevelWeightedBudget
import LongTails.Proofs.SublevelWeightedExpectation

namespace OracleTemplate.SublevelWeighted

open MeasureTheory LongTails.Setups.SublevelPLBoundedVariance

lemma execution_success (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (O : Oracle p.E p.E) (hadm : spec.admissible p f O) (N : ℕ)
    (hN : 1 ≤ 2 * p.L * p.ε * (p.τ / p.ε) ^ (2 / p.α) →
      ⌈110000 * p.L * p.ε * (p.τ / p.ε) ^ (2 / p.α) / (2 - p.α) *
        (1 + p.σ ^ 2 * (p.τ / p.ε) ^ (2 / p.α) / (2 - p.α))⌉₊ ≤ N) :
    let A := method p.toPublic
    spec.successful p f (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
      execute O A (fun _ => N) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  rcases hadm with ⟨g, μ, P, hIID, rfl, hgr, hlip, hbdd, hpl, _, hg, hgi, hmean, h2i, hvar⟩
  obtain ⟨hL, hτ, hα1, hα2, _, _, hε⟩ := hp
  let m := ⨅ y, f y
  have H : SublevelRobustGradient.Hyp f m p.L p.τ p.α p.x0 :=
    ⟨hL, hτ, hα1, hα2, hgr, hlip, fun x => ciInf_le hbdd x, hpl⟩
  let b := batch (steps p.toPublic) (scale p.toPublic)
  let k := horizon p.toPublic
  have hcost : calls b k ≤ N := by
    dsimp only [k, horizon]
    split_ifs with h
    · exact Nat.zero_le _
    · exact (sufficient_calls p.toPublic hL hτ hε hα1 hα2 (le_of_not_gt h)).trans
        (hN (le_of_not_gt h))
  let X := fun ξ => point p.L p.x0 b g ξ k
  have hres (s : Unit × (ℕ → p.Ω)) :
      execute ({ Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω } :
        Oracle p.E p.E) (method p.toPublic) (fun _ => N) s.1 s.2 = X s.2 := by
    exact (QueryPlan.execute_sampledPlan_of_le _ P p.x0 p.x0 _ N _ g s.1 s.2 hcost).trans
      (eval_output p.L p.x0 b g s.2 k)
  have hfm : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hm : Measurable (fun ξ => f (X ξ) - m) :=
    (hfm.comp (measurable_point _ _ _ hg _)).sub_const _
  have hX : Integrable (fun ξ => f (X ξ) - m) (P : Measure _) ∧
      (∫ ξ, f (X ξ) - m ∂(P : Measure _)) ≤ p.ε := by
    by_cases ht : 2 * p.L * p.ε * (p.τ / p.ε) ^ (2 / p.α) < 1
    · have hk : k = 0 := ite_eq_left ht
      simp only [X, hk, point, integrable_const, integral_const, probReal_univ, one_smul,
        true_and]
      exact trivial_gap p.toPublic H hε ht
    · have hk : k = steps p.toPublic := ite_eq_right ht
      simp only [X, hk]
      exact expected_output p.toPublic (μ : Measure _) (P : Measure _) hIID H hε
        ⟨hg, hgi, hmean, h2i, hvar⟩
  let Q := (Measure.dirac ()).prod (P : Measure (ℕ → p.Ω))
  have hmap : MeasurePreserving (Prod.snd : Unit × (ℕ → p.Ω) → _) Q (P : Measure _) :=
    measurePreserving_snd
  change Integrable (fun s => f (_) - m) Q ∧ (∫ s, f (_) - m ∂Q) ≤ p.ε
  simp_rw [hres]
  refine ⟨hmap.integrable_comp_of_integrable hX.1, ?_⟩
  exact (LongTails.Proofs.HessianAdaptiveCubicMoments.preserving_integral hmap
    hm.aestronglyMeasurable).trans_le hX.2

end OracleTemplate.SublevelWeighted
