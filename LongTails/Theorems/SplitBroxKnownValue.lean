import LongTails.Setups.KnownValueSmoothConvexLocalLinear
import LongTails.Proofs.SplitBroxExecution
import LongTails.Proofs.SplitBroxBudget

namespace OracleTemplate.SplitBrox

open LongTails.Setups.KnownValueSmoothConvexLocalLinear

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 3 * (⌈Real.sqrt (10 * p.L * p.R ^ 2 / p.ε)⌉₊ + 1)

theorem result : Convergence LongTails.Setups.KnownValueSmoothConvexLocalLinear.spec budget := by
  refine ⟨fun p => algorithm (horizon p) (baseRadius p) p.fstar p.x0, ?_, ?_⟩
  · rintro p ⟨hL, hR, he⟩ I O
      ⟨hC, hclosed, hx0, hgrad, hlow, hup, hfoo, hlocal, xs, hxs, hmin, hval, hdist⟩
    obtain ⟨hb, hDR, hDb, haccuracy⟩ := tuning p hL he
    let M : Model p.E :=
      { C := I.C, f := I.f, grad := gradient I.f, L := p.L, fstar := p.fstar,
        xstar := xs, convex := hC, L_nonneg := le_of_lt hL, star_mem := hxs,
        star_value := hval, lower := hlow, upper := hup }
    have hO : ValidOracle M O := ⟨hfoo, hlocal⟩
    have hd : ‖p.x0 - M.xstar‖ ^ 2 ≤ proofRadius p ^ 2 :=
      le_trans (pow_le_pow_left₀ (norm_nonneg _) hdist 2) hDR
    refine ⟨xs, hxs, hmin, hval, Filter.Eventually.of_forall ?_⟩
    rintro ⟨seed, ξ⟩
    have hs := execute_energy M hO hb hDb p.x0 hx0 hd seed ξ
    refine ⟨hs.1, ?_⟩
    have hw := horizon_weight_pos p
    have hg := le_trans hs.2 haccuracy
    have hgap := (mul_le_mul_iff_right₀ hw).mp hg
    change I.f (execute O (algorithm (horizon p) (baseRadius p) p.fstar p.x0)
      (fun _ => 3 * horizon p) seed ξ) - I.f xs ≤ p.ε
    rw [hval]
    exact hgap
  · intro p hp
    trivial

end OracleTemplate.SplitBrox
