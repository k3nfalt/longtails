import LongTails.Setups.SmoothConvexConcave
import LongTails.Proofs.Execution
import LongTails.Proofs.ExtragradientExecution
import LongTails.Proofs.SmoothConvexConcaveGap

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.SaddlePoint

open LongTails.Setups.SmoothConvexConcave

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 2 * max 1 ⌈2 * q.L * q.D ^ 2 / q.ε⌉₊

theorem result :
    Convergence LongTails.Setups.SmoothConvexConcave.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  unfold budget
  refine ⟨fun q => extragradient (q.L, q.D, q.ε, q.X, q.Y), ?_, fun _ _ => trivial⟩
  intro q hp φ O h
  rcases hp with ⟨hL, hD, hε, hx, hy, hxc, hyc, hxv, hyv, hdiam⟩
  rcases h with ⟨hc, ha, hg, hlip⟩
  let seed0 := (Classical.choice O.law.nonempty) 0
  let g := fun z => O.answer [] (0, z) seed0
  let N := max 1 ⌈2 * q.L * q.D ^ 2 / q.ε⌉₊
  let w := extraPredict q.X q.Y (1 / (2 * q.L)) g
  let output := (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N, w k
  have hN : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hanswer : ∀ k z seed, O.answer k (0, z) seed = g z := by
    intro k z seed
    apply Prod.ext
    · exact (hg k seed z).1.unique (hg [] seed0 z).1
    · exact neg_injective ((hg k seed z).2.unique (hg [] seed0 z).2)
  have hw : ∀ k, w k ∈ q.X ×ˢ q.Y :=
    extraPredict_mem hx hy hxc hyc hxv hyv _ g
  have hout : output ∈ q.X ×ˢ q.Y := by
    constructor
    · simpa [output, Prod.fst_sum, Prod.snd_sum] using average_mem hxv (fun k => (w k).1) hN (fun k _ => (hw k).1)
    · simpa [output, Prod.fst_sum, Prod.snd_sum] using average_mem hyv (fun k => (w k).2) hN (fun k _ => (hw k).2)
  have hregret : ∀ u ∈ q.X ×ˢ q.Y,
      (∑ k ∈ Finset.range N, (⟪(g (w k)).1, (w k).1 - u.1⟫ +
        ⟪(g (w k)).2, (w k).2 - u.2⟫)) ≤ 2 * q.L * q.D ^ 2 := by
    intro u hu
    have hr := extragradient_regret hx hy hxc hyc hxv hyv g hL (hlip [] seed0) u hu N
    have hd := hdiam (start q.X, start q.Y) ⟨start_mem hx, start_mem hy⟩ u hu
    have hf := (norm_fst_le ((start q.X, start q.Y) - u)).trans hd
    have hs := (norm_snd_le ((start q.X, start q.Y) - u)).trans hd
    have hf2 := mul_self_le_mul_self (norm_nonneg ((start q.X, start q.Y) - u).1) hf
    have hs2 := mul_self_le_mul_self (norm_nonneg ((start q.X, start q.Y) - u).2) hs
    change (∑ k ∈ Finset.range N, pairing (g (w k)) (w k - u)) ≤ _
    apply hr.trans
    dsimp [energy] at *
    nlinarith
  have hgap := average_gap_le_of_regret hx hy hc ha g (hg [] seed0) w hN
    (fun k _ => hw k) (2 * q.L * q.D ^ 2) hregret
  have hround : 2 * q.L * q.D ^ 2 / q.ε ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hacc : gap q.E q.F q.X q.Y φ output ≤ q.ε := by
    apply hgap.trans
    apply (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
    have := (div_le_iff₀ hε).mp hround
    linarith
  have hexec : ∀ seed : Unit × ((k : ℕ) → O.Seed k),
      execute O (extragradient (q.L, q.D, q.ε, q.X, q.Y)) (fun _ => (2 * N)) seed.1 seed.2 =
        output := by
    rintro ⟨⟨⟩, ξ⟩
    erw [execute_eq_of_answer_eq O g hanswer]
    exact execute_extragradient q.L q.D q.ε q.X q.Y g N (Nat.ne_of_gt hN)
  change spec.successful q φ
    (fun seed : Unit × ((k : ℕ) → O.Seed k) =>
      execute O (extragradient (q.L, q.D, q.ε, q.X, q.Y)) (fun _ => 2 * N) seed.1 seed.2) _
  erw [funext hexec]
  suffices ∀ P : ProbabilityMeasure (Unit × ((k : ℕ) → O.Seed k)),
      spec.successful q φ (fun _ => output) P from this _
  intro P
  dsimp only [spec]
  refine ⟨measurable_const, Filter.Eventually.of_forall (fun _ => hout), integrable_const _, ?_⟩
  simpa only [integral_const, probReal_univ, one_smul] using hacc

end OracleTemplate.SaddlePoint
