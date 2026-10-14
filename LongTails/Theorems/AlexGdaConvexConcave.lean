import LongTails.Proofs.Execution
import LongTails.Setups.BlockSmoothConvexConcave
import LongTails.Proofs.AlexGdaTuning

namespace OracleTemplate.BlockSaddle

open LongTails.Setups.BlockSmoothConvexConcave

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 2 * ⌈180 * q.γ ^ 4 * q.δ ^ 4 * (max q.Lx q.Ly + q.Lxy) ^ 2 * q.R ^ 2 / ((q.γ - 1) ^ 3 * q.ε ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.BlockSmoothConvexConcave.spec budget := by
  apply convergence_of_block_budget (S := spec) (fun q => ⌈180 * q.γ ^ 4 * q.δ ^ 4 * (max q.Lx q.Ly + q.Lxy) ^ 2 * q.R ^ 2 / ((q.γ - 1) ^ 3 * q.ε ^ 2)⌉₊)
    (fun _ => 2)
  refine ⟨fun p => alexGda p.γ p.δ ((p.γ - 1) / (4 * p.γ ^ 2 * p.δ ^ 2 * (p.Lx + p.Lxy)))
    ((p.γ - 1) / (4 * p.γ ^ 2 * p.δ ^ 2 * (p.Ly + p.Lxy))) p.x0 p.y0, ?_, ?_⟩
  · rintro q ⟨hLx, hLy, hLxy, hx, hy, hγ, hγ2, hδ, -, hε⟩
    intro K hK
    rintro f oracle
      ⟨gx, gy, hox, hoy, hgx, hgy, hcv, hcc, lxx, lxy, lyy, lyx, xs, ys, hs, hdist⟩
    have H := hyp_of_admissible hgx hgy hcv hcc lxx lxy lyy lyx hs
    let α := (q.γ - 1) / (4 * q.γ ^ 2 * q.δ ^ 2 * (q.Lx + q.Lxy))
    let β := (q.γ - 1) / (4 * q.γ ^ 2 * q.δ ^ 2 * (q.Ly + q.Lxy))
    have hacc := alex_guarantee H hLx hLy hLxy hx hy hγ hγ2 hδ hε hdist K ((Nat.le_ceil _).trans (Nat.cast_le.mpr hK))
    have hexec : ∀ seed : Unit × ((k : ℕ) → oracle.Seed k),
        execute oracle (alexGda q.γ q.δ α β q.x0 q.y0) (fun _ => (2 * K)) seed.1 seed.2 =
          (record gx gy q.γ q.δ α β q.x0 q.y0 K).1 := by
      rintro ⟨⟨⟩, ξ⟩
      erw [execute_eq_of_answer_eq oracle (answerFn gx gy)
        (by
          rintro k (z | z) seed
          · exact hox k seed z
          · exact hoy k seed z)]
      exact execute_alex gx gy q.γ q.δ α β q.x0 q.y0 K
    refine Filter.Eventually.of_forall (fun seed => ?_)
    · change ∀ (vx : q.E) (vy : q.F),
        HasGradientAt (fun x => f x
          (execute oracle (alexGda q.γ q.δ α β q.x0 q.y0) (fun _ => (2 * K)) seed.1 seed.2).2) vx
          (execute oracle (alexGda q.γ q.δ α β q.x0 q.y0) (fun _ => (2 * K)) seed.1 seed.2).1 →
        HasGradientAt (fun y => f
          (execute oracle (alexGda q.γ q.δ α β q.x0 q.y0) (fun _ => (2 * K)) seed.1 seed.2).1 y) vy
          (execute oracle (alexGda q.γ q.δ α β q.x0 q.y0) (fun _ => (2 * K)) seed.1 seed.2).2 →
        ‖vx‖ ^ 2 + ‖vy‖ ^ 2 ≤ q.ε ^ 2
      erw [hexec]
      intro vx vy hvx hvy
      rw [hvx.unique (hgx _), hvy.unique (hgy _)]
      exact hacc
  · rintro p ⟨-, -, -, hx, hy, hγ, -, hδ, -, -⟩
    have hc : 0 < p.γ - 1 := by linarith
    have hden : 0 < 4 * p.γ ^ 2 * p.δ ^ 2 := by
      have : 0 < p.γ := by linarith
      have : 0 < p.δ := by linarith
      positivity
    exact ⟨_, _, div_pos hc (mul_pos hden hx), div_pos hc (mul_pos hden hy), rfl⟩

end OracleTemplate.BlockSaddle
