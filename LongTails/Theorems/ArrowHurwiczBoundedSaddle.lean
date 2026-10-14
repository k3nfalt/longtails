import LongTails.Proofs.Execution
import LongTails.Setups.BoundedCompositeSaddle
import LongTails.Proofs.ArrowHurwiczRate

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.ArrowHurwicz.ArrowHurwiczBoundedSaddle

open LongTails.Setups.BoundedCompositeSaddle

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 4 * ⌈(11 * p.R * (p.L * p.R + p.M) / p.ε) ^ ((4 : ℝ) / 3)⌉₊

theorem result : Convergence LongTails.Setups.BoundedCompositeSaddle.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => arrowHurwicz (p.R / ((p.L * p.R + p.M) *
    (⌈(11 * p.R * (p.L * p.R + p.M) / p.ε) ^ ((4 : ℝ) / 3)⌉₊ : ℝ) ^ ((1 : ℝ) / 4))) p.x0 p.y0, ?_, ?_⟩
  · rintro p ⟨hX, hY, hx0, hy0, hRX, hRY, hR, hL, hM, hε⟩

    rintro I oracle
      ⟨hK, hg, hh, lg, lh, adj, px, py, hadj, hpx, hpy, o1, o2, o3, o4⟩
    set T := ⌈(11 * p.R * (p.L * p.R + p.M) / p.ε) ^ ((4 : ℝ) / 3)⌉₊ with hTdef
    obtain ⟨hT1, hηL, hηΛ, hfin⟩ := tuning hR hL hM hε T (Nat.le_ceil _)
    set η := p.R / ((p.L * p.R + p.M) * (T : ℝ) ^ ((1 : ℝ) / 4)) with hηdef
    have hηpos : 0 < η := by
      have : 0 < (T : ℝ) := by exact_mod_cast hT1
      positivity
    have H : Hyp p.X p.Y I.K I.g I.h adj px py η p.R p.L p.M p.x0 p.y0 :=
      { convX := hX, convY := hY, cvg := hg, cvh := hh, lipg := lg, liph := lh, normK := hK,
        hadj := hadj, proxX := fun u => hpx (u, η) hηpos, proxY := fun u => hpy (u, η) hηpos,
        boundX := hRX, boundY := hRY, hη := hηpos, hM := hM, memx := hx0, memy := hy0 }
    have hbudget : budget p 0 = 4 * T := rfl
    have hans : ∀ k q s, oracle.answer k (0, q) s = answerFn adj I.K px py q := by
      rintro k ((y | x) | (q | q)) s
      · exact o1 k s y
      · exact o2 k s x
      · exact o3 k s q
      · exact o4 k s q
    have hexec : ∀ seed : Unit × ((k : ℕ) → oracle.Seed k),
        execute oracle (arrowHurwicz η p.x0 p.y0) (fun _ => (budget p 0)) seed.1 seed.2 =
          (arrowHurwicz η p.x0 p.y0).output (stateAt adj I.K px py η p.x0 p.y0 T) := by
      rintro ⟨⟨⟩, ξ⟩
      erw [hbudget, execute_eq_of_answer_eq oracle (answerFn adj I.K px py) hans]
      exact execute_ah adj I.K px py η p.x0 p.y0 T
    have hTpos : 0 < T := hT1
    have hout := output_eq adj I.K px py η p.x0 p.y0 T hTpos
    refine Filter.Eventually.of_forall (fun seed => ?_)
    · change (execute oracle (arrowHurwicz η p.x0 p.y0) (fun _ => (budget p 0)) seed.1 seed.2).1 ∈ p.X ∧
        (execute oracle (arrowHurwicz η p.x0 p.y0) (fun _ => (budget p 0)) seed.1 seed.2).2 ∈ p.Y ∧
        ∀ x ∈ p.X, ∀ y ∈ p.Y,
          objective I (execute oracle (arrowHurwicz η p.x0 p.y0) (fun _ => (budget p 0)) seed.1 seed.2).1 y -
            objective I x (execute oracle (arrowHurwicz η p.x0 p.y0) (fun _ => (budget p 0)) seed.1 seed.2).2 ≤
            p.ε
      erw [hexec, hout]
      obtain ⟨mx, my⟩ := H.avg_mem T hTpos
      refine ⟨mx, my, fun x hx y hy => ?_⟩
      have hgap := H.avg_gap (xh := x) (yh := y) T hTpos
      obtain ⟨N, hN⟩ : ∃ N, T = N + 1 := ⟨T - 1, by omega⟩
      have htot := H.total_bound hx hy N hηL hηΛ
      rw [← Finset.mul_sum] at htot
      rw [hN] at hgap hfin ⊢
      have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      have hTr : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      set S := ∑ s ∈ Finset.range (N + 1),
        gapTerm I.K I.g I.h (xs adj I.K px py η p.x0 p.y0 (s + 1)) (ys adj I.K px py η p.x0 p.y0 (s + 1)) x y
      have hdiv : (((N + 1 : ℕ) : ℝ))⁻¹ * S ≤
          10 * p.R ^ 2 / (η * ((N + 1 : ℕ) : ℝ)) +
            η ^ 3 * p.L ^ 2 * (p.L * p.R + p.M) ^ 2 / 4 := by
        rw [hcast]
        have e : 10 * p.R ^ 2 / (η * ((N : ℝ) + 1)) + η ^ 3 * p.L ^ 2 * (p.L * p.R + p.M) ^ 2 / 4 =
            (10 * p.R ^ 2 + η ^ 4 * p.L ^ 2 * (p.L * p.R + p.M) ^ 2 * ((N : ℝ) + 1) / 4) /
              (η * ((N : ℝ) + 1)) := by
          field_simp
          try ring
        rw [e, le_div_iff₀ (by positivity)]
        have : ((N : ℝ) + 1)⁻¹ * S * (η * ((N : ℝ) + 1)) = η * S := by
          field_simp
          try ring
        rw [this]
        exact htot
      have hobj : objective I ((((N + 1 : ℕ) : ℝ))⁻¹ • ∑ s ∈ Finset.range (N + 1),
            (traj adj I.K px py η p.x0 p.y0 (s + 1)).1) y -
          objective I x ((((N + 1 : ℕ) : ℝ))⁻¹ • ∑ s ∈ Finset.range (N + 1),
            (traj adj I.K px py η p.x0 p.y0 (s + 1)).2) =
          gapTerm I.K I.g I.h ((((N + 1 : ℕ) : ℝ))⁻¹ • ∑ s ∈ Finset.range (N + 1),
            xs adj I.K px py η p.x0 p.y0 (s + 1))
            ((((N + 1 : ℕ) : ℝ))⁻¹ • ∑ s ∈ Finset.range (N + 1), ys adj I.K px py η p.x0 p.y0 (s + 1))
            x y := rfl
      rw [hobj]
      linarith
  · rintro p ⟨-, -, -, -, -, -, hR, hL, hM, hε⟩
    refine ⟨_, ?_, rfl⟩
    obtain ⟨hT1, -, -, -⟩ := tuning hR hL hM hε
      ⌈(11 * p.R * (p.L * p.R + p.M) / p.ε) ^ ((4 : ℝ) / 3)⌉₊ (Nat.le_ceil _)
    have : 0 < (⌈(11 * p.R * (p.L * p.R + p.M) / p.ε) ^ ((4 : ℝ) / 3)⌉₊ : ℝ) := by
      exact_mod_cast hT1
    positivity

end OracleTemplate.ArrowHurwicz.ArrowHurwiczBoundedSaddle
