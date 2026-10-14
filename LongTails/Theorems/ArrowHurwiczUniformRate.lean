import LongTails.Proofs.Execution
import LongTails.Setups.BoundedCompositeSaddle
import LongTails.Proofs.ArrowHurwiczFriction

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.ArrowHurwicz.ArrowHurwiczUniformRate

open LongTails.Setups.BoundedCompositeSaddle

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 4 * ⌈200 * p.R * (p.L * p.R + p.M) / p.ε⌉₊

theorem result : Convergence LongTails.Setups.BoundedCompositeSaddle.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => arrowHurwicz (1 / (2 * p.L)) p.x0 p.y0, ?_, ?_⟩
  · rintro p ⟨hX, hY, hx0, hy0, hRX, hRY, hR, hL, hM, hε⟩

    rintro I oracle
      ⟨hK, hg, hh, lg, lh, adj, px, py, hadj, hpx, hpy, o1, o2, o3, o4⟩
    set T := ⌈200 * p.R * (p.L * p.R + p.M) / p.ε⌉₊ with hTdef
    set η := 1 / (2 * p.L) with hηdef
    obtain ⟨hT1, hfin⟩ := uniform_tuning hR hL hM hε T (Nat.le_ceil _)
    have hηpos : 0 < η := by positivity
    have hηL : η * p.L ≤ 1 / 2 := by rw [hηdef]; field_simp; rfl
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
      have htot := H.uniform_total hx hy hηL T
      rw [← Finset.mul_sum] at htot
      have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
      set S := ∑ s ∈ Finset.range T,
        gapTerm I.K I.g I.h (xs adj I.K px py η p.x0 p.y0 (s + 1)) (ys adj I.K px py η p.x0 p.y0 (s + 1)) x y
      have hdiv : ((T : ℝ))⁻¹ * S ≤ (81 * p.R ^ 2 + 28 * (η * p.M * p.R)) / (η * T) := by
        rw [le_div_iff₀ (by positivity)]
        have : ((T : ℝ))⁻¹ * S * (η * T) = η * S := by field_simp
        rw [this]
        exact htot
      have hobj : objective I (((T : ℝ))⁻¹ • ∑ s ∈ Finset.range T,
            (traj adj I.K px py η p.x0 p.y0 (s + 1)).1) y -
          objective I x (((T : ℝ))⁻¹ • ∑ s ∈ Finset.range T,
            (traj adj I.K px py η p.x0 p.y0 (s + 1)).2) =
          gapTerm I.K I.g I.h (((T : ℝ))⁻¹ • ∑ s ∈ Finset.range T, xs adj I.K px py η p.x0 p.y0 (s + 1))
            (((T : ℝ))⁻¹ • ∑ s ∈ Finset.range T, ys adj I.K px py η p.x0 p.y0 (s + 1)) x y := rfl
      rw [hobj]
      linarith
  · rintro p ⟨-, -, -, -, -, -, hR, hL, hM, hε⟩
    exact ⟨_, by positivity, rfl⟩

end OracleTemplate.ArrowHurwicz.ArrowHurwiczUniformRate
