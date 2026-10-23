import LongTails.Setups.TwoSampleQuadraticPerceptron
import LongTails.Algorithms.TwoSampleQuadraticPerceptron
import LongTails.Proofs.Execution
import LongTails.Proofs.TwoSampleQuadraticPerceptronExecution
import LongTails.Proofs.TwoSampleQuadraticPerceptronSpectrum
import LongTails.Proofs.QuadraticPerceptronBudget

namespace OracleTemplate.TwoSampleQuadraticPerceptron

open LongTails.Setups.TwoSampleQuadraticPerceptron
open LongTails.Algorithms.TwoSampleQuadraticPerceptron
open LongTails.Proofs.TwoSampleQuadraticPerceptronExecution
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
open LongTails.Proofs.QuadraticPerceptronCone

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈24 * (p.radius * Real.log p.ratio / p.slowLower + 1) * (p.radius / p.gain + 1) ^ 2 * (3 + 2 * p.couplingUpper * Real.log p.ratio / p.slowLower + Real.log (p.size * (1 / p.wedgeLower + 8 * p.radius ^ 3 / (p.couplingLower ^ 3 * p.depthLower))))⌉₊

theorem result : Convergence LongTails.Setups.TwoSampleQuadraticPerceptron.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p =>
    ⌈24 * (p.radius * Real.log p.ratio / p.slowLower + 1) * (p.radius / p.gain + 1) ^ 2 *
      (3 + 2 * p.couplingUpper * Real.log p.ratio / p.slowLower +
        Real.log (p.size * (1 / p.wedgeLower +
          8 * p.radius ^ 3 / (p.couplingLower ^ 3 * p.depthLower))))⌉₊)
  refine ⟨algorithm, ?_, ?_⟩
  · rintro p ⟨hR, hgain, hβLo, hβ, hμ, hρ, haLo, hzLo, hS⟩ T hT D O
      ⟨hD, hb1, hb2, hg1, hg2, hcL, hcU, hslow, hratio, hz, hwedge, hb, hsize, hans⟩
    intro _
    rintro ⟨seed, ξ⟩
    have hfun : (fun θ => (algorithm (publicOf p)).update θ
        (answer p.model p.dimension D ((algorithm (publicOf p)).query θ).2)) =
        modelStep p.model p.dimension D (1 / (2 * p.radius)) := by
      funext θ
      simp only [algorithm, update, modelStep, answer, publicOf]
    change Separates p.model p.dimension D
      (execute O (algorithm (publicOf p)) (fun _ => T) seed ξ)
    erw [execute_eq_of_answer_eq O (fun θ => answer p.model p.dimension D θ)
      (fun k q s => hans k (0, q) s), execute_iterate, hfun]
    change Separates p.model p.dimension D
      ((modelStep p.model p.dimension D (1 / (2 * p.radius)))^[T] p.start)
    set c := coordinates p.model p.dimension D p.start with hc
    set σ : ℝ := -(SignType.sign c.z : ℝ) with hσdef
    have hzpos : 0 < |c.z| := lt_of_lt_of_le hzLo hz
    have hz0 : c.z ≠ 0 := abs_pos.mp hzpos
    have hσ : σ ^ 2 = 1 := by
      rcases lt_or_gt_of_ne hz0 with h | h
      · simp [hσdef, sign_neg h]
      · simp [hσdef, sign_pos h]
    have hZ : -σ * c.z = |c.z| := by rw [hσdef, neg_neg]; exact sign_mul_self c.z
    set γ : ℝ := 1 / (2 * p.radius) with hγdef
    have hγ : 0 < γ := by positivity
    have hs := spectrum_bounds D hD hb1 hb2
    obtain ⟨hf2, hs2, hc2, hl2, hl0⟩ := hs
    have hfirst : 0 < (eigenvalues p.model p.dimension D).first := lt_of_lt_of_le hgain hg1
    have hscale : ∀ x y : ℝ, x ≤ y → x / (2 * p.radius) ≤ γ * y := by
      intro x y hxy
      rw [hγdef, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hxy (by positivity)
    have hscale' : ∀ x y : ℝ, x ≤ y → γ * x ≤ y / (2 * p.radius) := by
      intro x y hxy
      rw [hγdef, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hxy (by positivity)
    have hle1 : ∀ y : ℝ, y ≤ 2 * p.radius → γ * y ≤ 1 := by
      intro y hy
      rw [hγdef, one_div_mul_eq_div, div_le_one (by positivity)]
      exact hy
    let g := gains p.model p.dimension D γ
    have hg : g.Standing :=
      { c1_pos := mul_pos hγ hfirst
        c1_le := hle1 _ hf2
        c2_pos := mul_pos hγ (lt_of_lt_of_le hgain hg2)
        c2_le := hle1 _ hs2
        e_pos := mul_pos hγ (lt_of_lt_of_le hβLo hcL)
        m_nonneg := mul_nonneg hγ.le hl0
        m_le := hle1 _ hl2 }
    have hslow' : ((embedState σ c 0).A = 0 ∧ (embedState σ c 0).B = 0) ∨
        p.slowLower / (2 * p.radius) ≤ g.m := by
      rcases model_cases (m := p.model) (d := p.dimension) D p.start with hm | hr
      · right; exact hscale _ _ (hslow hm)
      · left; simp only [embedState]; rw [hc, hr.1, hr.2]; simp
    have hZ' : (embedState σ c 0).Z = |c.z| := by simp only [embedState]; exact hZ
    have hS' : (embedState σ c 0).a + (embedState σ c 0).b + 2 * (embedState σ c 0).Z ≤ p.size := by
      rw [hZ']; simp only [embedState]; linarith
    have hstop := Gains.stops_within hg (x0 := embedState σ c 0)
      (by simp only [embedState]; linarith) (by simpa only [embedState] using hb)
      (by rw [hZ']; exact hzpos) rfl hR hgain hβLo hμ hρ haLo hzLo
      (hscale _ _ hg1) (hscale _ _ hg2) (hscale _ _ hcL) (hscale' _ _ hcU)
      (hle1 _ hc2) ((hcL.trans hc2)) hslow'
      (by simpa only [embedState] using hratio) (by simpa only [embedState] using hwedge)
      (by rw [hZ']; exact hz) hS'
    have hstopT := Gains.stopped_mono hstop hT
    obtain ⟨n, hn⟩ := traj_embed (m := p.model) (d := p.dimension) D hD hσ hγ hfirst p.start T
    rw [← hc] at hn
    change (gains p.model p.dimension D γ).Stopped
      ((gains p.model p.dimension D γ).traj (embedState σ c 0) T) at hstopT
    rw [hn] at hstopT
    exact (separates_iff (m := p.model) (d := p.dimension) D hD hσ hγ hfirst _ n).mpr hstopT
  · intro p hp
    exact ⟨id, 1 / (2 * p.radius), by have := hp.1; positivity, fun _ => rfl, fun _ => rfl,
      fun _ _ => rfl, fun _ => rfl⟩

end OracleTemplate.TwoSampleQuadraticPerceptron
