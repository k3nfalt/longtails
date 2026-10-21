import LongTails.Proofs.MuonNonconvex
import LongTails.Setups.MuonFrobenius
import LongTails.Setups.MuonSpectral

open MeasureTheory

namespace OracleTemplate.Muon

theorem transfer_integral {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ] (Q : Measure Ξ)
    (P : Measure Ω) (π : Ξ → Ω) (hπ : Measurable π) (hQ : Q.map π = P) (F : Ω → ℝ)
    (hF : AEStronglyMeasurable F P) :
    (Integrable F P → Integrable (fun ξ => F (π ξ)) Q) ∧ (∫ ξ, F (π ξ) ∂Q) = ∫ ω, F ω ∂P := by
  subst hQ
  refine ⟨fun h => (integrable_map_measure hF hπ.aemeasurable).mp h, ?_⟩
  exact (integral_map hπ.aemeasurable hF).symm

theorem exists_le_of_avg_le (T : ℕ) (hT : 1 ≤ T) (a : Fin T → ℝ) (ε : ℝ)
    (h : (1 / (T : ℝ)) * ∑ t, a t ≤ ε) : ∃ t, a t ≤ ε := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hne : (Finset.univ : Finset (Fin T)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hs : ∑ t, a t ≤ ∑ _t : Fin T, ε := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hTpos] at h
    linarith
  obtain ⟨t, -, ht⟩ := Finset.exists_le_of_sum_le hne hs
  exact ⟨t, ht⟩

end OracleTemplate.Muon

namespace OracleTemplate.MuonFrobenius

open Muon LongTails.Setups.MuonFrobenius

theorem guarantee {Ω : Type} [MeasurableSpace Ω] (q : Params) (hq : spec.valid q)
    (f : Mat q.m q.n → ℝ) (hf : FrobeniusSmooth q.L f) (hb : BddBelow (Set.range f))
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω)) (g : Mat q.m q.n → Ω → Mat q.m q.n)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat q.m q.n) Ω
      (μ : Measure Ω) f g q.σ)
    {Ξ : Type} [MeasurableSpace Ξ] (Q : Measure Ξ) (π : Ξ → (ℕ → Ω)) (hπ : Measurable π)
    (hQ : Q.map π = (P : Measure (ℕ → Ω))) :
    Guarantee q f (fun ξ (j : Fin (q.T + 1)) => (trajectory (publicInput q) g (π ξ) j).2.1) Q := by
  obtain ⟨hm, hn, hL, hσ, hη, hβ0, hβ1, hB, hT⟩ := hq
  have main := frobenius_main (publicInput q) q.L q.σ hL hσ hη hβ0 hβ1 hB hT f hf.1 hf.2 hb μ P g hiid ho
  obtain ⟨hWm, hAi, hFi, hineq⟩ := main
  set pq := publicInput q
  have tr := fun F hF => transfer_integral Q (P : Measure (ℕ → Ω)) π hπ hQ F hF
  have hAm : ∀ t, AEStronglyMeasurable (fun s => nuclearNorm (gradient f (trajectory pq g s t).2.1))
      (P : Measure (ℕ → Ω)) := fun t => (hAi t).aestronglyMeasurable
  have hFm : ∀ t, AEStronglyMeasurable (fun s => f (trajectory pq g s t).2.1) (P : Measure (ℕ → Ω)) :=
    fun t => (hFi t).aestronglyMeasurable
  have hsum : ∀ t, (∫ ξ, nuclearNorm (gradient f (trajectory pq g (π ξ) t).2.1) ∂Q) =
      ∫ s, nuclearNorm (gradient f (trajectory pq g s t).2.1) ∂(P : Measure (ℕ → Ω)) :=
    fun t => (tr _ (hAm t)).2
  have hdiff : (∫ ξ, f (trajectory pq g (π ξ) 0).2.1 - f (trajectory pq g (π ξ) q.T).2.1 ∂Q) =
      ∫ s, f (trajectory pq g s 0).2.1 - f (trajectory pq g s q.T).2.1 ∂(P : Measure (ℕ → Ω)) :=
    (tr _ ((hFm 0).sub (hFm q.T))).2
  have havg : averageNuclear q f (fun ξ (j : Fin (q.T + 1)) => (trajectory pq g (π ξ) j).2.1) Q =
      (1 / (q.T : ℝ)) * ∑ t ∈ Finset.range q.T,
        ∫ s, nuclearNorm (gradient f (trajectory pq g s t).2.1) ∂(P : Measure (ℕ → Ω)) := by
    simp only [averageNuclear, Fin.val_castSucc, hsum]
    rw [Fin.sum_univ_eq_sum_range (fun t => ∫ s, nuclearNorm (gradient f (trajectory pq g s t).2.1)
      ∂(P : Measure (ℕ → Ω))) q.T]
  have hdiff' : (∫ ξ, f ((fun ξ (j : Fin (q.T + 1)) => (trajectory pq g (π ξ) j).2.1) ξ 0) -
      f ((fun ξ (j : Fin (q.T + 1)) => (trajectory pq g (π ξ) j).2.1) ξ (Fin.last q.T)) ∂Q) =
      ∫ s, f (trajectory pq g s 0).2.1 - f (trajectory pq g s q.T).2.1 ∂(P : Measure (ℕ → Ω)) := by
    rw [← hdiff]; rfl
  have hr1 : (1 : ℝ) ≤ ((min q.m q.n : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ min q.m q.n by omega)
  have hTpos : (0 : ℝ) < q.T := by exact_mod_cast (show 0 < q.T by omega)
  set r : ℝ := ((min q.m q.n : ℕ) : ℝ)
  set Δ := f q.W0 - ⨅ W, f W
  have hEΔ : (∫ s, f (trajectory pq g s 0).2.1 - f (trajectory pq g s q.T).2.1 ∂(P : Measure (ℕ → Ω))) ≤ Δ := by
    have h1 : ∀ s, f (trajectory pq g s 0).2.1 - f (trajectory pq g s q.T).2.1 ≤ Δ := by
      intro s
      have := ciInf_le hb (trajectory pq g s q.T).2.1
      change f q.W0 - f (trajectory pq g s q.T).2.1 ≤ f q.W0 - ⨅ W, f W
      linarith
    calc _ ≤ ∫ _s, Δ ∂(P : Measure (ℕ → Ω)) :=
          integral_mono ((hFi 0).sub (hFi q.T)) (integrable_const _) h1
      _ = Δ := by simp
  refine ⟨fun t => (hWm t).comp hπ, fun t => (tr _ (hAm t)).1 (hAi t),
    fun t => (tr _ (hFm t)).1 (hFi t), ?_, ?_⟩
  · rw [havg, hdiff']
    exact hineq
  · intro hLpos hB1 hηdef hβdef
    have hBr : ((q.B : ℕ) : ℝ) = 1 := by rw [hB1]; norm_num
    have hrpos : 0 < r := by linarith
    have hK : 0 < r * q.L := by positivity
    have hηdef' : q.η = Real.sqrt ((1 - q.β) * Δ / (q.T * (r * q.L))) := by
      rw [hηdef]; congr 1; ring
    have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
    have hβdef' : 1 - q.β = if q.σ = 0 then 1 else
        min (Real.sqrt (r * q.L * Δ) / (q.σ * Real.sqrt (r * q.T))) 1 := by
      rw [hβdef]
      split_ifs with h0
      · rfl
      · congr 1
        rw [show r * q.L * Δ = r * (q.L * Δ) by ring, Real.sqrt_mul hrpos.le, Real.sqrt_mul hrpos.le,
          show q.σ * (Real.sqrt r * Real.sqrt q.T) = Real.sqrt r * (q.σ * Real.sqrt q.T) by ring,
          mul_div_mul_left _ _ hsr.ne']
    have tg := tuned_generic r (r * q.L) Δ q.σ q.β q.T q.η
      (∫ s, f (trajectory pq g s 0).2.1 - f (trajectory pq g s q.T).2.1 ∂(P : Measure (ℕ → Ω)))
      hrpos hK hσ hβ0 hβ1 hTpos hη hηdef' hβdef' hEΔ
    have hΔ : 0 < Δ := by
      by_contra hc
      have : (1 - q.β) * Δ / (r * q.T * q.L) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hc))
          (by positivity)
      rw [hηdef, Real.sqrt_eq_zero'.mpr this] at hη
      exact lt_irrefl _ hη
    have hbound : averageNuclear q f (fun ξ (j : Fin (q.T + 1)) => (trajectory pq g (π ξ) j).2.1) Q ≤
        6 * ((r ^ 2 * q.L * Δ * q.σ ^ 2 / q.T) ^ (1 / 4 : ℝ) + Real.sqrt (r * q.L * Δ / q.T) +
          Real.sqrt r * q.σ ^ 2 / Real.sqrt (q.L * Δ * q.T)) := by
      rw [havg]
      have hineq2 : (1 / (q.T : ℝ)) * ∑ t ∈ Finset.range q.T,
          (∫ s, nuclearNorm (gradient f (trajectory pq g s t).2.1) ∂(P : Measure (ℕ → Ω))) ≤
          (∫ s, f (trajectory pq g s 0).2.1 - f (trajectory pq g s q.T).2.1 ∂(P : Measure (ℕ → Ω))) /
            (q.T * q.η) + q.L * r * q.η / 2 +
          2 * q.σ * Real.sqrt (r * (1 - q.β)) / Real.sqrt (q.B * (1 + q.β)) +
          2 * q.β * q.σ * Real.sqrt r / ((1 - q.β) * q.T * Real.sqrt q.B) +
          2 * r * q.η * q.β * q.L / (1 - q.β) := hineq
      refine hineq2.trans ?_
      have e1 : r * (r * q.L) * Δ * q.σ ^ 2 / q.T = r ^ 2 * q.L * Δ * q.σ ^ 2 / q.T := by ring
      have e3 : r * q.σ ^ 2 / Real.sqrt (r * q.L * Δ * q.T) = Real.sqrt r * q.σ ^ 2 / Real.sqrt (q.L * Δ * q.T) := by
        rw [show r * q.L * Δ * q.T = r * (q.L * Δ * q.T) by ring, Real.sqrt_mul hrpos.le]
        rw [show r * q.σ ^ 2 = Real.sqrt r * (Real.sqrt r * q.σ ^ 2) by
          rw [← mul_assoc, Real.mul_self_sqrt hrpos.le], mul_div_mul_left _ _ hsr.ne']
      rw [e1, e3] at tg
      simp only [hBr, Real.sqrt_one, mul_one, one_mul]
      have x1 : r * q.L * q.η / 2 = q.L * r * q.η / 2 := by ring
      have x2 : 2 * q.η * q.β * (r * q.L) / (1 - q.β) = 2 * r * q.η * q.β * q.L / (1 - q.β) := by ring
      linarith
    refine ⟨hbound, fun ε hε hTbig => ?_⟩
    have hc := complexity_generic r (r * q.L) Δ q.σ q.T ε hrpos hK hΔ hTpos hε (by
      have e : 18 ^ 2 * r ^ 2 * q.σ ^ 4 / (r * q.L * Δ * ε ^ 2) = 18 ^ 2 * r * q.σ ^ 4 / (q.L * Δ * ε ^ 2) := by
        field_simp
      have e' : 18 ^ 4 * r * (r * q.L) * Δ * q.σ ^ 2 / ε ^ 4 = 18 ^ 4 * r ^ 2 * q.L * Δ * q.σ ^ 2 / ε ^ 4 := by
        ring
      rw [e, e', show 18 ^ 2 * (r * q.L) * Δ / ε ^ 2 = 18 ^ 2 * r * q.L * Δ / ε ^ 2 by ring]
      exact hTbig)
    have e1 : r * (r * q.L) * Δ * q.σ ^ 2 / q.T = r ^ 2 * q.L * Δ * q.σ ^ 2 / q.T := by ring
    have e3 : r * q.σ ^ 2 / Real.sqrt (r * q.L * Δ * q.T) = Real.sqrt r * q.σ ^ 2 / Real.sqrt (q.L * Δ * q.T) := by
      rw [show r * q.L * Δ * q.T = r * (q.L * Δ * q.T) by ring, Real.sqrt_mul hrpos.le]
      rw [show r * q.σ ^ 2 = Real.sqrt r * (Real.sqrt r * q.σ ^ 2) by
        rw [← mul_assoc, Real.mul_self_sqrt hrpos.le], mul_div_mul_left _ _ hsr.ne']
    rw [e1, e3] at hc
    have havgε := hbound.trans hc
    refine ⟨havgε, ?_⟩
    exact exists_le_of_avg_le q.T hT _ ε havgε

end OracleTemplate.MuonFrobenius

namespace OracleTemplate.MuonSpectral

open Muon LongTails.Setups.MuonSpectral

theorem guarantee {Ω : Type} [MeasurableSpace Ω] (q : Params) (hq : spec.valid q)
    (f : Mat q.m q.n → ℝ) (hf : SpectralSmooth q.Ls f) (hb : BddBelow (Set.range f))
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω)) (g : Mat q.m q.n → Ω → Mat q.m q.n)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat q.m q.n) Ω
      (μ : Measure Ω) f g q.σ)
    {Ξ : Type} [MeasurableSpace Ξ] (Q : Measure Ξ) (π : Ξ → (ℕ → Ω)) (hπ : Measurable π)
    (hQ : Q.map π = (P : Measure (ℕ → Ω))) :
    Guarantee q f (fun ξ (j : Fin (q.T + 1)) => (trajectory (publicInput q) g (π ξ) j).2.1) Q := by
  obtain ⟨hm, hn, hL, hσ, hη, hβ0, hβ1, hB, hT⟩ := hq
  have main := spectral_main (publicInput q) q.Ls q.σ hL hσ hη hβ0 hβ1 hB hT f hf.1 hf.2 hb μ P g hiid ho
  obtain ⟨hWm, hAi, hFi, hineq⟩ := main
  set pq := publicInput q
  have tr := fun F hF => transfer_integral Q (P : Measure (ℕ → Ω)) π hπ hQ F hF
  have hAm : ∀ t, AEStronglyMeasurable (fun s => nuclearNorm (gradient f (trajectory pq g s t).2.1))
      (P : Measure (ℕ → Ω)) := fun t => (hAi t).aestronglyMeasurable
  have hFm : ∀ t, AEStronglyMeasurable (fun s => f (trajectory pq g s t).2.1) (P : Measure (ℕ → Ω)) :=
    fun t => (hFi t).aestronglyMeasurable
  have hsum : ∀ t, (∫ ξ, nuclearNorm (gradient f (trajectory pq g (π ξ) t).2.1) ∂Q) =
      ∫ s, nuclearNorm (gradient f (trajectory pq g s t).2.1) ∂(P : Measure (ℕ → Ω)) :=
    fun t => (tr _ (hAm t)).2
  have hdiff : (∫ ξ, f (trajectory pq g (π ξ) 0).2.1 - f (trajectory pq g (π ξ) q.T).2.1 ∂Q) =
      ∫ s, f (trajectory pq g s 0).2.1 - f (trajectory pq g s q.T).2.1 ∂(P : Measure (ℕ → Ω)) :=
    (tr _ ((hFm 0).sub (hFm q.T))).2
  have havg : averageNuclear q f (fun ξ (j : Fin (q.T + 1)) => (trajectory pq g (π ξ) j).2.1) Q =
      (1 / (q.T : ℝ)) * ∑ t ∈ Finset.range q.T,
        ∫ s, nuclearNorm (gradient f (trajectory pq g s t).2.1) ∂(P : Measure (ℕ → Ω)) := by
    simp only [averageNuclear, Fin.val_castSucc, hsum]
    rw [Fin.sum_univ_eq_sum_range (fun t => ∫ s, nuclearNorm (gradient f (trajectory pq g s t).2.1)
      ∂(P : Measure (ℕ → Ω))) q.T]
  have hdiff' : (∫ ξ, f ((fun ξ (j : Fin (q.T + 1)) => (trajectory pq g (π ξ) j).2.1) ξ 0) -
      f ((fun ξ (j : Fin (q.T + 1)) => (trajectory pq g (π ξ) j).2.1) ξ (Fin.last q.T)) ∂Q) =
      ∫ s, f (trajectory pq g s 0).2.1 - f (trajectory pq g s q.T).2.1 ∂(P : Measure (ℕ → Ω)) := by
    rw [← hdiff]; rfl
  have hr1 : (1 : ℝ) ≤ ((min q.m q.n : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ min q.m q.n by omega)
  have hTpos : (0 : ℝ) < q.T := by exact_mod_cast (show 0 < q.T by omega)
  set r : ℝ := ((min q.m q.n : ℕ) : ℝ)
  set Δ := f q.W0 - ⨅ W, f W
  have hEΔ : (∫ s, f (trajectory pq g s 0).2.1 - f (trajectory pq g s q.T).2.1 ∂(P : Measure (ℕ → Ω))) ≤ Δ := by
    have h1 : ∀ s, f (trajectory pq g s 0).2.1 - f (trajectory pq g s q.T).2.1 ≤ Δ := by
      intro s
      have := ciInf_le hb (trajectory pq g s q.T).2.1
      change f q.W0 - f (trajectory pq g s q.T).2.1 ≤ f q.W0 - ⨅ W, f W
      linarith
    calc _ ≤ ∫ _s, Δ ∂(P : Measure (ℕ → Ω)) :=
          integral_mono ((hFi 0).sub (hFi q.T)) (integrable_const _) h1
      _ = Δ := by simp
  refine ⟨fun t => (hWm t).comp hπ, fun t => (tr _ (hAm t)).1 (hAi t),
    fun t => (tr _ (hFm t)).1 (hFi t), ?_, ?_⟩
  · rw [havg, hdiff']
    exact hineq
  · intro hLpos hB1 hηdef hβdef
    have hBr : ((q.B : ℕ) : ℝ) = 1 := by rw [hB1]; norm_num
    have hrpos : 0 < r := by linarith
    have tg := tuned_generic r q.Ls Δ q.σ q.β q.T q.η
      (∫ s, f (trajectory pq g s 0).2.1 - f (trajectory pq g s q.T).2.1 ∂(P : Measure (ℕ → Ω)))
      hrpos hLpos hσ hβ0 hβ1 hTpos hη hηdef hβdef hEΔ
    have hΔ : 0 < Δ := by
      by_contra hc
      have : (1 - q.β) * Δ / (q.T * q.Ls) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hc))
          (by positivity)
      rw [hηdef, Real.sqrt_eq_zero'.mpr this] at hη
      exact lt_irrefl _ hη
    have hbound : averageNuclear q f (fun ξ (j : Fin (q.T + 1)) => (trajectory pq g (π ξ) j).2.1) Q ≤
        6 * ((r * q.Ls * Δ * q.σ ^ 2 / q.T) ^ (1 / 4 : ℝ) + Real.sqrt (q.Ls * Δ / q.T) +
          r * q.σ ^ 2 / Real.sqrt (q.Ls * Δ * q.T)) := by
      rw [havg]
      have hineq2 : (1 / (q.T : ℝ)) * ∑ t ∈ Finset.range q.T,
          (∫ s, nuclearNorm (gradient f (trajectory pq g s t).2.1) ∂(P : Measure (ℕ → Ω))) ≤
          (∫ s, f (trajectory pq g s 0).2.1 - f (trajectory pq g s q.T).2.1 ∂(P : Measure (ℕ → Ω))) /
            (q.T * q.η) + q.Ls * q.η / 2 +
          2 * q.σ * Real.sqrt (r * (1 - q.β)) / Real.sqrt ((1 + q.β) * q.B) +
          2 * q.β * q.σ * Real.sqrt r / ((1 - q.β) * q.T * Real.sqrt q.B) +
          2 * q.η * q.β * q.Ls / (1 - q.β) := hineq
      refine hineq2.trans ?_
      simp only [hBr, Real.sqrt_one, mul_one] at hineq2 ⊢
      linarith
    refine ⟨hbound, fun ε hε hTbig => ?_⟩
    have hc := complexity_generic r q.Ls Δ q.σ q.T ε hrpos hLpos hΔ hTpos hε hTbig
    have havgε := hbound.trans hc
    exact ⟨havgε, exists_le_of_avg_le q.T hT _ ε havgε⟩

end OracleTemplate.MuonSpectral
