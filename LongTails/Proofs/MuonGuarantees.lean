import LongTails.Proofs.MuonNonconvex
import LongTails.Setups.MuonFrobenius
import LongTails.Setups.MuonSpectral
import Mathlib.Probability.ProbabilityMassFunction.Integrals

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

theorem guarantee {Ω : Type} [MeasurableSpace Ω] (q : Constants) (hq : Valid q)
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

theorem guarantee {Ω : Type} [MeasurableSpace Ω] (q : Constants) (hq : Valid q)
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

namespace OracleTemplate.MuonTuning

open OracleTemplate OracleTemplate.Muon

open OracleTemplate.MuonTuning

theorem tuning_bounds (p : OracleTemplate.MuonTuning.Public) (C : ℝ)
    (hm : 0 < p.m) (hn : 0 < p.n) (hC : 0 < C) (hΔ : 0 < p.Δ)
    (hε : 0 < p.ε) (hσ : 0 ≤ p.σ) :
    0 ≤ momentum p C ∧ momentum p C < 1 ∧ 0 < stepSize p C ∧
    1 ≤ horizon p C ∧ threshold p C ≤ (horizon p C : ℝ) := by
  have hr : (0 : ℝ) < (min p.m p.n : ℕ) := by
    exact_mod_cast (show 0 < min p.m p.n by omega)
  have hthreshold : 0 < threshold p C := by
    dsimp only [threshold]
    positivity
  have hceilpos : 0 < ⌈threshold p C⌉₊ := Nat.ceil_pos.mpr hthreshold
  have hK : 1 ≤ horizon p C :=
    (Nat.succ_le_of_lt hceilpos).trans (Nat.le_succ _)
  have hKpos : (0 : ℝ) < horizon p C := by
    exact_mod_cast (show 0 < horizon p C from hK)
  have hceil : threshold p C ≤ (horizon p C : ℝ) := by
    calc
      _ ≤ (⌈threshold p C⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ _ := by simp only [horizon, Nat.cast_add, Nat.cast_one]; linarith
  have ha : 0 < 1 - momentum p C ∧ 1 - momentum p C ≤ 1 := by
    simp only [momentum, sub_sub_cancel]
    by_cases hzero : p.σ = 0
    · simp only [hzero, ite_true]
      norm_num
    · simp only [hzero, ite_false]
      have hσpos : 0 < p.σ := lt_of_le_of_ne hσ (Ne.symm hzero)
      constructor
      · apply lt_min
        · apply div_pos
          · exact Real.sqrt_pos.mpr (mul_pos hC hΔ)
          · exact mul_pos hσpos (Real.sqrt_pos.mpr (mul_pos hr hKpos))
        · norm_num
      · exact min_le_right _ _
  refine ⟨by linarith [ha.2], by linarith [ha.1], ?_, hK, hceil⟩
  exact Real.sqrt_pos.mpr (div_pos (mul_pos ha.1 hΔ) (mul_pos hKpos hC))

theorem scalar_accuracy (p : OracleTemplate.MuonTuning.Public) (C E : ℝ)
    (hm : 0 < p.m) (hn : 0 < p.n) (hC : 0 < C) (hΔ : 0 < p.Δ)
    (hε : 0 < p.ε) (hσ : 0 ≤ p.σ) (hE : E ≤ p.Δ) :
    let r : ℝ := (min p.m p.n : ℕ)
    let K : ℝ := horizon p C
    let β := momentum p C
    let η := stepSize p C
    E / (K * η) + C * η / 2 + 2 * p.σ * Real.sqrt (r * (1 - β)) / Real.sqrt (1 + β) +
      2 * β * p.σ * Real.sqrt r / ((1 - β) * K) + 2 * η * β * C / (1 - β) ≤ p.ε := by
  dsimp only
  obtain ⟨hβ0, hβ1, hη, hK, hthreshold⟩ := tuning_bounds p C hm hn hC hΔ hε hσ
  have hr : (0 : ℝ) < (min p.m p.n : ℕ) := by
    exact_mod_cast (show 0 < min p.m p.n by omega)
  have hKpos : (0 : ℝ) < horizon p C := by
    exact_mod_cast (show 0 < horizon p C from hK)
  have hβ : 1 - momentum p C =
      if p.σ = 0 then 1 else
        min (Real.sqrt (C * p.Δ) / (p.σ * Real.sqrt (((min p.m p.n : ℕ) : ℝ) * horizon p C))) 1 := by
    simp only [momentum, sub_sub_cancel]
  apply (tuned_generic ((min p.m p.n : ℕ) : ℝ) C p.Δ p.σ (momentum p C)
    (horizon p C : ℝ) (stepSize p C) E hr hC hσ hβ0 hβ1 hKpos hη rfl hβ hE).trans
  exact complexity_generic ((min p.m p.n : ℕ) : ℝ) C p.Δ p.σ (horizon p C : ℝ) p.ε
    hr hC hΔ hKpos hε hthreshold

end OracleTemplate.MuonTuning

namespace OracleTemplate.MuonTuning

open OracleTemplate OracleTemplate.Muon

open OracleTemplate.MuonTuning

theorem execute_random {Ω : Type} [MeasurableSpace Ω] (q : OracleTemplate.Muon.Public)
    (N : ℕ) (hT : q.T = N + 1) (hB : 1 ≤ q.B)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Mat q.m q.n → Ω → Mat q.m q.n)
    (j : Fin (N + 1)) (tape : ℕ → Ω) :
    execute (sampleOracle P g) (randomMuon q N) (fun _ => q.T * q.B) j tape =
      (trajectory q g tape j.val).2.1 := by
  let s0 : OracleTemplate.Muon.State q := (muon q).initial ()
  let F : OracleTemplate.Muon.State q × ℕ → OracleTemplate.Muon.State q × ℕ :=
    fun sc => (OracleTemplate.Muon.step q sc.1 (g sc.1.point (tape sc.2)), sc.2 + 1)
  let F' : (OracleTemplate.Muon.State q × Fin (N + 1)) × ℕ →
      (OracleTemplate.Muon.State q × Fin (N + 1)) × ℕ :=
    fun sc => ((OracleTemplate.Muon.step q sc.1.1 (g sc.1.1.point (tape sc.2)), sc.1.2), sc.2 + 1)
  have hit : ∀ k, F'^[k] ((s0, j), 0) = (((F^[k] (s0, 0)).1, j), (F^[k] (s0, 0)).2) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
  have hj : j.val < q.T + 1 := by have := j.isLt; omega
  have hsource := congrFun (execute_muon q hB P g () tape) ⟨j.val, hj⟩
  erw [execute_indexed_of_answer _ _ _ _ _ (fun k query => g query.2 (tape k))
    (fun _ _ => rfl)] at hsource
  change (F^[q.T * q.B] (s0, 0)).1.iterates j.val = (trajectory q g tape j.val).2.1 at hsource
  erw [execute_indexed_of_answer _ _ _ _ _ (fun k query => g query.2 (tape k)) (fun _ _ => rfl)]
  change (F'^[q.T * q.B] ((s0, j), 0)).1.1.iterates
    (F'^[q.T * q.B] ((s0, j), 0)).1.2.val = (trajectory q g tape j.val).2.1
  rw [hit]
  exact hsource

theorem uniform_selection {Ω : Type} [MeasurableSpace Ω] {m n : ℕ} (N : ℕ)
    (P : ProbabilityMeasure Ω) (f : Mat m n → ℝ) (W : Fin (N + 1) → Ω → Mat m n)
    (hW : ∀ j, Measurable (W j))
    (hI : ∀ j, Integrable (fun ω => nuclearNorm (gradient f (W j ω))) (P : Measure Ω)) :
    Measurable (fun z : Fin (N + 1) × Ω => W z.1 z.2) ∧
    Integrable (fun z : Fin (N + 1) × Ω => nuclearNorm (gradient f (W z.1 z.2)))
      ((PMF.uniformOfFintype (Fin (N + 1))).toMeasure.prod (P : Measure Ω)) ∧
    (∫ z : Fin (N + 1) × Ω, nuclearNorm (gradient f (W z.1 z.2))
      ∂((PMF.uniformOfFintype (Fin (N + 1))).toMeasure.prod (P : Measure Ω))) =
      (1 / ((N + 1 : ℕ) : ℝ)) * ∑ j : Fin (N + 1),
        ∫ ω, nuclearNorm (gradient f (W j ω)) ∂(P : Measure Ω) := by
  classical
  let μ : Measure (Fin (N + 1)) := (PMF.uniformOfFintype (Fin (N + 1))).toMeasure
  let Q : Measure (Fin (N + 1) × Ω) := μ.prod (P : Measure Ω)
  let F (j : Fin (N + 1)) (ω : Ω) : ℝ := nuclearNorm (gradient f (W j ω))
  have hind (j : Fin (N + 1)) :
      Integrable ({z : Fin (N + 1) × Ω | z.1 = j}.indicator (fun z => F j z.2)) Q := by
    apply (measurePreserving_snd.integrable_comp_of_integrable (hI j)).indicator
    exact measurable_fst (measurableSet_singleton j)
  have hsplit : (fun z : Fin (N + 1) × Ω => F z.1 z.2) =
      fun z => ∑ j : Fin (N + 1), {z : Fin (N + 1) × Ω | z.1 = j}.indicator (fun z => F j z.2) z := by
    funext z
    simp [Set.indicator, eq_comm]
  have hprod : Integrable (fun z : Fin (N + 1) × Ω => F z.1 z.2) Q := by
    rw [hsplit]
    exact integrable_finsetSum Finset.univ (fun j _ => hind j)
  refine ⟨measurable_from_prod_countable_right hW, hprod, ?_⟩
  rw [integral_prod _ hprod, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, ← Finset.mul_sum, one_div]
  rfl

end OracleTemplate.MuonTuning

namespace OracleTemplate.MuonFrobenius

open OracleTemplate OracleTemplate.Muon

theorem trajectory_accuracy {Ω : Type} [MeasurableSpace Ω] (p : LongTails.Setups.MuonFrobenius.Params)
    (hp : LongTails.Setups.MuonFrobenius.spec.valid p) (f : Mat p.m p.n → ℝ)
    (hf : LongTails.Setups.MuonFrobenius.FrobeniusSmooth p.L f)
    (hb : BddBelow (Set.range f)) (hΔ : f p.W0 - ⨅ W, f W ≤ p.Δ)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Mat p.m p.n → Ω → Mat p.m p.n)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat p.m p.n) Ω
      (μ : Measure Ω) f g p.σ) :
    let q := OracleTemplate.MuonTuning.sourceInput p.toPublic (((min p.m p.n : ℕ) : ℝ) * p.L)
    (∀ t, Measurable (fun s => (trajectory q g s t).2.1)) ∧
    (∀ t, Integrable (fun s => nuclearNorm (gradient f (trajectory q g s t).2.1)) (P : Measure (ℕ → Ω))) ∧
    (1 / (q.T : ℝ)) * ∑ t ∈ Finset.range q.T,
      (∫ s, nuclearNorm (gradient f (trajectory q g s t).2.1) ∂(P : Measure (ℕ → Ω))) ≤ p.ε := by
  obtain ⟨hm, hn, hL, hσ, hD, hε⟩ := hp
  let C : ℝ := ((min p.m p.n : ℕ) : ℝ) * p.L
  have hr : (0 : ℝ) < (min p.m p.n : ℕ) := by
    exact_mod_cast (show 0 < min p.m p.n by omega)
  have hC : 0 < C := mul_pos hr hL
  obtain ⟨hβ0, hβ1, hη, hK, _⟩ :=
    OracleTemplate.MuonTuning.tuning_bounds p.toPublic C hm hn hC hD hε hσ
  let q := OracleTemplate.MuonTuning.sourceInput p.toPublic C
  obtain ⟨hW, hA, hF, hmain⟩ := frobenius_main q p.L p.σ hL.le hσ hη hβ0 hβ1
    (show 1 ≤ q.B from le_refl 1) hK f hf.1 hf.2 hb μ P g hiid ho
  have hE : (∫ s, f (trajectory q g s 0).2.1 - f (trajectory q g s q.T).2.1
      ∂(P : Measure (ℕ → Ω))) ≤ p.Δ := by
    have hpoint : ∀ s, f (trajectory q g s 0).2.1 - f (trajectory q g s q.T).2.1 ≤ p.Δ := by
      intro s
      have hlow := ciInf_le hb (trajectory q g s q.T).2.1
      change f p.W0 - f (trajectory q g s q.T).2.1 ≤ p.Δ
      linarith
    calc
      _ ≤ ∫ _s, p.Δ ∂(P : Measure (ℕ → Ω)) :=
        integral_mono ((hF 0).sub (hF q.T)) (integrable_const _) hpoint
      _ = p.Δ := by simp
  have hscalar := OracleTemplate.MuonTuning.scalar_accuracy p.toPublic C _ hm hn hC hD hε hσ hE
  refine ⟨hW, hA, hmain.trans ?_⟩
  convert hscalar using 1
  simp only [q, C, OracleTemplate.MuonTuning.sourceInput, Nat.cast_one, one_mul, mul_one, Real.sqrt_one]
  ring

theorem execution_accuracy (p : LongTails.Setups.MuonFrobenius.Params)
    (hp : LongTails.Setups.MuonFrobenius.spec.valid p) (f : Mat p.m p.n → ℝ)
    (O : Oracle (Mat p.m p.n) (Mat p.m p.n)) (hO : LongTails.Setups.MuonFrobenius.spec.admissible p f O) :
    let A := OracleTemplate.MuonTuning.frobenius p.toPublic
    LongTails.Setups.MuonFrobenius.spec.successful p f
      (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
        execute O A (fun _ => ⌈18 ^ 4 * ((min p.m p.n : ℕ) : ℝ) ^ 2 * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4 + 18 ^ 2 * ((min p.m p.n : ℕ) : ℝ) * p.L * p.Δ / p.ε ^ 2 + 18 ^ 2 * ((min p.m p.n : ℕ) : ℝ) * p.σ ^ 4 / (p.L * p.Δ * p.ε ^ 2)⌉₊ + 1) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hf, hb, hD, hmodel⟩ := hO
  obtain ⟨Ω, mΩ, hmodel⟩ := hmodel
  let : MeasurableSpace Ω := mΩ
  obtain ⟨μ, P, g, hiid, hg, rfl⟩ := hmodel
  let r : ℝ := (min p.m p.n : ℕ)
  let C := r * p.L
  let q := OracleTemplate.MuonTuning.sourceInput p.toPublic C
  let N := ⌈OracleTemplate.MuonTuning.threshold p.toPublic C⌉₊
  have hr : 0 < r := by
    change (0 : ℝ) < (min p.m p.n : ℕ)
    exact_mod_cast (show 0 < min p.m p.n by have := hp.1; have := hp.2.1; omega)
  have hthreshold : OracleTemplate.MuonTuning.threshold p.toPublic C =
      18 ^ 4 * r ^ 2 * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4 + 18 ^ 2 * r * p.L * p.Δ / p.ε ^ 2 +
      18 ^ 2 * r * p.σ ^ 4 / (p.L * p.Δ * p.ε ^ 2) := by
    dsimp only [OracleTemplate.MuonTuning.threshold, C]
    change 18 ^ 4 * r * (r * p.L) * p.Δ * p.σ ^ 2 / p.ε ^ 4 +
      18 ^ 2 * (r * p.L) * p.Δ / p.ε ^ 2 +
      18 ^ 2 * r ^ 2 * p.σ ^ 4 / (r * p.L * p.Δ * p.ε ^ 2) = _
    field_simp [ne_of_gt hr, ne_of_gt hp.2.2.1, ne_of_gt hp.2.2.2.2.1, ne_of_gt hp.2.2.2.2.2]
  have hbudget : ⌈18 ^ 4 * r ^ 2 * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4 +
      18 ^ 2 * r * p.L * p.Δ / p.ε ^ 2 + 18 ^ 2 * r * p.σ ^ 4 / (p.L * p.Δ * p.ε ^ 2)⌉₊ + 1 = q.T := by
    change _ = ⌈OracleTemplate.MuonTuning.threshold p.toPublic C⌉₊ + 1
    rw [hthreshold]
  let W : Fin (N + 1) → (ℕ → Ω) → Mat p.m p.n := fun j s => (trajectory q g s j.val).2.1
  have htraj := trajectory_accuracy p hp f hf hb hD μ P g hiid hg
  have hsel := OracleTemplate.MuonTuning.uniform_selection N P f W
    (fun j => htraj.1 j.val) (fun j => htraj.2.1 j.val)
  let out : Fin (N + 1) × (ℕ → Ω) → Mat p.m p.n := fun seed =>
    execute (sampleOracle P g) (OracleTemplate.MuonTuning.randomMuon q N)
      (fun _ => q.T) seed.1 seed.2
  have hout : out = fun seed => W seed.1 seed.2 := by
    funext seed
    have he := OracleTemplate.MuonTuning.execute_random q N rfl (le_refl 1) P g seed.1 seed.2
    change execute (sampleOracle P g) (OracleTemplate.MuonTuning.randomMuon q N)
      (fun _ => q.T * 1) seed.1 seed.2 = W seed.1 seed.2 at he
    dsimp only [q, OracleTemplate.MuonTuning.sourceInput] at he
    simpa only [out, q, OracleTemplate.MuonTuning.sourceInput, Nat.mul_one] using he
  dsimp only
  rw [hbudget]
  change Measurable out ∧
    Integrable (fun z => nuclearNorm (gradient f (out z)))
      ((PMF.uniformOfFintype (Fin (N + 1))).toMeasure.prod (P : Measure (ℕ → Ω))) ∧
    (∫ z, nuclearNorm (gradient f (out z))
      ∂((PMF.uniformOfFintype (Fin (N + 1))).toMeasure.prod (P : Measure (ℕ → Ω)))) ≤ p.ε
  rw [hout]
  refine ⟨hsel.1, hsel.2.1, hsel.2.2.trans_le ?_⟩
  change (1 / ((N + 1 : ℕ) : ℝ)) * ∑ j : Fin (N + 1),
    (∫ s, nuclearNorm (gradient f (trajectory q g s j.val).2.1) ∂(P : Measure (ℕ → Ω))) ≤ p.ε
  rw [Fin.sum_univ_eq_sum_range (fun t =>
    ∫ s, nuclearNorm (gradient f (trajectory q g s t).2.1) ∂(P : Measure (ℕ → Ω))) (N + 1)]
  exact htraj.2.2

end OracleTemplate.MuonFrobenius

namespace OracleTemplate.MuonSpectral

open OracleTemplate OracleTemplate.Muon

theorem trajectory_accuracy {Ω : Type} [MeasurableSpace Ω] (p : LongTails.Setups.MuonSpectral.Params)
    (hp : LongTails.Setups.MuonSpectral.spec.valid p) (f : Mat p.m p.n → ℝ)
    (hf : LongTails.Setups.MuonSpectral.SpectralSmooth p.L f)
    (hb : BddBelow (Set.range f)) (hΔ : f p.W0 - ⨅ W, f W ≤ p.Δ)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Mat p.m p.n → Ω → Mat p.m p.n)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat p.m p.n) Ω
      (μ : Measure Ω) f g p.σ) :
    let q := OracleTemplate.MuonTuning.sourceInput p.toPublic p.L
    (∀ t, Measurable (fun s => (trajectory q g s t).2.1)) ∧
    (∀ t, Integrable (fun s => nuclearNorm (gradient f (trajectory q g s t).2.1)) (P : Measure (ℕ → Ω))) ∧
    (1 / (q.T : ℝ)) * ∑ t ∈ Finset.range q.T,
      (∫ s, nuclearNorm (gradient f (trajectory q g s t).2.1) ∂(P : Measure (ℕ → Ω))) ≤ p.ε := by
  obtain ⟨hm, hn, hL, hσ, hD, hε⟩ := hp
  obtain ⟨hβ0, hβ1, hη, hK, _⟩ :=
    OracleTemplate.MuonTuning.tuning_bounds p.toPublic p.L hm hn hL hD hε hσ
  let q := OracleTemplate.MuonTuning.sourceInput p.toPublic p.L
  obtain ⟨hW, hA, hF, hmain⟩ := spectral_main q p.L p.σ hL.le hσ hη hβ0 hβ1
    (show 1 ≤ q.B from le_refl 1) hK f hf.1 hf.2 hb μ P g hiid ho
  have hE : (∫ s, f (trajectory q g s 0).2.1 - f (trajectory q g s q.T).2.1
      ∂(P : Measure (ℕ → Ω))) ≤ p.Δ := by
    have hpoint : ∀ s, f (trajectory q g s 0).2.1 - f (trajectory q g s q.T).2.1 ≤ p.Δ := by
      intro s
      have hlow := ciInf_le hb (trajectory q g s q.T).2.1
      change f p.W0 - f (trajectory q g s q.T).2.1 ≤ p.Δ
      linarith
    calc
      _ ≤ ∫ _s, p.Δ ∂(P : Measure (ℕ → Ω)) :=
        integral_mono ((hF 0).sub (hF q.T)) (integrable_const _) hpoint
      _ = p.Δ := by simp
  have hscalar := OracleTemplate.MuonTuning.scalar_accuracy p.toPublic p.L _ hm hn hL hD hε hσ hE
  refine ⟨hW, hA, hmain.trans ?_⟩
  convert hscalar using 1
  simp only [q, OracleTemplate.MuonTuning.sourceInput, Nat.cast_one, mul_one, Real.sqrt_one]

theorem execution_accuracy (p : LongTails.Setups.MuonSpectral.Params)
    (hp : LongTails.Setups.MuonSpectral.spec.valid p) (f : Mat p.m p.n → ℝ)
    (O : Oracle (Mat p.m p.n) (Mat p.m p.n)) (hO : LongTails.Setups.MuonSpectral.spec.admissible p f O) :
    let A := OracleTemplate.MuonTuning.spectral p.toPublic
    LongTails.Setups.MuonSpectral.spec.successful p f
      (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
        execute O A (fun _ => ⌈18 ^ 4 * ((min p.m p.n : ℕ) : ℝ) * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4 + 18 ^ 2 * p.L * p.Δ / p.ε ^ 2 + 18 ^ 2 * ((min p.m p.n : ℕ) : ℝ) ^ 2 * p.σ ^ 4 / (p.L * p.Δ * p.ε ^ 2)⌉₊ + 1) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hf, hb, hD, hmodel⟩ := hO
  obtain ⟨Ω, mΩ, hmodel⟩ := hmodel
  let : MeasurableSpace Ω := mΩ
  obtain ⟨μ, P, g, hiid, hg, rfl⟩ := hmodel
  let C := p.L
  let q := OracleTemplate.MuonTuning.sourceInput p.toPublic C
  let N := ⌈OracleTemplate.MuonTuning.threshold p.toPublic C⌉₊
  let W : Fin (N + 1) → (ℕ → Ω) → Mat p.m p.n := fun j s => (trajectory q g s j.val).2.1
  have htraj := trajectory_accuracy p hp f hf hb hD μ P g hiid hg
  have hsel := OracleTemplate.MuonTuning.uniform_selection N P f W
    (fun j => htraj.1 j.val) (fun j => htraj.2.1 j.val)
  let out : Fin (N + 1) × (ℕ → Ω) → Mat p.m p.n := fun seed =>
    execute (sampleOracle P g) (OracleTemplate.MuonTuning.randomMuon q N)
      (fun _ => q.T) seed.1 seed.2
  have hout : out = fun seed => W seed.1 seed.2 := by
    funext seed
    have he := OracleTemplate.MuonTuning.execute_random q N rfl (le_refl 1) P g seed.1 seed.2
    change execute (sampleOracle P g) (OracleTemplate.MuonTuning.randomMuon q N)
      (fun _ => q.T * 1) seed.1 seed.2 = W seed.1 seed.2 at he
    dsimp only [q, OracleTemplate.MuonTuning.sourceInput] at he
    simpa only [out, q, OracleTemplate.MuonTuning.sourceInput, Nat.mul_one] using he
  dsimp only
  change Measurable out ∧
    Integrable (fun z => nuclearNorm (gradient f (out z)))
      ((PMF.uniformOfFintype (Fin (N + 1))).toMeasure.prod (P : Measure (ℕ → Ω))) ∧
    (∫ z, nuclearNorm (gradient f (out z))
      ∂((PMF.uniformOfFintype (Fin (N + 1))).toMeasure.prod (P : Measure (ℕ → Ω)))) ≤ p.ε
  rw [hout]
  refine ⟨hsel.1, hsel.2.1, hsel.2.2.trans_le ?_⟩
  change (1 / ((N + 1 : ℕ) : ℝ)) * ∑ j : Fin (N + 1),
    (∫ s, nuclearNorm (gradient f (trajectory q g s j.val).2.1) ∂(P : Measure (ℕ → Ω))) ≤ p.ε
  rw [Fin.sum_univ_eq_sum_range (fun t =>
    ∫ s, nuclearNorm (gradient f (trajectory q g s t).2.1) ∂(P : Measure (ℕ → Ω))) (N + 1)]
  exact htraj.2.2

end OracleTemplate.MuonSpectral
