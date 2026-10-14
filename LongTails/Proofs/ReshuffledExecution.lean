import LongTails.Proofs.ReshuffledConvergence
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.Execution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open Finset MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.ReshuffledConvex

open LongTails.Setups.ReshuffledSmoothConvex

section Bounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {n : ℕ}
  [NeZero n] {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ} {Lavg Lmax σ : ℝ}
  {xstar : E}

omit [NeZero n] in
lemma marginal_sum {K : ℕ} (i : Fin K) (F : Equiv.Perm (Fin n) → ℝ) :
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ∑ s : Orders n K, F (s i) =
      (Fintype.card (Orders n K) : ℝ) * ∑ π : Equiv.Perm (Fin n), F π := by
  classical
  let e := Equiv.funSplitAt i (Equiv.Perm (Fin n))
  have h1 : ∑ s : Orders n K, F (s i) =
      ∑ p : Equiv.Perm (Fin n) × ({j : Fin K // j ≠ i} → Equiv.Perm (Fin n)), F p.1 :=
    Fintype.sum_equiv e _ _ (fun s => rfl)
  have hcard : Fintype.card (Orders n K) = Fintype.card (Equiv.Perm (Fin n)) *
      Fintype.card ({j : Fin K // j ≠ i} → Equiv.Perm (Fin n)) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr e
  rw [h1, Fintype.sum_prod_type, hcard]
  simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul]
  rw [← mul_sum]
  ring

lemma scatter_orders (h : Hyp f g ℓ Lavg Lmax σ xstar) {K : ℕ} (k : ℕ) (hk : k < K) :
    ∑ s : Orders n K, scatter g ℓ xstar (schedule s k) ≤
      (Fintype.card (Orders n K) : ℝ) * ((n : ℝ) ^ 2 * Lavg * σ ^ 2) := by
  have hs : ∀ s : Orders n K, schedule s k = s ⟨k, hk⟩ := fun s => by
    unfold schedule
    split
    · rfl
    · contradiction
  simp only [hs]
  have hm := marginal_sum (⟨k, hk⟩ : Fin K) (fun π => scatter g ℓ xstar π)
  have hb := scatter_sum_le h
  have hP : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by exact_mod_cast Fintype.card_pos
  have hN : (0 : ℝ) ≤ Fintype.card (Orders n K) := Nat.cast_nonneg _
  have h1 : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
      ∑ s : Orders n K, scatter g ℓ xstar (s ⟨k, hk⟩) ≤
      Fintype.card (Equiv.Perm (Fin n)) *
        ((Fintype.card (Orders n K) : ℝ) * ((n : ℝ) ^ 2 * Lavg * σ ^ 2)) := by
    rw [hm]
    calc (Fintype.card (Orders n K) : ℝ) * ∑ π : Equiv.Perm (Fin n), scatter g ℓ xstar π
        ≤ Fintype.card (Orders n K) *
          ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ((n : ℝ) ^ 2 * Lavg * σ ^ 2)) :=
          mul_le_mul_of_nonneg_left hb hN
      _ = _ := by ring
  exact le_of_mul_le_mul_left h1 hP

theorem reshuffled_gap (h : Hyp f g ℓ Lavg Lmax σ xstar) {γ R : ℝ} {K : ℕ} (hK : 0 < K)
    (hγ : 0 < γ) (hΛ : 8 * Real.sqrt (Lavg * Lmax) * γ ≤ 1 / 8) (x0 : E)
    (hR : ‖x0 - xstar‖ ≤ R) :
    ∑ s : Orders n K, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f
        (iterate g (schedule s) (fun k => SampledConvex.step γ K k / n) x0 (n * K)) -
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) ≤
      Fintype.card (Orders n K) * (3 * R ^ 2 / (γ * K) + 12 * γ ^ 2 * Lavg * σ ^ 2 / n) := by
  have hn' : (n : ℝ) ≠ 0 := (card_pos' n).ne'
  have hB0 : 0 ≤ (n : ℝ) ^ 2 * Lavg * σ ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) h.pos.le) (sq_nonneg _)
  have hmain := sum_gap h (fun s : Orders n K => schedule s) hK hγ hΛ hB0
    (fun k hk => scatter_orders h k hk) x0 hR
  have e : 12 * γ ^ 2 * ((n : ℝ) ^ 2 * Lavg * σ ^ 2) / (n : ℝ) ^ 3 =
      12 * γ ^ 2 * Lavg * σ ^ 2 / n := by
    rw [div_eq_div_iff (pow_ne_zero 3 hn') hn']
    ring
  rw [e] at hmain
  exact hmain

theorem any_order_gap (h : Hyp f g ℓ Lavg Lmax σ xstar) (ord : ℕ → Equiv.Perm (Fin n))
    {γ R : ℝ} {K : ℕ} (hK : 0 < K) (hγ : 0 < γ)
    (hΛ : 8 * Real.sqrt (Lavg * Lmax) * γ ≤ 1 / 8) (x0 : E) (hR : ‖x0 - xstar‖ ≤ R) :
    LongTails.Setups.FiniteSumSmoothAndConvex.objective f (iterate g ord (fun k => SampledConvex.step γ K k / n) x0 (n * K)) -
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar ≤
      3 * R ^ 2 / (γ * K) + 12 * γ ^ 2 * Lavg * σ ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := (card_pos' n).ne'
  have hB0 : 0 ≤ (n : ℝ) ^ 3 * Lavg * σ ^ 2 :=
    mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3) h.pos.le) (sq_nonneg _)
  have hB : ∀ k, k < K → ∑ _s : Unit, scatter g ℓ xstar (ord k) ≤
      (Fintype.card Unit : ℝ) * ((n : ℝ) ^ 3 * Lavg * σ ^ 2) := by
    intro k _
    simp only [univ_unique, sum_singleton, Fintype.card_unit, Nat.cast_one, one_mul]
    exact scatter_le h (ord k)
  have hmain := sum_gap h (fun _ : Unit => ord) hK hγ hΛ hB0 hB x0 hR
  simp only [univ_unique, sum_singleton, Fintype.card_unit, Nat.cast_one, one_mul] at hmain
  have e : 12 * γ ^ 2 * ((n : ℝ) ^ 3 * Lavg * σ ^ 2) / (n : ℝ) ^ 3 = 12 * γ ^ 2 * Lavg * σ ^ 2 := by
    rw [div_eq_iff (pow_ne_zero 3 hn')]
    ring
  rw [e] at hmain
  exact hmain

end Bounds

lemma tuning {Lavg Lmax R σ ε : ℝ} (hLa : 0 < Lavg) (hLm : Lavg ≤ Lmax) (hσ : 0 ≤ σ)
    (hε : 0 < ε) (n K : ℕ) (hn : 0 < n) (hKpos : 0 < K)
    (hK : 384 * Real.sqrt (Lavg * Lmax) * R ^ 2 / ε +
      30 * σ * R ^ 2 * Real.sqrt (Lavg / (n * ε ^ 3)) ≤ K) :
    0 < 1 / (64 * Real.sqrt (Lavg * Lmax) + 5 * σ * Real.sqrt (Lavg / (n * ε))) ∧
    8 * Real.sqrt (Lavg * Lmax) *
      (1 / (64 * Real.sqrt (Lavg * Lmax) + 5 * σ * Real.sqrt (Lavg / (n * ε)))) ≤ 1 / 8 ∧
    3 * R ^ 2 / (1 / (64 * Real.sqrt (Lavg * Lmax) + 5 * σ * Real.sqrt (Lavg / (n * ε))) * K) +
      12 * (1 / (64 * Real.sqrt (Lavg * Lmax) + 5 * σ * Real.sqrt (Lavg / (n * ε)))) ^ 2 *
        Lavg * σ ^ 2 / n ≤ ε := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hKpos
  obtain ⟨Λ, hΛd⟩ : ∃ Λ : ℝ, Λ = Real.sqrt (Lavg * Lmax) := ⟨_, rfl⟩
  have hΛ : 0 < Λ := by
    rw [hΛd]; exact Real.sqrt_pos.mpr (mul_pos hLa (lt_of_lt_of_le hLa hLm))
  obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = Real.sqrt (Lavg / (n * ε)) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hsd]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = Lavg / (n * ε) := by
    rw [hsd]; exact Real.sq_sqrt (div_nonneg hLa.le (mul_pos hnr hε).le)
  have hs3 : Real.sqrt (Lavg / (n * ε ^ 3)) = s / ε := by
    have e1 : Lavg / (n * ε ^ 3) = (s / ε) ^ 2 := by
      rw [div_pow, hs2]
      field_simp
    rw [e1, Real.sqrt_sq (div_nonneg hs0 hε.le)]
  rw [hs3, ← hΛd] at hK
  rw [← hΛd, ← hsd]
  obtain ⟨Dn, hDnd⟩ : ∃ Dn : ℝ, Dn = 64 * Λ + 5 * σ * s := ⟨_, rfl⟩
  rw [← hDnd]
  have hσs : 0 ≤ σ * s := mul_nonneg hσ hs0
  have hDn : 0 < Dn := by rw [hDnd]; nlinarith
  have hK' : 384 * Λ * R ^ 2 + 30 * σ * R ^ 2 * s ≤ ε * K := by
    have h1 := mul_le_mul_of_nonneg_left hK hε.le
    have e1 : ε * (384 * Λ * R ^ 2 / ε + 30 * σ * R ^ 2 * (s / ε)) =
        384 * Λ * R ^ 2 + 30 * σ * R ^ 2 * s := by
      field_simp
    linarith
  refine ⟨one_div_pos.mpr hDn, ?_, ?_⟩
  · rw [mul_one_div, div_le_iff₀ hDn, hDnd]
    linarith
  · have e1 : 3 * R ^ 2 / (1 / Dn * K) = 3 * R ^ 2 * Dn / K := by
      field_simp
    have e2 : 12 * (1 / Dn) ^ 2 * Lavg * σ ^ 2 / n = 12 * Lavg * σ ^ 2 / n / Dn ^ 2 := by
      field_simp
    have t1 : 3 * R ^ 2 * Dn / K ≤ ε / 2 := by
      rw [div_le_iff₀ hKr, hDnd]
      linarith
    have t2 : 12 * Lavg * σ ^ 2 / n / Dn ^ 2 ≤ ε / 2 := by
      rw [div_le_iff₀ (pow_pos hDn 2)]
      have hD2 : 25 * (σ ^ 2 * s ^ 2) ≤ Dn ^ 2 := by
        have e3 : Dn ^ 2 - 25 * (σ ^ 2 * s ^ 2) = 64 * Λ * (64 * Λ + 10 * (σ * s)) := by
          rw [hDnd]; ring
        have : 0 ≤ 64 * Λ * (64 * Λ + 10 * (σ * s)) := by positivity
        linarith
      have e4 : ε * (σ ^ 2 * s ^ 2) = Lavg * σ ^ 2 / n := by
        rw [hs2]
        field_simp
      have h5 : 0 ≤ Lavg * σ ^ 2 / n := div_nonneg (mul_nonneg hLa.le (sq_nonneg _)) hnr.le
      have h6 := mul_le_mul_of_nonneg_left hD2 (by linarith : (0 : ℝ) ≤ ε / 2)
      have e5 : 12 * Lavg * σ ^ 2 / n = 12 * (Lavg * σ ^ 2 / n) := by ring
      have e6 : ε / 2 * (25 * (σ ^ 2 * s ^ 2)) = 25 / 2 * (ε * (σ ^ 2 * s ^ 2)) := by ring
      rw [e5]
      rw [e6, e4] at h6
      linarith
    rw [e1, e2]
    linarith

section Execution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} [NeZero n]

lemma advance_iterate (g : Fin n → E → E) (ord : ℕ → Equiv.Perm (Fin n)) (η : ℕ → ℝ) (x0 : E)
    (T call t : ℕ) :
    StochasticGradient.advance
      (fun (_ : ℕ) (st : (ℕ → Equiv.Perm (Fin n)) × ℕ × E) =>
        ((st.1, st.2.1 + 1, st.2.2 - η (st.2.1 / n) •
          g (st.1 (st.2.1 / n) ⟨st.2.1 % n, Nat.mod_lt st.2.1 (NeZero.pos n)⟩) st.2.2) :
          (ℕ → Equiv.Perm (Fin n)) × ℕ × E))
      T call (ord, t, iterate g ord η x0 t) = (ord, t + T, iterate g ord η x0 (t + T)) := by
  induction T generalizing call t with
  | zero => rfl
  | succ T ih =>
    have h := ih (call + 1) (t + 1)
    have e : t + (T + 1) = t + 1 + T := by omega
    rw [e]
    exact h

lemma execute_reshuffled (g : Fin n → E → E) (K : ℕ) (η : ℕ → ℝ) (x0 : E) (T : ℕ)
    (seed : Orders n K) :
    execute ({ answer := fun _ (_, q) _ => g q.1 q.2 } : Oracle (Fin n × E) E)
        (reshuffledGradient K η x0) (fun _ => T) seed =
      iterate g (schedule seed) η x0 T := by
  have h := advance_iterate g (schedule seed) η x0 T 0 0
  rw [Nat.zero_add] at h
  exact (StochasticGradient.execute_advance
    ({ answer := fun _ (_, q) _ => g q.1 q.2 } : Oracle (Fin n × E) E)
    (reshuffledGradient K η x0) T seed (fun _ => ())).trans
    (congrArg (fun st : (ℕ → Equiv.Perm (Fin n)) × ℕ × E => st.2.2) h)

end Execution

noncomputable def scale (p : Params) : ℝ :=
  1 / (64 * Real.sqrt (p.Lavg * p.Lmax) + 5 * p.σ * Real.sqrt (p.Lavg / (p.n * p.ε)))

noncomputable def epochs (p : Params) : ℕ :=
  ⌈384 * Real.sqrt (p.Lavg * p.Lmax) * p.R ^ 2 / p.ε +
    30 * p.σ * p.R ^ 2 * Real.sqrt (p.Lavg / (p.n * p.ε ^ 3))⌉₊

noncomputable def tuned (p : Params) : Algorithm (Fin p.n × p.E) p.E p.E :=
  reshuffledGradient (epochs p) (fun k => SampledConvex.step (scale p) (epochs p) k / p.n) p.x0

set_option maxHeartbeats 1000000 in
theorem convergence : Convergence spec (fun p _ => p.n * epochs p) := by
  apply convergence_of_public_budget (S := spec) (fun p => p.n * epochs p)
  refine ⟨tuned, ?_, fun p _ => ⟨epochs p, _, rfl⟩⟩
  rintro p ⟨hLa, hLm, hR, hσ, hε⟩ f O
    ⟨hconv, hgrad, ⟨ℓ, hℓ0, hℓmax, havg, hlip⟩, xstar, hmin, hdist, hnoise⟩
  have hnpos : 0 < p.n := NeZero.pos p.n
  let ξ0 := Classical.choice O.law.nonempty
  let g : Fin p.n → p.E → p.E := fun i x => gradient (f i) x
  have hans : ∀ k (q : Fin p.n × p.E) seed, O.answer k (0, q) seed = g q.1 q.2 :=
    fun k q seed => (hgrad k seed q.1 q.2).gradient.symm
  have hgradg : ∀ i x, HasGradientAt (f i) (g i x) x := fun i x => by
    have := hgrad 0 (ξ0 0) i x
    rw [hans 0 (i, x) (ξ0 0)] at this
    exact this
  have hyp : Hyp f g ℓ p.Lavg p.Lmax p.σ xstar :=
    ⟨hLa, hLm, hconv, hgradg, hℓ0, hℓmax, havg, hlip, hmin, hnoise⟩
  let out := fun seed : Orders p.n (epochs p) =>
    iterate g (schedule seed) (fun k => SampledConvex.step (scale p) (epochs p) k / p.n) p.x0
      (p.n * epochs p)
  have hexec : ∀ (seed : Orders p.n (epochs p)) (ξ : (k : ℕ) → O.Seed k),
      execute O (tuned p) (fun _ => (p.n * epochs p)) seed ξ = out seed := by
    intro seed ξ
    have h1 := execute_eq_of_answer_eq O (fun q => g q.1 q.2) (fun k q s => hans k q s)
      (tuned p) (p.n * epochs p) seed ξ
    exact h1.trans (execute_reshuffled g (epochs p) _ p.x0 (p.n * epochs p) seed)
  have hbound : ∑ seed : Orders p.n (epochs p),
      (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) ≤
      Fintype.card (Orders p.n (epochs p)) * p.ε := by
    rcases Nat.eq_zero_or_pos (epochs p) with hK0 | hKpos
    · have hceil : 384 * Real.sqrt (p.Lavg * p.Lmax) * p.R ^ 2 / p.ε +
          30 * p.σ * p.R ^ 2 * Real.sqrt (p.Lavg / (p.n * p.ε ^ 3)) ≤ 0 :=
        Nat.ceil_eq_zero.mp hK0
      have hΛ : 0 < Real.sqrt (p.Lavg * p.Lmax) :=
        Real.sqrt_pos.mpr (mul_pos hLa (lt_of_lt_of_le hLa hLm))
      have ht2 : 0 ≤ 30 * p.σ * p.R ^ 2 * Real.sqrt (p.Lavg / (p.n * p.ε ^ 3)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hσ) (sq_nonneg _)) (Real.sqrt_nonneg _)
      have hc : 0 < 384 * Real.sqrt (p.Lavg * p.Lmax) / p.ε := by positivity
      have hR2 : p.R ^ 2 ≤ 0 := by
        by_contra hneg
        have hp := mul_pos hc (not_le.mp hneg)
        have e : 384 * Real.sqrt (p.Lavg * p.Lmax) * p.R ^ 2 / p.ε =
            384 * Real.sqrt (p.Lavg * p.Lmax) / p.ε * p.R ^ 2 := by ring
        linarith
      have hgap : LongTails.Setups.FiniteSumSmoothAndConvex.objective f p.x0 - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar ≤ p.ε := by
        have h1 := hyp.init_gap p.x0
        have h2 : ‖p.x0 - xstar‖ ^ 2 ≤ p.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
        have h3 := mul_le_mul_of_nonneg_left (h2.trans hR2) (by linarith : (0 : ℝ) ≤ p.Lavg / 2)
        linarith
      have hzero : p.n * epochs p = 0 := by rw [hK0, Nat.mul_zero]
      have hout : ∀ seed, out seed = p.x0 := fun seed => by
        show iterate g (schedule seed)
          (fun k => SampledConvex.step (scale p) (epochs p) k / p.n) p.x0 (p.n * epochs p) = p.x0
        rw [hzero]
        rfl
      calc ∑ seed : Orders p.n (epochs p),
            (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)
          ≤ ∑ _seed : Orders p.n (epochs p), p.ε :=
            sum_le_sum (fun seed _ => by rw [hout seed]; exact hgap)
        _ = Fintype.card (Orders p.n (epochs p)) * p.ε := by
            rw [sum_const, card_univ, nsmul_eq_mul]
    · have hKceil : 384 * Real.sqrt (p.Lavg * p.Lmax) * p.R ^ 2 / p.ε +
          30 * p.σ * p.R ^ 2 * Real.sqrt (p.Lavg / (p.n * p.ε ^ 3)) ≤ (epochs p : ℕ) :=
        Nat.le_ceil _
      obtain ⟨hγpos, hΛγ, htune⟩ := tuning hLa hLm hσ hε p.n (epochs p) hnpos hKpos hKceil
      have hmain := reshuffled_gap hyp hKpos hγpos hΛγ p.x0 hdist
      have hN : (0 : ℝ) ≤ Fintype.card (Orders p.n (epochs p)) := Nat.cast_nonneg _
      exact hmain.trans (mul_le_mul_of_nonneg_left htune hN)
  have hNpos : (0 : ℝ) < Fintype.card (Orders p.n (epochs p)) := by
    exact_mod_cast Fintype.card_pos
  have hres : ∀ seed : Orders p.n (epochs p) × ((k : ℕ) → O.Seed k),
      execute O (tuned p) (fun _ => (p.n * epochs p)) seed.1 seed.2 = out seed.1 :=
    fun seed => hexec seed.1 seed.2
  change spec.successful p f
      (fun seed => (execute O (tuned p) (fun _ => (p.n * epochs p)) seed.1 seed.2))
      ⟨(PMF.uniformOfFintype (Orders p.n (epochs p))).toMeasure.prod
        (O.law : Measure ((k : ℕ) → O.Seed k)), inferInstance⟩
  simp only [hres]
  change Measurable (fun seed : Orders p.n (epochs p) × ((k : ℕ) → O.Seed k) => out seed.1) ∧ _
  refine ⟨(measurable_from_top : Measurable out).comp measurable_fst, xstar, hmin, ?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun seed : Orders p.n (epochs p) =>
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)
        (μ := (PMF.uniformOfFintype (Orders p.n (epochs p))).toMeasure))
  · change (∫ seed : Orders p.n (epochs p) × ((k : ℕ) → O.Seed k),
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed.1) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar
        ∂(PMF.uniformOfFintype (Orders p.n (epochs p))).toMeasure.prod
          (O.law : Measure ((k : ℕ) → O.Seed k))) ≤ p.ε
    rw [integral_fun_fst (fun seed => LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)]
    simp only [probReal_univ, one_smul]
    have hint : (∫ seed : Orders p.n (epochs p),
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar
        ∂(PMF.uniformOfFintype (Orders p.n (epochs p))).toMeasure) =
        (Fintype.card (Orders p.n (epochs p)) : ℝ)⁻¹ * ∑ seed : Orders p.n (epochs p),
          (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) := by
      simp [PMF.integral_eq_sum, PMF.uniformOfFintype_apply, ← Finset.mul_sum]
    rw [hint]
    calc (Fintype.card (Orders p.n (epochs p)) : ℝ)⁻¹ * ∑ seed : Orders p.n (epochs p),
          (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)
        ≤ (Fintype.card (Orders p.n (epochs p)) : ℝ)⁻¹ *
          (Fintype.card (Orders p.n (epochs p)) * p.ε) :=
          mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hNpos.le)
      _ = p.ε := by rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]

end OracleTemplate.ReshuffledConvex
