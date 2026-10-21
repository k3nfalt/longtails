import outputs.Proofs.MuonStochastic
import outputs.Proofs.MuonExecution
import outputs.Setups.MuonFrobenius

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.Muon

theorem averaged_bound {Ξ : Type} [MeasurableSpace Ξ] (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (T : ℕ) (hT : 1 ≤ T) (η c κ : ℝ) (hη : 0 < η) (hκ : 0 ≤ κ)
    (A F Er : ℕ → Ξ → ℝ) (e : ℕ → ℝ) (hA : ∀ t, Integrable (A t) Q) (hF : ∀ t, Integrable (F t) Q)
    (hE : ∀ t, Integrable (Er t) Q)
    (hpath : ∀ t ω, η * A t ω ≤ F t ω - F (t + 1) ω + c + κ * Er t ω)
    (he : ∀ t, (∫ ω, Er t ω ∂Q) ≤ e t) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, A t ω ∂Q) ≤
      (∫ ω, F 0 ω - F T ω ∂Q) / (T * η) + c / η + κ / η * ((1 / (T : ℝ)) * ∑ t ∈ Finset.range T, e t) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have h1 : ∀ t, η * (∫ ω, A t ω ∂Q) ≤ (∫ ω, F t ω ∂Q) - (∫ ω, F (t + 1) ω ∂Q) + c + κ * e t := by
    intro t
    have i1 : Integrable (fun ω => F t ω - F (t + 1) ω) Q := (hF t).sub (hF (t + 1))
    have i2 : Integrable (fun ω => F t ω - F (t + 1) ω + c) Q := i1.add (integrable_const c)
    have i3 : Integrable (fun ω => κ * Er t ω) Q := (hE t).const_mul κ
    have hint : Integrable (fun ω => F t ω - F (t + 1) ω + c + κ * Er t ω) Q := i2.add i3
    have i0 : Integrable (fun ω => η * A t ω) Q := (hA t).const_mul η
    have hm := integral_mono i0 hint (fun ω => hpath t ω)
    rw [integral_const_mul, integral_add i2 i3, integral_add i1 (integrable_const c),
      integral_sub (hF t) (hF (t + 1)), integral_const_mul, integral_const, probReal_univ,
      one_smul] at hm
    nlinarith [mul_le_mul_of_nonneg_left (he t) hκ]
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range T) => h1 t)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_range_sub' (fun t => ∫ ω, F t ω ∂Q), Finset.sum_const, Finset.card_range,
    ← Finset.mul_sum, nsmul_eq_mul] at hsum
  rw [integral_sub (hF 0) (hF T)]
  have key : (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, A t ω ∂Q) =
      (η * ∑ t ∈ Finset.range T, (∫ ω, A t ω ∂Q)) / (T * η) := by
    field_simp
  rw [key, div_le_iff₀ (mul_pos hTpos hη)]
  have expand : ((∫ ω, F 0 ω ∂Q) - (∫ ω, F T ω ∂Q)) / (T * η) * (T * η) +
      c / η * (T * η) + κ / η * ((1 / (T : ℝ)) * ∑ t ∈ Finset.range T, e t) * (T * η) =
      ((∫ ω, F 0 ω ∂Q) - (∫ ω, F T ω ∂Q)) + T * c + κ * ∑ t ∈ Finset.range T, e t := by
    field_simp
  rw [add_mul, add_mul, expand]
  linarith

theorem measurable_gradient_of {m n : ℕ} (f : Mat m n → ℝ) : Measurable (gradient f) := by
  have h : gradient f = fun W => (InnerProductSpace.toDual ℝ (Mat m n)).symm (fderiv ℝ f W) := rfl
  rw [h]
  exact (InnerProductSpace.toDual ℝ (Mat m n)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

theorem integrable_of_abs_le {Ξ : Type} [MeasurableSpace Ξ] (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (X : Ξ → ℝ) (hX : Measurable X) (C : ℝ) (hC : ∀ ω, |X ω| ≤ C) : Integrable X Q := by
  exact Integrable.of_bound hX.aestronglyMeasurable C (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs]; exact hC ω))

theorem weights_recursion {m n : ℕ} (β : ℝ) (N : ℕ → Mat m n) (t : ℕ) :
    ∑ i ∈ Finset.range (t + 2), (if i = 0 then β ^ (t + 1) else (1 - β) * β ^ (t + 1 - i)) • N i =
      β • ∑ i ∈ Finset.range (t + 1), (if i = 0 then β ^ t else (1 - β) * β ^ (t - i)) • N i +
        (1 - β) • N (t + 1) := by
  rw [Finset.sum_range_succ, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [smul_smul]
    congr 1
    by_cases h0 : i = 0
    · simp only [h0, ite_true]; ring
    · simp only [h0, ite_false]
      rw [show t + 1 - i = (t - i) + 1 by omega]
      ring
  · simp

theorem spectralNorm_zero {m n : ℕ} : spectralNorm (0 : Mat m n) = 0 := by
  have h := spectralNorm_smul 0 (0 : Mat m n)
  rw [zero_smul, abs_zero, zero_mul] at h
  exact h

theorem spectralNorm_add_le {m n : ℕ} (A B : Mat m n) :
    spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B := by
  unfold spectralNorm
  rw [show toMatrix (A + B) = toMatrix A + toMatrix B from rfl, map_add, map_add]
  exact norm_add_le _ _

theorem distance_from_start {m n : ℕ} (η : ℝ) (hη : 0 ≤ η) (W M : ℕ → Mat m n)
    (hW : ∀ t, W (t + 1) = W t - η • orthogonalize (M t)) (t : ℕ) :
    ‖W t - W 0‖ ≤ t * η * Real.sqrt ((min m n : ℕ) : ℝ) ∧ spectralNorm (W t - W 0) ≤ t * η := by
  induction t with
  | zero => simp only [sub_self, norm_zero, CharP.cast_eq_zero, zero_mul, le_refl, spectralNorm_zero,
      and_self]
  | succ t ih =>
    have e : W (t + 1) - W 0 = (W t - W 0) + (-η) • orthogonalize (M t) := by
      rw [hW]; module
    rw [e]
    constructor
    · refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη]
      have hP : ‖orthogonalize (M t)‖ ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
        rw [Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)]; exact norm_orthogonalize_sq_le _
      have := mul_le_mul_of_nonneg_left hP hη
      have hc : ((t + 1 : ℕ) : ℝ) = t + 1 := by push_cast; ring
      rw [hc]
      nlinarith [ih.1]
    · refine (spectralNorm_add_le _ _).trans ?_
      rw [spectralNorm_smul, abs_neg, abs_of_nonneg hη]
      have := mul_le_of_le_one_right hη (spectralNorm_orthogonalize_le (M t))
      have hc : ((t + 1 : ℕ) : ℝ) = t + 1 := by push_cast; ring
      rw [hc]
      nlinarith [ih.2]

theorem geom_tail_le (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (T : ℕ) :
    ∑ t ∈ Finset.range T, β ^ (t + 1) ≤ β / (1 - β) := by
  have h1 : ∑ t ∈ Finset.range T, β ^ (t + 1) = β * ∑ t ∈ Finset.range T, β ^ t := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun t _ => by ring)
  rw [h1, geom_sum_eq (ne_of_lt hβ1) T]
  have hb : 0 < 1 - β := by linarith
  have : (β ^ T - 1) / (β - 1) = (1 - β ^ T) / (1 - β) := by
    rw [← neg_sub, ← neg_sub 1 β, neg_div_neg_eq]
  rw [this, mul_div_assoc']
  apply div_le_div_of_nonneg_right _ hb.le
  nlinarith [pow_nonneg hβ0 T]

theorem noise_mean_bound {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω)) {m n : ℕ}
    (X : (ℕ → Ω) → Mat m n) (hXm : Measurable X)
    (hX2 : Integrable (fun s => ‖X s‖ ^ 2) (P : Measure (ℕ → Ω))) (σ β : ℝ) (B t : ℕ) (hσ : 0 ≤ σ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hB : 1 ≤ B)
    (hle : (∫ s, ‖X s‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤
      σ ^ 2 / B * ((1 - β) / (1 + β) + (1 - (1 - β) / (1 + β)) * β ^ (2 * t))) :
    Integrable (fun s => ‖X s‖) (P : Measure (ℕ → Ω)) ∧
      (∫ s, ‖X s‖ ∂(P : Measure (ℕ → Ω))) ≤
        σ / Real.sqrt B * (Real.sqrt ((1 - β) / (1 + β)) + β ^ (t + 1)) := by
  obtain ⟨hi, hj⟩ := integral_norm_le_sqrt (P : Measure (ℕ → Ω)) X hXm hX2
  refine ⟨hi, hj.trans ?_⟩
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hy0 : 0 ≤ β ^ t := pow_nonneg hβ0 t
  have hy1 : β ^ t ≤ 1 := pow_le_one₀ hβ0 hβ1.le
  have hs := momentum_sqrt_le β hβ0 hβ1 (β ^ t) hy0 hy1
  rw [← pow_mul, mul_comm t 2] at hs
  refine (Real.sqrt_le_sqrt hle).trans ?_
  rw [Real.sqrt_mul (by positivity), Real.sqrt_div' _ hBpos.le, Real.sqrt_sq hσ, pow_succ, mul_comm (β ^ t) β]
  exact mul_le_mul_of_nonneg_left hs (by positivity)

theorem frobenius_main {Ω : Type} [MeasurableSpace Ω] (q : Public) (L σ : ℝ) (hL : 0 ≤ L)
    (hσ : 0 ≤ σ) (hη : 0 < q.η) (hβ0 : 0 ≤ q.β) (hβ1 : q.β < 1) (hB : 1 ≤ q.B) (hT : 1 ≤ q.T)
    (f : Mat q.m q.n → ℝ) (hg : ∀ W, HasGradientAt f (gradient f W) W)
    (hlip : ∀ W W', ‖gradient f W - gradient f W'‖ ≤ L * ‖W - W'‖) (hbdd : BddBelow (Set.range f))
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω)) (g : Mat q.m q.n → Ω → Mat q.m q.n)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat q.m q.n) Ω
      (μ : Measure Ω) f g σ) :
    (∀ t, Measurable (fun s => (trajectory q g s t).2.1)) ∧
    (∀ t, Integrable (fun s => nuclearNorm (gradient f (trajectory q g s t).2.1)) (P : Measure (ℕ → Ω))) ∧
    (∀ t, Integrable (fun s => f (trajectory q g s t).2.1) (P : Measure (ℕ → Ω))) ∧
    (1 / (q.T : ℝ)) * ∑ t ∈ Finset.range q.T,
        (∫ s, nuclearNorm (gradient f (trajectory q g s t).2.1) ∂(P : Measure (ℕ → Ω))) ≤
      (∫ s, f (trajectory q g s 0).2.1 - f (trajectory q g s q.T).2.1 ∂(P : Measure (ℕ → Ω))) /
          (q.T * q.η) + L * ((min q.m q.n : ℕ) : ℝ) * q.η / 2 +
        2 * σ * Real.sqrt (((min q.m q.n : ℕ) : ℝ) * (1 - q.β)) / Real.sqrt (q.B * (1 + q.β)) +
        2 * q.β * σ * Real.sqrt ((min q.m q.n : ℕ) : ℝ) / ((1 - q.β) * q.T * Real.sqrt q.B) +
        2 * ((min q.m q.n : ℕ) : ℝ) * q.η * q.β * L / (1 - q.β) := by
  set r : ℝ := ((min q.m q.n : ℕ) : ℝ) with hr
  set β := q.β
  set η := q.η
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hb1 : 0 < 1 - β := by linarith
  let Wt : ℕ → (ℕ → Ω) → Mat q.m q.n := fun t s => (trajectory q g s t).2.1
  let Mt : ℕ → (ℕ → Ω) → Mat q.m q.n := fun t s => (trajectory q g s (t + 1)).2.2
  let Gt : ℕ → (ℕ → Ω) → Mat q.m q.n := fun t s => batchGradient q g s t (Wt t s)
  have hW : ∀ s t, Wt (t + 1) s = Wt t s - η • orthogonalize (Mt t s) := by
    intro s t
    simp only [Wt, Mt]
    rw [trajectory_succ_eq]
  have hM0 : ∀ s, Mt 0 s = Gt 0 s := by
    intro s
    simp only [Mt, Gt, Wt]
    rw [trajectory_succ_eq]
    simp
  have hM : ∀ s t, Mt (t + 1) s = β • Mt t s + (1 - β) • Gt (t + 1) s := by
    intro s t
    simp only [Mt, Gt, Wt]
    rw [trajectory_succ_eq q g s (t + 1)]
    simp only [Nat.add_one_ne_zero, ite_false]
    rfl
  let D : ℕ → (ℕ → Ω) → Mat q.m q.n := fun t s => ∑ i ∈ Finset.range (t + 1),
    (if i = 0 then β ^ t else (1 - β) * β ^ (t - i)) • (Gt i s - gradient f (Wt i s))
  have hD0 : ∀ s, D 0 s = Gt 0 s - gradient f (Wt 0 s) := by
    intro s; simp [D]
  have hD : ∀ s t, D (t + 1) s = β • D t s + (1 - β) • (Gt (t + 1) s - gradient f (Wt (t + 1) s)) :=
    fun s t => weights_recursion β (fun i => Gt i s - gradient f (Wt i s)) t
  have hgm := measurable_gradient_of f
  have hWm : ∀ t, Measurable (Wt t) := fun t => measurable_fst.comp (trajectory_measurable q g ho.measurable t)
  have hWk : ∀ t s s', (∀ j < t * q.B, s j = s' j) → Wt t s = Wt t s' := fun t s s' h => by
    simp only [Wt]; rw [trajectory_prefix q g t s s' h]
  have hnoise := fun t => momentum_noise μ P hiid f g σ ho hgm β hβ0 hβ1 q.B hB Wt hWm hWk D
    (fun s => hD0 s) (fun t s => hD s t) t
  have hEr := fun t => noise_mean_bound P (D t) (hnoise t).1 (hnoise t).2.2.1 σ β q.B t hσ hβ0 hβ1 hB
    (hnoise t).2.2.2
  have hpath : ∀ t s, η * nuclearNorm (gradient f (Wt t s)) ≤ f (Wt t s) - f (Wt (t + 1) s) +
      (r * L * η ^ 2 / 2 + 2 * r * β * L * η ^ 2 / (1 - β)) + 2 * η * Real.sqrt r * ‖D t s‖ := by
    intro t s
    have h1 := step_frobenius f L η hη hL hg hlip (Wt t s) (Mt t s)
    rw [← hW] at h1
    have h2 := momentum_tracking_frobenius f L η β hL hη.le hβ0 hβ1 hlip (fun t => Wt t s)
      (fun t => Mt t s) (fun t => Gt t s) (fun t => D t s) (hW s) (hM0 s) (hM s) (hD0 s) (hD s) t
    have hrr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * η * Real.sqrt r)
    have e : 2 * η * Real.sqrt r * (Real.sqrt r * β * L * η / (1 - β)) = 2 * r * β * L * η ^ 2 / (1 - β) := by
      rw [show 2 * η * Real.sqrt r * (Real.sqrt r * β * L * η / (1 - β)) =
        2 * β * L * η ^ 2 / (1 - β) * (Real.sqrt r * Real.sqrt r) by ring, hrr]
      ring
    nlinarith
  obtain ⟨lb, hlb⟩ := hbdd
  have hlb' : ∀ x, lb ≤ f x := fun x => hlb ⟨x, rfl⟩
  have hW0 : ∀ s, Wt 0 s = q.W0 := fun s => by simp only [Wt]; rw [trajectory_zero]
  have hdist : ∀ t s, ‖Wt t s - q.W0‖ ≤ t * η * Real.sqrt r := fun t s => by
    have := (distance_from_start η hη.le (fun t => Wt t s) (fun t => Mt t s) (hW s) t).1
    rwa [hW0] at this
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun x => (hg x).hasFDerivAt.continuousAt
  have hAi : ∀ t, Integrable (fun s => nuclearNorm (gradient f (Wt t s))) (P : Measure (ℕ → Ω)) := by
    intro t
    refine integrable_of_abs_le _ _ (measurable_nuclearNorm.comp (hgm.comp (hWm t)))
      (Real.sqrt r * (‖gradient f q.W0‖ + L * (t * η * Real.sqrt r))) (fun s => ?_)
    rw [abs_of_nonneg (nuclearNorm_nonneg _)]
    refine (nuclearNorm_le_sqrt_mul_norm _).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    have h1 := hlip (Wt t s) q.W0
    have h2 := norm_le_insert' (gradient f (Wt t s)) (gradient f q.W0)
    nlinarith [hdist t s, mul_le_mul_of_nonneg_left (hdist t s) hL]
  have hFi : ∀ t, Integrable (fun s => f (Wt t s)) (P : Measure (ℕ → Ω)) := by
    intro t
    set R := t * η * Real.sqrt r
    refine integrable_of_abs_le _ _ (hcont.measurable.comp (hWm t))
      (|lb| + |f q.W0| + ‖gradient f q.W0‖ * R + L * R ^ 2 / 2) (fun s => ?_)
    have hd := frobenius_descent f L hg hlip q.W0 (Wt t s - q.W0)
    rw [add_sub_cancel] at hd
    have hi := real_inner_le_norm (gradient f q.W0) (Wt t s - q.W0)
    have hR := hdist t s
    have hn := norm_nonneg (Wt t s - q.W0)
    have hsq : ‖Wt t s - q.W0‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hn hR 2
    rw [abs_le]
    constructor
    · nlinarith [hlb' (Wt t s), abs_nonneg lb, neg_abs_le lb, abs_nonneg (f q.W0),
        norm_nonneg (gradient f q.W0), mul_nonneg hL (sq_nonneg R)]
    · nlinarith [mul_le_mul_of_nonneg_left hR (norm_nonneg (gradient f q.W0)),
        mul_le_mul_of_nonneg_left hsq hL, le_abs_self (f q.W0), abs_nonneg lb]
  have havg := averaged_bound (P : Measure (ℕ → Ω)) q.T hT η (r * L * η ^ 2 / 2 + 2 * r * β * L * η ^ 2 / (1 - β))
    (2 * η * Real.sqrt r) hη (by positivity) (fun t s => nuclearNorm (gradient f (Wt t s)))
    (fun t s => f (Wt t s)) (fun t s => ‖D t s‖)
    (fun t => σ / Real.sqrt q.B * (Real.sqrt ((1 - β) / (1 + β)) + β ^ (t + 1)))
    hAi hFi (fun t => (hEr t).1) hpath (fun t => (hEr t).2)
  refine ⟨hWm, hAi, hFi, havg.trans ?_⟩
  have hTpos : (0 : ℝ) < q.T := by exact_mod_cast (show 0 < q.T by omega)
  have hBpos : (0 : ℝ) < q.B := by exact_mod_cast (show 0 < q.B by omega)
  have hgeo := geom_tail_le β hβ0 hβ1 q.T
  have hsum : (1 / (q.T : ℝ)) * ∑ t ∈ Finset.range q.T,
      σ / Real.sqrt q.B * (Real.sqrt ((1 - β) / (1 + β)) + β ^ (t + 1)) ≤
      σ / Real.sqrt q.B * (Real.sqrt ((1 - β) / (1 + β)) + β / (1 - β) / q.T) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hc : 0 ≤ σ / Real.sqrt q.B := by positivity
    rw [show (1 / (q.T : ℝ)) * (σ / Real.sqrt q.B * (q.T * Real.sqrt ((1 - β) / (1 + β)) +
        ∑ t ∈ Finset.range q.T, β ^ (t + 1))) = σ / Real.sqrt q.B * (Real.sqrt ((1 - β) / (1 + β)) +
        (∑ t ∈ Finset.range q.T, β ^ (t + 1)) / q.T) by field_simp]
    gcongr
  have hk : 0 ≤ 2 * η * Real.sqrt r / η := by positivity
  have hstep := mul_le_mul_of_nonneg_left hsum hk
  have e1 : (r * L * η ^ 2 / 2 + 2 * r * β * L * η ^ 2 / (1 - β)) / η =
      L * r * η / 2 + 2 * r * η * β * L / (1 - β) := by field_simp
  have e2 : 2 * η * Real.sqrt r / η * (σ / Real.sqrt q.B * (Real.sqrt ((1 - β) / (1 + β)) + β / (1 - β) / q.T)) =
      2 * σ * Real.sqrt (r * (1 - β)) / Real.sqrt (q.B * (1 + β)) +
        2 * β * σ * Real.sqrt r / ((1 - β) * q.T * Real.sqrt q.B) := by
    rw [Real.sqrt_mul hr0, Real.sqrt_mul hBpos.le, Real.sqrt_div' _ (by linarith : (0:ℝ) ≤ 1 + β)]
    have : 0 < Real.sqrt (1 + β) := Real.sqrt_pos.mpr (by linarith)
    have : 0 < Real.sqrt (q.B : ℝ) := Real.sqrt_pos.mpr hBpos
    field_simp
  have hFT : (∫ s, f (Wt 0 s) - f (Wt q.T s) ∂(P : Measure (ℕ → Ω))) =
      ∫ s, f (trajectory q g s 0).2.1 - f (trajectory q g s q.T).2.1 ∂(P : Measure (ℕ → Ω)) := rfl
  rw [hFT, e1] at *
  linarith [e2 ▸ hstep]

theorem spectral_main {Ω : Type} [MeasurableSpace Ω] (q : Public) (L σ : ℝ) (hL : 0 ≤ L)
    (hσ : 0 ≤ σ) (hη : 0 < q.η) (hβ0 : 0 ≤ q.β) (hβ1 : q.β < 1) (hB : 1 ≤ q.B) (hT : 1 ≤ q.T)
    (f : Mat q.m q.n → ℝ) (hg : ∀ W, HasGradientAt f (gradient f W) W)
    (hlip : ∀ W W', nuclearNorm (gradient f W - gradient f W') ≤ L * spectralNorm (W - W')) (hbdd : BddBelow (Set.range f))
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω)) (g : Mat q.m q.n → Ω → Mat q.m q.n)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat q.m q.n) Ω
      (μ : Measure Ω) f g σ) :
    (∀ t, Measurable (fun s => (trajectory q g s t).2.1)) ∧
    (∀ t, Integrable (fun s => nuclearNorm (gradient f (trajectory q g s t).2.1)) (P : Measure (ℕ → Ω))) ∧
    (∀ t, Integrable (fun s => f (trajectory q g s t).2.1) (P : Measure (ℕ → Ω))) ∧
    (1 / (q.T : ℝ)) * ∑ t ∈ Finset.range q.T,
        (∫ s, nuclearNorm (gradient f (trajectory q g s t).2.1) ∂(P : Measure (ℕ → Ω))) ≤
      (∫ s, f (trajectory q g s 0).2.1 - f (trajectory q g s q.T).2.1 ∂(P : Measure (ℕ → Ω))) /
          (q.T * q.η) + L * q.η / 2 +
        2 * σ * Real.sqrt (((min q.m q.n : ℕ) : ℝ) * (1 - q.β)) / Real.sqrt ((1 + q.β) * q.B) +
        2 * q.β * σ * Real.sqrt ((min q.m q.n : ℕ) : ℝ) / ((1 - q.β) * q.T * Real.sqrt q.B) +
        2 * q.η * q.β * L / (1 - q.β) := by
  set r : ℝ := ((min q.m q.n : ℕ) : ℝ) with hr
  set β := q.β
  set η := q.η
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hb1 : 0 < 1 - β := by linarith
  let Wt : ℕ → (ℕ → Ω) → Mat q.m q.n := fun t s => (trajectory q g s t).2.1
  let Mt : ℕ → (ℕ → Ω) → Mat q.m q.n := fun t s => (trajectory q g s (t + 1)).2.2
  let Gt : ℕ → (ℕ → Ω) → Mat q.m q.n := fun t s => batchGradient q g s t (Wt t s)
  have hW : ∀ s t, Wt (t + 1) s = Wt t s - η • orthogonalize (Mt t s) := by
    intro s t
    simp only [Wt, Mt]
    rw [trajectory_succ_eq]
  have hM0 : ∀ s, Mt 0 s = Gt 0 s := by
    intro s
    simp only [Mt, Gt, Wt]
    rw [trajectory_succ_eq]
    simp
  have hM : ∀ s t, Mt (t + 1) s = β • Mt t s + (1 - β) • Gt (t + 1) s := by
    intro s t
    simp only [Mt, Gt, Wt]
    rw [trajectory_succ_eq q g s (t + 1)]
    simp only [Nat.add_one_ne_zero, ite_false]
    rfl
  let D : ℕ → (ℕ → Ω) → Mat q.m q.n := fun t s => ∑ i ∈ Finset.range (t + 1),
    (if i = 0 then β ^ t else (1 - β) * β ^ (t - i)) • (Gt i s - gradient f (Wt i s))
  have hD0 : ∀ s, D 0 s = Gt 0 s - gradient f (Wt 0 s) := by
    intro s; simp [D]
  have hD : ∀ s t, D (t + 1) s = β • D t s + (1 - β) • (Gt (t + 1) s - gradient f (Wt (t + 1) s)) :=
    fun s t => weights_recursion β (fun i => Gt i s - gradient f (Wt i s)) t
  have hgm := measurable_gradient_of f
  have hWm : ∀ t, Measurable (Wt t) := fun t => measurable_fst.comp (trajectory_measurable q g ho.measurable t)
  have hWk : ∀ t s s', (∀ j < t * q.B, s j = s' j) → Wt t s = Wt t s' := fun t s s' h => by
    simp only [Wt]; rw [trajectory_prefix q g t s s' h]
  have hnoise := fun t => momentum_noise μ P hiid f g σ ho hgm β hβ0 hβ1 q.B hB Wt hWm hWk D
    (fun s => hD0 s) (fun t s => hD s t) t
  have hEr := fun t => noise_mean_bound P (D t) (hnoise t).1 (hnoise t).2.2.1 σ β q.B t hσ hβ0 hβ1 hB
    (hnoise t).2.2.2
  have hpath : ∀ t s, η * nuclearNorm (gradient f (Wt t s)) ≤ f (Wt t s) - f (Wt (t + 1) s) +
      (L * η ^ 2 / 2 + 2 * β * L * η ^ 2 / (1 - β)) + 2 * η * Real.sqrt r * ‖D t s‖ := by
    intro t s
    have h1 := step_spectral f L η hη hL hg hlip (Wt t s) (Mt t s)
    rw [← hW] at h1
    have h2 := momentum_tracking_spectral f L η β hL hη.le hβ0 hβ1 hlip (fun t => Wt t s)
      (fun t => Mt t s) (fun t => Gt t s) (fun t => D t s) (hW s) (hM0 s) (hM s) (hD0 s) (hD s) t
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * η)
    have e : 2 * η * (β * L * η / (1 - β)) = 2 * β * L * η ^ 2 / (1 - β) := by ring
    nlinarith
  obtain ⟨lb, hlb⟩ := hbdd
  have hlb' : ∀ x, lb ≤ f x := fun x => hlb ⟨x, rfl⟩
  have hW0 : ∀ s, Wt 0 s = q.W0 := fun s => by simp only [Wt]; rw [trajectory_zero]
  have hdist : ∀ t s, spectralNorm (Wt t s - q.W0) ≤ t * η := fun t s => by
    have := (distance_from_start η hη.le (fun t => Wt t s) (fun t => Mt t s) (hW s) t).2
    rwa [hW0] at this
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun x => (hg x).hasFDerivAt.continuousAt
  have hAi : ∀ t, Integrable (fun s => nuclearNorm (gradient f (Wt t s))) (P : Measure (ℕ → Ω)) := by
    intro t
    refine integrable_of_abs_le _ _ (measurable_nuclearNorm.comp (hgm.comp (hWm t)))
      (nuclearNorm (gradient f q.W0) + L * (t * η)) (fun s => ?_)
    rw [abs_of_nonneg (nuclearNorm_nonneg _)]
    have h1 := hlip (Wt t s) q.W0
    have h2 := nuclearNorm_le_add_inner (gradient f q.W0) (gradient f (Wt t s) - gradient f q.W0)
    rw [add_sub_cancel] at h2
    nlinarith [mul_le_mul_of_nonneg_left (hdist t s) hL]
  have hFi : ∀ t, Integrable (fun s => f (Wt t s)) (P : Measure (ℕ → Ω)) := by
    intro t
    set R := t * η
    have hR0 : 0 ≤ R := by positivity
    refine integrable_of_abs_le _ _ (hcont.measurable.comp (hWm t))
      (|lb| + |f q.W0| + nuclearNorm (gradient f q.W0) * R + L * R ^ 2 / 2) (fun s => ?_)
    have hd := spectral_descent f L hg hlip q.W0 (Wt t s - q.W0)
    rw [add_sub_cancel] at hd
    have hi := inner_le_nuclearNorm_mul_spectralNorm (gradient f q.W0) (Wt t s - q.W0)
    have hR := hdist t s
    have hn := spectralNorm_nonneg (Wt t s - q.W0)
    have hsq : spectralNorm (Wt t s - q.W0) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hn hR 2
    have hnuc := nuclearNorm_nonneg (gradient f q.W0)
    rw [abs_le]
    constructor
    · nlinarith [hlb' (Wt t s), abs_nonneg lb, neg_abs_le lb, abs_nonneg (f q.W0),
        mul_nonneg hnuc hR0, mul_nonneg hL (sq_nonneg R)]
    · nlinarith [mul_le_mul_of_nonneg_left hR hnuc,
        mul_le_mul_of_nonneg_left hsq hL, le_abs_self (f q.W0), abs_nonneg lb]
  have havg := averaged_bound (P : Measure (ℕ → Ω)) q.T hT η (L * η ^ 2 / 2 + 2 * β * L * η ^ 2 / (1 - β))
    (2 * η * Real.sqrt r) hη (by positivity) (fun t s => nuclearNorm (gradient f (Wt t s)))
    (fun t s => f (Wt t s)) (fun t s => ‖D t s‖)
    (fun t => σ / Real.sqrt q.B * (Real.sqrt ((1 - β) / (1 + β)) + β ^ (t + 1)))
    hAi hFi (fun t => (hEr t).1) hpath (fun t => (hEr t).2)
  refine ⟨hWm, hAi, hFi, havg.trans ?_⟩
  have hTpos : (0 : ℝ) < q.T := by exact_mod_cast (show 0 < q.T by omega)
  have hBpos : (0 : ℝ) < q.B := by exact_mod_cast (show 0 < q.B by omega)
  have hgeo := geom_tail_le β hβ0 hβ1 q.T
  have hsum : (1 / (q.T : ℝ)) * ∑ t ∈ Finset.range q.T,
      σ / Real.sqrt q.B * (Real.sqrt ((1 - β) / (1 + β)) + β ^ (t + 1)) ≤
      σ / Real.sqrt q.B * (Real.sqrt ((1 - β) / (1 + β)) + β / (1 - β) / q.T) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hc : 0 ≤ σ / Real.sqrt q.B := by positivity
    rw [show (1 / (q.T : ℝ)) * (σ / Real.sqrt q.B * (q.T * Real.sqrt ((1 - β) / (1 + β)) +
        ∑ t ∈ Finset.range q.T, β ^ (t + 1))) = σ / Real.sqrt q.B * (Real.sqrt ((1 - β) / (1 + β)) +
        (∑ t ∈ Finset.range q.T, β ^ (t + 1)) / q.T) by field_simp]
    gcongr
  have hk : 0 ≤ 2 * η * Real.sqrt r / η := by positivity
  have hstep := mul_le_mul_of_nonneg_left hsum hk
  have e1 : (L * η ^ 2 / 2 + 2 * β * L * η ^ 2 / (1 - β)) / η =
      L * η / 2 + 2 * η * β * L / (1 - β) := by field_simp
  have e2 : 2 * η * Real.sqrt r / η * (σ / Real.sqrt q.B * (Real.sqrt ((1 - β) / (1 + β)) + β / (1 - β) / q.T)) =
      2 * σ * Real.sqrt (r * (1 - β)) / Real.sqrt ((1 + β) * q.B) +
        2 * β * σ * Real.sqrt r / ((1 - β) * q.T * Real.sqrt q.B) := by
    rw [Real.sqrt_mul hr0, Real.sqrt_mul (by linarith : (0:ℝ) ≤ 1 + β), Real.sqrt_div' _ (by linarith : (0:ℝ) ≤ 1 + β)]
    have : 0 < Real.sqrt (1 + β) := Real.sqrt_pos.mpr (by linarith)
    have : 0 < Real.sqrt (q.B : ℝ) := Real.sqrt_pos.mpr hBpos
    field_simp
  have hFT : (∫ s, f (Wt 0 s) - f (Wt q.T s) ∂(P : Measure (ℕ → Ω))) =
      ∫ s, f (trajectory q g s 0).2.1 - f (trajectory q g s q.T).2.1 ∂(P : Measure (ℕ → Ω)) := rfl
  rw [hFT, e1] at *
  linarith [e2 ▸ hstep]

theorem quarter_root_eq (x Q : ℝ) (hx : 0 ≤ x) (h : x ^ 4 = Q) : Q ^ (1 / 4 : ℝ) = x := by
  rw [← h, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast hx (by norm_num)

theorem tuned_generic (r K Δ σ β T η E : ℝ) (hr : 0 < r) (hK : 0 < K) (hσ : 0 ≤ σ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hT : 0 < T) (hη : 0 < η)
    (hηdef : η = Real.sqrt ((1 - β) * Δ / (T * K)))
    (hβdef : 1 - β = if σ = 0 then 1 else min (Real.sqrt (K * Δ) / (σ * Real.sqrt (r * T))) 1)
    (hE : E ≤ Δ) :
    E / (T * η) + K * η / 2 + 2 * σ * Real.sqrt (r * (1 - β)) / Real.sqrt (1 + β) +
        2 * β * σ * Real.sqrt r / ((1 - β) * T) + 2 * η * β * K / (1 - β) ≤
      6 * ((r * K * Δ * σ ^ 2 / T) ^ (1 / 4 : ℝ) + Real.sqrt (K * Δ / T) +
        r * σ ^ 2 / Real.sqrt (K * Δ * T)) := by
  have ha0 : 0 < 1 - β := by linarith
  have hΔ : 0 < Δ := by
    by_contra h
    have h' : Δ ≤ 0 := not_lt.mp h
    have : (1 - β) * Δ / (T * K) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos ha0.le h') (by positivity)
    rw [hηdef, Real.sqrt_eq_zero'.mpr this] at hη
    exact lt_irrefl _ hη
  have hsa : 0 < Real.sqrt (1 - β) := Real.sqrt_pos.mpr ha0
  have hsD : 0 < Real.sqrt Δ := Real.sqrt_pos.mpr hΔ
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have qa : Real.sqrt (1 - β) ^ 2 = 1 - β := Real.sq_sqrt ha0.le
  have qD : Real.sqrt Δ ^ 2 = Δ := Real.sq_sqrt hΔ.le
  have qT : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  have qK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have qr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have sa1 : Real.sqrt (1 - β) ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have eη : η = Real.sqrt (1 - β) * Real.sqrt Δ / (Real.sqrt T * Real.sqrt K) := by
    rw [hηdef, Real.sqrt_div (by positivity), Real.sqrt_mul ha0.le, Real.sqrt_mul hT.le]
  have eY : Real.sqrt (K * Δ / T) = Real.sqrt K * Real.sqrt Δ / Real.sqrt T := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul hK.le]
  set sa := Real.sqrt (1 - β)
  set sD := Real.sqrt Δ
  set sT := Real.sqrt T
  set sK := Real.sqrt K
  set sr := Real.sqrt r
  set Y := Real.sqrt (K * Δ / T)
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hX0 : 0 ≤ (r * K * Δ * σ ^ 2 / T) ^ (1 / 4 : ℝ) := by positivity
  have hZ0 : 0 ≤ r * σ ^ 2 / Real.sqrt (K * Δ * T) := by positivity
  have t1 : E / (T * η) ≤ Y / sa := by
    rw [eη, eY, div_le_div_iff₀ (by positivity) hsa]
    have h2 : E * sa ≤ sD ^ 2 * sa := mul_le_mul_of_nonneg_right (qD ▸ hE) hsa.le
    have e : sK * sD / sT * (T * (sa * sD / (sT * sK))) = sD ^ 2 * sa := by
      rw [← qT]; field_simp
    linarith
  have t2 : K * η / 2 ≤ Y / 2 := by
    rw [eη, eY]
    have e : K * (sa * sD / (sT * sK)) = sa * (sK * sD / sT) := by rw [← qK]; field_simp
    rw [e]
    have hy : 0 ≤ sK * sD / sT := by positivity
    nlinarith [mul_le_mul_of_nonneg_right sa1 hy]
  have t5 : 2 * η * β * K / (1 - β) ≤ 2 * Y / sa := by
    rw [eη, eY, div_le_div_iff₀ ha0 hsa]
    have e : 2 * (sa * sD / (sT * sK)) * β * K * sa = (1 - β) * (2 * (sK * sD / sT)) * β := by
      rw [← qK, ← qa]; field_simp
    rw [e]
    have hy : 0 ≤ (1 - β) * (2 * (sK * sD / sT)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (show β ≤ 1 by linarith) hy]
  have t3 : 2 * σ * Real.sqrt (r * (1 - β)) / Real.sqrt (1 + β) ≤ 2 * σ * sr * sa := by
    rw [Real.sqrt_mul hr.le]
    have h1 : 1 ≤ Real.sqrt (1 + β) := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ 2 * σ * (sr * sa) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 this]
  by_cases hσ0 : σ = 0
  · rw [ite_eq_left hσ0] at hβdef
    have hβz : β = 0 := by linarith
    have hsa1 : sa = 1 := by
      show Real.sqrt (1 - β) = 1
      rw [hβz, sub_zero, Real.sqrt_one]
    rw [hsa1, div_one] at t1
    have z4 : 2 * β * σ * Real.sqrt r / ((1 - β) * T) = 0 := by rw [hσ0]; ring
    have z5 : 2 * η * β * K / (1 - β) = 0 := by rw [hβz]; ring
    have z3 : 2 * σ * Real.sqrt (r * (1 - β)) / Real.sqrt (1 + β) = 0 := by rw [hσ0]; ring
    rw [z4, z5, z3]
    linarith
  · have hσp : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσ0)
    rw [ite_eq_right hσ0] at hβdef
    have ec : Real.sqrt (K * Δ) / (σ * Real.sqrt (r * T)) = sK * sD / (σ * sr * sT) := by
      rw [Real.sqrt_mul hK.le, Real.sqrt_mul hr.le]; ring
    rw [ec] at hβdef
    rcases le_total 1 (sK * sD / (σ * sr * sT)) with hc | hc
    · rw [min_eq_right hc] at hβdef
      have hβz : β = 0 := by linarith
      have hsa1 : sa = 1 := by
        show Real.sqrt (1 - β) = 1
        rw [hβz, sub_zero, Real.sqrt_one]
      rw [hsa1, div_one] at t1
      rw [hsa1, mul_one] at t3
      have hσY : σ * sr ≤ Y := by
        rw [eY, le_div_iff₀ hsT]
        rw [le_div_iff₀ (by positivity)] at hc
        linarith
      have z4 : 2 * β * σ * Real.sqrt r / ((1 - β) * T) = 0 := by rw [hβz]; ring
      have z5 : 2 * η * β * K / (1 - β) = 0 := by rw [hβz]; ring
      rw [z4, z5]
      nlinarith
    · rw [min_eq_left hc] at hβdef
      have hsa2 : sa ^ 2 = sK * sD / (σ * sr * sT) := by rw [qa, hβdef]
      have hYsa : Y / sa = σ * sr * sa := by
        rw [div_eq_iff hsa.ne', eY]
        have : σ * sr * sa * sa = σ * sr * sa ^ 2 := by ring
        rw [this, hsa2]
        field_simp
      have hX : (r * K * Δ * σ ^ 2 / T) ^ (1 / 4 : ℝ) = σ * sr * sa := by
        apply quarter_root_eq _ _ (by positivity)
        rw [mul_pow, mul_pow, show sa ^ 4 = (sa ^ 2) ^ 2 by ring, hsa2, ← qr, ← qK, ← qD, ← qT]
        field_simp
      have hZ : 2 * β * σ * sr / ((1 - β) * T) ≤ 2 * (r * σ ^ 2 / Real.sqrt (K * Δ * T)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hK.le, hβdef]
        rw [div_le_iff₀ (by positivity)]
        have e : 2 * (r * σ ^ 2 / (sK * sD * sT)) * (sK * sD / (σ * sr * sT) * T) = 2 * σ * sr := by
          rw [← qr, ← qT]; field_simp
        rw [e]
        have hm := mul_le_mul_of_nonneg_right (show β ≤ 1 by linarith) (by positivity : (0:ℝ) ≤ 2 * σ * sr)
        calc 2 * β * σ * sr = β * (2 * σ * sr) := by ring
          _ ≤ 1 * (2 * σ * sr) := hm
          _ = 2 * σ * sr := one_mul _
      have e2 : 2 * Y / sa = 2 * (Y / sa) := by ring
      linarith [hX, hZ, t1, t2, t3, t5, hY0, hZ0, hYsa, e2]

theorem complexity_generic (r K Δ σ T ε : ℝ) (hr : 0 < r) (hK : 0 < K) (hΔ : 0 < Δ) (hT : 0 < T)
    (hε : 0 < ε)
    (hTbig : 18 ^ 4 * r * K * Δ * σ ^ 2 / ε ^ 4 + 18 ^ 2 * K * Δ / ε ^ 2 +
      18 ^ 2 * r ^ 2 * σ ^ 4 / (K * Δ * ε ^ 2) ≤ T) :
    6 * ((r * K * Δ * σ ^ 2 / T) ^ (1 / 4 : ℝ) + Real.sqrt (K * Δ / T) +
      r * σ ^ 2 / Real.sqrt (K * Δ * T)) ≤ ε := by
  have a1 : 0 ≤ 18 ^ 4 * r * K * Δ * σ ^ 2 / ε ^ 4 := by positivity
  have a2 : 0 ≤ 18 ^ 2 * K * Δ / ε ^ 2 := by positivity
  have a3 : 0 ≤ 18 ^ 2 * r ^ 2 * σ ^ 4 / (K * Δ * ε ^ 2) := by positivity
  have hX : (r * K * Δ * σ ^ 2 / T) ^ (1 / 4 : ℝ) ≤ ε / 18 := by
    have hQ : r * K * Δ * σ ^ 2 / T ≤ (ε / 18) ^ 4 := by
      have h1 : 18 ^ 4 * r * K * Δ * σ ^ 2 / ε ^ 4 ≤ T := by linarith
      rw [div_le_iff₀ (by positivity)] at h1
      rw [div_le_iff₀ hT]
      have : (ε / 18) ^ 4 * T = ε ^ 4 * T / 18 ^ 4 := by ring
      rw [this, le_div_iff₀ (by norm_num)]
      nlinarith
    calc (r * K * Δ * σ ^ 2 / T) ^ (1 / 4 : ℝ) ≤ ((ε / 18) ^ 4) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hQ (by norm_num)
      _ = ε / 18 := quarter_root_eq _ _ (by positivity) rfl
  have hY : Real.sqrt (K * Δ / T) ≤ ε / 18 := by
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : 18 ^ 2 * K * Δ / ε ^ 2 ≤ T := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ hT]
    have : (ε / 18) ^ 2 * T = ε ^ 2 * T / 18 ^ 2 := by ring
    rw [this, le_div_iff₀ (by norm_num)]
    nlinarith
  have hZ : r * σ ^ 2 / Real.sqrt (K * Δ * T) ≤ ε / 18 := by
    have hs : 0 < Real.sqrt (K * Δ * T) := Real.sqrt_pos.mpr (by positivity)
    rw [div_le_iff₀ hs]
    have h1 : 18 ^ 2 * r ^ 2 * σ ^ 4 / (K * Δ * ε ^ 2) ≤ T := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    have hsq : (r * σ ^ 2) ^ 2 ≤ (ε / 18 * Real.sqrt (K * Δ * T)) ^ 2 := by
      rw [mul_pow (ε / 18), Real.sq_sqrt (by positivity)]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  linarith

theorem momentum_error {Ω : Type} [MeasurableSpace Ω] (q : Public) (σ : ℝ) (hσ : 0 ≤ σ)
    (hβ0 : 0 ≤ q.β) (hβ1 : q.β < 1) (hB : 1 ≤ q.B) (f : Mat q.m q.n → ℝ)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω)) (g : Mat q.m q.n → Ω → Mat q.m q.n)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat q.m q.n) Ω
      (μ : Measure Ω) f g σ)
    (C : ℕ → (ℕ → Ω) → Mat q.m q.n) (hC0 : ∀ s, C 0 s = gradient f (trajectory q g s 0).2.1)
    (hC : ∀ t s, C (t + 1) s = q.β • C t s + (1 - q.β) • gradient f (trajectory q g s (t + 1)).2.1)
    (t : ℕ) :
    Integrable (fun s => ‖C t s - (trajectory q g s (t + 1)).2.2‖) (P : Measure (ℕ → Ω)) ∧
      (∫ s, ‖C t s - (trajectory q g s (t + 1)).2.2‖ ∂(P : Measure (ℕ → Ω))) ≤
        Real.sqrt ((1 - q.β) / (1 + q.β)) * σ / Real.sqrt q.B + q.β ^ t * σ / Real.sqrt q.B := by
  set β := q.β
  let Wt : ℕ → (ℕ → Ω) → Mat q.m q.n := fun t s => (trajectory q g s t).2.1
  let Mt : ℕ → (ℕ → Ω) → Mat q.m q.n := fun t s => (trajectory q g s (t + 1)).2.2
  let Gt : ℕ → (ℕ → Ω) → Mat q.m q.n := fun t s => batchGradient q g s t (Wt t s)
  have hM0 : ∀ s, Mt 0 s = Gt 0 s := by
    intro s
    simp only [Mt, Gt, Wt]
    rw [trajectory_succ_eq]
    simp
  have hM : ∀ s t, Mt (t + 1) s = β • Mt t s + (1 - β) • Gt (t + 1) s := by
    intro s t
    simp only [Mt, Gt, Wt]
    rw [trajectory_succ_eq q g s (t + 1)]
    simp only [Nat.add_one_ne_zero, ite_false]
    rfl
  let D : ℕ → (ℕ → Ω) → Mat q.m q.n := fun t s => ∑ i ∈ Finset.range (t + 1),
    (if i = 0 then β ^ t else (1 - β) * β ^ (t - i)) • (Gt i s - gradient f (Wt i s))
  have hD0 : ∀ s, D 0 s = Gt 0 s - gradient f (Wt 0 s) := by
    intro s; simp [D]
  have hD : ∀ s t, D (t + 1) s = β • D t s + (1 - β) • (Gt (t + 1) s - gradient f (Wt (t + 1) s)) :=
    fun s t => weights_recursion β (fun i => Gt i s - gradient f (Wt i s)) t
  have hCM : ∀ t s, C t s - Mt t s = -D t s := by
    intro t
    induction t with
    | zero => intro s; rw [hC0, hM0, hD0]; simp only [Wt]; module
    | succ t ih =>
      intro s
      have e : C t s = Mt t s - D t s := by rw [← sub_eq_zero]; have := ih s; rw [← sub_eq_zero] at this; rw [← this]; module
      rw [hC, hM, hD, e]
      simp only [Wt]
      module
  have hWm : ∀ t, Measurable (Wt t) := fun t => measurable_fst.comp (trajectory_measurable q g ho.measurable t)
  have hWk : ∀ t s s', (∀ j < t * q.B, s j = s' j) → Wt t s = Wt t s' := fun t s s' h => by
    simp only [Wt]; rw [trajectory_prefix q g t s s' h]
  have hnoise := momentum_noise μ P hiid f g σ ho (measurable_gradient_of f) β hβ0 hβ1 q.B hB Wt hWm hWk D
    (fun s => hD0 s) (fun t s => hD s t) t
  have hEr := noise_mean_bound P (D t) hnoise.1 hnoise.2.2.1 σ β q.B t hσ hβ0 hβ1 hB hnoise.2.2.2
  have hnorm : (fun s => ‖C t s - (trajectory q g s (t + 1)).2.2‖) = fun s => ‖D t s‖ := by
    funext s
    rw [show (trajectory q g s (t + 1)).2.2 = Mt t s from rfl, hCM t s, norm_neg]
  rw [hnorm]
  refine ⟨hEr.1, hEr.2.trans ?_⟩
  have hBpos : 0 < Real.sqrt q.B := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < q.B by omega))
  have hpow : β ^ (t + 1) ≤ β ^ t := pow_le_pow_of_le_one hβ0 hβ1.le (Nat.le_succ t)
  rw [div_mul_eq_mul_div, mul_add, add_div]
  have h1 : σ * Real.sqrt ((1 - β) / (1 + β)) / Real.sqrt q.B =
      Real.sqrt ((1 - β) / (1 + β)) * σ / Real.sqrt q.B := by ring
  have h2 : σ * β ^ (t + 1) / Real.sqrt q.B ≤ β ^ t * σ / Real.sqrt q.B := by
    rw [mul_comm σ]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hσ) hBpos.le
  linarith

end OracleTemplate.Muon
