import LongTails.Proofs.QuarticAccelerationWeights
import LongTails.Proofs.QuarticAccelerationRadius

namespace LongTails.Proofs.QuarticAccelerationRate

open LongTails.Proofs.QuarticAccelerationTrace LongTails.Proofs.QuarticAccelerationWeights
open LongTails.Proofs.QuarticAccelerationGrowth
open LongTails.Algorithms.QuarticAcceleration
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma valid_prefix {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 : E} {N M : ℕ}
    (hv : Valid t f γ x0 N) (hM : M ≤ N) : Valid t f γ x0 M where
  initial := hv.initial
  guess_pos k hk := hv.guess_pos k (hk.trans hM)
  lam_pos k hk := hv.lam_pos k (hk.trans_le hM)
  first_guess h := hv.first_guess (h.trans_le hM)
  advance_eq k hk := hv.advance_eq k (hk.trans_le hM)
  guess_eq k hk := hv.guess_eq k (hk.trans_le hM)
  support k hk := hv.support k (hk.trans_le hM)
  residual k hk := hv.residual k (hk.trans_le hM)

lemma root_prefix_growth {t : Trace E} {f : E → ℝ} {γ R : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ) (hR : 0 < R)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x) : ∀ k ≤ N,
    (1 / (8 * (γ * R ^ 2) ^ (1 / 5 : ℝ))) *
      (∑ i ∈ Finset.range k, if t.guess i < lam t γ i then (t.state (i + 1)).weight ^ (1 / 5 : ℝ) else 0) ≤
      ((t.state k).weight ^ (1 / 5 : ℝ)) ^ 2 := by
  classical
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    positivity
  have hkp : 0 < k := Nat.pos_of_ne_zero hk0
  have hvk := valid_prefix hv hk
  let selected := (Finset.range k).filter (fun i => t.guess i < lam t γ i)
  have hsel (i : ℕ) (hi : i ∈ selected) : i < k := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hw : (∑ i ∈ selected, 1 / Real.sqrt (t.guess i)) ≤ 8 * Real.sqrt (t.state k).weight := by
    apply le_trans _ (weight_sum hvk hkp)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => by positivity)
  have he : (∑ i ∈ selected, (t.state (i + 1)).weight * t.guess i ^ 2) ≤ 2 * (γ * R ^ 2) := by
    simpa only [selected, Finset.sum_filter, mul_assoc] using up_energy_sum hvk hc hγ hx0 hmin
  have hh := normalized_growth selected (fun i => (t.state (i + 1)).weight) t.guess
    (fun i hi => weight_nonneg hvk (i + 1) (Nat.succ_le_of_lt (hsel i hi)))
    (fun i hi => hvk.guess_pos i (hsel i hi).le) (by positivity : 0 < γ * R ^ 2)
    (weight_nonneg hvk k le_rfl) he hw
  simpa only [selected, Finset.sum_filter] using hh

lemma up_root_growth {t : Trace E} {f : E → ℝ} {γ R : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ) (hR : 0 < R)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x) :
    (1 / (8 * (γ * R ^ 2) ^ (1 / 5 : ℝ))) *
      (∑ i ∈ Finset.range N, if t.guess i < lam t γ i then (1 : ℝ) else 0) / 2 ≤
      (t.state N).weight ^ (1 / 5 : ℝ) := by
  classical
  apply QuarticAccelerationCount.selected_sequence_growth
    (fun k => (t.state k).weight ^ (1 / 5 : ℝ)) (fun k => t.guess k < lam t γ k) N
    (by positivity) _ _ _ (root_prefix_growth hv hc hγ hR hx0 hmin) N le_rfl
  · intro k hk
    exact Real.rpow_nonneg (weight_nonneg hv k hk) _
  · intro k hk
    exact Real.rpow_le_rpow (weight_nonneg hv k hk.le) (weight_strict hv hk).le (by norm_num)
  · intro k hk _
    exact Real.rpow_pos_of_pos (weight_pos hv (Nat.zero_lt_succ _) (Nat.succ_le_of_lt hk)) _

lemma up_count_power {t : Trace E} {f : E → ℝ} {γ R : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ) (hR : 0 < R)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x) :
    (∑ i ∈ Finset.range N, if t.guess i < lam t γ i then (1 : ℝ) else 0) ^ 5 ≤
      2 ^ 20 * γ * R ^ 2 * (t.state N).weight := by
  have hh := up_root_growth hv hc hγ hR hx0 hmin
  have hroot : 0 < (γ * R ^ 2) ^ (1 / 5 : ℝ) := by positivity
  have hm := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hh
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 8 * (γ * R ^ 2) ^ (1 / 5 : ℝ) by positivity)
  have he : (8 * (γ * R ^ 2) ^ (1 / 5 : ℝ)) * (1 / (8 * (γ * R ^ 2) ^ (1 / 5 : ℝ))) = 1 := by field_simp
  rw [← mul_assoc, he, one_mul] at hm'
  have hn : 0 ≤ ∑ i ∈ Finset.range N, if t.guess i < lam t γ i then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hp := pow_le_pow_left₀ hn hm' 5
  rw [mul_pow, mul_pow, mul_pow, fifth_root_pow (by positivity : 0 ≤ γ * R ^ 2),
    fifth_root_pow (weight_nonneg hv N le_rfl)] at hp
  convert hp using 1; ring

lemma guess_log {t : Trace E} {f : E → ℝ} {γ : ℝ} {x0 : E} {N : ℕ}
    (hv : Valid t f γ x0 N) : ∀ k ≤ N,
    Real.log (t.guess k) = Real.log (t.guess 0) +
      (2 * (∑ i ∈ Finset.range k, if t.guess i < lam t γ i then (1 : ℝ) else 0) - k) * Real.log 4 := by
  classical
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have hlt : k < N := by omega
    have hi := ih hlt.le
    rw [hv.guess_eq k hlt]
    unfold nextGuess
    by_cases hu : t.guess k < lam t γ k
    · rw [ite_eq_right (not_le.mpr hu), Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (hv.guess_pos k hlt.le).ne',
        Finset.sum_range_succ, ite_eq_left hu, hi]
      push_cast
      ring
    · rw [ite_eq_left (le_of_not_gt hu), Real.log_div (hv.guess_pos k hlt.le).ne' (by norm_num : (4 : ℝ) ≠ 0),
        Finset.sum_range_succ, ite_eq_right hu, hi]
      push_cast
      ring

lemma guess_threshold {t : Trace E} {f : E → ℝ} {γ X : ℝ} {x0 : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hN : 0 < N) (hX : 0 < X) (hfinal : (t.state N).weight < X) :
    ∀ k ≤ N, 1 / (4 * X) < t.guess k := by
  have hfirst : 1 / t.guess 0 < X := by
    rw [one_div, ← first_weight hv hN]
    exact (weight_mono hv hN le_rfl).trans_lt hfinal
  intro k hk
  induction k with
  | zero =>
    have hh := (div_lt_iff₀ (hv.guess_pos 0 (Nat.zero_le N))).mp hfirst
    apply (div_lt_iff₀ (by positivity : 0 < 4 * X)).mpr
    nlinarith only [hh]
  | succ k ih =>
    have hlt : k < N := by omega
    rw [hv.guess_eq k hlt]
    unfold nextGuess
    split_ifs with hd
    · have hweight := (LongTails.Proofs.QuarticAcceleration.advance_down_weight (t.state k)
        (g := t.gradient k) (hv.guess_pos k hlt.le) (weight_nonneg hv k hlt.le) (hv.lam_pos k hlt) hd).1
      rw [← hv.advance_eq k hlt] at hweight
      have hlo := LongTails.Proofs.CompositeCubicAcceleration.trialWeight_lower
        (hv.guess_pos k hlt.le) (weight_nonneg hv k hlt.le)
      have hnext := (weight_mono hv hk le_rfl).trans_lt hfinal
      have hinv : 1 / t.guess k < X := by
        rw [one_div]
        nlinarith only [hlo, hweight, hnext, weight_nonneg hv k hlt.le]
      have hh := (div_lt_iff₀ (hv.guess_pos k hlt.le)).mp hinv
      apply (div_lt_iff₀ (by positivity : 0 < 4 * X)).mpr
      nlinarith only [hh]
    · have hp := hv.guess_pos k hlt.le
      linarith [ih hlt.le]


lemma log_four_lower : 1 ≤ Real.log 4 := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  norm_num at hh
  linarith

lemma logarithm_bound {v : ℝ} (hv : 0 < v) :
    Real.log (8 * v) ≤ (3 / 2 + 5 * v ^ (1 / 5 : ℝ)) * Real.log 4 := by
  have hr : 0 < v ^ (1 / 5 : ℝ) := by positivity
  have hh := Real.log_le_sub_one_of_pos hr
  rw [Real.log_rpow hv] at hh
  have he4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have he8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hm := mul_le_mul_of_nonneg_left log_four_lower (show 0 ≤ 5 * v ^ (1 / 5 : ℝ) by positivity)
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hv.ne', he8]
  nlinarith only [hh, hm, he4]

lemma weight_after_budget {t : Trace E} {f : E → ℝ} {γ R X : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ) (hR : 0 < R) (hX : 0 < X)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x)
    (hbudget : 64 * (1 + (γ * R ^ 2 * X) ^ (1 / 5 : ℝ)) ≤ (N : ℝ)) :
    X ≤ (t.state N).weight := by
  classical
  let u := ∑ i ∈ Finset.range N, if t.guess i < lam t γ i then (1 : ℝ) else 0
  let v := γ * R ^ 2 * X
  let r := v ^ (1 / 5 : ℝ)
  have hvpos : 0 < v := by dsimp [v]; positivity
  have hr : 0 < r := Real.rpow_pos_of_pos hvpos _
  have hu : 0 ≤ u := Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hN : 0 < N := by
    have hh : (0 : ℝ) < N := by change 64 * (1 + r) ≤ (N : ℝ) at hbudget; linarith
    exact_mod_cast hh
  by_contra hnot
  have hfinal : (t.state N).weight < X := lt_of_not_ge hnot
  have hup : u < 16 * r := by
    have hh := up_count_power hv hc hγ hR hx0 hmin
    have hs := mul_lt_mul_of_pos_left hfinal (show 0 < 2 ^ 20 * γ * R ^ 2 by positivity)
    have hp : (16 * r) ^ 5 = 2 ^ 20 * γ * R ^ 2 * X := by
      dsimp [r]
      rw [mul_pow, fifth_root_pow hvpos.le]
      dsimp [v]
      ring
    apply (pow_lt_pow_iff_left₀ hu (by positivity : 0 ≤ 16 * r) (by norm_num : (5 : ℕ) ≠ 0)).mp
    rw [hp]
    exact hh.trans_lt hs
  have hμ0 := hv.guess_pos 0 (Nat.zero_le N)
  have hμN := hv.guess_pos N le_rfl
  have hguess0 : t.guess 0 ≤ 2 * γ * R ^ 2 := by
    have hh := QuarticAccelerationRadius.large_parameter_radius hv hc hγ hx0 hmin hN (hv.first_guess hN).le
    rw [hv.first_guess hN]
    unfold lam parameter
    have hm := mul_le_mul_of_nonneg_left hh hγ.le
    nlinarith only [hm]
  have hlower := guess_threshold hv hN hX hfinal N le_rfl
  have hratio : t.guess 0 / t.guess N < 8 * v := by
    have hh := (div_lt_iff₀ (show 0 < 4 * X by positivity)).mp hlower
    have hm := mul_lt_mul_of_pos_left hh (show 0 < 2 * γ * R ^ 2 by positivity)
    apply (div_lt_iff₀ hμN).mpr
    dsimp [v]
    nlinarith only [hguess0, hm]
  have hlog := Real.log_lt_log (div_pos hμ0 hμN) hratio
  rw [Real.log_div hμ0.ne' hμN.ne'] at hlog
  have hidentity := guess_log hv N le_rfl
  change Real.log (t.guess N) = Real.log (t.guess 0) + (2 * u - N) * Real.log 4 at hidentity
  have hlbound := logarithm_bound hvpos
  change Real.log (8 * v) ≤ (3 / 2 + 5 * r) * Real.log 4 at hlbound
  have hln4 : 0 < Real.log 4 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) log_four_lower
  have htotal : (N : ℝ) < 2 * u + 3 / 2 + 5 * r := by
    apply (mul_lt_mul_iff_right₀ hln4).mp
    nlinarith only [hlog, hidentity, hlbound]
  change 64 * (1 + r) ≤ (N : ℝ) at hbudget
  nlinarith only [hbudget, htotal, hup, hr]


lemma objective_accuracy {t : Trace E} {f : E → ℝ} {γ R ε : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ) (hR : 0 < R) (hε : 0 < ε)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x)
    (hbudget : 64 * (1 + (γ * R ^ 4 / ε) ^ (1 / 5 : ℝ)) ≤ (N : ℝ)) :
    f (t.state N).point - f xstar ≤ ε := by
  have hX : 0 < R ^ 2 / ε := by positivity
  have hbudget' : 64 * (1 + (γ * R ^ 2 * (R ^ 2 / ε)) ^ (1 / 5 : ℝ)) ≤ (N : ℝ) := by
    convert hbudget using 1; congr 3; ring
  have hA := weight_after_budget hv hc hγ hR hX hx0 hmin hbudget'
  have he := (energy_bounds hv hc hγ hx0 hmin (le_refl N)).1
  have hg := sub_nonneg.mpr (hmin (t.state N).point)
  have hm := mul_le_mul_of_nonneg_right hA hg
  have hs : (R ^ 2 / ε) * ε = R ^ 2 := by field_simp
  apply (mul_le_mul_iff_right₀ hX).mp
  rw [hs]
  unfold potential at he
  nlinarith only [he, hm, sq_nonneg ‖(t.state N).momentum - xstar‖, sq_nonneg R]


end LongTails.Proofs.QuarticAccelerationRate
