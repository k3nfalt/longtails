import LongTails.Algorithms.GeneralizedLipschitzPilot
import LongTails.Proofs.ClippedScalarDescent
import LongTails.Proofs.Clipping
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open MeasureTheory

namespace LongTails.Proofs.GeneralizedLipschitzPilot

lemma secondMoment_upper_of_deviation
    (q estimate error scale : ℝ) (hq : 0 ≤ q) (hscale : 0 ≤ scale)
    (hdev : error ^ 2 ≤ 16 * scale * q)
    (hestimate : q - error ≤ estimate) :
    q ≤ 2 * estimate + 16 * scale := by
  have hbound : error ≤ q / 2 + 8 * scale := by
    nlinarith [sq_nonneg (q / 2 - 8 * scale)]
  linarith

lemma secondMoment_lower_of_deviation
    (q estimate error scale : ℝ) (hq : 0 ≤ q) (hscale : 0 ≤ scale)
    (hdev : error ^ 2 ≤ 16 * scale * q)
    (hestimate : estimate ≤ q + error) :
    estimate ≤ 2 * q + 16 * scale := by
  have hbound : error ≤ q + 4 * scale := by
    nlinarith [sq_nonneg (q - 4 * scale)]
  linarith

lemma rawTail_mass_lower
    (g noise κ p : ℝ) (hg : 0 < g) (hnoise : 0 ≤ noise)
    (hnoiseSmall : noise ≤ g / 2) (hκ : 1 ≤ κ) (hp : 0 ≤ p)
    (hmass : g / 2 ≤ 2 * κ * g * p + noise * Real.sqrt p) :
    1 / (16 * κ) ≤ p := by
  by_contra h
  have hpSmall : p < 1 / (16 * κ) := lt_of_not_ge h
  have hκpos : 0 < κ := by linarith
  have hprod : 16 * κ * p < 1 := by
    have := (lt_div_iff₀ (show 0 < 16 * κ by positivity)).mp hpSmall
    nlinarith
  have hpBound : p < 1 / 16 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hκ) hp]
  have hsqrt : Real.sqrt p < 1 / 4 := by
    nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p]
  have hfirst : 2 * κ * g * p < g / 8 := by
    nlinarith [mul_pos hg (show 0 < 1 - 16 * κ * p by linarith)]
  have hsecond : noise * Real.sqrt p ≤ g / 8 := by
    calc
      noise * Real.sqrt p ≤ noise * (1 / 4) :=
        mul_le_mul_of_nonneg_left (le_of_lt hsqrt) hnoise
      _ ≤ g / 8 := by linarith
  linarith

lemma clippedNorm_certificate
    (g observed m : ℝ) (hm : 0 ≤ m)
    (hlow : m / 4 ≤ observed) (hhigh : observed ≤ 2 * m)
    (hforward : g ≤ observed + m / 16 + g / 512)
    (hbackward : observed ≤ g + m / 16 + g / 512) :
    m / 6 ≤ g ∧ g ≤ 3 * m := by
  constructor <;> linarith

lemma moment_trigger_lower {q qhat t : ℝ}
    (herr : |qhat - q| ≤ q / 4 + t / 64) (haccept : t / 32 ≤ qhat) :
    t / 80 ≤ q := by
  have h := (abs_le.mp herr).2
  linarith

lemma moment_rejection_upper {q qhat t : ℝ}
    (herr : |qhat - q| ≤ q / 4 + t / 64) (hreject : qhat < t / 32) :
    q < t / 16 := by
  have h := (abs_le.mp herr).1
  linarith

lemma mean_rejection_halving {g observed m : ℝ} (hm : 0 < m)
    (herr : |observed - g| ≤ 5 * m / 128) (hreject : observed < m / 4) :
    g < m / 2 := by
  have h := (abs_le.mp herr).1
  linarith

lemma moment_rejection_halving {S q G0 κ m : ℝ} (hκ : 1 ≤ κ)
    (hG0 : 0 ≤ G0) (hm : 64 * G0 < m)
    (hS : S ≤ 2 * q + 2 * G0 ^ 2) (hq : q < κ * m ^ 2 / 16) :
    S < κ * (m / 2) ^ 2 := by
  have hmpos : 0 < m := by linarith
  have hs : (64 * G0) ^ 2 < m ^ 2 :=
    sq_lt_sq₀ (by positivity) hmpos.le |>.mpr hm
  have hk := mul_le_mul_of_nonneg_right hκ (sq_nonneg m)
  nlinarith

lemma moment_accept_gap {κ m G0 a q : ℝ} (hκ : 1 ≤ κ) (hG0 : 0 ≤ G0)
    (hm : 64 * G0 < m) (ha : 0 ≤ a) (hq : κ * m ^ 2 / 80 ≤ q)
    (hS : q ≤ 2 * G0 ^ 2 + 2 * a ^ 2) : m / 16 ≤ a := by
  have hmpos : 0 < m := by linarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 64 * G0) hm.le 2
  have hk := mul_le_mul_of_nonneg_right hκ (sq_nonneg m)
  by_contra h
  have hh : a < m / 16 := lt_of_not_ge h
  have hs2 := sq_lt_sq₀ ha (by positivity : 0 ≤ m / 16) |>.mpr hh
  nlinarith

lemma mean_accept_gap {m G0 a g observed : ℝ} (hG0 : 0 ≤ G0)
    (hm : 64 * G0 < m) (herr : |observed - g| ≤ 5 * m / 128)
    (haccept : m / 4 ≤ observed) (hg : g ≤ G0 + a) : m / 16 ≤ a := by
  have h := (abs_le.mp herr).2
  linarith

lemma pilot_accept_gap {κ m G0 a q qhat g observed : ℝ}
    (hκ : 1 ≤ κ) (hG0 : 0 ≤ G0) (hm : 64 * G0 < m) (ha : 0 ≤ a)
    (hq : |qhat - q| ≤ q / 4 + κ * m ^ 2 / 64)
    (hS : q ≤ 2 * G0 ^ 2 + 2 * a ^ 2) (hg : g ≤ G0 + a)
    (hmean : qhat < κ * m ^ 2 / 32 → |observed - g| ≤ 5 * m / 128)
    (haccept : κ * m ^ 2 / 32 ≤ qhat ∨ m / 4 ≤ observed) : m / 16 ≤ a := by
  by_cases hqaccept : κ * m ^ 2 / 32 ≤ qhat
  · exact moment_accept_gap hκ hG0 hm ha (moment_trigger_lower hq hqaccept) hS
  · exact mean_accept_gap hG0 hm (hmean (lt_of_not_ge hqaccept)) (haccept.resolve_left hqaccept) hg

open LongTails.Algorithms.GeneralizedLipschitzPilot

lemma tuning_counts_pos (κ δ : ℝ) :
    0 < (tuning κ δ).rawCount ∧ 0 < (tuning κ δ).scales ∧
    0 < (tuning κ δ).momentCount ∧ 0 < (tuning κ δ).meanCount ∧
    0 < (tuning κ δ).repetitions ∧ 0 < (tuning κ δ).updateCount := by
  dsimp [tuning]
  omega
lemma tuning_calls_pos (κ δ : ℝ) : 0 < (tuning κ δ).calls := by
  have h := (tuning_counts_pos κ δ).1
  unfold Config.calls
  omega

lemma tuning_count_bounds (κ δ : ℝ) :
    16 * κ * Real.log (9 / δ) ≤ ((tuning κ δ).rawCount : ℝ) ∧
    67108864 * κ ≤ ((tuning κ δ).momentCount : ℝ) ∧
    9216 * κ ≤ ((tuning κ δ).meanCount : ℝ) ∧
    16 * κ ≤ ((tuning κ δ).updateCount : ℝ) := by
  have h (x : ℝ) : x ≤ ((max 1 ⌈x⌉₊ : ℕ) : ℝ) :=
    (Nat.le_ceil x).trans (by exact_mod_cast le_max_right 1 ⌈x⌉₊)
  exact ⟨h _, h _, h _, h _⟩

section Selection

open LongTails.Algorithms.GeneralizedLipschitzPilot

variable {E : Type*} [NormedAddCommGroup E]

lemma norm_le_rawMaximum {n : ℕ} (samples : Fin n → E) (i : Fin n) :
    ‖samples i‖ ≤ rawMaximum samples := by
  exact_mod_cast (Finset.le_sup (f := fun j => ‖samples j‖₊) (Finset.mem_univ i))
lemma rawMaximum_le {n : ℕ} (samples : Fin n → E) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i, ‖samples i‖ ≤ M) : rawMaximum samples ≤ M := by
  have hs : Finset.univ.sup (fun i => ‖samples i‖₊) ≤ (⟨M, hM⟩ : NNReal) := by
    apply Finset.sup_le
    intro i _
    exact_mod_cast h i
  exact_mod_cast hs
lemma rawScale_ge_floor {n : ℕ} (G0 : ℝ) (samples : Fin n → E) :
    2 * G0 ≤ rawScale G0 samples := by
  exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
lemma rawScale_ge_sample {n : ℕ} (G0 : ℝ) (samples : Fin n → E) (i : Fin n) :
    2 * ‖samples i‖ ≤ rawScale G0 samples := by
  exact mul_le_mul_of_nonneg_left ((norm_le_rawMaximum samples i).trans (le_max_right _ _))
    (by norm_num)

lemma rawScale_moment_invariants {n : ℕ} (samples : Fin n → E)
    {G0 g κ t S : ℝ} (hG0 : 0 ≤ G0) (hκ : 0 ≤ κ) (ht : 0 ≤ t)
    (hS : S ≤ 16 * κ * t ^ 2)
    (hmean : g ≤ 2 * G0 ∨ ∃ i, g / 2 < ‖samples i‖)
    (hrms : t ≤ max g G0 ∨ ∃ i, t < ‖samples i‖) :
    g ≤ rawScale G0 samples ∧ S ≤ 16 * κ * (rawScale G0 samples) ^ 2 := by
  have hf := rawScale_ge_floor G0 samples
  have hg : g ≤ rawScale G0 samples := by
    rcases hmean with hg | ⟨i, hi⟩
    · exact hg.trans hf
    · have h := rawScale_ge_sample G0 samples i
      linarith
  have ht' : t ≤ rawScale G0 samples := by
    rcases hrms with ht' | ⟨i, hi⟩
    · exact ht'.trans (max_le hg (by linarith))
    · have h := rawScale_ge_sample G0 samples i
      linarith [norm_nonneg (samples i)]
  exact ⟨hg, hS.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht ht' 2) (by positivity))⟩

lemma rawScale_upper {n : ℕ} (samples : Fin n → E) {G0 g K : ℝ}
    (hG0 : 0 ≤ G0) (hK : 1 ≤ K) (h : ∀ i, ‖samples i‖ ≤ K * max g G0) :
    rawScale G0 samples ≤ 2 * K * max g G0 := by
  have hH : 0 ≤ max g G0 := hG0.trans (le_max_right _ _)
  have hKH : max g G0 ≤ K * max g G0 := by nlinarith
  have hm := rawMaximum_le samples (by positivity : 0 ≤ K * max g G0) h
  unfold rawScale
  have hb : max G0 (rawMaximum samples) ≤ K * max g G0 :=
    max_le ((le_max_right _ _).trans hKH) hm
  nlinarith

lemma select_update_spec (G0 initial κ : ℝ) (moments : ℕ → ℝ) (means : ℕ → E)
    (remaining index chosen : ℕ)
    (h : select G0 initial κ moments means index remaining = .update chosen) :
    index ≤ chosen ∧ chosen < index + remaining ∧
      64 * G0 < scale G0 initial chosen ∧
      (κ * (scale G0 initial chosen) ^ 2 / 32 ≤ moments chosen ∨
        scale G0 initial chosen / 4 ≤ ‖means chosen‖) := by
  induction remaining generalizing index with
  | zero => simp [select] at h
  | succ remaining ih =>
    by_cases ht : scale G0 initial index ≤ 64 * G0
    · simp [select, ht] at h
    · by_cases ha : κ * (scale G0 initial index) ^ 2 / 32 ≤ moments index ∨
          scale G0 initial index / 4 ≤ ‖means index‖
      · simp only [select, ite_eq_right ht, ite_eq_left ha, Decision.update.injEq] at h
        subst chosen
        exact ⟨le_rfl, by omega, lt_of_not_ge ht, ha⟩
      · simp only [select, ite_eq_right ht, ite_eq_right ha] at h
        obtain ⟨hlo, hhi, hscale, haccept⟩ := ih (index + 1) h
        exact ⟨by omega, by omega, hscale, haccept⟩

lemma select_terminal_spec (G0 initial κ : ℝ) (moments : ℕ → ℝ) (means : ℕ → E)
    (remaining index : ℕ)
    (h : select G0 initial κ moments means index remaining = .terminal) :
    ∃ chosen, index ≤ chosen ∧ chosen < index + remaining ∧
      scale G0 initial chosen ≤ 64 * G0 := by
  induction remaining generalizing index with
  | zero => simp [select] at h
  | succ remaining ih =>
    by_cases ht : scale G0 initial index ≤ 64 * G0
    · exact ⟨index, le_rfl, by omega, ht⟩
    · by_cases ha : κ * (scale G0 initial index) ^ 2 / 32 ≤ moments index ∨
          scale G0 initial index / 4 ≤ ‖means index‖
      · simp [select, ht, ha] at h
      · simp only [select, ite_eq_right ht, ite_eq_right ha] at h
        obtain ⟨chosen, hlo, hhi, hscale⟩ := ih (index + 1) h
        exact ⟨chosen, by omega, by omega, hscale⟩

lemma select_invariant (G0 initial κ : ℝ) (moments : ℕ → ℝ) (means : ℕ → E)
    (P : ℕ → Prop) (remaining index : ℕ)
    (hstep : ∀ j, index ≤ j → j < index + remaining → P j → 64 * G0 < scale G0 initial j →
      ¬(κ * (scale G0 initial j) ^ 2 / 32 ≤ moments j ∨
        scale G0 initial j / 4 ≤ ‖means j‖) → P (j + 1))
    (hinit : P index) :
    match select G0 initial κ moments means index remaining with
    | .terminal => ∃ j, index ≤ j ∧ j < index + remaining ∧ P j ∧
        scale G0 initial j ≤ 64 * G0
    | .update j => P j
    | .exhausted => P (index + remaining) := by
  induction remaining generalizing index with
  | zero => simpa [select] using hinit
  | succ remaining ih =>
    by_cases ht : scale G0 initial index ≤ 64 * G0
    · simp only [select, ite_eq_left ht]
      exact ⟨index, le_rfl, by omega, hinit, ht⟩
    · by_cases ha : κ * (scale G0 initial index) ^ 2 / 32 ≤ moments index ∨
          scale G0 initial index / 4 ≤ ‖means index‖
      · simpa only [select, ite_eq_right ht, ite_eq_left ha] using hinit
      · simp only [select, ite_eq_right ht, ite_eq_right ha]
        have h := ih (index + 1) (by
          intro j hlo hhi
          exact hstep j (by omega) (by omega))
          (hstep index le_rfl (by omega) hinit (lt_of_not_ge ht) ha)
        cases he : select G0 initial κ moments means (index + 1) remaining with
        | terminal =>
          rw [he] at h
          obtain ⟨j, hlo, hhi, hp, ht⟩ := h
          exact ⟨j, by omega, by omega, hp, ht⟩
        | update j => simpa only [he] using h
        | exhausted => simpa only [he, Nat.add_assoc, Nat.add_comm 1 remaining] using h

lemma scale_halving {G0 initial : ℝ} (hG0 : 0 ≤ G0) (j : ℕ)
    (hm : 64 * G0 < scale G0 initial j) :
    scale G0 initial (j + 1) = scale G0 initial j / 2 := by
  have h : G0 < initial / 2 ^ j := by
    by_contra hn
    have hi := le_of_not_gt hn
    simp only [scale, max_eq_left hi] at hm
    linarith
  have he : initial / (2 : ℝ) ^ (j + 1) = (initial / 2 ^ j) / 2 := by
    rw [pow_succ, div_mul_eq_div_div]
  rw [scale, he, scale, max_eq_right h.le]
  apply max_eq_right
  simp only [scale, max_eq_right h.le] at hm
  linarith

lemma selection_preserves_bounds (G0 initial κ g S : ℝ)
    (moments q : ℕ → ℝ) (means : ℕ → E) (hG0 : 0 ≤ G0) (hκ : 1 ≤ κ)
    (remaining index : ℕ)
    (hstats : ∀ j, index ≤ j → j < index + remaining → g ≤ scale G0 initial j →
      S ≤ 2 * q j + 2 * G0 ^ 2 ∧
      |moments j - q j| ≤ q j / 4 + κ * (scale G0 initial j) ^ 2 / 64 ∧
      (moments j < κ * (scale G0 initial j) ^ 2 / 32 →
        |‖means j‖ - g| ≤ 5 * scale G0 initial j / 128))
    (hinit : g ≤ scale G0 initial index ∧ S ≤ 16 * κ * (scale G0 initial index) ^ 2) :
    match select G0 initial κ moments means index remaining with
    | .terminal => g ≤ 64 * G0
    | .update j => g ≤ scale G0 initial j ∧ S ≤ 16 * κ * (scale G0 initial j) ^ 2
    | .exhausted => g ≤ scale G0 initial (index + remaining) ∧
        S ≤ 16 * κ * (scale G0 initial (index + remaining)) ^ 2 := by
  let P := fun j => g ≤ scale G0 initial j ∧ S ≤ 16 * κ * (scale G0 initial j) ^ 2
  have hstep : ∀ j, index ≤ j → j < index + remaining → P j → 64 * G0 < scale G0 initial j →
      ¬(κ * (scale G0 initial j) ^ 2 / 32 ≤ moments j ∨
        scale G0 initial j / 4 ≤ ‖means j‖) → P (j + 1) := by
    intro j hlo hhi hj hm hr
    obtain ⟨hS, hq, hmean⟩ := hstats j hlo hhi hj.1
    have hqr : moments j < κ * (scale G0 initial j) ^ 2 / 32 :=
      lt_of_not_ge (fun h => hr (Or.inl h))
    have hmr : ‖means j‖ < scale G0 initial j / 4 :=
      lt_of_not_ge (fun h => hr (Or.inr h))
    have hg := mean_rejection_halving (by linarith : 0 < scale G0 initial j) (hmean hqr) hmr
    have hs := moment_rejection_halving hκ hG0 hm hS (moment_rejection_upper hq hqr)
    change g ≤ scale G0 initial (j + 1) ∧ S ≤ 16 * κ * (scale G0 initial (j + 1)) ^ 2
    rw [scale_halving hG0 j hm]
    exact ⟨hg.le, hs.le.trans (by nlinarith [sq_nonneg (scale G0 initial j / 2)])⟩
  have h := select_invariant G0 initial κ moments means P remaining index hstep hinit
  cases he : select G0 initial κ moments means index remaining with
  | terminal =>
    rw [he] at h
    obtain ⟨j, _, _, hp, ht⟩ := h
    exact hp.1.trans ht
  | update j => simpa only [he] using h
  | exhausted => simpa only [he] using h

lemma selection_no_exhaustion (G0 initial κ g : ℝ)
    (moments : ℕ → ℝ) (means : ℕ → E) (hG0 : 0 ≤ G0)
    (remaining index : ℕ) (hremaining : 0 < remaining)
    (hmean : ∀ j, index ≤ j → j < index + remaining → g ≤ scale G0 initial j →
      moments j < κ * (scale G0 initial j) ^ 2 / 32 →
      |‖means j‖ - g| ≤ 5 * scale G0 initial j / 128)
    (hinit : g ≤ scale G0 initial index)
    (hlast : scale G0 initial (index + remaining) ≤ max g G0) :
    select G0 initial κ moments means index remaining ≠ .exhausted := by
  let P := fun j => g ≤ scale G0 initial j ∧
    (index < j → g < scale G0 initial j ∧ G0 < scale G0 initial j)
  have hstep : ∀ j, index ≤ j → j < index + remaining → P j →
      64 * G0 < scale G0 initial j →
      ¬(κ * (scale G0 initial j) ^ 2 / 32 ≤ moments j ∨
        scale G0 initial j / 4 ≤ ‖means j‖) → P (j + 1) := by
    intro j hlo hhi hj hm hr
    have hqr : moments j < κ * (scale G0 initial j) ^ 2 / 32 :=
      lt_of_not_ge (fun h => hr (Or.inl h))
    have hmr : ‖means j‖ < scale G0 initial j / 4 :=
      lt_of_not_ge (fun h => hr (Or.inr h))
    have hg := mean_rejection_halving (by linarith : 0 < scale G0 initial j)
      (hmean j hlo hhi hj.1 hqr) hmr
    have hf := scale_halving hG0 j hm
    change g ≤ scale G0 initial (j + 1) ∧ _
    refine ⟨by rw [hf]; exact hg.le, ?_⟩
    intro _
    rw [hf]
    exact ⟨hg, by linarith⟩
  have h := select_invariant G0 initial κ moments means P remaining index hstep
    ⟨hinit, by omega⟩
  intro he
  rw [he] at h
  have hs := h.2 (by omega : index < index + remaining)
  exact (not_lt_of_ge hlast) (max_lt hs.1 hs.2)

lemma scale_at_cap {G0 initial g K : ℝ} (hG0 : 0 ≤ G0)
    (hinit : initial ≤ 2 * K * max g G0) (J : ℕ) (hJ : 2 * K ≤ (2 : ℝ) ^ J) :
    scale G0 initial J ≤ max g G0 := by
  unfold scale
  apply max_le (le_max_right _ _)
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) J)).mpr
  have hH : 0 ≤ max g G0 := hG0.trans (le_max_right _ _)
  have hh := mul_le_mul_of_nonneg_right hJ hH
  nlinarith

lemma le_two_pow_ceil_log {C : ℝ} (hC : 0 < C) :
    C ≤ (2 : ℝ) ^ ⌈Real.log C / Real.log 2⌉₊ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil (Real.log C / Real.log 2)
  have hp := (div_le_iff₀ hlog2).mp hc
  calc
    C = Real.exp (Real.log C) := (Real.exp_log hC).symm
    _ ≤ Real.exp ((⌈Real.log C / Real.log 2⌉₊ : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hp
    _ = (2 : ℝ) ^ ⌈Real.log C / Real.log 2⌉₊ := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

lemma configured_scale_cap {G0 initial g κ δ : ℝ} (hG0 : 0 ≤ G0) (hκ : 0 < κ)
    (hinit : initial ≤ 2 * (2 * κ + Real.sqrt (9 * ((tuning κ δ).rawCount : ℝ) / δ)) * max g G0) :
    scale G0 initial (tuning κ δ).scales ≤ max g G0 := by
  let K := 2 * κ + Real.sqrt (9 * ((tuning κ δ).rawCount : ℝ) / δ)
  have hK : 0 < 2 * K := by dsimp [K]; positivity
  have hj : 2 * K ≤ (2 : ℝ) ^ (tuning κ δ).scales := by
    have h := le_two_pow_ceil_log hK
    refine h.trans (pow_le_pow_right₀ (by norm_num) ?_)
    change ⌈Real.log (2 * K) / Real.log 2⌉₊ ≤ ⌈Real.log (2 * K) / Real.log 2⌉₊ + 2
    omega
  exact scale_at_cap hG0 hinit _ hj

end Selection

section Clipping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma residual_le_unbounded_part (u v : E) {B : ℝ} (hB : 0 ≤ B) (hv : ‖v‖ ≤ B) :
    ‖u + v - OracleTemplate.clip B (u + v)‖ ≤ ‖u‖ := by
  rw [OracleTemplate.clip_residual_norm hB]
  apply max_le (norm_nonneg _)
  have h := norm_add_le u v
  linarith

lemma split_square_le_clipped_square (u v : E) {B : ℝ} (hB : 0 ≤ B) (hv : ‖v‖ ≤ B) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖OracleTemplate.clip B (u + v)‖ ^ 2 + 2 * ‖u‖ ^ 2 := by
  have hr := residual_le_unbounded_part u v hB hv
  have hn := norm_sub_norm_le (u + v) (OracleTemplate.clip B (u + v))
  have hb : ‖u + v‖ ≤ ‖OracleTemplate.clip B (u + v)‖ + ‖u‖ := by linarith
  have hs := pow_le_pow_left₀ (norm_nonneg (u + v)) hb 2
  nlinarith [sq_nonneg (‖OracleTemplate.clip B (u + v)‖ - ‖u‖)]

lemma residual_le_unbounded_square (u v : E) {B : ℝ} (hB : 0 < B) (hv : ‖v‖ ≤ B / 2) :
    ‖u + v - OracleTemplate.clip B (u + v)‖ ≤ ‖u‖ ^ 2 / (B / 2) := by
  have h := OracleTemplate.clip_residual_le_moment (p := 2) hB (by norm_num) hv (u + v)
  simpa only [add_sub_cancel_right, Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num,
    Real.rpow_one] using h

end Clipping

section Probability

variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma tail_norm_integral {u : Ω → E} (hu : Measurable u)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P) {σ : ℝ} (hσ : 0 ≤ σ)
    (hbound : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ σ ^ 2)
    {s : Set Ω} (hs : MeasurableSet s) :
    (∫ ω, s.indicator (fun z => ‖u z‖) ω ∂P) ≤ σ * Real.sqrt (P.real s) := by
  have h := ClippedScalarDescent.holder_indicator (μ := P) (p := 2) (by norm_num)
    hu.norm (fun ω => norm_nonneg (u ω))
    (by simpa only [Real.rpow_two] using hu2) hs
  have ht : (∫ ω, ‖u ω‖ ^ 2 ∂P) ^ (1 / (2 : ℝ)) ≤ σ := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_iff).mpr ⟨hσ, hbound⟩
  have h' : (∫ ω, s.indicator (fun z => ‖u z‖) ω ∂P) ≤
      (∫ ω, ‖u ω‖ ^ 2 ∂P) ^ (1 / (2 : ℝ)) * Real.sqrt (P.real s) := by
    simpa only [Real.rpow_two, show ((2 : ℝ) - 1) / 2 = 1 / 2 by norm_num,
      Real.sqrt_eq_rpow] using h
  exact h'.trans (mul_le_mul_of_nonneg_right ht (Real.sqrt_nonneg _))

omit [CompleteSpace E] in
lemma clipped_bias_split {X u v : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hu : Measurable u) (hui : Integrable u P)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω)
    {σ V B : ℝ} (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (hmoment : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ σ ^ 2)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ V) :
    ‖(∫ ω, X ω ∂P) - ∫ ω, OracleTemplate.clip B (X ω) ∂P‖ ≤
      σ * Real.sqrt (P.real {ω | B < ‖X ω‖}) + V * P.real {ω | B < ‖X ω‖} := by
  let s : Set Ω := {ω | B < ‖X ω‖}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hX.norm
  have hclip : Integrable (fun ω => OracleTemplate.clip B (X ω)) P := by
    apply Integrable.mono' (integrable_const B)
      (((OracleTemplate.measurable_clip B).comp hX).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => OracleTemplate.norm_clip_le hB (X ω))
  have hres := (hXi.sub hclip).norm
  have hdom : ∀ᵐ ω ∂P,
      ‖X ω - OracleTemplate.clip B (X ω)‖ ≤
        s.indicator (fun z => ‖u z‖) ω + s.indicator (fun _ => V) ω := by
    filter_upwards [hsplit, hv] with ω he hvω
    by_cases hω : ω ∈ s
    · simp only [Set.indicator_of_mem hω]
      rw [OracleTemplate.clip_residual_norm hB]
      have hb : B < ‖X ω‖ := hω
      rw [max_eq_right (by linarith)]
      have hn : ‖X ω‖ ≤ ‖u ω‖ + ‖v ω‖ := by rw [he]; exact norm_add_le _ _
      linarith
    · have hb : ‖X ω‖ ≤ B := le_of_not_gt hω
      simp [OracleTemplate.clip_eq_self hb, Set.indicator_of_notMem hω]
  have hcomp := integral_mono_ae hres
    ((hui.norm.indicator hs).add ((integrable_const V).indicator hs)) hdom
  simp only [Pi.add_apply, Pi.sub_apply] at hcomp
  rw [integral_add (hui.norm.indicator hs) ((integrable_const V).indicator hs)] at hcomp
  have hconst : (∫ ω, s.indicator (fun _ => V) ω ∂P) = V * P.real s := by
    rw [integral_indicator hs, integral_const]
    simp [Measure.real, mul_comm]
  rw [hconst] at hcomp
  have htail := tail_norm_integral hu hu2 hσ hmoment hs
  rw [← integral_sub hXi hclip]
  exact (norm_integral_le_integral_norm _).trans (hcomp.trans (by linarith))

omit [CompleteSpace E] [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma split_secondMoment_integrable {X u v : Ω → E} (hX : Measurable X)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {V : ℝ}
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ V) :
    Integrable (fun ω => ‖X ω‖ ^ 2) P := by
  apply Integrable.mono' ((hu2.const_mul 2).add (integrable_const (2 * V ^ 2)))
    ((hX.norm.pow_const 2).aestronglyMeasurable)
  filter_upwards [hsplit, hv] with ω he hvω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  have hn : ‖X ω‖ ≤ ‖u ω‖ + V := by
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)
  have hs := pow_le_pow_left₀ (norm_nonneg (X ω)) hn 2
  nlinarith [sq_nonneg (‖u ω‖ - V)]

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma split_secondMoment_tail {X u v : Ω → E} (hX : Measurable X)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {V B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ V) :
    (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ (∫ ω, ‖OracleTemplate.clip B (X ω)‖ ^ 2 ∂P) +
      2 * (∫ ω, ‖u ω‖ ^ 2 ∂P) + 2 * V ^ 2 * P.real {ω | B < ‖X ω‖} := by
  let s : Set Ω := {ω | B < ‖X ω‖}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hX.norm
  have hclip : Integrable (fun ω => ‖OracleTemplate.clip B (X ω)‖ ^ 2) P := by
    apply Integrable.mono' (integrable_const (B ^ 2))
      ((((OracleTemplate.measurable_clip B).comp hX).norm.pow_const 2).aestronglyMeasurable)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (OracleTemplate.norm_clip_le hB _) 2
  have hdom : ∀ᵐ ω ∂P, ‖X ω‖ ^ 2 ≤ ‖OracleTemplate.clip B (X ω)‖ ^ 2 +
      2 * ‖u ω‖ ^ 2 + s.indicator (fun _ => 2 * V ^ 2) ω := by
    filter_upwards [hsplit, hv] with ω he hvω
    by_cases hω : ω ∈ s
    · simp only [Set.indicator_of_mem hω]
      have hn : ‖X ω‖ ≤ ‖u ω‖ + V := by
        rw [he]
        exact (norm_add_le _ _).trans (by linarith)
      have hsq := pow_le_pow_left₀ (norm_nonneg (X ω)) hn 2
      nlinarith [sq_nonneg (‖u ω‖ - V), sq_nonneg ‖OracleTemplate.clip B (X ω)‖]
    · have hb : ‖X ω‖ ≤ B := le_of_not_gt hω
      simp only [OracleTemplate.clip_eq_self hb, Set.indicator_of_notMem hω, add_zero]
      nlinarith [sq_nonneg ‖u ω‖]
  have hi := integral_mono_ae (split_secondMoment_integrable hX hu2 hsplit hv)
    ((hclip.add (hu2.const_mul 2)).add ((integrable_const (2 * V ^ 2)).indicator hs)) hdom
  simp only [Pi.add_apply] at hi
  have hsum : Integrable (fun ω => ‖OracleTemplate.clip B (X ω)‖ ^ 2 + 2 * ‖u ω‖ ^ 2) P :=
    hclip.add (hu2.const_mul 2)
  rw [integral_add hsum ((integrable_const (2 * V ^ 2)).indicator hs),
    integral_add hclip (hu2.const_mul 2), integral_const_mul, integral_indicator hs,
    integral_const] at hi
  simpa only [smul_eq_mul, Measure.real, Measure.restrict_apply_univ, mul_comm] using hi

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma split_secondMoment_clipped {X u v : Ω → E} (hX : Measurable X)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ B) :
    (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ 2 * (∫ ω, ‖OracleTemplate.clip B (X ω)‖ ^ 2 ∂P) +
      2 * (∫ ω, ‖u ω‖ ^ 2 ∂P) := by
  have hclip : Integrable (fun ω => ‖OracleTemplate.clip B (X ω)‖ ^ 2) P := by
    apply Integrable.mono' (integrable_const (B ^ 2))
      ((((OracleTemplate.measurable_clip B).comp hX).norm.pow_const 2).aestronglyMeasurable)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (OracleTemplate.norm_clip_le hB _) 2
  have hdom : ∀ᵐ ω ∂P, ‖X ω‖ ^ 2 ≤
      2 * ‖OracleTemplate.clip B (X ω)‖ ^ 2 + 2 * ‖u ω‖ ^ 2 := by
    filter_upwards [hsplit, hv] with ω he hvω
    rw [he]
    exact split_square_le_clipped_square _ _ hB hvω
  have hi := integral_mono_ae (split_secondMoment_integrable hX hu2 hsplit hv)
    ((hclip.const_mul 2).add (hu2.const_mul 2)) hdom
  simpa only [Pi.add_apply, integral_add (hclip.const_mul 2) (hu2.const_mul 2),
    integral_const_mul] using hi

omit [CompleteSpace E] in
lemma clipped_bias_bounded_part {X u v : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {B : ℝ} (hB : 0 < B)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ B / 2) :
    ‖(∫ ω, X ω ∂P) - ∫ ω, OracleTemplate.clip B (X ω) ∂P‖ ≤
      (∫ ω, ‖u ω‖ ^ 2 ∂P) / (B / 2) := by
  have hclip : Integrable (fun ω => OracleTemplate.clip B (X ω)) P := by
    apply Integrable.mono' (integrable_const B)
      (((OracleTemplate.measurable_clip B).comp hX).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => OracleTemplate.norm_clip_le hB.le (X ω))
  have hdom : ∀ᵐ ω ∂P, ‖X ω - OracleTemplate.clip B (X ω)‖ ≤ ‖u ω‖ ^ 2 / (B / 2) := by
    filter_upwards [hsplit, hv] with ω he hvω
    rw [he]
    exact residual_le_unbounded_square _ _ hB hvω
  have hi := integral_mono_ae (hXi.sub hclip).norm (hu2.div_const (B / 2)) hdom
  simp only [Pi.sub_apply] at hi
  rw [integral_div] at hi
  rw [← integral_sub hXi hclip]
  exact (norm_integral_le_integral_norm _).trans hi

omit [CompleteSpace E] in
lemma raw_mean_detection {X u v : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hu : Measurable u) (hui : Integrable u P)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {g σ κ : ℝ}
    (hg : 0 < g) (hgdef : ‖∫ ω, X ω ∂P‖ = g) (hσ : 0 ≤ σ)
    (hσg : σ ≤ g / 2) (hκ : 1 ≤ κ)
    (hmoment : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ σ ^ 2)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ 2 * κ * g) :
    1 / (16 * κ) ≤ P.real {ω | g / 2 < ‖X ω‖} := by
  have hb := clipped_bias_split hX hXi hu hui hu2 hsplit hσ
    (show 0 ≤ g / 2 by positivity) hmoment hv
  have hc : ‖∫ ω, OracleTemplate.clip (g / 2) (X ω) ∂P‖ ≤ g / 2 := by
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (μ := P) (Filter.Eventually.of_forall
        (fun ω => OracleTemplate.norm_clip_le (show 0 ≤ g / 2 by positivity) (X ω)))
  have hn := norm_sub_norm_le (∫ ω, X ω ∂P) (∫ ω, OracleTemplate.clip (g / 2) (X ω) ∂P)
  rw [hgdef] at hn
  apply rawTail_mass_lower g σ κ _ hg hσ hσg hκ measureReal_nonneg
  linarith

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma raw_rms_detection {X u v : Ω → E} (hX : Measurable X)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {κ t : ℝ}
    (hκ : 1 ≤ κ) (ht : 0 < t)
    (hS : 16 * κ * t ^ 2 ≤ ∫ ω, ‖X ω‖ ^ 2 ∂P)
    (hu : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ t ^ 2)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ 2 * κ * t) :
    1 / (16 * κ) ≤ P.real {ω | t < ‖X ω‖} := by
  have hb := split_secondMoment_tail hX hu2 hsplit ht.le hv
  have hc : (∫ ω, ‖OracleTemplate.clip t (X ω)‖ ^ 2 ∂P) ≤ t ^ 2 := by
    have h := integral_mono_of_nonneg (μ := P)
      (Filter.Eventually.of_forall (fun ω => sq_nonneg ‖OracleTemplate.clip t (X ω)‖))
      (integrable_const (t ^ 2)) (Filter.Eventually.of_forall (fun ω =>
        pow_le_pow_left₀ (norm_nonneg _) (OracleTemplate.norm_clip_le ht.le (X ω)) 2))
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hκpos : 0 < κ := by linarith
  by_contra hn
  have hp : P.real {ω | t < ‖X ω‖} < 1 / (16 * κ) := lt_of_not_ge hn
  have hmul := (lt_div_iff₀ (show 0 < 16 * κ by positivity)).mp hp
  have hs := mul_lt_mul_of_pos_right hmul (show 0 < κ * t ^ 2 by positivity)
  have hk := mul_le_mul_of_nonneg_right hκ (sq_nonneg t)
  nlinarith

omit [CompleteSpace E] [IsProbabilityMeasure P] in
lemma canonical_residual_secondMoment {X u v : Ω → E} (hX : Measurable X)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {B σ : ℝ} (hB : 0 ≤ B)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ B) (hmoment : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ σ ^ 2) :
    Integrable (fun ω => ‖X ω - OracleTemplate.clip B (X ω)‖ ^ 2) P ∧
      (∫ ω, ‖X ω - OracleTemplate.clip B (X ω)‖ ^ 2 ∂P) ≤ σ ^ 2 := by
  have hdom : ∀ᵐ ω ∂P, ‖X ω - OracleTemplate.clip B (X ω)‖ ^ 2 ≤ ‖u ω‖ ^ 2 := by
    filter_upwards [hsplit, hv] with ω he hvω
    rw [he]
    exact pow_le_pow_left₀ (norm_nonneg _) (residual_le_unbounded_part _ _ hB hvω) 2
  have hi : Integrable (fun ω => ‖X ω - OracleTemplate.clip B (X ω)‖ ^ 2) P := by
    apply Integrable.mono' hu2
      (((hX.sub ((OracleTemplate.measurable_clip B).comp hX)).norm.pow_const 2).aestronglyMeasurable)
    filter_upwards [hdom] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hω
  exact ⟨hi, (integral_mono_ae hi hu2 hdom).trans hmoment⟩

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma split_moment_bounds {X u v : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hu : Measurable u)
    (hu2 : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hsplit : ∀ᵐ ω ∂P, X ω = u ω + v ω) {σ V : ℝ} (hσ : 0 ≤ σ)
    (hσ2 : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ σ ^ 2)
    (hv : ∀ᵐ ω ∂P, ‖v ω‖ ≤ V) :
    ‖∫ ω, X ω ∂P‖ ≤ σ + V ∧
      (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ 2 * σ ^ 2 + 2 * V ^ 2 := by
  have hui : Integrable (fun ω => ‖u ω‖) P := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hu2) hu.norm.aestronglyMeasurable
    filter_upwards [] with ω
    simp only [Real.norm_eq_abs, abs_norm, Pi.add_apply]
    nlinarith [sq_nonneg (‖u ω‖ - 1)]
  have hu1 : (∫ ω, ‖u ω‖ ∂P) ≤ σ := by
    simpa using tail_norm_integral hu hu2 hσ hσ2 MeasurableSet.univ
  have hdom : ∀ᵐ ω ∂P, ‖X ω‖ ≤ ‖u ω‖ + V := by
    filter_upwards [hsplit, hv] with ω he hvω
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)
  constructor
  · have h := integral_mono_ae hXi.norm (hui.add (integrable_const V)) hdom
    simp only [Pi.add_apply] at h
    rw [integral_add hui (integrable_const V)] at h
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    exact (norm_integral_le_integral_norm _).trans (by linarith)
  · have hd : ∀ᵐ ω ∂P, ‖X ω‖ ^ 2 ≤ 2 * ‖u ω‖ ^ 2 + 2 * V ^ 2 := by
      filter_upwards [hdom] with ω hω
      have h := pow_le_pow_left₀ (norm_nonneg _) hω 2
      nlinarith [sq_nonneg (‖u ω‖ - V)]
    have h := integral_mono_ae (split_secondMoment_integrable hX hu2 hsplit hv)
      ((hu2.const_mul 2).add (integrable_const (2 * V ^ 2))) hd
    simp only [Pi.add_apply] at h
    rw [integral_add (hu2.const_mul 2) (integrable_const (2 * V ^ 2)), integral_const_mul] at h
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    linarith

end Probability

end LongTails.Proofs.GeneralizedLipschitzPilot
