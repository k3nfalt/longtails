import LongTails.Proofs.StochasticEqualityDescent

namespace LongTails.Proofs.StochasticEqualityStopped

open scoped BigOperators

lemma trajectory_energy (φ r v : ℕ → ℝ) (η C : ℝ) (n : ℕ)
    (hstep : ∀ i < n, φ (i + 1) ≤ φ i - η * r i / 2 + η * C * v i) :
    φ n + η / 2 * (∑ i ∈ Finset.range n, r i) ≤
      φ 0 + η * C * (∑ i ∈ Finset.range n, v i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hn := hstep n (Nat.lt_succ_self n)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    nlinarith only [hp, hn]

def freeze {X : Type*} (active : ℕ → Prop) [DecidablePred active] (x : ℕ → X) : ℕ → X
  | 0 => x 0
  | n + 1 => if active n then x (n + 1) else freeze active x n

lemma freeze_eq_of_active {X : Type*} (active : ℕ → Prop) [DecidablePred active]
    (x : ℕ → X) (hmono : ∀ k n, k ≤ n → active n → active k)
    (n : ℕ) (hn : active n) : freeze active x n = x n := by
  cases n with
  | zero => rfl
  | succ n => simp only [freeze, hmono n (n + 1) (by omega) hn, ↓reduceIte]

lemma frozen_step {X : Type*} (active : ℕ → Prop) [DecidablePred active]
    (x : ℕ → X) (φ : X → ℝ) (r v : ℕ → ℝ) (η C : ℝ)
    (hmono : ∀ k n, k ≤ n → active n → active k) (n : ℕ)
    (hstep : active n → φ (x (n + 1)) ≤ φ (x n) - η * r n / 2 + η * C * v n) :
    φ (freeze active x (n + 1)) ≤ φ (freeze active x n) -
      η * (if active n then r n else 0) / 2 + η * C * (if active n then v n else 0) := by
  by_cases hn : active n
  · simpa only [freeze, hn, ↓reduceIte, freeze_eq_of_active active x hmono n hn] using hstep hn
  · simp only [freeze, hn, ↓reduceIte, mul_zero, zero_div, sub_zero, add_zero, le_refl]

lemma frozen_energy {X : Type*} (active : ℕ → Prop) [DecidablePred active]
    (x : ℕ → X) (φ : X → ℝ) (r v : ℕ → ℝ) (η C : ℝ) (n : ℕ)
    (hmono : ∀ k j, k ≤ j → active j → active k)
    (hstep : ∀ k < n, active k → φ (x (k + 1)) ≤ φ (x k) - η * r k / 2 + η * C * v k) :
    φ (freeze active x n) + η / 2 * (∑ k ∈ Finset.range n, if active k then r k else 0) ≤
      φ (x 0) + η * C * (∑ k ∈ Finset.range n, if active k then v k else 0) := by
  exact trajectory_energy (fun k => φ (freeze active x k))
    (fun k => if active k then r k else 0) (fun k => if active k then v k else 0) η C n
    (fun k hk => frozen_step active x φ r v η C hmono k (hstep k hk))

lemma frozen_masked_energy {X : Type*} (active : ℕ → Prop) [DecidablePred active]
    (good : Prop) [Decidable good] (x : ℕ → X) (φ : X → ℝ)
    (r v : ℕ → ℝ) (η C : ℝ) (n : ℕ)
    (hgood : ∀ k, active k → good)
    (hmono : ∀ k j, k ≤ j → active j → active k)
    (hstep : ∀ k < n, active k → φ (x (k + 1)) ≤ φ (x k) - η * r k / 2 + η * C * v k) :
    (if good then φ (freeze active x n) else 0) +
      η / 2 * (∑ k ∈ Finset.range n, if active k then r k else 0) ≤
      (if good then φ (x 0) else 0) +
        η * C * (∑ k ∈ Finset.range n, if active k then v k else 0) := by
  by_cases hg : good
  · simpa only [hg, ↓reduceIte] using frozen_energy active x φ r v η C n hmono hstep
  · have ha (k : ℕ) : ¬ active k := fun hk => hg (hgood k hk)
    simp [hg, ha]

lemma trajectory_residual_bound (φ r v : ℕ → ℝ) {η C W : ℝ} (hη : 0 < η) (n : ℕ)
    (hstep : ∀ i < n, φ (i + 1) ≤ φ i - η * r i / 2 + η * C * v i)
    (hgap : φ 0 - φ n ≤ W) :
    (∑ i ∈ Finset.range n, r i) ≤ 2 * W / η + 2 * C * (∑ i ∈ Finset.range n, v i) := by
  have h := trajectory_energy φ r v η C n hstep
  have he : 2 * W / η + 2 * C * (∑ i ∈ Finset.range n, v i) =
      (2 * W + 2 * C * (∑ i ∈ Finset.range n, v i) * η) / η := by
    field_simp
  rw [he]
  apply (le_div_iff₀ hη).mpr
  nlinarith only [h, hgap]

lemma trajectory_movement_bound (φ r v a : ℕ → ℝ) {η C W : ℝ} (hη : 0 ≤ η) (n : ℕ)
    (hstep : ∀ i < n, φ (i + 1) ≤ φ i - η * r i / 2 + η * C * v i)
    (hgap : φ 0 - φ n ≤ W)
    (ha : ∀ i < n, a i ≤ 2 * η ^ 2 * (r i + v i)) :
    (∑ i ∈ Finset.range n, a i) ≤
      4 * η * W + (4 * C + 2) * η ^ 2 * (∑ i ∈ Finset.range n, v i) := by
  have h := trajectory_energy φ r v η C n hstep
  have hr : η / 2 * (∑ i ∈ Finset.range n, r i) ≤
      W + η * C * (∑ i ∈ Finset.range n, v i) := by linarith only [h, hgap]
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 4 * η by positivity)
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun i hi => ha i (Finset.mem_range.mp hi))
  simp_rw [mul_add] at hs
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  nlinarith only [hs, hm]

lemma restoration_invariant (v : ℕ → ℝ) {a F U : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hF : F ≤ U) (hinit : v 0 ≤ U) (n : ℕ)
    (hstep : ∀ i < n, v (i + 1) ≤ (1 - a) * v i + a * F) : v n ≤ U := by
  induction n with
  | zero => exact hinit
  | succ n ih =>
    have hp := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hn := hstep n (Nat.lt_succ_self n)
    have h₁ := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr ha1)
    have h₂ := mul_le_mul_of_nonneg_left hF ha
    nlinarith only [hn, h₁, h₂]

lemma restoration_contraction (v : ℕ → ℝ) {a F : ℝ} (ha1 : a ≤ 1) (hF : 0 ≤ F)
    (n : ℕ) (hstep : ∀ i < n, v (i + 1) ≤ (1 - a) * v i + a * F) :
    v n ≤ (1 - a) ^ n * v 0 + F := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    have hp := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hn := hstep n (Nat.lt_succ_self n)
    have hm := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr ha1)
    rw [pow_succ]
    nlinarith only [hn, hm]

lemma restoration_accuracy (v : ℕ → ℝ) {a r C : ℝ} (ha1 : a ≤ 1)
    (hr : 0 < r) (hinit : v 0 ≤ C ^ 2) (n : ℕ)
    (hsteps : Real.log (16 * (1 + C ^ 2) / r ^ 2) ≤ a * n)
    (hstep : ∀ i < n, v (i + 1) ≤ (1 - a) * v i + a * (r ^ 2 / 16)) :
    v n < r ^ 2 / 8 := by
  have h := restoration_contraction v ha1 (show 0 ≤ r ^ 2 / 16 by positivity) n hstep
  have hp : (1 - a) ^ n ≤ Real.exp (-(a * n)) := by
    have he : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
    calc
      _ ≤ Real.exp (-a) ^ n := pow_le_pow_left₀ (sub_nonneg.mpr ha1) he n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have he : Real.exp (-(a * n)) ≤ r ^ 2 / (16 * (1 + C ^ 2)) := by
    calc
      _ ≤ Real.exp (-Real.log (16 * (1 + C ^ 2) / r ^ 2)) :=
        Real.exp_le_exp.mpr (neg_le_neg hsteps)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hC : (1 - a) ^ n * v 0 ≤ (r ^ 2 / (16 * (1 + C ^ 2))) * C ^ 2 :=
    (mul_le_mul_of_nonneg_left hinit (pow_nonneg (sub_nonneg.mpr ha1) n)).trans
      (mul_le_mul_of_nonneg_right (hp.trans he) (sq_nonneg C))
  have hstrict : (r ^ 2 / (16 * (1 + C ^ 2))) * C ^ 2 < r ^ 2 / 16 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 16 * (1 + C ^ 2))).mpr
    nlinarith [sq_pos_of_pos hr]
  linarith only [h, hC, hstrict]

lemma penalty_majorant (a b G : ℝ) :
    8 * ((a + b * G) ^ 2 + (a + b * G) + 1) ≤
      16 * a ^ 2 + 8 * a + 12 + 20 * b ^ 2 * G ^ 2 := by
  nlinarith only [sq_nonneg (a - b * G), sq_nonneg (b * G - 1)]

lemma localization_feedback {B L W r G : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hG : G ^ 2 = 8 * (1 + L) * W)
    (hr : r ^ 2 = 1 / (1 + 8 * B * (1 + L))) :
    B * G ^ 2 * r ^ 2 / 2 ≤ W / 2 := by
  have hd : 0 < 1 + 8 * B * (1 + L) := by positivity
  have hratio : (4 * B * (1 + L)) / (1 + 8 * B * (1 + L)) ≤ 1 / 2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hratio hW
  rw [hG, hr]
  convert hm using 1 <;> ring

lemma joint_exit_bounds {F φ g c L β W : ℝ} (hF : 0 ≤ F) (hL : 0 ≤ L)
    (hβ : 0 < β) (hW : 0 < W)
    (hcoercive : F / 2 + β * c ^ 2 / 4 ≤ φ)
    (hgradient : g ^ 2 ≤ 2 * L * F) (hupper : φ ≤ 2 * W - 1) :
    g ^ 2 < 8 * (1 + L) * W ∧ c ^ 2 < 16 * W / β := by
  have hFbound : F ≤ 2 * φ := by nlinarith [mul_nonneg hβ.le (sq_nonneg c)]
  have hg := mul_le_mul_of_nonneg_left hFbound (show 0 ≤ 2 * L by positivity)
  have hφ := mul_le_mul_of_nonneg_left hupper (show 0 ≤ 4 * L by positivity)
  constructor
  · nlinarith only [hgradient, hg, hφ, hW, hL]
  · apply (lt_div_iff₀ hβ).mpr
    nlinarith only [hcoercive, hupper, hF, hW]

end LongTails.Proofs.StochasticEqualityStopped
