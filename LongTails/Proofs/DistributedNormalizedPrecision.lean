import LongTails.Algorithms.DistributedNormalizedTuning
import LongTails.Proofs.DistributedNormalizedPath

namespace LongTails.Proofs.DistributedNormalizedPrecision

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedTuning

lemma grid_margin_size (M : ℝ) :
    M ≤ ((2 ^ (Nat.size ⌈M⌉₊ + 2) - 1 : ℕ) : ℝ) / 2 - 1 := by
  let N := ⌈M⌉₊
  have hp : (N : ℝ) + 1 ≤ ((2 ^ Nat.size N : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_size_self N)
  have hpow : ((2 ^ (Nat.size N + 2) : ℕ) : ℝ) = 4 * ((2 ^ Nat.size N : ℕ) : ℝ) := by
    rw [pow_add]
    push_cast
    ring
  have hpos : 1 ≤ 2 ^ (Nat.size N + 2) := by
    have h : 0 < 2 ^ (Nat.size N + 2) := by positivity
    omega
  have hc : M ≤ (N : ℝ) := Nat.le_ceil M
  change M ≤ ((2 ^ (Nat.size N + 2) - 1 : ℕ) : ℝ) / 2 - 1
  rw [Nat.cast_sub hpos, Nat.cast_one, hpow]
  nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]

lemma stepSize_pos (p : Params) (hL : 0 < p.L) (hε : 0 < p.ε) : 0 < stepSize p := by
  exact div_pos hε (mul_pos (by norm_num) hL)

lemma accuracyScale_ge_one (p : Params) (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ) :
    1 ≤ accuracyScale p := by
  have h : 0 ≤ p.L * p.Δ / p.ε ^ 2 := div_nonneg (mul_nonneg hL hΔ) (sq_nonneg _)
  dsimp [accuracyScale]
  linarith

lemma iterations_le_scale (p : Params) (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ) :
    ((iterations p : ℕ) : ℝ) ≤ 1025 * accuracyScale p := by
  have hr : 0 ≤ p.L * p.Δ / p.ε ^ 2 := div_nonneg (mul_nonneg hL hΔ) (sq_nonneg _)
  have ht : 0 ≤ 1024 * p.L * p.Δ / p.ε ^ 2 := by positivity
  have hc := (Nat.ceil_lt_add_one ht).le
  change ((max 1 ⌈1024 * p.L * p.Δ / p.ε ^ 2⌉₊ : ℕ) : ℝ) ≤ _
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · have hA := accuracyScale_ge_one p hL hΔ
    linarith
  · dsimp [accuracyScale]
    have he : 1024 * p.L * p.Δ / p.ε ^ 2 = 1024 * (p.L * p.Δ / p.ε ^ 2) := by ring
    rw [he] at hc ⊢
    linarith

lemma downlink_margin (p : Params) :
    1048576 * (1 + accuracyScale p * Real.sqrt p.d) ≤
      ((2 ^ downlinkWidth p - 1 : ℕ) : ℝ) / 2 - 1 :=
  grid_margin_size _

lemma downlink_precision (p : Params) (hd : 0 < p.d) (hL : 0 < p.L)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    0 < (config p).incrementSpacing ∧ 0 < (config p).refreshSpacing ∧
      (config p).incrementSpacing ≤ p.d * (config p).stepSize ∧
      p.d * (config p).refreshSpacing ^ 2 ≤ (config p).stepSize ^ 2 / 16 ∧
      p.d * (config p).stepSize ≤ (config p).incrementSpacing *
        (((2 ^ (config p).downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1) ∧
      (iterations p : ℕ) * (config p).stepSize ≤ (config p).refreshSpacing *
        (((2 ^ (config p).downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1) := by
  let η := stepSize p
  let s := Real.sqrt p.d
  let A := accuracyScale p
  let M := ((2 ^ downlinkWidth p - 1 : ℕ) : ℝ) / 2 - 1
  have hη : 0 < η := stepSize_pos p hL hε
  have hs : 0 < s := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hs2 : s ^ 2 = (p.d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hd' : (1 : ℝ) ≤ p.d := by exact_mod_cast Nat.succ_le_of_lt hd
  have hsd : s ≤ (p.d : ℝ) := by nlinarith [sq_nonneg (s - 1)]
  have hA : 1 ≤ A := accuracyScale_ge_one p hL.le hΔ
  have hM : 1048576 * (1 + A * s) ≤ M := downlink_margin p
  have hAs : 0 ≤ A * s := mul_nonneg (by linarith) hs.le
  have hsM : s ≤ M := by
    have h := mul_le_mul_of_nonneg_right hA hs.le
    nlinarith
  have hK := iterations_le_scale p hL.le hΔ
  have hKM : 4 * ((iterations p : ℕ) : ℝ) * s ≤ M := by
    change ((iterations p : ℕ) : ℝ) ≤ 1025 * A at hK
    have h := mul_le_mul_of_nonneg_right hK (show 0 ≤ 4 * s by positivity)
    nlinarith
  have href : (p.d : ℝ) * (η / (4 * s)) ^ 2 = η ^ 2 / 16 := by
    rw [← hs2]
    field_simp
    ring
  change 0 < η * s ∧ 0 < η / (4 * s) ∧ η * s ≤ p.d * η ∧
    p.d * (η / (4 * s)) ^ 2 ≤ η ^ 2 / 16 ∧ p.d * η ≤ η * s * M ∧
    (iterations p : ℕ) * η ≤ η / (4 * s) * M
  refine ⟨mul_pos hη hs, div_pos hη (by positivity), ?_, href.le, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hsd hη.le]
  · rw [← hs2]
    nlinarith [mul_le_mul_of_nonneg_left hsM (mul_nonneg hη.le hs.le)]
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (show 0 < 4 * s by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hKM hη.le]

lemma configured_worker_path (p : Params) (hd : 0 < p.d) (hL : 0 < p.L)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (draws : LongTails.Algorithms.DistributedNormalizedDownlink.Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (k : ℕ) (hk : k ≤ iterations p) (i : Fin p.n) :
    ‖(LongTails.Algorithms.DistributedNormalizedDownlink.trajectory p (config p) draws g samples k).workers i - p.x0‖ ≤
      4 * p.d * ((iterations p : ℕ) + 1 : ℕ) * stepSize p := by
  have hη := (stepSize_pos p hL hε).le
  obtain ⟨hsi, hsr, hinc, href, hcapi, hcapr⟩ := downlink_precision p hd hL hΔ hε
  have hp := DistributedNormalizedPath.worker_path p (config p) hη (iterations p)
    hsi hsr hinc href hcapi hcapr draws g samples k hk i
  exact hp.trans (DistributedNormalizedPath.path_radius_le hη hd hk)

lemma configured_worker_gradient (p : Params) (hd : 0 < p.d) (hL : 0 < p.L)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (f : Point p → ℝ)
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (draws : LongTails.Algorithms.DistributedNormalizedDownlink.Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (k : ℕ) (hk : k ≤ iterations p) (i : Fin p.n) :
    ‖gradient f ((LongTails.Algorithms.DistributedNormalizedDownlink.trajectory p (config p)
      draws g samples k).workers i)‖ ≤ gradientRadius p := by
  have hp := configured_worker_path p hd hL hΔ hε draws g samples k hk i
  have hg := DistributedNormalizedPath.gradient_at_bounded_point p f hL hf hlip lower hlower hgap _ _ hp
  unfold gradientRadius
  convert hg using 1
  ring

lemma compressionVariance_nonneg (p : Params) (hd : 0 < p.d) :
    0 ≤ compressionVariance p := by
  have hd' : (1 : ℝ) ≤ p.d := by exact_mod_cast Nat.succ_le_of_lt hd
  unfold compressionVariance
  split_ifs
  · rfl
  · exact div_nonneg (sub_nonneg.mpr hd') (by positivity)

lemma batch_ge_target (p : Params) :
    16384 * p.σ ^ 2 * (1 + compressionVariance p) / (p.n * p.ε ^ 2) ≤ (batch p : ℝ) := by
  let t := 16384 * p.σ ^ 2 * (1 + compressionVariance p) / (p.n * p.ε ^ 2)
  change t ≤ ((max 1 ⌈t⌉₊ : ℕ) : ℝ)
  exact (Nat.le_ceil t).trans (by exact_mod_cast Nat.le_max_right 1 ⌈t⌉₊)

lemma batch_noise_bound (p : Params) (hd : 0 < p.d) (hε : 0 < p.ε) :
    p.σ ^ 2 / batch p ≤ p.σ ^ 2 ∧ p.σ ^ 2 / batch p ≤ p.n * p.ε ^ 2 / 16384 := by
  have hb : (0 : ℝ) < batch p := by exact_mod_cast (batch p).pos
  have hb1 : (1 : ℝ) ≤ batch p := by exact_mod_cast Nat.succ_le_of_lt (batch p).pos
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hω := compressionVariance_nonneg p hd
  have ht := (div_le_iff₀ (show 0 < (p.n : ℝ) * p.ε ^ 2 by positivity)).mp (batch_ge_target p)
  constructor
  · apply (div_le_iff₀ hb).mpr
    nlinarith [mul_nonneg (sq_nonneg p.σ) (sub_nonneg.mpr hb1)]
  · apply (div_le_iff₀ hb).mpr
    nlinarith [mul_nonneg (sq_nonneg p.σ) hω]

lemma gradientRadius_bound (p : Params) (hd : 0 < p.d) (hL : 0 < p.L)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    gradientRadius p ≤ 40 * p.d * accuracyScale p * p.ε := by
  let A := accuracyScale p
  let K : ℝ := (iterations p : ℕ)
  have hA : 1 ≤ A := accuracyScale_ge_one p hL.le hΔ
  have hK : K ≤ 1025 * A := iterations_le_scale p hL.le hΔ
  have hd' : (1 : ℝ) ≤ p.d := by exact_mod_cast Nat.succ_le_of_lt hd
  have he : (p.ε * A) ^ 2 = p.ε ^ 2 + 2 * p.L * p.Δ + (p.L * p.Δ / p.ε) ^ 2 := by
    dsimp [A, accuracyScale]
    field_simp
    ring
  have hs : Real.sqrt (2 * p.L * p.Δ) ≤ p.ε * A := by
    have hnonneg : 0 ≤ 2 * p.L * p.Δ := by positivity
    have hAe : 0 ≤ p.ε * A := mul_nonneg hε.le (by linarith)
    nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (2 * p.L * p.Δ),
      sq_nonneg p.ε, sq_nonneg (p.L * p.Δ / p.ε)]
  have hG : gradientRadius p = Real.sqrt (2 * p.L * p.Δ) + p.d * (K + 1) * p.ε / 32 := by
    dsimp [gradientRadius, stepSize, K]
    push_cast
    field_simp
    ring
  have hK1 : K + 1 ≤ 1026 * A := by linarith
  have hm := mul_le_mul_of_nonneg_right hK1 (show 0 ≤ (p.d : ℝ) * p.ε / 32 by positivity)
  have hda := mul_nonneg (sub_nonneg.mpr hd') (show 0 ≤ A * p.ε by positivity)
  have hpos : 0 ≤ (p.d : ℝ) * A * p.ε := by positivity
  rw [hG]
  change Real.sqrt (2 * p.L * p.Δ) + p.d * (K + 1) * p.ε / 32 ≤ 40 * p.d * A * p.ε
  nlinarith

lemma clipMargin_bound (p : Params) (hd : 0 < p.d) (hε : 0 < p.ε) :
    clipMargin p ≤ p.ε * (1 + 32 * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) := by
  obtain ⟨hvσ, hvn⟩ := batch_noise_bound p hd hε
  have hvn' : p.σ ^ 2 / batch p ≤ p.n * p.ε ^ 2 := by
    have hpos : 0 ≤ (p.n : ℝ) * p.ε ^ 2 := by positivity
    linarith
  have hv : (p.σ ^ 2 / batch p) / p.ε ^ 2 ≤ min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ) :=
    le_min (div_le_div_of_nonneg_right hvσ (sq_nonneg p.ε))
      ((div_le_iff₀ (sq_pos_of_pos hε)).mpr hvn')
  have hvm := (div_le_iff₀ (sq_pos_of_pos hε)).mp hv
  have hdiv : (p.σ ^ 2 / batch p) / p.ε ≤
      p.ε * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ) := by
    apply (div_le_iff₀ hε).mpr
    nlinarith
  unfold clipMargin
  rw [mul_div_assoc]
  linarith

lemma uplink_margin (p : Params) :
    1048576 * (1 + ((p.d : ℝ) ^ 2 * accuracyScale p +
      p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n) ≤
      ((2 ^ uplinkWidth p - 1 : ℕ) : ℝ) / 2 - 1 :=
  grid_margin_size _

lemma uplink_scaled_capacity (p : Params) (hd : 0 < p.d) (hL : 0 < p.L)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    0 ≤ ((2 ^ uplinkWidth p - 1 : ℕ) : ℝ) / 2 - 1 ∧
      64 * p.d * (gradientRadius p + clipMargin p) ≤
        p.ε * Real.sqrt p.n * (((2 ^ uplinkWidth p - 1 : ℕ) : ℝ) / 2 - 1) := by
  let A := accuracyScale p
  let q := min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)
  let s := Real.sqrt p.n
  let M := ((2 ^ uplinkWidth p - 1 : ℕ) : ℝ) / 2 - 1
  have hA : 1 ≤ A := accuracyScale_ge_one p hL.le hΔ
  have hq : 0 ≤ q := le_min (div_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hs : 0 < s := Real.sqrt_pos.mpr hn
  have hd' : (1 : ℝ) ≤ p.d := by exact_mod_cast Nat.succ_le_of_lt hd
  have hmargin : 1048576 * (1 + ((p.d : ℝ) ^ 2 * A + p.d * q) / s) ≤ M := uplink_margin p
  have hM : 0 ≤ M := (by positivity : 0 ≤ 1048576 *
    (1 + ((p.d : ℝ) ^ 2 * A + p.d * q) / s)).trans hmargin
  refine ⟨hM, ?_⟩
  have hR : gradientRadius p + clipMargin p ≤ p.ε * (40 * p.d * A + 1 + 32 * q) := by
    have hG := gradientRadius_bound p hd hL hΔ hε
    have ha := clipMargin_bound p hd hε
    change gradientRadius p ≤ 40 * p.d * A * p.ε at hG
    change clipMargin p ≤ p.ε * (1 + 32 * q) at ha
    nlinarith
  have he : s * (1048576 * (1 + ((p.d : ℝ) ^ 2 * A + p.d * q) / s)) =
      1048576 * (s + (p.d : ℝ) ^ 2 * A + p.d * q) := by
    field_simp
    ring
  have hm := mul_le_mul_of_nonneg_left hmargin hs.le
  rw [he] at hm
  have hme := mul_le_mul_of_nonneg_left hm hε.le
  have hRmul := mul_le_mul_of_nonneg_left hR (show 0 ≤ 64 * (p.d : ℝ) by positivity)
  have hD : (p.d : ℝ) ≤ (p.d : ℝ) ^ 2 * A := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ p.d by positivity) (sub_nonneg.mpr hd'),
      mul_nonneg (sq_nonneg (p.d : ℝ)) (sub_nonneg.mpr hA)]
  have hDe := mul_le_mul_of_nonneg_right hD hε.le
  have hX : 0 ≤ (p.d : ℝ) ^ 2 * A * p.ε := by positivity
  have hY : 0 ≤ (p.d : ℝ) * q * p.ε := by positivity
  have hS : 0 ≤ s * p.ε := by positivity
  change 64 * p.d * (gradientRadius p + clipMargin p) ≤ p.ε * s * M
  nlinarith

lemma gradientRadius_nonneg (p : Params) (hL : 0 < p.L) (hε : 0 < p.ε) :
    0 ≤ gradientRadius p := by
  have hη := stepSize_pos p hL hε
  unfold gradientRadius
  positivity

lemma clipMargin_pos (p : Params) (hε : 0 < p.ε) : 0 < clipMargin p := by
  unfold clipMargin
  positivity

lemma uplink_spacing_pos (p : Params) (hd : 0 < p.d) (hε : 0 < p.ε) :
    0 < (config p).uplinkSpacing := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hd' : (0 : ℝ) < p.d := Nat.cast_pos.mpr hd
  have hm : (0 : ℝ) < uplinkCount p := by exact_mod_cast (uplinkCount p).pos
  change 0 < if fullUplink p then p.ε * Real.sqrt ((p.n : ℝ) / p.d) / 64
    else p.ε * Real.sqrt ((uplinkCount p : ℝ) * p.n) / 64
  split_ifs <;> positivity

lemma uplink_capacity (p : Params) (hd : 0 < p.d) (hL : 0 < p.L)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    (if fullUplink p then 1 else (p.d : ℝ)) * (gradientRadius p + clipMargin p) ≤
      (config p).uplinkSpacing * (((2 ^ uplinkWidth p - 1 : ℕ) : ℝ) / 2 - 1) := by
  let R := gradientRadius p + clipMargin p
  let M := ((2 ^ uplinkWidth p - 1 : ℕ) : ℝ) / 2 - 1
  let s := Real.sqrt p.n
  have hR : 0 ≤ R := add_nonneg (gradientRadius_nonneg p hL hε) (clipMargin_pos p hε).le
  obtain ⟨hM, hcap⟩ := uplink_scaled_capacity p hd hL hΔ hε
  change 0 ≤ M at hM
  change 64 * p.d * R ≤ p.ε * s * M at hcap
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hs : 0 < s := Real.sqrt_pos.mpr hn
  cases hf : fullUplink p with
  | false =>
    have hm : (1 : ℝ) ≤ uplinkCount p := by exact_mod_cast Nat.succ_le_of_lt (uplinkCount p).pos
    have hmn : (p.n : ℝ) ≤ (uplinkCount p : ℝ) * p.n := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hm) hn.le]
    have hsq : s ≤ Real.sqrt ((uplinkCount p : ℝ) * p.n) := Real.sqrt_le_sqrt hmn
    have hspace := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hε.le)
      (show (0 : ℝ) ≤ 64 by norm_num)
    have hb : (p.d : ℝ) * R ≤ (p.ε * s / 64) * M := by nlinarith
    have ht := mul_le_mul_of_nonneg_right hspace hM
    simp only [config, hf, Bool.false_eq_true, ite_false]
    exact hb.trans ht
  | true =>
    let q := Real.sqrt p.d
    have hq : 0 < q := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
    have hq2 : q ^ 2 = (p.d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
    have hd' : (1 : ℝ) ≤ p.d := by exact_mod_cast Nat.succ_le_of_lt hd
    have hqd : q ≤ (p.d : ℝ) := by nlinarith [sq_nonneg (q - 1)]
    have hh := mul_le_mul_of_nonneg_right hqd (show 0 ≤ 64 * R by positivity)
    have hc : 64 * q * R ≤ p.ε * s * M := by nlinarith
    simp only [config, hf, ite_true, one_mul]
    change R ≤ p.ε * Real.sqrt ((p.n : ℝ) / p.d) / 64 * M
    rw [Real.sqrt_div hn.le]
    have he : p.ε * (s / q) / 64 * M = p.ε * s * M / (64 * q) := by
      field_simp
    change R ≤ p.ε * (s / q) / 64 * M
    rw [he]
    apply (le_div_iff₀ (show 0 < 64 * q by positivity)).mpr
    nlinarith

end LongTails.Proofs.DistributedNormalizedPrecision
