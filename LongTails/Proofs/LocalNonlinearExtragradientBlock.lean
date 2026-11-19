import LongTails.Proofs.LocalNonlinearExtragradientGeometry

namespace LongTails.Proofs.LocalNonlinearExtragradientBlock

open scoped RealInnerProductSpace

lemma linear_decay_power {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ)
    (hn : (n : ℝ) * a ≤ 1) : (1 - a) ^ n ≤ 1 - (n : ℝ) * a / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn' : (n : ℝ) * a ≤ 1 := by
        push_cast at hn
        nlinarith
      have hh := mul_le_mul_of_nonneg_right (ih hn') (sub_nonneg.mpr ha1)
      have hs := mul_le_mul_of_nonneg_right hn' ha
      rw [pow_succ]
      push_cast
      nlinarith

lemma perturbed_geometric_growth (b : ℕ → ℝ) {q G c d : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hG : 1 ≤ G) (hc : 0 ≤ c)
    (hinit : b 0 ≤ d) (hstep : ∀ k, b (k + 1) ≤ q * b k + c * G ^ k) :
    ∀ k, b k ≤ q ^ k * d + c * (k : ℝ) * G ^ k := by
  intro k
  induction k with
  | zero => simpa using hinit
  | succ k ih =>
      have hp : 0 ≤ G ^ k := pow_nonneg (by linarith) k
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      have hm := mul_le_mul_of_nonneg_left ih hq
      have hqterm := mul_le_mul_of_nonneg_right hq1
        (show 0 ≤ c * (k : ℝ) * G ^ k by positivity)
      have hGterm := mul_le_mul_of_nonneg_left hG
        (show 0 ≤ c * ((k : ℝ) + 1) * G ^ k by positivity)
      have hs := hstep k
      rw [pow_succ, pow_succ]
      push_cast
      nlinarith

lemma local_mean_margin {a t κ ρ M L d B : ℝ}
    (ht : 0 ≤ t) (hκ : 0 < κ) (hρ : 0 < ρ) (hL : 0 < L)
    (hd : 0 ≤ d) (hB : 0 < B)
    (hguard : M * d ≤ L / (16 * κ * ρ * B))
    (ha : a ≤ (1 - t / (16 * κ)) * d + ρ * M / (4 * L) * d ^ 2 * t * B) :
    a ≤ (1 - 3 * t / (64 * κ)) * d := by
  have hh := mul_le_mul_of_nonneg_right hguard
    (show 0 ≤ ρ * t * B / (4 * L) * d by positivity)
  have hl : M * d * (ρ * t * B / (4 * L) * d) =
      ρ * M / (4 * L) * d ^ 2 * t * B := by ring
  have hr : L / (16 * κ * ρ * B) * (ρ * t * B / (4 * L) * d) =
      t / (64 * κ) * d := by field_simp; ring
  rw [hl, hr] at hh
  have he : (1 - t / (16 * κ)) * d + t / (64 * κ) * d =
      (1 - 3 * t / (64 * κ)) * d := by ring
  linarith

lemma local_power_mean_margin {a κ ρ M L d G : ℝ} (T : ℕ)
    (hκ : 1 ≤ κ) (hρ : 0 < ρ) (hL : 0 < L) (hd : 0 ≤ d) (hG : 1 ≤ G)
    (hT : (T : ℝ) ≤ κ)
    (hguard : M * d ≤ L / (16 * κ * ρ * G ^ T))
    (ha : a ≤ (1 - 1 / (8 * κ)) ^ T * d +
      ρ * M / (4 * L) * d ^ 2 * (T : ℝ) * G ^ T) :
    a ≤ (1 - 3 * (T : ℝ) / (64 * κ)) * d := by
  have hκ0 : 0 < κ := by linarith
  have hα : 0 ≤ (1 / (8 * κ) : ℝ) := by positivity
  have hα1 : (1 / (8 * κ) : ℝ) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hprod : (T : ℝ) * (1 / (8 * κ)) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hp := linear_decay_power hα hα1 T hprod
  have he : (T : ℝ) * (1 / (8 * κ)) / 2 = (T : ℝ) / (16 * κ) := by ring
  rw [he] at hp
  apply local_mean_margin (Nat.cast_nonneg T) hκ0 hρ hL hd
    (pow_pos (by linarith : 0 < G) T) hguard
  exact ha.trans (add_le_add (mul_le_mul_of_nonneg_right hp hd) le_rfl)

lemma clipped_average_contraction {a v d s : ℝ}
    (ha0 : 0 ≤ a) (hd : 0 ≤ d) (hs : 0 ≤ s) (hs1 : s ≤ 1 / 128)
    (ha : a ≤ (1 - 5 * s) * d) (hv : v ≤ 2 * s * d ^ 2) :
    a ^ 2 + v ≤ (1 - 2 * s) * d ^ 2 := by
  have hq : 0 ≤ 1 - 5 * s := by linarith
  have hsq := (sq_le_sq₀ ha0 (mul_nonneg hq hd)).mpr ha
  have hqq : (1 - 5 * s) ^ 2 ≤ 1 - 5 * s := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hqq (sq_nonneg d)
  nlinarith [mul_nonneg hs (sq_nonneg d)]

lemma clipped_parameter_contraction {κ t B d r n : ℝ}
    (hκ : 1 ≤ κ) (ht : 1 ≤ t) (htκ : t ≤ κ) (hB : 1 ≤ B)
    (hd : 0 ≤ d) (hr : 0 < r) (hdr : d ≤ r) (hn : 64 * κ * B ≤ n) :
    ((1 - 3 * t / (64 * κ)) * d +
      (2 * (B * d ^ 2) + 2 * d ^ 2) / (256 * κ * (B + 1) * r / t)) ^ 2 +
      B * d ^ 2 / n ≤ (1 - t / (64 * κ)) * d ^ 2 := by
  have hκ0 : 0 < κ := by linarith
  have ht0 : 0 < t := by linarith
  have hB0 : 0 < B := by linarith
  have hBp : 0 < B + 1 := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hs : 0 ≤ t / (128 * κ) := by positivity
  have hs1 : t / (128 * κ) ≤ 1 / 128 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hbase : 0 ≤ 1 - 3 * t / (64 * κ) := by
    have hh : 3 * t / (64 * κ) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hbias : (2 * (B * d ^ 2) + 2 * d ^ 2) / (256 * κ * (B + 1) * r / t) ≤
      t / (128 * κ) * d := by
    have he : (2 * (B * d ^ 2) + 2 * d ^ 2) / (256 * κ * (B + 1) * r / t) =
        t / (128 * κ) * (d ^ 2 / r) := by
      field_simp
      ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ hs
    exact (div_le_iff₀ hr).mpr (by nlinarith)
  have hmean : (1 - 3 * t / (64 * κ)) * d +
      (2 * (B * d ^ 2) + 2 * d ^ 2) / (256 * κ * (B + 1) * r / t) ≤
      (1 - 5 * (t / (128 * κ))) * d := by
    have he : (1 - 3 * t / (64 * κ)) * d + t / (128 * κ) * d =
        (1 - 5 * (t / (128 * κ))) * d := by ring
    linarith
  have hratio : B / n ≤ 1 / (64 * κ) := by
    apply (div_le_div_iff₀ hn0 (by positivity : 0 < 64 * κ)).mpr
    nlinarith
  have hvar : B * d ^ 2 / n ≤ 2 * (t / (128 * κ)) * d ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hratio (sq_nonneg d)
    have ht' := mul_le_mul_of_nonneg_right ht
      (show 0 ≤ 1 / (64 * κ) * d ^ 2 by positivity)
    calc
      _ ≤ 1 / (64 * κ) * d ^ 2 := by simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
      _ ≤ t * (1 / (64 * κ) * d ^ 2) := by simpa using ht'
      _ = _ := by ring
  have hh := clipped_average_contraction
    (show 0 ≤ (1 - 3 * t / (64 * κ)) * d +
      (2 * (B * d ^ 2) + 2 * d ^ 2) / (256 * κ * (B + 1) * r / t) by positivity)
    hd hs hs1 hmean hvar
  convert hh using 1
  ring

lemma mean_run_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (z e : ℕ → E) {L μ ρ M d G : ℝ}
    (hL : 0 < L) (hμ : 0 ≤ μ) (hμL : μ ≤ L) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hG : 1 ≤ G) (hA : ‖A‖ ≤ L) (hm : ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪A v, v⟫)
    (hinit : ‖z 0‖ ≤ d)
    (hrec : ∀ k, z (k + 1) = z k - (1 / (4 * L)) • A (z k) +
      (1 / (4 * L)) ^ 2 • A (A (z k)) + e k)
    (he : ∀ k, ‖e k‖ ≤ ρ * M / (4 * L) * d ^ 2 * G ^ k) (k : ℕ) :
    ‖z k‖ ≤ (1 - μ / (8 * L)) ^ k * d +
      (ρ * M / (4 * L) * d ^ 2) * (k : ℝ) * G ^ k := by
  have hq : 0 ≤ 1 - μ / (8 * L) := by
    have h := (div_le_one (show 0 < 8 * L by positivity)).mpr (show μ ≤ 8 * L by linarith)
    linarith
  have hq1 : 1 - μ / (8 * L) ≤ 1 := by
    have : 0 ≤ μ / (8 * L) := by positivity
    linarith
  apply perturbed_geometric_growth (fun k => ‖z k‖) hq hq1 hG
    (show 0 ≤ ρ * M / (4 * L) * d ^ 2 by positivity) hinit _ k
  intro j
  rw [hrec]
  exact (norm_add_le _ _).trans (add_le_add
    (LocalNonlinearExtragradientGeometry.linear_extragradient_norm A (z j) hL hμ hμL hA hm)
    (he j))

end LongTails.Proofs.LocalNonlinearExtragradientBlock
