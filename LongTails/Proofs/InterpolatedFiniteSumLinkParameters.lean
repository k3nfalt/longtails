import LongTails.Proofs.InterpolatedFiniteSumExponentialParameters

namespace LongTails.Proofs.InterpolatedFiniteSumLinkParameters

lemma radius_tuned (T : ℕ) (hT : 0 < T) (R : ℝ) :
    (T : ℝ) * (R / Real.sqrt T) ^ 2 = R ^ 2 := by
  have hs : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt (Nat.cast_nonneg T)
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hT
  rw [div_pow, hs]
  field_simp

lemma first_gradient (T : ℕ) (hT : 0 < T) (η L R : ℝ) (hη : 0 ≤ η) (hR : 0 < R)
    (hderiv : 128 * η * Real.sqrt T ≤ L * R) : 2 * η / (R / Real.sqrt T) ≤ L / 14 := by
  have hTs : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have he : 2 * η / (R / Real.sqrt T) = 2 * η * Real.sqrt T / R := by field_simp
  rw [he]
  apply (div_le_iff₀ hR).mpr
  have hh : 0 ≤ η * Real.sqrt T := by positivity
  nlinarith only [hderiv, hh]

lemma first_curvature (T : ℕ) (hT : 0 < T) (η L R : ℝ) (hη : 0 ≤ η) (hL : 0 < L) (hR : 0 < R)
    (hderiv : 128 * η * Real.sqrt T ≤ L * R)
    (hwidth : 2 * (1 + η) * Real.sqrt T ≤ L * R) :
    6 * η / (R / Real.sqrt T) ^ 2 ≤ (4 * L ^ 2 / 49) / 3 := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg T)
  have hs0 := Real.sqrt_nonneg (T : ℝ)
  have hm := mul_le_mul_of_nonneg_right hderiv hs0
  have hn : 2 * Real.sqrt T ≤ L * R := by nlinarith only [hwidth, mul_nonneg hη hs0]
  have hq := mul_le_mul_of_nonneg_left hn (show 0 ≤ L * R by positivity)
  have hm' : 128 * η * T ≤ L * R * Real.sqrt T := by
    calc
      _ = 128 * η * (Real.sqrt T) ^ 2 := by rw [hs]
      _ = 128 * η * Real.sqrt T * Real.sqrt T := by ring
      _ ≤ _ := hm
  have hbound : 256 * η * T ≤ (L * R) ^ 2 := by nlinarith only [hm', hq]
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hT
  have he : 6 * η / (R / Real.sqrt T) ^ 2 = 6 * η * T / R ^ 2 := by
    rw [div_pow, hs]
    field_simp
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
  have hh : 0 ≤ L ^ 2 * R ^ 2 := by positivity
  nlinarith only [hbound, hh]

lemma threshold (T : ℕ) (hT : 0 < T) (η L R : ℝ) (hη : 0 ≤ η) (hL : 0 < L)
    (hderiv : 128 * η * Real.sqrt T ≤ L * R) (hq : 64 ≤ L * R) :
    4 * R + (η + 4) / (L / 14) ≤ 5 * R := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hs1 : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt hT1
  have hm := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ 128 * η)
  have hh : (η + 4) / (L / 14) ≤ R := by
    apply (div_le_iff₀ (by positivity : 0 < L / 14)).mpr
    nlinarith only [hm, hderiv, hq]
  linarith only [hh]

lemma hiding_ratio (L R : ℝ) (hL : 0 < L) :
    (5 * R) ^ 2 / (1 / (16 * L)) ^ 2 = 6400 * (L * R) ^ 2 := by
  field_simp
  ring

lemma initial_penalty (g T : ℕ) (hg : 0 < g) (hT : 0 < T) (δ η ε L R : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hL : 0 < L) (hR : 0 < R)
    (hexp : δ * Real.exp η = δ + 2 * g * ε)
    (hwidth : 2 * (1 + η) * Real.sqrt T ≤ L * R) :
    (δ / g) * (2 * η * Real.exp η / (R / Real.sqrt T)) * (1 / (16 * L)) ≤ ε / 8 := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hTs : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have he : (δ / g) * (2 * η * Real.exp η / (R / Real.sqrt T)) * (1 / (16 * L)) =
      δ * η * Real.exp η * Real.sqrt T / (8 * g * (L * R)) := by field_simp; ring
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < 8 * (g : ℝ) * (L * R))).mpr
  have hegap : δ * (Real.exp η - 1) = 2 * g * ε := by nlinarith only [hexp]
  have hexpbound := mul_le_mul_of_nonneg_left (Real.add_one_le_exp η) hδ.le
  have hc : δ * η * Real.exp η ≤ (δ * (Real.exp η - 1)) * (1 + η) := by nlinarith only [hexpbound]
  rw [hegap] at hc
  have hm := mul_le_mul_of_nonneg_right hc hTs.le
  have hw := mul_le_mul_of_nonneg_left hwidth (show 0 ≤ (g : ℝ) * ε by positivity)
  nlinarith only [hm, hw]

lemma terminal (T : ℕ) (hT : 0 < T) (η L R : ℝ) (hη : 0 ≤ η) (hL : 0 < L) (hR : 0 < R)
    (hshape : L * R ≤ 64 * T * Real.sqrt T) :
    let s := 2 * η * Real.exp η / (R / Real.sqrt T)
    let K := 256 * (s / L) * (1 + max 0 (Real.log (256 * (s / L))))
    Real.exp η - 1 ≤ (T : ℝ) * K := by
  dsimp only
  let s := 2 * η * Real.exp η / (R / Real.sqrt T)
  let K := 256 * (s / L) * (1 + max 0 (Real.log (256 * (s / L))))
  change Real.exp η - 1 ≤ (T : ℝ) * K
  have hTs : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hK : 256 * (s / L) ≤ K := by
    have hh := mul_nonneg (show 0 ≤ 256 * (s / L) by positivity) (le_max_left 0 (Real.log (256 * (s / L))))
    dsimp [K]
    nlinarith only [hh]
  have hm := mul_le_mul_of_nonneg_right hK (show 0 ≤ (T : ℝ) * (L * R) by positivity)
  have he : (256 * (s / L)) * ((T : ℝ) * (L * R)) =
      512 * η * Real.exp η * T * Real.sqrt T := by dsimp [s]; field_simp; ring
  rw [he] at hm
  have hh := mul_le_mul_of_nonneg_left hshape (show 0 ≤ 8 * η * Real.exp η by positivity)
  have hk : 8 * η * Real.exp η ≤ (T : ℝ) * K := by
    apply (mul_le_mul_iff_right₀ (show 0 < L * R by positivity)).mp
    nlinarith only [hm, hh]
  have hn := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-η)) (Real.exp_pos η).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hn
  have hp : 0 ≤ η * Real.exp η := by positivity
  nlinarith only [hk, hn, hp]

lemma setup_dimension
    (p : LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.Params)
    (hp : LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum.spec.valid p)
    (T b : ℕ) (hT : 0 < T) (hTq : (T : ℝ) ≤ p.L1 * p.R) (hb : b ≤ p.n * T) :
    8 * ((T : ℝ) ^ 2 + T + (b + 1 : ℕ) * T * (6400 * (p.L1 * p.R) ^ 2)) ≤ p.d := by
  let S := 1 + (p.n : ℝ) + p.L1 * p.R + p.L0 * p.R ^ 2 / p.ε
  have hn : 0 < p.n := by have := hp.2.2.2.2.1; omega
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast hn
  have hq : 0 ≤ p.L1 * p.R := mul_nonneg hp.2.1 hp.2.2.1.le
  have hH : 0 ≤ p.L0 * p.R ^ 2 / p.ε := by
    exact div_nonneg (mul_nonneg hp.1.le (sq_nonneg _)) hp.2.2.2.1.le
  have hS : 1 ≤ S := by dsimp [S]; have := Nat.cast_nonneg (α := ℝ) p.n; linarith
  have hnS : (p.n : ℝ) ≤ S := by dsimp [S]; linarith
  have hqS : p.L1 * p.R ≤ S := by dsimp [S]; have := Nat.cast_nonneg (α := ℝ) p.n; linarith
  have hCS : 6400 * (p.L1 * p.R) ^ 2 ≤ 25600 * S ^ 4 := by
    calc
      _ ≤ 6400 * S ^ 2 := by gcongr
      _ ≤ _ := mul_le_mul (by norm_num) (pow_le_pow_right₀ hS (by omega)) (by positivity) (by positivity)
  have hbplus : b + 1 ≤ 2 * p.n * T := by
    have hpT := Nat.mul_pos hn hT
    have hh : b + 1 ≤ 2 * (p.n * T) := by omega
    simpa only [Nat.mul_assoc] using hh
  have hbnd := InterpolatedFiniteSumExponentialParameters.dimension_polynomial p.n T b S
    (6400 * (p.L1 * p.R) ^ 2) hS hnS (hTq.trans hqS) hbplus (by positivity) hCS
  have hTn : (T : ℝ) ≤ p.n * T := by
    have hh := mul_le_mul_of_nonneg_right hn1 (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
    simpa only [one_mul] using hh
  have hpoly : 8 * ((T : ℝ) ^ 2 + T + (b + 1 : ℕ) * T * (6400 * (p.L1 * p.R) ^ 2)) ≤
      2 ^ 19 * S ^ 8 := by
    apply le_trans _ hbnd
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg T : (0 : ℝ) ≤ T) hTn 2
    have hm := mul_le_mul_of_nonneg_left hTn
      (show 0 ≤ ((b + 1 : ℕ) : ℝ) * (6400 * (p.L1 * p.R) ^ 2) by positivity)
    nlinarith only [hsq, hm, hTn]
  have hpow : S ^ 8 ≤ S ^ 24 := pow_le_pow_right₀ hS (by omega)
  have hcoef : (2 : ℝ) ^ 19 ≤ 2 ^ 80 := by norm_num
  have hdim : (⌈(2 : ℝ) ^ 80 * S ^ 24⌉₊ : ℝ) ≤ p.d := by
    dsimp only [S]
    exact_mod_cast hp.2.2.2.2.2.2.2
  calc
    _ ≤ 2 ^ 19 * S ^ 8 := hpoly
    _ ≤ 2 ^ 80 * S ^ 24 := mul_le_mul hcoef hpow (by positivity) (by positivity)
    _ ≤ (⌈(2 : ℝ) ^ 80 * S ^ 24⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ _ := hdim

end LongTails.Proofs.InterpolatedFiniteSumLinkParameters
