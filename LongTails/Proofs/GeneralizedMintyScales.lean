import LongTails.Setups.HighDimensionalGeneralizedMinty
import LongTails.Proofs.GeneralizedMintyChain

namespace LongTails.Proofs.GeneralizedMintyScales

open LongTails.Setups.GeneralizedLipschitzMinty
structure Scales (p : Params) where
  m : ℕ
  κ : ℝ
  r : ℝ
  B : ℝ
  M : ℝ
  D : ℝ
  slope : 0 < κ
  spacing : 0 < r
  radius : 0 < B
  cap : 1 ≤ M
  width : 0 < D
  far : 4 * ((2 * m : ℕ) + 1 : ℝ) * r ^ 2 ≤ B ^ 2
  root : ((2 * m : ℕ) + 1 : ℝ) * r ^ 2 ≤ p.R ^ 2
  base : 12 * κ ≤ p.L0
  localScale : M ≤ 2 ∨ 48 ≤ p.L1 * r
  saturation : Real.log M ≤ p.L1 / 2 * (r * Real.sqrt ((m : ℝ) + 1) / 4)
  barrier : 8 * p.ε ≤ M * κ * r
  space : D + ((2 * m + 1 : ℕ) : ℝ) ≤ p.d
  count : 4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 * (B ^ 2 / (r / 4) ^ 2) ≤ D

lemma scales (p : Params) (hp : LongTails.Setups.HighDimensionalGeneralizedMinty.spec.valid p) :
    ∃ s : Scales p, s.m = ⌊(p.R * (p.L0 / p.ε + p.L1) / 1024) ^ 2⌋₊ := by
  obtain ⟨⟨h0, h1, hR, he⟩, hT, hlog, hd⟩ := hp
  let C := p.L0 / p.ε + p.L1
  let T := p.R * C / 1024
  have hC : 0 < C := by dsimp [C]; positivity
  have hT' : 1 ≤ T := by dsimp [T, C]; linarith
  have hRp : 0 < p.R := by
    by_contra! hh
    have := mul_nonpos_of_nonpos_of_nonneg hh hC.le
    dsimp only [T] at hT'
    linarith
  let m := ⌊T ^ 2⌋₊
  let a := Real.sqrt ((m : ℝ) + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha2 : a ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hmt : (m : ℝ) ≤ T ^ 2 := Nat.floor_le (sq_nonneg T)
  have hat : a ≤ 2 * T := by nlinarith [sq_nonneg (a - 2 * T), sq_nonneg (T - 1)]
  let r := p.R / (2 * a)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrad : 2 * r * a = p.R := by dsimp [r]; field_simp
  have hlen : 4 * r ^ 2 * ((m : ℝ) + 1) = p.R ^ 2 := by rw [← ha2, ← hrad]; ring
  have hrC : 256 ≤ r * C := by
    have hh := mul_le_mul_of_nonneg_left hat (by positivity : 0 ≤ 2 * r)
    rw [hrad] at hh
    dsimp only [T] at hh
    by_contra! hbad
    nlinarith [mul_pos hRp (sub_pos.mpr hbad)]
  let M := 1 + p.L1 * p.ε / p.L0
  have hM : 1 ≤ M := by dsimp [M]; linarith [div_nonneg (mul_nonneg h1 he.le) h0.le]
  have hMe : M * p.L0 = C * p.ε := by dsimp [M, C]; field_simp
  let D := 4096 * ((m : ℝ) + 1) ^ 3
  refine ⟨⟨m, p.L0 / 12, r, 2 * p.R, M, D, by positivity, hr, by positivity, hM, by dsimp [D]; positivity,
    ?_, ?_, by linarith, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · push_cast
    nlinarith [sq_nonneg r]
  · push_cast
    nlinarith [sq_nonneg r, mul_nonneg (Nat.cast_nonneg m (α := ℝ)) (sq_nonneg r)]
  · by_cases h : M ≤ 2
    · exact Or.inl h
    · right
      have hh : p.L0 / p.ε ≤ p.L1 := by
        apply (div_le_iff₀ he).mpr
        have hratio : 1 ≤ p.L1 * p.ε / p.L0 := by dsimp [M] at h; linarith
        linarith [(le_div_iff₀ h0).mp hratio]
      dsimp only [C] at hrC
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hh)]
  · change Real.log M ≤ p.L1 / 2 * (r * a / 4)
    change 32 * Real.log M ≤ p.L1 * p.R at hlog
    rw [← hrad] at hlog
    nlinarith [mul_nonneg h1 (mul_nonneg hr.le ha.le)]
  · nlinarith [congrArg (fun x : ℝ => x * r) hMe, mul_nonneg he.le (sub_nonneg.mpr hrC)]
  · change 8192 * (1 + m) ^ 3 ≤ p.d at hd
    have h := (Nat.cast_le (α := ℝ)).mpr hd
    dsimp [D]
    push_cast at h ⊢
    nlinarith [sq_nonneg (m : ℝ), pow_nonneg (Nat.cast_nonneg m (α := ℝ)) 3]
  · have eq : (2 * p.R) ^ 2 / (r / 4) ^ 2 = 256 * ((m : ℝ) + 1) := by
      rw [div_eq_iff (by positivity)]
      nlinarith [hlen]
    rw [eq]
    dsimp [D]
    push_cast
    nlinarith [sq_nonneg (m : ℝ), Nat.cast_nonneg m (α := ℝ)]

end LongTails.Proofs.GeneralizedMintyScales
