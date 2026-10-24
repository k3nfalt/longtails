import LongTails.Proofs.ManySampleConvolutionalPerceptronStability

namespace LongTails.Proofs.ClusteredConvolutionalPerceptronStability

open ManySampleConvolutionalPerceptronStability

lemma signed_mass_gap {b a q : ℝ} (hb : b ≠ 0) (hb1 : |b| ≤ 1)
    (hswitch : b * a * q ≤ 0) :
    |a + b * q + (q + b * a)| + |a + b * q - (q + b * a)| =
      |a + q| + |a - q| - |b| * abs (|a + q| - |a - q|) ∧
    abs (|a + b * q + (q + b * a)| - |a + b * q - (q + b * a)|) =
      abs (abs (|a + q| - |a - q|) - |b| * (|a + q| + |a - q|)) := by
  by_cases hp : 0 < b
  · have haq : a * q ≤ 0 := by nlinarith
    have h := (switch_criterion a q).mpr haq
    have he : scalarStep b (a + q) (a - q) =
        (a + b * q + (q + b * a), a + b * q - (q + b * a)) := by
      simp only [scalarStep, ite_eq_left h]
      congr 1 <;> ring
    have hmass := scalarStep_mass (s := a + q) (d := a - q) hp.le
      (by simpa [abs_of_pos hp] using hb1)
    have hgap := scalarStep_gap (s := a + q) (d := a - q) hp.le
      (by simpa [abs_of_pos hp] using hb1)
    rw [he] at hmass hgap
    simpa [abs_of_pos hp] using And.intro hmass hgap
  · have hn : b < 0 := lt_of_le_of_ne (le_of_not_gt hp) hb
    have haq : 0 ≤ a * q := by nlinarith
    have h : |a - q| ≤ |a + q| := by rw [← sq_le_sq]; nlinarith
    have he : scalarStep (-b) (a - q) (a + q) =
        (a + b * q - (q + b * a), a + b * q + (q + b * a)) := by
      simp only [scalarStep, ite_eq_left h]
      congr 1 <;> ring
    have hmass := scalarStep_mass (s := a - q) (d := a + q) (by linarith : 0 ≤ -b)
      (by simpa [abs_of_neg hn] using hb1)
    have hgap := scalarStep_gap (s := a - q) (d := a + q) (by linarith : 0 ≤ -b)
      (by simpa [abs_of_neg hn] using hb1)
    rw [he] at hmass hgap
    constructor
    · simpa only [abs_of_neg hn, abs_sub_comm, add_comm] using hmass
    · simpa only [abs_of_neg hn, abs_sub_comm, add_comm] using hgap

lemma signed_forced_mass_gap {b a q f : ℝ} (hb : b ≠ 0) (hb1 : |b| ≤ 1)
    (hswitch : b * a * q ≤ 0) :
    |a + b * q + f + (q + b * a)| + |a + b * q + f - (q + b * a)| ≤
      |a + q| + |a - q| - |b| * abs (|a + q| - |a - q|) + 2 * |f| ∧
    |b| * (|a + q| + |a - q|) - abs (|a + q| - |a - q|) - 2 * |f| ≤
      abs (|a + b * q + f + (q + b * a)| - |a + b * q + f - (q + b * a)|) := by
  obtain ⟨hmass, hgap⟩ := signed_mass_gap hb hb1 hswitch
  have hm := shifted_mass_le (a + b * q + (q + b * a)) (a + b * q - (q + b * a)) f
  have hg := shifted_gap_ge (a + b * q + (q + b * a)) (a + b * q - (q + b * a)) f
  rw [hmass] at hm
  rw [hgap] at hg
  have he1 : a + b * q + (q + b * a) + f = a + b * q + f + (q + b * a) := by ring
  have he2 : a + b * q - (q + b * a) + f = a + b * q + f - (q + b * a) := by ring
  rw [he1, he2] at hm hg
  refine ⟨hm, ?_⟩
  have hn := neg_le_abs (abs (|a + q| - |a - q|) - |b| * (|a + q| + |a - q|))
  linarith

lemma signed_two_step {ρ b b' a q f f' : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hρb : ρ ≤ |b|) (hρb' : ρ ≤ |b'|) (hb1 : |b| ≤ 1) (hb1' : |b'| ≤ 1)
    (hswitch : b * a * q ≤ 0)
    (hswitch' : b' * (a + b * q + f) * (q + b * a) ≤ 0) :
    let a' := a + b * q + f
    let q' := q + b * a
    |a' + b' * q' + f' + (q' + b' * a')| +
      |a' + b' * q' + f' - (q' + b' * a')| ≤
      (1 - ρ ^ 2 / 2) * (|a + q| + |a - q|) + 4 * |f| + 2 * |f'| := by
  dsimp only
  obtain ⟨hm, hg⟩ := signed_forced_mass_gap (f := f) hb hb1 hswitch
  obtain ⟨hm', _⟩ := signed_forced_mass_gap (f := f') hb' hb1' hswitch'
  have ht := two_step_contraction hρ hρb hρb' hρ1
    (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _) (abs_nonneg _)
    (by positivity : 0 ≤ 2 * |f|) hm hg hm'
  linarith

lemma mass_controls_mean (a q : ℝ) : 2 * |a| ≤ |a + q| + |a - q| := by
  have h := abs_add_le (a + q) (a - q)
  have he : a + q + (a - q) = 2 * a := by ring
  rw [he, abs_mul] at h
  norm_num at h
  exact h

lemma mass_controls_product (a q : ℝ) :
    |a * q| ≤ (|a + q| + |a - q|) ^ 2 / 4 := by
  have ha := mass_controls_mean a q
  have hq := mass_controls_mean q a
  rw [add_comm q a, abs_sub_comm q a] at hq
  have hm := mul_le_mul ha hq (by positivity) (by positivity)
  rw [abs_mul]
  nlinarith

lemma lorentz_step {ℓ t T t' : ℝ} (hℓ : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1)
    (ht : 0 ≤ t) (hT : 0 ≤ T) (hcone : ℓ * T ^ 2 ≤ t ^ 2)
    (hstep : t + ℓ * T ≤ t') : ℓ * (T + t) ^ 2 ≤ t' ^ 2 := by
  have hbase : 0 ≤ t + ℓ * T := by positivity
  have hsquare : (t + ℓ * T) ^ 2 ≤ t' ^ 2 := by nlinarith
  have hm := mul_nonneg (sub_nonneg.mpr hℓ1) (sub_nonneg.mpr hcone)
  nlinarith

lemma lorentz_forcing {δ g L t T : ℝ} (hδ : 0 ≤ δ) (hg : 0 < g)
    (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hsmall : δ ≤ L ^ 2 * g) (hcone : δ * g * T ^ 2 ≤ t ^ 2) :
    δ * T ≤ L * t := by
  have hm := mul_le_mul_of_nonneg_left hcone hδ
  have hn := mul_le_mul_of_nonneg_right hsmall (sq_nonneg t)
  have hs : g * ((δ * T) ^ 2) ≤ g * ((L * t) ^ 2) := by nlinarith
  have hs' : (δ * T) ^ 2 ≤ (L * t) ^ 2 := (mul_le_mul_iff_right₀ hg).mp (by simpa [mul_comm] using hs)
  nlinarith [mul_nonneg hL ht]

lemma two_step_moving_bound {V U : ℕ → ℝ} {r A B : ℝ} {K : ℕ}
    (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hmono : ∀ i j, i ≤ j → j ≤ K → U i ≤ U j)
    (hzero : V 0 ≤ A + B * U 0) (hone : 1 ≤ K → V 1 ≤ A + B * U 1)
    (hstep : ∀ n, n + 2 ≤ K →
      V (n + 2) ≤ r * V n + (1 - r) * B * U (n + 2)) :
    ∀ n, n ≤ K → V n ≤ A * r ^ (n / 2) + B * U n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro _; simpa using hzero
  | one => intro hn; simpa using hone hn
  | more n ih _ =>
    intro hn
    have hm := mul_le_mul_of_nonneg_left (ih (by omega)) hr
    have hu := mul_le_mul_of_nonneg_left (hmono n (n + 2) (by omega) hn)
      (mul_nonneg hr hB)
    have hs := hstep n hn
    have hd : (n + 2) / 2 = n / 2 + 1 := by omega
    rw [hd, pow_succ]
    nlinarith

end LongTails.Proofs.ClusteredConvolutionalPerceptronStability
