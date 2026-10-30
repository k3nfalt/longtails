import LongTails.Proofs.FractalChebyshevSchedule
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OracleTemplate.FractalChebyshev

open Real Finset OracleTemplate.ScheduleBlock

noncomputable def phiSum (k : ℕ) (x : ℝ) : ℝ := ((angles k).map fun θ => 1 / (x + cos θ)).sum

lemma sum_flatMap_split (g : ℝ → ℝ) (l : List ℝ) :
    ((l.flatMap split).map g).sum = (l.map fun ψ => g (π / 2 - ψ / 2) + g (π / 2 + ψ / 2)).sum := by
  induction l with
  | nil => simp
  | cons ψ l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih]
    simp [split]

lemma pair_recip {x ψ : ℝ} (hx : 1 < x) :
    1 / (x + cos (π / 2 - ψ / 2)) + 1 / (x + cos (π / 2 + ψ / 2)) =
      4 * x * (1 / (dbl x + cos ψ)) := by
  rw [cos_first, cos_second, cos_eq_half ψ]
  have hs := sin_le_one (ψ / 2)
  have hs' := neg_one_le_sin (ψ / 2)
  have h1 : 0 < x + sin (ψ / 2) := by linarith
  have h2 : 0 < x + -sin (ψ / 2) := by linarith
  have h3 : 0 < dbl x + (1 - 2 * sin (ψ / 2) ^ 2) := by
    unfold dbl; nlinarith
  field_simp
  unfold dbl
  ring

lemma phiSum_succ (k : ℕ) {x : ℝ} (hx : 1 < x) : phiSum (k + 1) x = 4 * x * phiSum k (dbl x) := by
  unfold phiSum
  rw [angles, sum_flatMap_split]
  simp_rw [pair_recip hx]
  rw [← List.sum_map_mul_left]

lemma dbl_cosh (t : ℝ) : dbl (cosh t) = cosh (2 * t) := by
  unfold dbl
  rw [cosh_two_mul, cosh_sq]
  ring

lemma dbl_iterate_cosh (k : ℕ) : ∀ t : ℝ, dbl^[k] (cosh t) = cosh (2 ^ k * t) := by
  induction k with
  | zero => intro t; simp
  | succ k ih =>
    intro t
    rw [Function.iterate_succ_apply, dbl_cosh, ih, pow_succ]
    ring_nf

lemma phiSum_cosh (k : ℕ) : ∀ t : ℝ, 0 < t →
    phiSum k (cosh t) * sinh t * cosh (2 ^ k * t) = 2 ^ k * sinh (2 ^ k * t) := by
  induction k with
  | zero =>
    intro t _
    simp only [phiSum, angles, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      cos_pi_div_two, add_zero, pow_zero, one_mul]
    have := cosh_pos t
    field_simp
  | succ k ih =>
    intro t ht
    have hc : 1 < cosh t := one_lt_cosh.mpr ht.ne'
    rw [phiSum_succ k hc, dbl_cosh]
    have h := ih (2 * t) (by linarith)
    rw [show (2:ℝ) ^ (k + 1) * t = 2 ^ k * (2 * t) by ring]
    rw [sinh_two_mul] at h
    calc 4 * cosh t * phiSum k (cosh (2 * t)) * sinh t * cosh (2 ^ k * (2 * t))
        = 2 * (phiSum k (cosh (2 * t)) * (2 * sinh t * cosh t) * cosh (2 ^ k * (2 * t))) := by
          ring
      _ = _ := by rw [h, pow_succ]; ring

lemma sum_range_getD (l : List ℝ) : ∑ j ∈ range l.length, l.getD j 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; ring

lemma stepOf_eq {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L) (θ : ℝ) :
    stepOf L μ θ = 2 / (L - μ) * (1 / ((L + μ) / (L - μ) + cos θ)) := by
  have hd : 0 < L - μ := by linarith
  have hr := (root_bounds hμL θ).1
  have hr0 : 0 < (L + μ) / 2 + (L - μ) / 2 * cos θ := by linarith
  have h2 : (L + μ) / (L - μ) + cos θ = ((L + μ) / 2 + (L - μ) / 2 * cos θ) * (2 / (L - μ)) := by
    field_simp
  unfold stepOf
  rw [h2]
  field_simp

lemma ssum_etaOf {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L) (k : ℕ) :
    ssum (etaOf L μ k) (2 ^ k) = 2 / (L - μ) * phiSum k ((L + μ) / (L - μ)) := by
  unfold ssum etaOf
  rw [← schedule_length L μ k, sum_range_getD]
  unfold schedule phiSum
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro θ _
  exact stepOf_eq hμ hμL θ

lemma nat_add_two_le_pow {k : ℕ} (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

lemma tauOf_bounds {k : ℕ} (hk : 2 ≤ k) :
    0 < tauOf k ∧ tauOf k ≤ 2 ∧ 2 ^ k * tauOf k = 2 * ((k : ℝ) + 2) := by
  have hn : (0:ℝ) < 2 ^ k := by positivity
  have hle : ((k : ℝ) + 2) ≤ 2 ^ k := by exact_mod_cast nat_add_two_le_pow hk
  unfold tauOf
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ hn]; linarith
  · field_simp

lemma exp_two_le : Real.exp 2 ≤ 7.4 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  nlinarith [Real.exp_pos 1]

lemma two_le_exp_one : (2:ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp 1; linarith

lemma sinh_le_mul_exp (t : ℝ) : sinh t ≤ t * Real.exp t := by
  rw [sinh_eq]
  have h := Real.add_one_le_exp (-(2 * t))
  have e : Real.exp (-t) = Real.exp (-(2 * t)) * Real.exp t := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have := Real.exp_pos t
  nlinarith

lemma cosh_le_five {t : ℝ} (ht : 0 ≤ t) (ht2 : t ≤ 2) : cosh t ≤ 5 := by
  rw [cosh_eq]
  have h1 : Real.exp t ≤ Real.exp 2 := Real.exp_le_exp.mpr ht2
  have h2 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  linarith [exp_two_le]

lemma cosh_sub_one_ge {t : ℝ} (ht : 0 ≤ t) : t ^ 2 / 2 ≤ cosh t - 1 := by
  have e : cosh t = 1 + 2 * sinh (t / 2) ^ 2 := by
    rw [show t = 2 * (t / 2) by ring, cosh_two_mul, cosh_sq]; ring_nf
  have hs : t / 2 ≤ sinh (t / 2) := self_le_sinh_iff.mpr (by linarith)
  rw [e]
  nlinarith

lemma exp_ge_four_pow (k : ℕ) : (4:ℝ) ^ (k + 2) ≤ Real.exp (2 * ((k : ℝ) + 2)) := by
  have h : Real.exp (2 * ((k : ℝ) + 2)) = Real.exp 2 ^ (k + 2) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [h]
  apply pow_le_pow_left₀ (by norm_num)
  have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]; nlinarith [two_le_exp_one]

lemma sinh_ge_half_cosh {x : ℝ} (hx : 1 ≤ x) : cosh x / 2 ≤ sinh x := by
  rw [cosh_eq, sinh_eq]
  have h1 : Real.exp 1 ≤ Real.exp x := Real.exp_le_exp.mpr hx
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have := two_le_exp_one
  have := Real.exp_pos (-x)
  nlinarith

section Params

variable {L : ℝ} {k : ℕ}

lemma muOf_bounds (hL : 0 < L) (hk : 2 ≤ k) : 0 < muOf L k ∧ muOf L k < L := by
  obtain ⟨h0, -, -⟩ := tauOf_bounds hk
  have hc : 1 < cosh (tauOf k) := one_lt_cosh.mpr h0.ne'
  unfold muOf
  constructor
  · apply div_pos (mul_pos hL (by linarith)) (by linarith)
  · rw [div_lt_iff₀ (by linarith)]; nlinarith

lemma x0_eq_cosh (hL : 0 < L) (hk : 2 ≤ k) :
    (L + muOf L k) / (L - muOf L k) = cosh (tauOf k) := by
  obtain ⟨h0, -, -⟩ := tauOf_bounds hk
  have hc : 1 < cosh (tauOf k) := one_lt_cosh.mpr h0.ne'
  have hlm := (muOf_bounds hL hk).2
  rw [div_eq_iff (by linarith)]
  unfold muOf
  field_simp
  ring

lemma kappa_le (hL : 0 < L) (hk : 2 ≤ k) :
    L / muOf L k ≤ 3 * (2 ^ k) ^ 2 / ((k : ℝ) + 2) ^ 2 := by
  obtain ⟨h0, h2, hn⟩ := tauOf_bounds hk
  have hc : 1 < cosh (tauOf k) := one_lt_cosh.mpr h0.ne'
  have h5 := cosh_le_five h0.le h2
  have hsq := cosh_sub_one_ge h0.le
  have hμ := (muOf_bounds hL hk).1
  have e : L / muOf L k = (cosh (tauOf k) + 1) / (cosh (tauOf k) - 1) := by
    unfold muOf; field_simp
  rw [e]
  have hτ : tauOf k = 2 * ((k : ℝ) + 2) / 2 ^ k := rfl
  have hm : (0:ℝ) < (k : ℝ) + 2 := by positivity
  have hn' : (0:ℝ) < 2 ^ k := by positivity
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  have : tauOf k ^ 2 * (2 ^ k) ^ 2 = 4 * ((k : ℝ) + 2) ^ 2 := by
    rw [← mul_pow, mul_comm, hn]; ring
  nlinarith

lemma one_le_kappa (hL : 0 < L) (hk : 2 ≤ k) : 1 ≤ L / muOf L k := by
  have := muOf_bounds hL hk
  rw [le_div_iff₀ this.1]; linarith

lemma ssum_closed (hL : 0 < L) (hk : 2 ≤ k) :
    ssum (etaOf L (muOf L k) k) (2 ^ k) * sinh (tauOf k) * cosh (2 ^ k * tauOf k) * L =
      2 ^ k * sinh (2 ^ k * tauOf k) * (cosh (tauOf k) + 1) := by
  obtain ⟨h0, -, -⟩ := tauOf_bounds hk
  have hc : 1 < cosh (tauOf k) := one_lt_cosh.mpr h0.ne'
  have hlm := (muOf_bounds hL hk).2
  rw [ssum_etaOf (muOf_bounds hL hk).1 hlm, x0_eq_cosh hL hk]
  have hφ := phiSum_cosh k (tauOf k) h0
  have hd : 2 / (L - muOf L k) = (cosh (tauOf k) + 1) / L := by
    unfold muOf
    rw [div_eq_div_iff (by unfold muOf at hlm; linarith) hL.ne']
    field_simp
    ring
  rw [hd]
  have e : (cosh (tauOf k) + 1) / L * phiSum k (cosh (tauOf k)) * sinh (tauOf k) *
      cosh (2 ^ k * tauOf k) * L =
      (cosh (tauOf k) + 1) *
        (phiSum k (cosh (tauOf k)) * sinh (tauOf k) * cosh (2 ^ k * tauOf k)) := by
    field_simp
  rw [e, hφ]
  ring

lemma ssum_lower (hL : 0 < L) (hk : 2 ≤ k) :
    (2 ^ k) ^ 2 / (16 * ((k : ℝ) + 2) * L) ≤ ssum (etaOf L (muOf L k) k) (2 ^ k) := by
  obtain ⟨h0, h2, hn⟩ := tauOf_bounds hk
  have hcl := ssum_closed hL hk
  set S := ssum (etaOf L (muOf L k) k) (2 ^ k)
  have hm : (1:ℝ) ≤ 2 ^ k * tauOf k := by
    rw [hn]
    have : (0:ℝ) ≤ k := by positivity
    linarith
  have hsh := sinh_ge_half_cosh hm
  have hcoshpos := cosh_pos (2 ^ k * tauOf k)
  have hsinh := sinh_le_mul_exp (tauOf k)
  have he : Real.exp (tauOf k) ≤ 7.4 := (Real.exp_le_exp.mpr h2).trans exp_two_le
  have hc1 : 1 ≤ cosh (tauOf k) := one_le_cosh _
  have hsinhpos : 0 < sinh (tauOf k) := sinh_pos_iff.mpr h0
  have hsl : sinh (tauOf k) ≤ 8 * tauOf k := by
    have := mul_le_mul_of_nonneg_left he h0.le
    linarith
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    etaOf_nonneg (muOf_bounds hL hk).1 (muOf_bounds hL hk).2 k j
  have hkey : 2 ^ k * cosh (2 ^ k * tauOf k) ≤ S * (8 * tauOf k) * cosh (2 ^ k * tauOf k) * L := by
    have hsp : 0 ≤ sinh (2 ^ k * tauOf k) := le_trans (by positivity) hsh
    have p1 : cosh (2 ^ k * tauOf k) / 2 * 2 ≤ sinh (2 ^ k * tauOf k) * (cosh (tauOf k) + 1) :=
      mul_le_mul hsh (by linarith) (by norm_num) hsp
    have hn' : (0:ℝ) ≤ 2 ^ k := by positivity
    have p2 : S * sinh (tauOf k) * cosh (2 ^ k * tauOf k) * L ≤
        S * (8 * tauOf k) * cosh (2 ^ k * tauOf k) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsl hS0) hcoshpos.le) hL.le
    calc 2 ^ k * cosh (2 ^ k * tauOf k) = 2 ^ k * (cosh (2 ^ k * tauOf k) / 2 * 2) := by ring
      _ ≤ 2 ^ k * (sinh (2 ^ k * tauOf k) * (cosh (tauOf k) + 1)) :=
          mul_le_mul_of_nonneg_left p1 hn'
      _ = S * sinh (tauOf k) * cosh (2 ^ k * tauOf k) * L := by rw [hcl]; ring
      _ ≤ _ := p2
  have hkey' : 2 ^ k ≤ S * (8 * tauOf k) * L := by
    have := (mul_le_mul_iff_of_pos_right hcoshpos).mp (by linarith [hkey] :
      2 ^ k * cosh (2 ^ k * tauOf k) ≤ (S * (8 * tauOf k) * L) * cosh (2 ^ k * tauOf k))
    exact this
  have hτ : tauOf k = 2 * ((k : ℝ) + 2) / 2 ^ k := rfl
  rw [div_le_iff₀ (by positivity)]
  have hn' : (0:ℝ) < 2 ^ k := by positivity
  have : S * (8 * tauOf k) * L * 2 ^ k = S * (16 * ((k : ℝ) + 2) * L) := by
    rw [show S * (8 * tauOf k) * L * 2 ^ k = 8 * S * L * (2 ^ k * tauOf k) by ring, hn]; ring
  nlinarith

lemma ssum_upper (hL : 0 < L) (hk : 2 ≤ k) :
    ssum (etaOf L (muOf L k) k) (2 ^ k) ≤ 3 * (2 ^ k) ^ 2 / (((k : ℝ) + 2) * L) := by
  obtain ⟨h0, h2, hn⟩ := tauOf_bounds hk
  have hcl := ssum_closed hL hk
  set S := ssum (etaOf L (muOf L k) k) (2 ^ k)
  have hsc := sinh_lt_cosh (2 ^ k * tauOf k)
  have hcoshpos := cosh_pos (2 ^ k * tauOf k)
  have hsinh : tauOf k ≤ sinh (tauOf k) := self_le_sinh_iff.mpr h0.le
  have h5 := cosh_le_five h0.le h2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    etaOf_nonneg (muOf_bounds hL hk).1 (muOf_bounds hL hk).2 k j
  have hn' : (0:ℝ) < 2 ^ k := by positivity
  have hkey : S * tauOf k * cosh (2 ^ k * tauOf k) * L ≤ 2 ^ k * cosh (2 ^ k * tauOf k) * 6 := by
    have : S * tauOf k * cosh (2 ^ k * tauOf k) * L ≤
        S * sinh (tauOf k) * cosh (2 ^ k * tauOf k) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsinh hS0) hcoshpos.le) hL.le
    have : 2 ^ k * sinh (2 ^ k * tauOf k) * (cosh (tauOf k) + 1) ≤
        2 ^ k * cosh (2 ^ k * tauOf k) * 6 := by
      have hsp : 0 ≤ sinh (2 ^ k * tauOf k) :=
        sinh_nonneg_iff.mpr (by positivity)
      have p : sinh (2 ^ k * tauOf k) * (cosh (tauOf k) + 1) ≤ cosh (2 ^ k * tauOf k) * 6 :=
        mul_le_mul hsc.le (by linarith) (by linarith [one_le_cosh (tauOf k)]) hcoshpos.le
      calc 2 ^ k * sinh (2 ^ k * tauOf k) * (cosh (tauOf k) + 1)
          = 2 ^ k * (sinh (2 ^ k * tauOf k) * (cosh (tauOf k) + 1)) := by ring
        _ ≤ 2 ^ k * (cosh (2 ^ k * tauOf k) * 6) := mul_le_mul_of_nonneg_left p hn'.le
        _ = 2 ^ k * cosh (2 ^ k * tauOf k) * 6 := by ring
    linarith
  have hkey' : S * tauOf k * L ≤ 2 ^ k * 6 := by
    have := (mul_le_mul_iff_of_pos_right hcoshpos).mp (by linarith [hkey] :
      (S * tauOf k * L) * cosh (2 ^ k * tauOf k) ≤ (2 ^ k * 6) * cosh (2 ^ k * tauOf k))
    exact this
  rw [le_div_iff₀ (by positivity)]
  have : S * (((k : ℝ) + 2) * L) * 2 = S * tauOf k * L * 2 ^ k := by
    rw [show S * tauOf k * L * 2 ^ k = S * L * (2 ^ k * tauOf k) by ring, hn]; ring
  nlinarith

lemma top_ge (hL : 0 < L) (hk : 2 ≤ k) :
    8 * (2 ^ k) ^ 2 ≤ dbl^[k] ((L + muOf L k) / (L - muOf L k)) := by
  obtain ⟨h0, -, hn⟩ := tauOf_bounds hk
  rw [x0_eq_cosh hL hk, dbl_iterate_cosh, hn, cosh_eq]
  have h1 := exp_ge_four_pow k
  have h2 := Real.exp_pos (-(2 * ((k : ℝ) + 2)))
  have : (4:ℝ) ^ (k + 2) = 16 * (2 ^ k) ^ 2 := by
    rw [pow_add, show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
  linarith

lemma final_hyp (hL : 0 < L) (hk : 2 ≤ k) :
    1 + 2 * L * ssum (etaOf L (muOf L k) k) (2 ^ k) ≤
      (dbl^[k] ((L + muOf L k) / (L - muOf L k))) ^ 2 := by
  have hT := top_ge hL hk
  have hS := ssum_upper hL hk
  have hm : (4:ℝ) ≤ (k : ℝ) + 2 := by
    have : (2:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hn : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hLS : L * ssum (etaOf L (muOf L k) k) (2 ^ k) ≤ (2 ^ k) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hS hL.le
    have e : L * (3 * (2 ^ k) ^ 2 / (((k : ℝ) + 2) * L)) = 3 * (2 ^ k) ^ 2 / ((k : ℝ) + 2) := by
      field_simp
    rw [e] at h1
    have h2 : 3 * ((2:ℝ) ^ k) ^ 2 / ((k : ℝ) + 2) ≤ (2 ^ k) ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have : (0:ℝ) ≤ (2 ^ k) ^ 2 := by positivity
      nlinarith
    linarith
  have hT0 : 0 ≤ 8 * (2 ^ k : ℝ) ^ 2 := by positivity
  have hT2 := pow_le_pow_left₀ hT0 hT 2
  have h3 : 1 + 2 * (2 ^ k : ℝ) ^ 2 ≤ (8 * (2 ^ k : ℝ) ^ 2) ^ 2 := by
    have : (1:ℝ) ≤ (2 ^ k) ^ 2 := by nlinarith
    nlinarith
  have e2 : 2 * L * ssum (etaOf L (muOf L k) k) (2 ^ k) =
      2 * (L * ssum (etaOf L (muOf L k) k) (2 ^ k)) := by ring
  rw [e2]
  linarith

end Params

end OracleTemplate.FractalChebyshev
