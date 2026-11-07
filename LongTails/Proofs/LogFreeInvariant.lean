import LongTails.Proofs.LogFreeTransition
import LongTails.Proofs.ThirdOrderOperatorBounds
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.LogFreeInvariant

open OracleTemplate LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LogFreeProxNewton
open LongTails.Proofs.LogFreeGeometry LongTails.Proofs.LogFreeTail
  LongTails.Proofs.LogFreeTransition LongTails.Proofs.LogFreeParameters
  LongTails.Proofs.LogFreeLinearAlgebra
open scoped RealInnerProductSpace

variable (p : Params) (f : p.E → ℝ)

noncomputable def finalLevel : ℕ := ⌈20 + 2 * Real.log (logArgument p)⌉₊

noncomputable def coerciveLevel (j : ℕ) : ℝ := 3 * weight p / 4 - weight p / 8 * (1 - 1 / 2 ^ j)

noncomputable def radius (j : ℕ) : ℝ :=
  Real.sqrt (2 * threshold p / weight p) +
    4 / 3 * (1 - 1 / 4 ^ j) * Real.sqrt (tailLevel p / (weight p / 2))

structure TailGood (st : State p.E) : Prop where
  coer : ∀ v, coerciveLevel p st.level * ‖v‖ ^ 2 ≤ ⟪sys f (weight p) st.cur.x v, v⟫
  dec : decrement (weight p) st.center st.cur * 16 ^ st.level ≤ tailLevel p
  dec3 : 1 ≤ st.level → decrement (weight p) st.center st.cur * 16 ^ st.level ≤ 3 * p.Δ
  loc : ‖st.cur.x - st.center‖ ≤ radius p st.level
  lev : st.level ≤ finalLevel p

structure Good (n : ℕ) (st : State p.E) : Prop where
  cur : st.cur = exact p f st.cur.x
  center : st.centerValue = f st.center
  mono : regF f (weight p) st.center st.cur.x ≤ f st.center
  top : f st.center ≤ f p.x0
  path : ‖st.cur.x - p.x0‖ ≤ 2 * scale p * n
  tailInv : st.tail = true → TailGood p f st
  out : st.done = true → ‖gradient f st.out‖ ≤ p.ε

noncomputable def phaseWeight : ℝ := 2 ^ 14 + 3

noncomputable def potential (st : State p.E) : ℝ :=
  if st.done then 0 else
    phaseWeight * (f st.center - (f p.x0 - p.Δ)) / threshold p + finalLevel p +
      (if st.tail then 1 - (st.level : ℝ) else
        2 + max 0 (64 * (regF f (weight p) st.center st.cur.x - f st.center + threshold p) /
          tailLevel p + 1))

lemma coerciveLevel_ge (hp : spec.valid p) (j : ℕ) : weight p / 2 ≤ coerciveLevel p j := by
  unfold coerciveLevel
  have hw := weight_pos p hp
  have ha0 : 0 ≤ 1 / (2 : ℝ) ^ j := by positivity
  nlinarith [mul_nonneg hw.le ha0]

lemma coerciveLevel_succ (hp : spec.valid p) (j : ℕ) :
    coerciveLevel p (j + 1) ≤ (1 - tolerance j) * coerciveLevel p j := by
  unfold coerciveLevel tolerance
  have hw := weight_pos p hp
  have h1 : (1 : ℝ) / 2 ^ (j + 1) = 1 / 2 ^ j / 2 := by rw [pow_succ]; field_simp
  have h4 : (1 : ℝ) / 2 ^ (j + 4) = 1 / 2 ^ j / 16 := by rw [pow_add]; norm_num; field_simp
  rw [h1, h4]
  set a := (1 : ℝ) / 2 ^ j with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  nlinarith [mul_nonneg (mul_pos hw ha0).le (by linarith : (0 : ℝ) ≤ 3 - a)]

lemma direction_spec {γ μ : ℝ} (hμ : 0 < μ) (c : p.E) (d : Data p.E)
    (hcoer : ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪system γ d v, v⟫) :
    system γ d (direction γ c d) = -residual γ c d := by
  have hex := solve_exists hμ hcoer (-residual γ c d)
  unfold direction
  rw [dite_eq_left hex]
  exact hex.choose_spec

lemma decrement_eq {γ μ : ℝ} (hμ : 0 < μ) (c : p.E) (d : Data p.E)
    (hcoer : ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪system γ d v, v⟫) :
    decrement γ c d = ⟪system γ d (direction γ c d), direction γ c d⟫ := by
  rw [direction_spec p hμ c d hcoer, inner_neg_left]; rfl

lemma system_exact (γ : ℝ) (x : p.E) : system γ (exact p f x) = sys f γ x := rfl

lemma radius_bound (hp : spec.valid p) (j : ℕ) :
    weight p * radius p j ≤ 2 / 5 * p.ε := by
  have hw := weight_pos p hp
  have hu := unit_pos p hp
  have hwu := weight_unit_sq p hp
  have hε := hp.2.2.2
  have hu' : unit p = 256 * p.ε ^ 2 / weight p := by
    rw [eq_div_iff hw.ne']; linarith [hwu]
  unfold radius threshold tailLevel
  have h1 : weight p * Real.sqrt (2 * (unit p / 4096) / weight p) ≤ 9 / 25 * p.ε := by
    have hX : 0 ≤ 2 * (unit p / 4096) / weight p := by positivity
    have hsq : (weight p * Real.sqrt (2 * (unit p / 4096) / weight p)) ^ 2 = p.ε ^ 2 / 8 := by
      rw [mul_pow, Real.sq_sqrt hX, hu']; field_simp; ring
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp
    rw [hsq]; nlinarith
  have h2 : weight p * Real.sqrt (unit p / 2 ^ 20 / (weight p / 2)) ≤ 1 / 40 * p.ε := by
    have hX : 0 ≤ unit p / 2 ^ 20 / (weight p / 2) := by positivity
    have hsq : (weight p * Real.sqrt (unit p / 2 ^ 20 / (weight p / 2))) ^ 2 =
        p.ε ^ 2 / 2 ^ 11 := by
      rw [mul_pow, Real.sq_sqrt hX, hu']; field_simp; ring
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp
    rw [hsq]; nlinarith
  have hc : 0 ≤ 4 / 3 * (1 - 1 / (4 : ℝ) ^ j) := by
    have : 1 / (4 : ℝ) ^ j ≤ 1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    linarith
  have hc' : 4 / 3 * (1 - 1 / (4 : ℝ) ^ j) ≤ 4 / 3 := by
    have : 0 ≤ 1 / (4 : ℝ) ^ j := by positivity
    linarith
  have hs : 0 ≤ Real.sqrt (unit p / 2 ^ 20 / (weight p / 2)) := Real.sqrt_nonneg _
  calc weight p * (Real.sqrt (2 * (unit p / 4096) / weight p) +
        4 / 3 * (1 - 1 / 4 ^ j) * Real.sqrt (unit p / 2 ^ 20 / (weight p / 2)))
      = weight p * Real.sqrt (2 * (unit p / 4096) / weight p) +
        4 / 3 * (1 - 1 / 4 ^ j) * (weight p * Real.sqrt (unit p / 2 ^ 20 / (weight p / 2))) := by
          ring
    _ ≤ 9 / 25 * p.ε + 4 / 3 * (1 / 40 * p.ε) := by
          have hW0 : 0 ≤ weight p * Real.sqrt (unit p / 2 ^ 20 / (weight p / 2)) :=
            mul_nonneg hw.le (Real.sqrt_nonneg _)
          have h4 : 4 / 3 * (1 - 1 / 4 ^ j) * (weight p * Real.sqrt (unit p / 2 ^ 20 /
              (weight p / 2))) ≤ 4 / 3 * (weight p * Real.sqrt (unit p / 2 ^ 20 / (weight p / 2))) :=
            mul_le_mul_of_nonneg_right hc' hW0
          linarith
    _ ≤ 2 / 5 * p.ε := by nlinarith

structure Admissible : Prop where
  smooth : ContDiff ℝ 3 f
  lip : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x - fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤
    p.L₃ * ‖x - y‖
  gap : ∀ x, f p.x0 - f x ≤ p.Δ
  start : ‖fderiv ℝ (gradient f) p.x0‖ ≤ p.H₀

lemma log16 : (2 : ℝ) ≤ Real.log 16 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  nlinarith [Real.exp_pos 1]

lemma steps_le (hp : spec.valid p) : (steps p : ℝ) ≤ 2 ^ 29 * logArgument p := by
  have hΓ := logArgument_ge p hp
  have hS := complexity_le_log p hp
  have hl : Real.log (logArgument p) ≤ logArgument p := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < logArgument p); linarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ 27 * (1 + complexity p + Real.log (logArgument p)) by
    have : 0 ≤ complexity p := by rw [complexity_eq p hp]; exact div_nonneg hp.2.1.le (unit_pos p hp).le
    have : 0 ≤ Real.log (logArgument p) := Real.log_nonneg (by linarith)
    positivity)
  unfold steps
  nlinarith

lemma final_power (hp : spec.valid p) {j : ℕ} (hj : finalLevel p ≤ j) :
    2 ^ 70 * logArgument p ^ 3 ≤ (16 : ℝ) ^ j := by
  have hΓ := logArgument_ge p hp
  have hlog : 0 ≤ Real.log (logArgument p) := Real.log_nonneg (by linarith)
  have hj' : 20 + 2 * Real.log (logArgument p) ≤ (j : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hj)
  have h1 : (16 : ℝ) ^ (20 + 2 * Real.log (logArgument p)) ≤ (16 : ℝ) ^ (j : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hj'
  rw [Real.rpow_natCast] at h1
  have h2 : (16 : ℝ) ^ (20 + 2 * Real.log (logArgument p)) =
      16 ^ (20 : ℝ) * Real.exp (2 * Real.log (logArgument p) * Real.log 16) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 16)
      (2 * Real.log (logArgument p))]
    ring_nf
  have h3 : logArgument p ^ 4 ≤ Real.exp (2 * Real.log (logArgument p) * Real.log 16) := by
    have : Real.exp (4 * Real.log (logArgument p)) = logArgument p ^ 4 := by
      rw [show (4 : ℝ) * Real.log (logArgument p) = (4 : ℕ) * Real.log (logArgument p) by norm_num,
        Real.exp_nat_mul, Real.exp_log (by linarith)]
    rw [← this]
    apply Real.exp_le_exp.mpr
    nlinarith [log16]
  have h4 : (16 : ℝ) ^ (20 : ℝ) = 2 ^ 80 := by
    rw [show (20 : ℝ) = (20 : ℕ) by norm_num, Real.rpow_natCast]; norm_num
  have h5 : logArgument p ^ 3 ≤ logArgument p ^ 4 := by
    have : 1 ≤ logArgument p := by linarith
    calc logArgument p ^ 3 = logArgument p ^ 3 * 1 := by ring
      _ ≤ logArgument p ^ 3 * logArgument p := by gcongr
      _ = logArgument p ^ 4 := by ring
  have h6 : (0 : ℝ) ≤ logArgument p ^ 3 := by positivity
  rw [h2, h4] at h1
  nlinarith

lemma finalLevel_ge (hp : spec.valid p) : 20 ≤ finalLevel p := by
  have hΓ := logArgument_ge p hp
  have hlog : 0 ≤ Real.log (logArgument p) := Real.log_nonneg (by linarith)
  have h := Nat.le_ceil (20 + 2 * Real.log (logArgument p))
  have : (20 : ℝ) ≤ finalLevel p := le_trans (by linarith) h
  exact_mod_cast this

lemma final_factor (hp : spec.valid p) {N j : ℕ} (hN : N ≤ steps p) (hj : finalLevel p ≤ j) :
    (28 * p.H₀ + 108 * (p.L₃ * Real.sqrt (p.Δ / p.L₃)) + 28 * p.L₃ * (2 * scale p * N) ^ 2 +
      weight p) * (3 * p.Δ) ≤ 9 / 25 * p.ε ^ 2 * 16 ^ j := by
  obtain ⟨hL, hΔ, hH, hε⟩ := hp
  have hp' : spec.valid p := ⟨hL, hΔ, hH, hε⟩
  have hΓ := logArgument_ge p hp'
  have hS := complexity_le_log p hp'
  have hpow := final_power p hp' hj
  have hNr : (N : ℝ) ≤ 2 ^ 29 * logArgument p := (Nat.cast_le.mpr hN).trans (steps_le p hp')
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hr := scale_pos p hp'
  have hc := scale_cube p hp'
  set Γ := logArgument p with hΓdef
  have hε2 : 0 < p.ε ^ 2 := by positivity
  have hH0 : p.H₀ * p.Δ / p.ε ^ 2 ≤ Γ := by
    rw [hΓdef]; unfold logArgument; have : 0 ≤ p.L₃ * p.Δ ^ 3 / p.ε ^ 4 := by positivity
    linarith
  have hcube : p.L₃ * p.Δ ^ 3 / p.ε ^ 4 ≤ Γ := by
    rw [hΓdef]; unfold logArgument; have : 0 ≤ p.H₀ * p.Δ / p.ε ^ 2 := by positivity
    linarith
  have hsig : p.L₃ * Real.sqrt (p.Δ / p.L₃) * p.Δ / p.ε ^ 2 ≤ Γ := by
    set x := p.L₃ * Real.sqrt (p.Δ / p.L₃) * p.Δ / p.ε ^ 2 with hx
    have hx0 : 0 ≤ x := by positivity
    have hx2 : x ^ 2 = p.L₃ * p.Δ ^ 3 / p.ε ^ 4 := by
      rw [hx, div_pow, mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hΔ.le hL.le)]
      field_simp
    nlinarith
  have hSeq : p.L₃ * scale p ^ 2 * p.Δ / p.ε ^ 2 = complexity p := by
    rw [complexity_eq p hp', unit_eq p hp']
    rw [← hc]; field_simp
  have hw : weight p * p.Δ / p.ε ^ 2 = 256 * complexity p := by
    rw [weight_eq, ← hSeq]; ring
  have hS0 : 0 ≤ complexity p := by rw [complexity_eq p hp']; exact div_nonneg hΔ.le (unit_pos p hp').le
  have hkey : (28 * p.H₀ + 108 * (p.L₃ * Real.sqrt (p.Δ / p.L₃)) + 28 * p.L₃ * (2 * scale p * N) ^ 2 +
      weight p) * (3 * p.Δ) / p.ε ^ 2 =
      3 * (28 * (p.H₀ * p.Δ / p.ε ^ 2) + 108 * (p.L₃ * Real.sqrt (p.Δ / p.L₃) * p.Δ / p.ε ^ 2) +
        112 * (N : ℝ) ^ 2 * (p.L₃ * scale p ^ 2 * p.Δ / p.ε ^ 2) + weight p * p.Δ / p.ε ^ 2) := by
    field_simp; ring
  have hNN : (N : ℝ) ^ 2 ≤ 2 ^ 58 * Γ ^ 2 := by
    have := mul_le_mul hNr hNr hN0 (by positivity); nlinarith
  have hb : (28 * p.H₀ + 108 * (p.L₃ * Real.sqrt (p.Δ / p.L₃)) + 28 * p.L₃ * (2 * scale p * N) ^ 2 +
      weight p) * (3 * p.Δ) / p.ε ^ 2 ≤ 2 ^ 67 * Γ ^ 3 := by
    rw [hkey, hSeq, hw]
    have hSN : (N : ℝ) ^ 2 * complexity p ≤ 2 ^ 58 * Γ ^ 2 * Γ :=
      mul_le_mul hNN hS hS0 (by positivity)
    have hΓ1 : 1 ≤ Γ := by linarith
    have hΓ3 : Γ ≤ Γ ^ 3 := by nlinarith
    linarith
  rw [div_le_iff₀ hε2] at hb
  have h3 := mul_le_mul_of_nonneg_left hpow hε2.le
  have h4 : 0 ≤ Γ ^ 3 * p.ε ^ 2 := by positivity
  linarith

lemma tail_coercive (hp : spec.valid p) {st : State p.E} (hcur : st.cur = exact p f st.cur.x)
    (ht : TailGood p f st) :
    ∀ v, weight p / 2 * ‖v‖ ^ 2 ≤ ⟪system (weight p) st.cur v, v⟫ := by
  intro v
  rw [hcur, system_exact]
  exact (mul_le_mul_of_nonneg_right (coerciveLevel_ge p hp st.level) (sq_nonneg _)).trans (ht.coer v)

lemma tail_final (hp : spec.valid p) (ha : Admissible p f) {n : ℕ} (hn : n ≤ steps p)
    {st : State p.E} (hg : Good p f n st) (ht : st.tail = true)
    (hlev : finalLevel p ≤ st.level) : ‖gradient f st.cur.x‖ ≤ p.ε := by
  have TG := hg.tailInv ht
  have hw := weight_pos p hp
  have hμ : 0 < weight p / 2 := by positivity
  have hcoer := tail_coercive p f hp hg.cur TG
  set y := st.cur.x with hy
  set c := st.center with hc
  set d := direction (weight p) c st.cur with hd
  have hspec := direction_spec p hμ c st.cur hcoer
  have hdec := decrement_eq p hμ c st.cur hcoer
  have hcur := hg.cur
  have hhe : st.cur.hess = fderiv ℝ (gradient f) y := congrArg Data.hess hcur
  have hgr : st.cur.grad = gradient f y := congrArg Data.grad hcur
  have hsys : system (weight p) st.cur = sys f (weight p) y := by
    unfold system sys; rw [hhe]
  rw [hsys] at hspec hdec
  set B := sys f (weight p) y with hB
  have hBsymm : Symm B := sys_symm ha.smooth (weight p) y
  have hBpos : ∀ v, 0 ≤ ⟪B v, v⟫ := fun v =>
    le_trans (by positivity) ((hcoer v).trans_eq (by rw [hsys]))
  have hres : LongTails.Algorithms.LogFreeProxNewton.residual (weight p) c st.cur = -(B d) := by rw [hspec, neg_neg]
  have hgrad : gradient f y = LongTails.Algorithms.LogFreeProxNewton.residual (weight p) c st.cur - weight p • (y - c) := by
    simp [LongTails.Algorithms.LogFreeProxNewton.residual, hgr, hy]
  have hBd := image_norm_sq hBsymm hBpos d
  have hΛ : decrement (weight p) c st.cur = ⟪B d, d⟫ := hdec
  have hj1 : 1 ≤ st.level := le_trans (by linarith [finalLevel_ge p hp]) hlev
  have hdec3 := TG.dec3 hj1
  rw [hΛ] at hdec3
  have hres_norm : ‖LongTails.Algorithms.LogFreeProxNewton.residual (weight p) c st.cur‖ = ‖B d‖ := by rw [hres, norm_neg]
  have hBnorm : ‖B‖ ≤ ‖fderiv ℝ (gradient f) y‖ + weight p := by
    rw [hB, sys]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hw]
    exact mul_le_of_le_one_right hw.le ContinuousLinearMap.norm_id_le
  have hσ : 0 < Real.sqrt (p.Δ / p.L₃) := Real.sqrt_pos.mpr (div_pos hp.2.1 hp.1)
  have hΔσ : p.Δ = p.L₃ * Real.sqrt (p.Δ / p.L₃) ^ 2 := by
    have hLL : p.L₃ * (p.Δ / p.L₃) = p.Δ := by have := hp.1; field_simp
    rw [Real.sq_sqrt (div_nonneg hp.2.1.le hp.1.le), hLL]
  have hgrow := ThirdOrderOperatorBounds.hessian_growth ha.smooth hp.1 hσ hp.2.2.1 hΔσ ha.lip
    p.x0 y ha.gap ha.start
  have hpath : ‖y - p.x0‖ ≤ 2 * scale p * steps p := by
    have := scale_pos p hp
    exact hg.path.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (by positivity))
  have hHy : ‖fderiv ℝ (gradient f) y‖ ≤ 28 * p.H₀ + 108 * (p.L₃ * Real.sqrt (p.Δ / p.L₃)) +
      28 * p.L₃ * (2 * scale p * steps p) ^ 2 := by
    refine hgrow.trans ?_
    have h0 : 0 ≤ ‖y - p.x0‖ := norm_nonneg _
    have : ‖y - p.x0‖ ^ 2 ≤ (2 * scale p * steps p) ^ 2 := pow_le_pow_left₀ h0 hpath 2
    have := hp.1
    nlinarith
  have hfac := final_factor p hp (le_refl (steps p)) hlev
  have hΛ0 : 0 ≤ ⟪B d, d⟫ := hBpos d
  have h16 : (0 : ℝ) < 16 ^ st.level := by positivity
  have hBd' : ‖B d‖ ^ 2 ≤ 9 / 25 * p.ε ^ 2 := by
    have hK : 0 ≤ 28 * p.H₀ + 108 * (p.L₃ * Real.sqrt (p.Δ / p.L₃)) +
        28 * p.L₃ * (2 * scale p * steps p) ^ 2 + weight p := by
      have := hp.2.2.1; have := hp.1; positivity
    have hBle : ‖B‖ ≤ 28 * p.H₀ + 108 * (p.L₃ * Real.sqrt (p.Δ / p.L₃)) +
        28 * p.L₃ * (2 * scale p * steps p) ^ 2 + weight p := by linarith
    have h1 : ‖B d‖ ^ 2 * 16 ^ st.level ≤ (28 * p.H₀ + 108 * (p.L₃ * Real.sqrt (p.Δ / p.L₃)) +
        28 * p.L₃ * (2 * scale p * steps p) ^ 2 + weight p) * (3 * p.Δ) := by
      calc ‖B d‖ ^ 2 * 16 ^ st.level ≤ ‖B‖ * ⟪B d, d⟫ * 16 ^ st.level := by gcongr
        _ = ‖B‖ * (⟪B d, d⟫ * 16 ^ st.level) := by ring
        _ ≤ _ := mul_le_mul hBle hdec3 (by positivity) hK
    have h2 := h1.trans hfac
    nlinarith
  have hres_le : ‖LongTails.Algorithms.LogFreeProxNewton.residual (weight p) c st.cur‖ ≤ 3 / 5 * p.ε := by
    rw [hres_norm]
    have : (3 / 5 * p.ε) ^ 2 = 9 / 25 * p.ε ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by have := hp.2.2.2; positivity)
      (by norm_num : (2 : ℕ) ≠ 0)).mp (by nlinarith)
  have hloc := radius_bound p hp st.level
  have hdist : weight p * ‖y - c‖ ≤ 2 / 5 * p.ε :=
    (mul_le_mul_of_nonneg_left TG.loc hw.le).trans hloc
  rw [hgrad]
  calc ‖LongTails.Algorithms.LogFreeProxNewton.residual (weight p) c st.cur - weight p • (y - c)‖ ≤
        ‖LongTails.Algorithms.LogFreeProxNewton.residual (weight p) c st.cur‖ + ‖weight p • (y - c)‖ := norm_sub_le _ _
    _ ≤ 3 / 5 * p.ε + 2 / 5 * p.ε := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hw]; exact hdist
    _ = p.ε := by ring

end LongTails.Proofs.LogFreeInvariant
