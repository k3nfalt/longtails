import LongTails.Proofs.QuasarCubicExecution
import LongTails.Proofs.QuasarCubicStepBound
import LongTails.Proofs.QuasarCubicTuning
import LongTails.Proofs.HessianLipschitzModel

open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.QuasarCubicConvergence

open LongTails.Setups.QuasarConvexHessianLipschitz
open LongTails.Algorithms.QuasarCubicNewton
open LongTails.Proofs.QuasarCubicStep
open LongTails.Proofs.QuasarCubicPotential
open LongTails.Proofs.QuasarCubicStepBound
open LongTails.Proofs.QuasarCubicTuning
open LongTails.Proofs.QuasarCubicExecution
open OracleTemplate.ComponentEnvelope (Program)

def reply {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (q : E) : Reply E :=
  (f q, gradient f q, fderiv ℝ (gradient f) q)

def invSum (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, 1 / Real.sqrt (total (i + 1))

structure Hyp (p : Params) (f : p.E → ℝ) (xstar : p.E) : Prop where
  valid : spec.valid p
  hf : ∀ x, HasFDerivAt f (innerSL ℝ (gradient f x)) x
  hg : ∀ x, HasFDerivAt (gradient f) (fderiv ℝ (gradient f) x) x
  hLip : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.H * ‖x - y‖
  hsym : ∀ z, ∀ x y : p.E, ⟪x, fderiv ℝ (gradient f) z y⟫ = ⟪fderiv ℝ (gradient f) z x, y⟫
  hA0 : ‖fderiv ℝ (gradient f) p.x0‖ ≤ p.L₀
  hmin : IsMinOn f Set.univ xstar
  hquasar : ∀ x, p.γ * (f x - f xstar) ≤ ⟪gradient f x, x - xstar⟫
  hR : ‖p.x0 - xstar‖ ≤ p.R

def Inv (p : Params) (f : p.E → ℝ) (xstar : p.E) (st : Outer p.E) : Prop :=
  st.data = reply f st.x ∧ st.c + ⟪st.s, xstar⟫ ≤ total st.k * f xstar ∧
  ∃ q ρs : ℝ, 0 ≤ q ∧ 0 ≤ ρs ∧
    total st.k * f st.x + reg p / 32 * q -
        (st.k * coupleError p + total st.k * searchError p) ≤
      psi (est p) p.x0 st.c st.s (center (est p) p.x0 st.s) ∧
    ‖st.x - xstar‖ ≤ 8 / 5 * p.R + ρs ∧
    ρs ≤ (p.γ / (23 * p.R)) ^ 2 / 3 * q + 2 * (23 * p.R) / (3 * p.γ) * invSum st.k

def step (p : Params) (f : p.E → ℝ) (st : Outer p.E) : Outer p.E :=
  Program.eval (reply f) (outerStep (reg p) (est p) p.γ (depth p) p.x0 st)

lemma total_mono {j k : ℕ} (h : j ≤ k) : total j ≤ total k := by
  unfold total
  have : (j : ℝ) ≤ k := by exact_mod_cast h
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  gcongr

lemma invSum_le (k : ℕ) : invSum k ≤ 147 / 20 := by
  have h := inv_total_sum k
  have h6 : Real.sqrt 6 ≤ 49 / 20 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  unfold invSum
  linarith

lemma cube_root_bound {a R : ℝ} (hR : 0 < R) (h : a ^ 3 ≤ 4 * R ^ 3) :
    a ≤ 8 / 5 * R := by
  by_contra hc
  push Not at hc
  have : (8 / 5 * R) ^ 3 < a ^ 3 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
  have e : (8 / 5 * R) ^ 3 = 512 / 125 * R ^ 3 := by ring
  have : 0 < R ^ 3 := by positivity
  linarith

lemma seg_bound {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {x v xstar : E}
    {τ B : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hx : ‖x - xstar‖ ≤ B) (hv : ‖v - xstar‖ ≤ B) :
    ‖x + τ • (v - x) - xstar‖ ≤ B := by
  have e : x + τ • (v - x) - xstar = (1 - τ) • (x - xstar) + τ • (v - xstar) := by module
  rw [e]
  have h1 := norm_add_le ((1 - τ) • (x - xstar)) (τ • (v - xstar))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith), abs_of_nonneg hτ0] at h1
  nlinarith [mul_le_mul_of_nonneg_left hx (by linarith : 0 ≤ 1 - τ),
    mul_le_mul_of_nonneg_left hv hτ0]

section

variable {p : Params} {f : p.E → ℝ} {xstar : p.E} (hyp : Hyp p f xstar)
include hyp

lemma errors_le {k : ℕ} (hk : k ≤ iterations p) :
    k * coupleError p + total k * searchError p ≤ est p / 6 * p.R ^ 3 := by
  have hp := hyp.valid
  obtain ⟨hH, hγ, hγ1, hR, hL, hε⟩ := id hp
  have hc := couple_budget hp
  have hs := search_budget hp
  have hc0 : 0 ≤ coupleError p := by unfold coupleError radius; have := reg_pos hp; positivity
  have hs0 : 0 ≤ searchError p := by unfold searchError radius; have := gap_pos (p := p); positivity
  have h1 : (k : ℝ) * coupleError p ≤ iterations p * coupleError p :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hc0
  have h2 : total k * searchError p ≤ total (iterations p) * searchError p :=
    mul_le_mul_of_nonneg_right (total_mono hk) hs0
  have he : est p / 6 * p.R ^ 3 = 2 * (7776 * reg p / p.γ ^ 3 / 12 * p.R ^ 3) := by
    unfold est; ring
  rw [he]
  linarith

lemma bounds {st : Outer p.E} (hI : Inv p f xstar st) (hk : st.k ≤ iterations p) :
    ‖center (est p) p.x0 st.s - xstar‖ ≤ 8 / 5 * p.R ∧
    ‖st.x - xstar‖ ≤ 8 / 5 * p.R + 166 * p.R / p.γ := by
  have hp := hyp.valid
  obtain ⟨hH, hγ, hγ1, hR, hL, hε⟩ := id hp
  obtain ⟨-, hc, q, ρs, hq, hρs, hpsi, hx, hρ⟩ := hI
  have hN : 0 < est p := by unfold est; have := reg_pos hyp.valid; positivity
  have hM := reg_pos hyp.valid
  set v := center (est p) p.x0 st.s
  have hlow := psi_lower hN p.x0 st.c st.s xstar
  have hstar : psi (est p) p.x0 st.c st.s xstar ≤ total st.k * f xstar + est p / 6 * p.R ^ 3 := by
    unfold psi
    have h3 : ‖xstar - p.x0‖ ^ 3 ≤ p.R ^ 3 := by
      rw [norm_sub_rev]; exact pow_le_pow_left₀ (norm_nonneg _) hyp.hR 3
    have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ est p / 6)
    linarith
  have herr := errors_le hyp hk
  have hfx : total st.k * f xstar ≤ total st.k * f st.x :=
    mul_le_mul_of_nonneg_left (hyp.hmin (Set.mem_univ st.x)) (total_nonneg _)
  have hcomb : est p / 12 * ‖xstar - v‖ ^ 3 + reg p / 32 * q ≤ est p / 3 * p.R ^ 3 := by
    linarith
  have hv3 : ‖v - xstar‖ ^ 3 ≤ 4 * p.R ^ 3 := by
    rw [norm_sub_rev]
    have : 0 ≤ reg p / 32 * q := by positivity
    have h := (show est p / 12 * ‖xstar - v‖ ^ 3 ≤ est p / 3 * p.R ^ 3 by linarith)
    have e : est p / 3 * p.R ^ 3 = est p / 12 * (4 * p.R ^ 3) := by ring
    rw [e] at h
    exact le_of_mul_le_mul_left h (by positivity)
  have hqb : q ≤ 82944 * p.R ^ 3 / p.γ ^ 3 := by
    have h : reg p / 32 * q ≤ est p / 3 * p.R ^ 3 := by
      have : 0 ≤ est p / 12 * ‖xstar - v‖ ^ 3 := by positivity
      linarith
    have e : est p / 3 * p.R ^ 3 = reg p / 32 * (82944 * p.R ^ 3 / p.γ ^ 3) := by
      unfold est; field_simp; ring
    rw [e] at h
    exact le_of_mul_le_mul_left h (by positivity)
  refine ⟨cube_root_bound hR hv3, ?_⟩
  have hinv := invSum_le st.k
  have hρ1 : (p.γ / (23 * p.R)) ^ 2 / 3 * q ≤ (p.γ / (23 * p.R)) ^ 2 / 3 * (82944 * p.R ^ 3 / p.γ ^ 3) :=
    mul_le_mul_of_nonneg_left hqb (by positivity)
  have e1 : (p.γ / (23 * p.R)) ^ 2 / 3 * (82944 * p.R ^ 3 / p.γ ^ 3) = 82944 / 1587 * p.R / p.γ := by
    field_simp; ring
  have hρ2 : 2 * (23 * p.R) / (3 * p.γ) * invSum st.k ≤ 2 * (23 * p.R) / (3 * p.γ) * (147 / 20) :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  have e2 : 2 * (23 * p.R) / (3 * p.γ) * (147 / 20) = 3381 / 30 * p.R / p.γ := by
    field_simp; ring
  have hsum : 82944 / 1587 * p.R / p.γ + 3381 / 30 * p.R / p.γ ≤ 166 * p.R / p.γ := by
    rw [← add_div, div_le_div_iff_of_pos_right hγ]; nlinarith
  linarith

lemma step_inv {st : Outer p.E} (hI : Inv p f xstar st) (hk : st.k < iterations p) :
    Inv p f xstar (step p f st) ∧ (step p f st).k = st.k + 1 := by
  have hp := hyp.valid
  obtain ⟨hH, hγ, hγ1, hR, hL, hε⟩ := id hp
  have hb := bounds hyp hI hk.le
  obtain ⟨hdata, hc, q, ρs, hq, hρs, hpsi, hx, hρ⟩ := hI
  set M := reg p
  set N := est p
  set n := depth p
  set v := center N p.x0 st.s
  set x := st.x
  have hMpos : 0 < M := reg_pos hyp.valid
  have hM2 := reg_ge hyp.valid
  set ch := Program.eval (reply f) (coupling M n x v (reply f x) (reply f v)) with hch
  have hspec := coupling_spec (f := f) (g := gradient f) (A := fderiv ℝ (gradient f))
    M hMpos n x v hyp.hsym
  simp only at hspec
  change ch.2 = reply f (x + ch.1 • (v - x)) ∧ envelope M ch.2 ≤ f x ∧ 0 ≤ ch.1 ∧ ch.1 ≤ 1 ∧
    (ch.1 = 1 ∨ (ch.1 + 1 / 2 ^ n ≤ 1 ∧ f x < envelope M
      (reply f (x + (ch.1 + 1 / 2 ^ n) • (v - x))))) at hspec
  obtain ⟨hch2, henv, hτ0, hτ1, hcase⟩ := hspec
  set τ := ch.1
  set y := x + τ • (v - x)
  set h := cubicStep (gradient f y) (fderiv ℝ (gradient f) y) M
  set z := y + h
  have hstep : step p f st = ⟨z, reply f z, st.s + (weight st.k / p.γ) • gradient f z,
      st.c + weight st.k * (f z - ⟪gradient f z, z⟫ / p.γ), st.k + 1⟩ := by
    simp only [step, outerStep, Program.eval, Program.eval_bind]
    rw [hdata]
    rw [← hch, hch2]
    rfl
  rw [hstep]
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · have hz := hyp.hquasar z
    have hw := (weight_pos st.k).le
    have : weight st.k * (f z + ⟪gradient f z, xstar - z⟫ / p.γ) ≤ weight st.k * f xstar := by
      apply mul_le_mul_of_nonneg_left _ hw
      have : ⟪gradient f z, xstar - z⟫ = -⟪gradient f z, z - xstar⟫ := by
        rw [← inner_neg_right, neg_sub]
      rw [this, neg_div, ← sub_eq_add_neg, sub_le_iff_le_add, ← sub_le_iff_le_add',
        le_div_iff₀ hγ]
      linarith
    rw [total_succ]
    simp only [inner_add_left, real_inner_smul_left, inner_sub_right] at this ⊢
    have e : weight st.k * (f z + (⟪gradient f z, xstar⟫ - ⟪gradient f z, z⟫) / p.γ) =
        weight st.k * (f z - ⟪gradient f z, z⟫ / p.γ) + weight st.k / p.γ * ⟪gradient f z, xstar⟫ := by
      field_simp; ring
    linarith
  · have hy : y = x + τ • (v - x) := rfl
    have hyb : ‖y - xstar‖ ≤ 8 / 5 * p.R + ρs :=
      seg_bound hτ0 hτ1 hx (by have : 0 ≤ ρs := hρs; linarith [hb.1])
    have hyb2 : ‖y - xstar‖ ≤ 8 / 5 * p.R + 166 * p.R / p.γ :=
      seg_bound hτ0 hτ1 hb.2 (by have : 0 ≤ 166 * p.R / p.γ := by positivity
                                 linarith [hb.1])
    have hdD : ‖v - x‖ ≤ radius p := by
      have h1 : ‖v - x‖ ≤ ‖v - xstar‖ + ‖x - xstar‖ := by
        have := norm_sub_le (v - xstar) (x - xstar)
        simpa using this
      have hrad : radius p = 200 * p.R / p.γ := rfl
      have hRγ : p.R ≤ p.R / p.γ := by rw [le_div_iff₀ hγ]; nlinarith
      rw [hrad]
      have : 8 / 5 * p.R + (8 / 5 * p.R + 166 * p.R / p.γ) ≤ 200 * p.R / p.γ := by
        have e : 200 * p.R / p.γ = 166 * p.R / p.γ + 34 * (p.R / p.γ) := by ring
        rw [e]; linarith
      linarith [hb.1, hb.2]
    have hBn : ‖fderiv ℝ (gradient f) y‖ ≤ p.L₀ + p.H * radius p := by
      have h1 := hyp.hLip y p.x0
      have h2 : ‖fderiv ℝ (gradient f) y‖ ≤ ‖fderiv ℝ (gradient f) p.x0‖ +
          ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) p.x0‖ := by
        have := norm_add_le (fderiv ℝ (gradient f) p.x0)
          (fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) p.x0)
        simpa using this
      have hy0 : ‖y - p.x0‖ ≤ radius p := by
        have := norm_sub_le (y - xstar) (p.x0 - xstar)
        have e : y - xstar - (p.x0 - xstar) = y - p.x0 := by abel
        rw [e] at this
        have hrad : radius p = 200 * p.R / p.γ := rfl
        have hRγ : p.R ≤ p.R / p.γ := by rw [le_div_iff₀ hγ]; nlinarith
        rw [hrad]
        have e2 : 200 * p.R / p.γ = 166 * p.R / p.γ + 34 * (p.R / p.γ) := by ring
        rw [e2]
        linarith [hyp.hR, norm_sub_rev p.x0 xstar]
      have h3 := mul_le_mul_of_nonneg_left hy0 hH.le
      linarith [hyp.hA0]
    have hdesc := step_descent (M := M) hyp.hf hyp.hg hyp.hLip y
    have hinner := step_inner (M := M) hyp.hg hyp.hLip hMpos y (hyp.hsym y)
    have hey : envelope M (f y, gradient f y, fderiv ℝ (gradient f) y) ≤ f x := by
      have : ch.2 = (f y, gradient f y, fderiv ℝ (gradient f) y) := hch2
      rw [← this]; exact henv
    have hcoup : τ = 1 ∨ -(p.H * ‖h‖ ^ 2 * ‖v - x‖ + gap p * ‖v - x‖ ^ 2 *
        (‖fderiv ℝ (gradient f) y‖ / 2 + p.H / 2 * ‖h‖ + p.H / 6 * (gap p * ‖v - x‖))) ≤
        ⟪gradient f z, v - x⟫ := by
      rcases hcase with h1 | ⟨-, h2⟩
      · exact Or.inl h1
      right
      have hinc := envelope_increment (M := M) hyp.hf hyp.hg hyp.hLip hMpos hyp.hsym y
        (gap p • (v - x))
      have eyw : y + gap p • (v - x) = x + (τ + 1 / 2 ^ n) • (v - x) := by
        simp only [y, gap, n]; module
      rw [eyw] at hinc
      have hgt : 0 < envelope M (f (x + (τ + 1 / 2 ^ n) • (v - x)),
          gradient f (x + (τ + 1 / 2 ^ n) • (v - x)),
          fderiv ℝ (gradient f) (x + (τ + 1 / 2 ^ n) • (v - x))) -
          envelope M (f y, gradient f y, fderiv ℝ (gradient f) y) := by
        have : f x < envelope M (reply f (x + (τ + 1 / 2 ^ n) • (v - x))) := h2
        simp only [reply] at this
        linarith
      have hg0 := gap_pos (p := p)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hg0, real_inner_smul_right] at hinc
      have key : 0 < gap p * (⟪gradient f z, v - x⟫ + (p.H * ‖h‖ ^ 2 * ‖v - x‖ + gap p * ‖v - x‖ ^ 2 *
          (‖fderiv ℝ (gradient f) y‖ / 2 + p.H / 2 * ‖h‖ + p.H / 6 * (gap p * ‖v - x‖)))) := by
        have : gap p * (⟪gradient f z, v - x⟫ + (p.H * ‖h‖ ^ 2 * ‖v - x‖ + gap p * ‖v - x‖ ^ 2 *
            (‖fderiv ℝ (gradient f) y‖ / 2 + p.H / 2 * ‖h‖ + p.H / 6 * (gap p * ‖v - x‖)))) =
            gap p * ⟪gradient f z, v - x⟫ + p.H * ‖h‖ ^ 2 * (gap p * ‖v - x‖) +
            (‖fderiv ℝ (gradient f) y‖ / 2 + p.H / 2 * ‖h‖ + p.H / 6 * (gap p * ‖v - x‖)) *
              (gap p * ‖v - x‖) ^ 2 := by ring
        rw [this]
        linarith
      have := (pos_iff_pos_of_mul_pos key).mp hg0
      linarith
    have hpot := potential_step (N := N) (M := M) (H := p.H) (γ := p.γ) (δ := gap p)
      (D := radius p) (L := p.L₀) (R := p.R) (Λ2 := coupleError p) (Λ3 := searchError p)
      (x0 := p.x0) (x := x) (v := v) (y := y) (z := z) (h := h) (gz := gradient f z) (s := st.s)
      (c := st.c) (fx := f x) (fz := f z)
      (ey := envelope M (f y, gradient f y, fderiv ℝ (gradient f) y)) (q := q) (τ := τ)
      (Bn := ‖fderiv ℝ (gradient f) y‖) (k := st.k)
      rfl hM2 hH hγ hγ1 hR (radius_ge hyp.valid) hL rfl rfl rfl hτ0 hτ1 hpsi hey hdesc
      hinner.1 hinner.2 hcoup hdD (norm_nonneg _) hBn (gap_pos) (gap_le_one)
      (gap_le_step hyp.valid) rfl rfl
    refine ⟨q + total (st.k + 1) * ‖h‖ ^ 3, ρs + ‖h‖,
      add_nonneg hq (mul_nonneg (total_nonneg _) (by positivity)), add_nonneg hρs (norm_nonneg _),
      hpot, ?_, ?_⟩
    · have := norm_add_le (y - xstar) h
      have e : z - xstar = (y - xstar) + h := by simp only [z]; abel
      rw [e]
      linarith
    · have hA1 : 0 < total (st.k + 1) := (weight_pos st.k).trans_le (weight_le_total st.k)
      set cc := p.γ / (23 * p.R) * Real.sqrt (total (st.k + 1))
      have hcc : 0 < cc := by positivity
      have hy := young_cube (norm_nonneg h) hcc
      have e1 : cc ^ 2 = (p.γ / (23 * p.R)) ^ 2 * total (st.k + 1) := by
        simp only [cc, mul_pow, Real.sq_sqrt hA1.le]
      have e2 : 2 / (3 * cc) = 2 * (23 * p.R) / (3 * p.γ) * (1 / Real.sqrt (total (st.k + 1))) := by
        simp only [cc]; field_simp
      rw [e1, e2] at hy
      have hsum : invSum (st.k + 1) = invSum st.k + 1 / Real.sqrt (total (st.k + 1)) := by
        simp only [invSum, Finset.sum_range_succ]
      rw [hsum]
      have : (p.γ / (23 * p.R)) ^ 2 * total (st.k + 1) * ‖h‖ ^ 3 / 3 =
          (p.γ / (23 * p.R)) ^ 2 / 3 * (total (st.k + 1) * ‖h‖ ^ 3) := by ring
      linarith

lemma initial_inv :
    Inv p f xstar ⟨p.x0, reply f p.x0, 0, 0, 0⟩ := by
  have hR := hyp.valid.2.2.2.1
  refine ⟨rfl, by simp [total], 0, 0, le_rfl, le_rfl, ?_, ?_, ?_⟩
  · simp [psi, center, total]
  · simp only [add_zero]; linarith [hyp.hR, norm_sub_rev p.x0 xstar]
  · simp [invSum]

lemma iterate_inv (j : ℕ) (hj : j ≤ iterations p) :
    Inv p f xstar ((step p f)^[j] ⟨p.x0, reply f p.x0, 0, 0, 0⟩) ∧
      ((step p f)^[j] ⟨p.x0, reply f p.x0, 0, 0, 0⟩).k = j := by
  induction j with
  | zero => exact ⟨initial_inv hyp, rfl⟩
  | succ j ih =>
      obtain ⟨hI, hk⟩ := ih (by omega)
      rw [Function.iterate_succ_apply']
      have := step_inv hyp hI (by omega)
      exact ⟨this.1, by rw [this.2, hk]⟩

lemma final_accuracy :
    f ((step p f)^[iterations p] ⟨p.x0, reply f p.x0, 0, 0, 0⟩).x - f xstar ≤ p.ε := by
  have hp := hyp.valid
  obtain ⟨hI, hk⟩ := iterate_inv hyp (iterations p) le_rfl
  set st := (step p f)^[iterations p] ⟨p.x0, reply f p.x0, 0, 0, 0⟩
  obtain ⟨-, hc, q, ρs, hq, -, hpsi, -, -⟩ := hI
  rw [hk] at hc hpsi
  have hγ := hp.2.1
  have hN : 0 < est p := by unfold est; have := reg_pos hp; positivity
  have hlow := psi_lower hN p.x0 st.c st.s xstar
  have hstar : psi (est p) p.x0 st.c st.s xstar ≤ total (iterations p) * f xstar + est p / 6 * p.R ^ 3 := by
    unfold psi
    have h3 : ‖xstar - p.x0‖ ^ 3 ≤ p.R ^ 3 := by
      rw [norm_sub_rev]; exact pow_le_pow_left₀ (norm_nonneg _) hyp.hR 3
    have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ est p / 6)
    linarith
  have herr := errors_le hyp (le_refl (iterations p))
  have hq0 : 0 ≤ reg p / 32 * q := by have := reg_pos hp; positivity
  have hd0 : 0 ≤ est p / 12 * ‖xstar - center (est p) p.x0 st.s‖ ^ 3 := by positivity
  have htot : 0 < total (iterations p) := by
    have h1 := iterations_pos hp
    have := total_lower (iterations p)
    have : (0 : ℝ) < (iterations p : ℝ) ^ 3 / 6 := by
      have : (0 : ℝ) < iterations p := by exact_mod_cast h1
      positivity
    linarith
  have hmain : total (iterations p) * (f st.x - f xstar) ≤ est p / 3 * p.R ^ 3 := by nlinarith
  have hrate := final_rate hp
  have e : est p / 3 * p.R ^ 3 / total (iterations p) = 7776 * reg p / p.γ ^ 3 / 3 * p.R ^ 3 /
      total (iterations p) := by unfold est; ring
  have : f st.x - f xstar ≤ est p / 3 * p.R ^ 3 / total (iterations p) := by
    rw [le_div_iff₀ htot]; linarith
  linarith

end

lemma hyp_of_admissible {p : Params} {f : p.E → ℝ} {xstar : p.E} (hp : spec.valid p)
    (hC2 : ContDiff ℝ 2 f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.H * ‖x - y‖)
    (hA0 : ‖fderiv ℝ (gradient f) p.x0‖ ≤ p.L₀) (hQ : QuasarConvexAt f p.γ xstar)
    (hR : ‖p.x0 - xstar‖ ≤ p.R) : Hyp p f xstar := by
  refine ⟨hp, ?_, ?_, hLip, ?_, hA0, hQ.1, hQ.2, hR⟩
  · intro x
    have hh := (hC2.differentiable (by norm_num) x).hasFDerivAt
    rw [← toDual_gradient] at hh
    exact hh
  · intro x
    exact ((OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hC2).differentiable
      (by norm_num) x).hasFDerivAt
  · intro z x y
    exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hC2 z x y).symm

end LongTails.Proofs.QuasarCubicConvergence
