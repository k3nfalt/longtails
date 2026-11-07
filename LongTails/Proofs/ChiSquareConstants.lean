import LongTails.Proofs.ChiSquareExecution

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ChiSquareDro

open LongTails.Setups.ChiSquareConstrainedDro

variable {q : Params}

structure Adm (q : Params) (I : Instance q) (proj : q.E → q.E) : Prop where
  convex : Convex ℝ I.domain
  x0_mem : q.x0 ∈ I.domain
  proj_meas : Measurable proj
  proj_mem : ∀ x, proj x ∈ I.domain
  proj_vi : ∀ x, ∀ u ∈ I.domain, ⟪x - proj x, u - proj x⟫ ≤ 0
  loss_meas : Measurable (Function.uncurry I.loss)
  sub_meas : Measurable (Function.uncurry I.sub)
  subgrad : ∀ ξ, ∀ x ∈ I.domain, ∀ y ∈ I.domain, I.loss x ξ + ⟪I.sub x ξ, y - x⟫ ≤ I.loss y ξ
  bounds : ∀ ξ, ∀ x ∈ I.domain, 0 ≤ I.loss x ξ ∧ I.loss x ξ ≤ q.B
  sub_le : ∀ ξ, ∀ x ∈ I.domain, ‖I.sub x ξ‖ ≤ q.G

lemma radius_sq (hρ : 0 < q.ρ) : radius q ^ 2 = 1 + 2 * q.ρ := Real.sq_sqrt (by linarith)

lemma radius_ge_one (hρ : 0 < q.ρ) : 1 ≤ radius q := by
  unfold radius
  have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 2 * q.ρ by linarith)
  rwa [Real.sqrt_one] at this

lemma radius_pos (hρ : 0 < q.ρ) : 0 < radius q := lt_of_lt_of_le one_pos (radius_ge_one hρ)

lemma tailBound_pos (hρ : 0 < q.ρ) (hB : 0 < q.B) : 0 < tailBound q := by
  unfold tailBound; have := Real.sqrt_pos.mpr hρ; positivity

lemma tailBound_sq_le (hρ : 0 < q.ρ) : tailBound q ^ 2 ≤ 2 * (q.B ^ 2 * (1 + 1 / q.ρ)) := by
  unfold tailBound
  have hs := Real.sq_sqrt hρ.le
  have hpos := Real.sqrt_pos.mpr hρ
  have e : (q.B / Real.sqrt q.ρ) ^ 2 = q.B ^ 2 / q.ρ := by rw [div_pow, hs]
  nlinarith [sq_nonneg (q.B - q.B / Real.sqrt q.ρ), e, show q.B ^ 2 * (1 + 1 / q.ρ) =
    q.B ^ 2 + q.B ^ 2 / q.ρ by ring]

lemma B_sub_etaLow : q.B - etaLow q = tailBound q := by unfold etaLow tailBound; ring

lemma etaLow_le (hρ : 0 < q.ρ) (hB : 0 < q.B) : etaLow q ≤ q.B := by
  unfold etaLow; have := Real.sqrt_pos.mpr hρ; have : 0 ≤ q.B / Real.sqrt q.ρ := by positivity
  linarith

lemma zero_mem_eta (hρ : 0 < q.ρ) (hB : 0 < q.B) : (0 : ℝ) ∈ Icc (etaLow q) q.B := by
  unfold etaLow; have := Real.sqrt_pos.mpr hρ; have : 0 ≤ q.B / Real.sqrt q.ρ := by positivity
  constructor <;> linarith

lemma scaleLow_pos (hρ : 0 < q.ρ) (hε : 0 < q.ε) (j : ℕ) : 0 < scaleLow q j := by
  unfold scaleLow; have := radius_pos hρ; positivity

lemma scaleLow_ge (hρ : 0 < q.ρ) (hε : 0 < q.ε) (j : ℕ) : q.ε / (8 * radius q) ≤ scaleLow q j := by
  unfold scaleLow
  have := radius_pos hρ
  have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  rw [mul_div_assoc]
  have : 0 ≤ q.ε / (8 * radius q) := by positivity
  nlinarith

lemma scaleLow_succ (j : ℕ) : scaleLow q (j + 1) = 2 * scaleLow q j := by
  unfold scaleLow; rw [pow_succ]; ring

lemma hyp_cfg {I : Instance q} {proj : q.E → q.E} (h : Adm q I proj) (hρ : 0 < q.ρ) (hG : 0 < q.G)
    (hB : 0 < q.B) (hε : 0 < q.ε) (j : ℕ) :
    Hyp (cfg q j) I.domain proj I.loss I.sub q.B q.G where
  c_pos := radius_pos hρ
  gx_pos := by
    change 0 < stepX q; unfold stepX; have := radius_pos hρ; positivity
  ge_pos := by
    change 0 < stepEta q; unfold stepEta; positivity
  gs_pos := by
    change 0 < stepScale q j; unfold stepScale
    have := radius_pos hρ; have := scaleLow_pos hρ hε j; positivity
  slo_pos := scaleLow_pos hρ hε j
  s_le := by
    change scaleLow q j ≤ 4 * scaleLow q j; have := scaleLow_pos hρ hε j; linarith
  e_le := etaLow_le hρ hB
  elo_le := etaLow_le hρ hB
  proj_mem := h.proj_mem
  proj_vi := h.proj_vi
  subgrad := h.subgrad
  loss_nonneg := fun ω x hx => (h.bounds ω x hx).1
  loss_le := fun ω x hx => (h.bounds ω x hx).2
  sub_le := h.sub_le

lemma noiseConst_eq (hρ : 0 < q.ρ) (hG : 0 < q.G) (hε : 0 < q.ε) (j : ℕ) :
    noiseConst (cfg q j) q.B q.G = q.ε / 32 := by
  unfold noiseConst
  change 2 * stepX q * radius q ^ 2 * q.G ^ 2 + stepEta q * (2 + 4 * radius q ^ 2) +
    stepScale q j * (radius q ^ 2 / 2 + radius q ^ 2 * (q.B - etaLow q) ^ 2 / scaleLow q j ^ 2) =
    q.ε / 32
  rw [B_sub_etaLow]
  unfold stepX stepEta stepScale
  have hc := radius_pos hρ
  have hs := scaleLow_pos hρ hε j
  have ht : 0 < scaleLow q j ^ 2 / 2 + tailBound q ^ 2 := by positivity
  field_simp
  ring

lemma noiseSlope_le (hρ : 0 < q.ρ) (hG : 0 < q.G) (hε : 0 < q.ε) (j : ℕ) :
    noiseSlope (cfg q j) q.B q.G ≤ 1 := by
  unfold noiseSlope
  change 4 * stepX q * radius q * q.G ^ 2 / scaleLow q j + 8 * stepEta q * radius q / scaleLow q j +
    2 * stepScale q j * radius q * (q.B - etaLow q) ^ 2 / scaleLow q j ^ 3 ≤ 1
  rw [B_sub_etaLow]
  have hc := radius_pos hρ
  have hs := scaleLow_pos hρ hε j
  have hge := scaleLow_ge hρ hε j
  set c := radius q with hcdef
  set s := scaleLow q j with hsdef
  set b := tailBound q with hbdef
  have hr : q.ε / (c * s) ≤ 8 := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hge
    linarith
  have hr0 : 0 ≤ q.ε / (c * s) := by positivity
  have e1 : 4 * stepX q * c * q.G ^ 2 / s = q.ε / (c * s) / 32 := by
    unfold stepX; rw [← hcdef]; field_simp; ring
  have e2 : 8 * stepEta q * c / s = q.ε / (c * s) * (c ^ 2 / (16 * (2 + 4 * c ^ 2))) := by
    unfold stepEta; rw [← hcdef]; field_simp; ring
  have e3 : 2 * stepScale q j * c * b ^ 2 / s ^ 3 =
      q.ε / (c * s) * (b ^ 2 / (64 * (s ^ 2 / 2 + b ^ 2))) := by
    unfold stepScale; rw [← hcdef, ← hsdef, ← hbdef]; field_simp; ring
  have f2 : c ^ 2 / (16 * (2 + 4 * c ^ 2)) ≤ 1 / 64 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have f3 : b ^ 2 / (64 * (s ^ 2 / 2 + b ^ 2)) ≤ 1 / 64 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [sq_nonneg s]
  rw [e1, e2, e3]
  nlinarith [mul_le_mul_of_nonneg_left f2 hr0, mul_le_mul_of_nonneg_left f3 hr0]

lemma sgdSteps_pos : 0 < sgdSteps q := by unfold sgdSteps; omega

lemma sgdSteps_ge :
    2 ^ 16 * (1 + 2 * q.ρ) * (q.G ^ 2 * q.R ^ 2 + q.B ^ 2 * (1 + 1 / q.ρ)) / q.ε ^ 2 + 144 ≤
      (sgdSteps q : ℝ) := by
  unfold sgdSteps
  push_cast
  linarith [Nat.le_ceil (2 ^ 16 * (1 + 2 * q.ρ) * (q.G ^ 2 * q.R ^ 2 + q.B ^ 2 * (1 + 1 / q.ρ)) /
    q.ε ^ 2)]

lemma scaleLow_top (hρ : 0 < q.ρ) (hε : 0 < q.ε) :
    tailBound q ≤ scaleLow q (numBrackets q - 1) := by
  have hN : numBrackets q - 1 = Nat.clog 2 ⌈8 * radius q * tailBound q / q.ε⌉₊ := by
    unfold numBrackets; omega
  rw [hN]
  have hc := radius_pos hρ
  have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) ⌈8 * radius q * tailBound q / q.ε⌉₊
  have h2 : 8 * radius q * tailBound q / q.ε ≤ (2 : ℝ) ^ Nat.clog 2 ⌈8 * radius q * tailBound q / q.ε⌉₊ :=
    (Nat.le_ceil _).trans (by exact_mod_cast h1)
  unfold scaleLow
  rw [div_le_iff₀ hε] at h2
  rw [le_div_iff₀ (by positivity)]
  linarith

lemma good_bracket (hρ : 0 < q.ρ) (hε : 0 < q.ε) {s : ℝ} (hs0 : 0 ≤ s)
    (hsB : s ≤ tailBound q) :
    ∃ j < numBrackets q, ∃ ss ∈ Icc (scaleLow q j) (4 * scaleLow q j),
      radius q * (ss - s) ^ 2 / (2 * ss) ≤ q.ε / 16 ∧
      radius q ^ 2 * scaleLow q j ^ 2 ≤ q.ε ^ 2 / 64 + radius q ^ 2 * tailBound q ^ 2 := by
  have hc := radius_pos hρ
  have hN : 0 < numBrackets q := by unfold numBrackets; omega
  have h0 : scaleLow q 0 = q.ε / (8 * radius q) := by unfold scaleLow; simp
  by_cases hlow : s < scaleLow q 0
  · refine ⟨0, hN, scaleLow q 0, ⟨le_rfl, by linarith [scaleLow_pos hρ hε 0]⟩, ?_, ?_⟩
    · have hs := scaleLow_pos hρ hε 0
      have : (scaleLow q 0 - s) ^ 2 ≤ scaleLow q 0 ^ 2 := by nlinarith
      rw [div_le_iff₀ (by positivity)]
      have e : q.ε / 16 * (2 * scaleLow q 0) = radius q * scaleLow q 0 ^ 2 := by
        rw [h0]; field_simp; ring
      rw [e]; exact mul_le_mul_of_nonneg_left this hc.le
    · rw [h0]
      have : radius q ^ 2 * (q.ε / (8 * radius q)) ^ 2 = q.ε ^ 2 / 64 := by field_simp; ring
      rw [this]; nlinarith [sq_nonneg (radius q * tailBound q)]
  · replace hlow := not_lt.mp hlow
    have hex : ∃ j, s < scaleLow q (j + 1) := by
      refine ⟨numBrackets q - 1, ?_⟩
      rw [scaleLow_succ]
      have := scaleLow_top hρ hε
      have := scaleLow_pos hρ hε (numBrackets q - 1)
      linarith
    classical
    set j := Nat.find hex
    have hj : s < scaleLow q (j + 1) := Nat.find_spec hex
    have hjN : j < numBrackets q := by
      have : j ≤ numBrackets q - 1 := Nat.find_min' hex (by
        rw [scaleLow_succ]
        have := scaleLow_top hρ hε
        have := scaleLow_pos hρ hε (numBrackets q - 1)
        linarith)
      omega
    have hlo : scaleLow q j ≤ s := by
      by_cases h : j = 0
      · rw [h]; exact hlow
      · have := Nat.find_min hex (show j - 1 < j by omega)
        replace this := not_lt.mp this
        rwa [Nat.sub_add_cancel (by omega)] at this
    refine ⟨j, hjN, s, ⟨hlo, ?_⟩, ?_, ?_⟩
    · rw [scaleLow_succ] at hj; linarith [scaleLow_pos hρ hε j]
    · simp only [sub_self]; norm_num; positivity
    · have hs := scaleLow_pos hρ hε j
      have : scaleLow q j ^ 2 ≤ tailBound q ^ 2 := pow_le_pow_left₀ hs.le (hlo.trans hsB) 2
      nlinarith [sq_nonneg q.ε, sq_nonneg (radius q)]

end OracleTemplate.ChiSquareDro
