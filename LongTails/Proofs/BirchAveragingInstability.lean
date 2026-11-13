import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue

namespace BirchNonIIDInstability

noncomputable def tanhSlope (x : ℝ) : ℝ := 1 - Real.tanh x ^ 2

theorem hasDerivAt_tanhSlope_value (x : ℝ) : HasDerivAt Real.tanh (tanhSlope x) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have he : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 =
      tanhSlope x := by
    rw [tanhSlope, Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hf : Real.sinh / Real.cosh = Real.tanh := by
    funext y
    exact (Real.tanh_eq_sinh_div_cosh y).symm
  rwa [hf, he] at hd

@[fun_prop] theorem continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanhSlope_value x).continuousAt)

theorem tanhSlope_pos (x : ℝ) : 0 < tanhSlope x := by
  dsimp [tanhSlope]
  linarith [Real.tanh_sq_lt_one x]

theorem tanhSlope_le_one (x : ℝ) : tanhSlope x ≤ 1 := by
  dsimp [tanhSlope]
  nlinarith [sq_nonneg (Real.tanh x)]

theorem tanh_lipschitz (x y : ℝ) : |Real.tanh y - Real.tanh x| ≤ |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (𝕜 := ℝ) (f := Real.tanh) (C := 1)
    (fun z _ => (hasDerivAt_tanhSlope_value z).differentiableAt)
    (fun z _ => by
      rw [(hasDerivAt_tanhSlope_value z).deriv, Real.norm_eq_abs, abs_of_pos (tanhSlope_pos z)]
      exact tanhSlope_le_one z)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem abs_tanh_le_abs (x : ℝ) : |Real.tanh x| ≤ |x| := by
  simpa using tanh_lipschitz 0 x

theorem tanhSlope_lower (x : ℝ) : 1 - x ^ 2 ≤ tanhSlope x := by
  have h := (sq_le_sq).mpr (abs_tanh_le_abs x)
  dsimp [tanhSlope]
  linarith

noncomputable def potential (x y : ℝ) : ℝ :=
  x ^ 2 / 2 + x / 50 + y ^ 2 / 2 - 2 * Real.log (Real.cosh y) -
    Real.tanh x * (1 - Real.exp (-y ^ 2)) / 5

noncomputable def horizontal (x y : ℝ) : ℝ :=
  x + 1 / 50 - tanhSlope x * (1 - Real.exp (-y ^ 2)) / 5

noncomputable def vertical (x y : ℝ) : ℝ :=
  y - 2 * Real.tanh y - 2 / 5 * Real.tanh x * y * Real.exp (-y ^ 2)

theorem potential_horizontal_derivative (x y : ℝ) :
    HasDerivAt (fun z => potential z y) (horizontal x y) x := by
  have hd := (((((hasDerivAt_id x).pow 2).div_const 2).add
    ((hasDerivAt_id x).div_const 50)).add_const (y ^ 2 / 2)).sub_const (2 * Real.log (Real.cosh y))
  have hh := hd.sub (((hasDerivAt_tanhSlope_value x).mul_const
    (1 - Real.exp (-y ^ 2))).div_const 5)
  convert hh using 1
  · rfl
  · dsimp [horizontal]
    ring

theorem potential_vertical_derivative (x y : ℝ) :
    HasDerivAt (fun z => potential x z) (vertical x y) y := by
  have hlog := ((Real.hasDerivAt_cosh y).log (ne_of_gt (Real.cosh_pos y))).const_mul 2
  have he := (((hasDerivAt_id y).pow 2).neg).exp
  have hc := (((hasDerivAt_const y (1 : ℝ)).sub he).const_mul (Real.tanh x)).div_const 5
  have hd := (((hasDerivAt_const y (x ^ 2 / 2 + x / 50)).add
    (((hasDerivAt_id y).pow 2).div_const 2)).sub hlog).sub hc
  convert hd using 1
  · rfl
  · dsimp [vertical]
    simp only [Real.tanh_eq_sinh_div_cosh]
    ring

noncomputable def directionX (δ sign x y : ℝ) : ℝ :=
  horizontal x y + sign * δ * tanhSlope x * Real.tanh y

noncomputable def directionY (δ sign s x y : ℝ) : ℝ :=
  vertical x y + sign * δ * (Real.tanh x * tanhSlope y - Real.tanh s)

def reflect (z : ℝ × ℝ) : ℝ × ℝ := (z.1, -z.2)

noncomputable def phaseStep (δ sign s : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 - directionX δ sign z.1 z.2 / 100,
    z.2 - directionY δ sign s z.1 z.2 / 100)

noncomputable def phasePath (δ sign s : ℝ) : ℕ → ℝ × ℝ
  | 0 => (s, 0)
  | k + 1 => phaseStep δ sign s (phasePath δ sign s k)

theorem phaseStep_reflection (δ sign s : ℝ) (z : ℝ × ℝ) :
    phaseStep δ (-sign) s (reflect z) = reflect (phaseStep δ sign s z) := by
  apply Prod.ext <;>
    simp only [phaseStep, reflect, directionX, directionY, horizontal, vertical, tanhSlope,
      Real.tanh_neg, neg_sq] <;> ring

theorem phasePath_reflection (δ sign s : ℝ) (k : ℕ) :
    phasePath δ (-sign) s k = reflect (phasePath δ sign s k) := by
  induction k with
  | zero => simp [phasePath, reflect]
  | succ k ih =>
    rw [phasePath, ih, phaseStep_reflection]
    rfl

theorem phasePath_first (δ sign s : ℝ) :
    phasePath δ sign s 1 = (s - (s + 1 / 50) / 100, 0) := by
  simp [phasePath, phaseStep, directionX, directionY, horizontal, vertical, tanhSlope]

@[fun_prop] theorem continuous_phaseStep (δ sign : ℝ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => phaseStep δ sign p.1 p.2) := by
  unfold phaseStep directionX directionY horizontal vertical tanhSlope
  fun_prop

theorem continuous_phasePath (δ sign : ℝ) (k : ℕ) :
    Continuous (fun s => phasePath δ sign s k) := by
  induction k with
  | zero => exact continuous_id.prodMk continuous_const
  | succ k ih => exact (continuous_phaseStep δ sign).comp (continuous_id.prodMk ih)

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem tanh_increment_small {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1 / 5) (hab : a ≤ b) :
    19 / 20 * (b - a) ≤ Real.tanh b - Real.tanh a := by
  apply (convex_Icc (0 : ℝ) (1 / 5)).mul_sub_le_image_sub_of_le_deriv
    continuous_tanh.continuousOn
    (fun x _ => (hasDerivAt_tanhSlope_value x).differentiableAt.differentiableWithinAt)
    (fun x hx => ?_) a ⟨ha, hab.trans hb⟩ b ⟨ha.trans hab, hb⟩ hab
  rw [(hasDerivAt_tanhSlope_value x).deriv]
  have hx' := Set.mem_Icc.mp (interior_subset hx)
  have hbnd := tanhSlope_lower x
  nlinarith

theorem phasePath_second_y (δ s : ℝ) :
    (phasePath δ 1 s 2).2 =
      δ / 100 * (Real.tanh s - Real.tanh (s - (s + 1 / 50) / 100)) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, phasePath, phasePath_first]
  simp [phaseStep, directionY, vertical, tanhSlope]
  ring

/-- The common first step produces a transverse escape seed, positive when δ > 0. -/
theorem phasePath_escape_seed {δ s : ℝ} (hδ : 0 ≤ δ)
    (hs : s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50)) :
    (16 / 1000000 : ℝ) * δ ≤ (phasePath δ 1 s 2).2 := by
  have hinc := tanh_increment_small
    (a := s - (s + 1 / 50) / 100) (b := s) (by linarith [hs.1])
    (by linarith [hs.2]) (by linarith [hs.1])
  have hm := mul_le_mul_of_nonneg_left hinc (show 0 ≤ δ / 100 by positivity)
  rw [phasePath_second_y]
  nlinarith [mul_nonneg hδ (sub_nonneg.mpr hs.1)]

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem monotone_tanh : Monotone Real.tanh := by
  apply monotone_of_deriv_nonneg (fun x => (hasDerivAt_tanhSlope_value x).differentiableAt)
  intro x
  rw [(hasDerivAt_tanhSlope_value x).deriv]
  exact (tanhSlope_pos x).le

theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  simpa using monotone_tanh hx

theorem tanh_cubic_lower {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 3 ≤ Real.tanh x := by
  let f := fun x : ℝ => Real.tanh x - x + x ^ 3 / 3
  have hd (z : ℝ) : HasDerivAt f (tanhSlope z - 1 + z ^ 2) z := by
    convert ((hasDerivAt_tanhSlope_value z).sub (hasDerivAt_id z)).add
      (((hasDerivAt_id z).pow 3).div_const 3) using 1
    · rfl
    · dsimp
      ring
  have hm : Monotone f := monotone_of_deriv_nonneg (fun z => (hd z).differentiableAt)
    (fun z => by rw [(hd z).deriv]; linarith [tanhSlope_lower z])
  have h := hm hx
  dsimp [f] at h
  simp only [Real.tanh_zero, sub_zero] at h
  linarith

theorem tanh_small_lower {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    99 / 100 * y ≤ Real.tanh y := by
  have h := tanh_cubic_lower hy.1
  have hs : y ^ 2 ≤ 1 / 100 := by nlinarith [hy.1, hy.2]
  have hm := mul_le_mul_of_nonneg_right hs hy.1
  nlinarith [hy.1]

theorem correctionY_nonpos {s x y : ℝ} (hs : 0 ≤ s) (hx : x ≤ s) :
    Real.tanh x * tanhSlope y - Real.tanh s ≤ 0 := by
  have hmono := monotone_tanh hx
  have hs0 := tanh_nonneg hs
  by_cases hx0 : 0 ≤ Real.tanh x
  · have hm := mul_le_mul_of_nonneg_left (tanhSlope_le_one y) hx0
    nlinarith
  · have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hx0) (tanhSlope_pos y).le
    linarith

theorem vertical_initial_bound {x y : ℝ} (hx : -(3 / 100 : ℝ) ≤ x)
    (hy : y ∈ Set.Icc (0 : ℝ) (1 / 10)) : vertical x y ≤ -(121 / 125 : ℝ) * y := by
  have ht : -(3 / 100 : ℝ) ≤ Real.tanh x := by
    have h := (abs_le.mp (abs_tanh_le_abs (-(3 / 100 : ℝ)))).1
    have hm := monotone_tanh hx
    rw [Real.tanh_neg] at hm
    norm_num at h
    linarith
  have he0 := (Real.exp_pos (-y ^ 2)).le
  have he1 : Real.exp (-y ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
  have hm := mul_le_mul_of_nonneg_right ht he0
  have he : -(3 / 100 : ℝ) ≤ Real.tanh x * Real.exp (-y ^ 2) := by nlinarith
  have hmy := mul_le_mul_of_nonneg_right he hy.1
  have htan := tanh_small_lower hy
  dsimp [vertical]
  nlinarith

/-- Before the first threshold, transverse displacement grows by at least 1.009 per step. -/
theorem phaseStep_initial_growth {δ s x y : ℝ} (hδ : 0 ≤ δ) (hs : 0 ≤ s)
    (hx : x ∈ Set.Icc (-(3 / 100 : ℝ)) s) (hy : y ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    (1009 / 1000 : ℝ) * y ≤ (phaseStep δ 1 s (x, y)).2 := by
  have hv := vertical_initial_bound hx.1 hy
  have hc := mul_nonpos_of_nonneg_of_nonpos hδ (correctionY_nonpos hs hx.2 (y := y))
  dsimp [phaseStep, directionY]
  nlinarith [hy.1]

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem hasDerivAt_tanhSlope (x : ℝ) :
    HasDerivAt tanhSlope (-2 * Real.tanh x * tanhSlope x) x := by
  convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_tanhSlope_value x).pow 2) using 1
  · rfl
  · ring

theorem directionX_derivative (δ x y : ℝ) :
    HasDerivAt (fun z => directionX δ 1 z y)
      (1 + 2 / 5 * (Real.tanh x * tanhSlope x * (1 - Real.exp (-y ^ 2))) -
        2 * δ * (Real.tanh x * tanhSlope x * Real.tanh y)) x := by
  have hh := ((hasDerivAt_id x).add_const (1 / 50)).sub
    (((hasDerivAt_tanhSlope x).mul_const (1 - Real.exp (-y ^ 2))).div_const 5)
  have hc := ((hasDerivAt_tanhSlope x).const_mul δ).mul_const (Real.tanh y)
  convert hh.add hc using 1
  · funext z
    simp [directionX, horizontal]
  · ring

theorem abs_mul_le_one {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul]
  simpa using mul_le_mul ha hb (abs_nonneg b) (by norm_num : (0 : ℝ) ≤ 1)

theorem directionX_derivative_le {δ x y : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    1 + 2 / 5 * (Real.tanh x * tanhSlope x * (1 - Real.exp (-y ^ 2))) -
        2 * δ * (Real.tanh x * tanhSlope x * Real.tanh y) ≤ 4 := by
  have ha : |Real.tanh x * tanhSlope x| ≤ 1 := abs_mul_le_one
    (Real.abs_tanh_lt_one x).le (by rw [abs_of_pos (tanhSlope_pos x)]; exact tanhSlope_le_one x)
  have he0 := (Real.exp_pos (-y ^ 2)).le
  have he1 : Real.exp (-y ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
  have he : |1 - Real.exp (-y ^ 2)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb := (abs_le.mp (abs_mul_le_one ha he)).2
  have hc := (abs_le.mp (abs_mul_le_one ha (Real.abs_tanh_lt_one y).le)).1
  have hm := mul_le_mul_of_nonneg_left hc hδ.1
  nlinarith [hδ.2]

theorem monotone_phaseStep_x {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (s y : ℝ) :
    Monotone (fun x => (phaseStep δ 1 s (x, y)).1) := by
  have hd (x : ℝ) := (hasDerivAt_id x).sub ((directionX_derivative δ x y).div_const 100)
  apply monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
  intro x
  rw [(hd x).deriv]
  have hb := directionX_derivative_le (x := x) (y := y) hδ
  linarith

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem directionX_left_boundary {δ y : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) :
    directionX δ 1 (-(3 / 100)) y ≤ 0 := by
  have he : 0 ≤ 1 - Real.exp (-y ^ 2) := by
    have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
    linarith
  have hbase := mul_nonneg (tanhSlope_pos (-(3 / 100 : ℝ))).le he
  have hb := (abs_le.mp (abs_mul_le_one
    (show |tanhSlope (-(3 / 100 : ℝ))| ≤ 1 by
      rw [abs_of_pos (tanhSlope_pos _)]; exact tanhSlope_le_one _)
    (Real.abs_tanh_lt_one y).le)).2
  have hm := mul_le_mul_of_nonneg_left hb hδ.1
  dsimp [directionX, horizontal]
  nlinarith [hδ.2]

theorem directionX_anchor_boundary {δ s y : ℝ} (hδ : 0 ≤ δ)
    (hs : (4 / 25 : ℝ) ≤ s) (hy : y ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    0 ≤ directionX δ 1 s y := by
  have he0 : 0 ≤ 1 - Real.exp (-y ^ 2) := by
    have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
    linarith
  have he1 : 1 - Real.exp (-y ^ 2) ≤ 1 / 100 := by
    have h := Real.add_one_le_exp (-y ^ 2)
    nlinarith [hy.1, hy.2]
  have hm := mul_le_mul (tanhSlope_le_one s) he1 he0 (by norm_num : (0 : ℝ) ≤ 1)
  have hcorr := mul_nonneg (mul_nonneg hδ (tanhSlope_pos s).le) (tanh_nonneg hy.1)
  dsimp [directionX, horizontal]
  nlinarith

theorem phaseStep_initial_region {δ s x y : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000))
    (hs : s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50))
    (hx : x ∈ Set.Icc (-(3 / 100 : ℝ)) s) (hy : y ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    (phaseStep δ 1 s (x, y)).1 ∈ Set.Icc (-(3 / 100 : ℝ)) s ∧
      0 ≤ (phaseStep δ 1 s (x, y)).2 := by
  have hm := monotone_phaseStep_x (show δ ∈ Set.Icc (0 : ℝ) 1 from
    ⟨hδ.1, by linarith [hδ.2]⟩) s y
  have hlo := hm hx.1
  have hhi := hm hx.2
  have hleft := directionX_left_boundary (y := y) hδ
  have hright := directionX_anchor_boundary hδ.1 hs.1 hy
  have hg := phaseStep_initial_growth hδ.1 (by linarith [hs.1]) hx hy
  dsimp [phaseStep] at hlo hhi hg ⊢
  exact ⟨⟨by linarith, by linarith⟩, by nlinarith [hy.1]⟩

/-- The narrow strip is valid through every step before the first height crossing. -/
theorem phasePath_initial_region {δ s : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000))
    (hs : s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50)) (k : ℕ)
    (hbelow : ∀ j, j < k → (phasePath δ 1 s j).2 ≤ 1 / 10) :
    (phasePath δ 1 s k).1 ∈ Set.Icc (-(3 / 100 : ℝ)) s ∧
      0 ≤ (phasePath δ 1 s k).2 := by
  induction k with
  | zero => simp only [phasePath]; exact ⟨⟨by linarith [hs.1], le_rfl⟩, le_rfl⟩
  | succ k ih =>
    have hp := ih (fun j hj => hbelow j (by omega))
    have hstep := phaseStep_initial_region hδ hs hp.1 ⟨hp.2, hbelow k (by omega)⟩
    simpa only [phasePath, Prod.mk.eta] using hstep

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem concaveOn_tanh_nonneg : ConcaveOn ℝ (Set.Ici (0 : ℝ)) Real.tanh := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici (0 : ℝ)) continuous_tanh.continuousOn
    (fun x _ => (hasDerivAt_tanhSlope_value x).hasDerivWithinAt)
    (fun x _ => (hasDerivAt_tanhSlope x).hasDerivWithinAt)
  intro x hx
  have hx0 : 0 ≤ x := interior_subset hx
  have hp := mul_nonneg (tanh_nonneg hx0) (tanhSlope_pos x).le
  nlinarith

theorem tanh_nine_fifths_lower : (189 / 200 : ℝ) ≤ Real.tanh (9 / 5) := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 18 / 5) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  have he : (389 / 11 : ℝ) ≤ Real.exp (18 / 5) := by linarith
  have hsq : Real.exp (18 / 5 : ℝ) = Real.exp (9 / 5 : ℝ) ^ 2 := by
    rw [show (18 / 5 : ℝ) = 9 / 5 + 9 / 5 by ring, Real.exp_add, pow_two]
  rw [hsq] at he
  have hprod : Real.exp (-(9 / 5 : ℝ)) * Real.exp (9 / 5 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [Real.tanh_eq]
  apply (le_div_iff₀ (add_pos (Real.exp_pos _) (Real.exp_pos _))).mpr
  apply (mul_le_mul_iff_of_pos_right (Real.exp_pos (9 / 5 : ℝ))).mp
  nlinarith

theorem tanh_phase_two_lower {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) (9 / 5)) :
    (21 / 40 : ℝ) * y ≤ Real.tanh y := by
  have ha : 0 ≤ 1 - 5 * y / 9 := by linarith [hy.2]
  have hb : 0 ≤ 5 * y / 9 := by linarith [hy.1]
  have h := concaveOn_tanh_nonneg.2 (show (0 : ℝ) ∈ Set.Ici 0 by simp)
    (show (9 / 5 : ℝ) ∈ Set.Ici 0 by norm_num) ha hb (by ring)
  have harg : (5 * y / 9) * (9 / 5) = y := by ring
  simp only [smul_eq_mul, Real.tanh_zero, mul_zero, zero_add, harg] at h
  have hm := mul_le_mul_of_nonneg_left tanh_nine_fifths_lower hb
  nlinarith

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem phasePath_geometric_seed {δ s : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000))
    (hs : s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50)) (n : ℕ)
    (hbelow : ∀ j, j < 2 + n → (phasePath δ 1 s j).2 ≤ 1 / 10) :
    (1009 / 1000 : ℝ) ^ n * ((16 / 1000000 : ℝ) * δ) ≤ (phasePath δ 1 s (2 + n)).2 := by
  induction n with
  | zero => simpa using phasePath_escape_seed hδ.1 hs
  | succ n ih =>
    have hp := ih (fun j hj => hbelow j (by omega))
    have hr := phasePath_initial_region hδ hs (2 + n) (fun j hj => hbelow j (by omega))
    have hg := phaseStep_initial_growth hδ.1 (by linarith [hs.1]) hr.1
      ⟨hr.2, hbelow (2 + n) (by omega)⟩
    have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 1009 / 1000)
    change (1009 / 1000 : ℝ) * (phasePath δ 1 s (2 + n)).2 ≤
      (phasePath δ 1 s ((2 + n) + 1)).2 at hg
    rw [pow_succ, Nat.add_succ]
    nlinarith

theorem phasePath_crosses_of_power {δ s : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000))
    (hs : s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50)) (n : ℕ)
    (hpow : (1 / 10 : ℝ) ≤ (1009 / 1000 : ℝ) ^ n * ((16 / 1000000 : ℝ) * δ)) :
    ∃ j, j ≤ 2 + n ∧ (1 / 10 : ℝ) ≤ (phasePath δ 1 s j).2 := by
  by_contra h
  push Not at h
  have hg := phasePath_geometric_seed hδ hs n (fun j hj => (h j (by omega)).le)
  have he := h (2 + n) le_rfl
  linarith

theorem power_ceil_log_ge {a b : ℝ} (ha : 0 < a) (hb : 1 < b) :
    a ≤ b ^ ⌈Real.log a / Real.log b⌉₊ := by
  have hb0 : 0 < b := by linarith
  have hlog := Real.log_pos hb
  have hceil := Nat.le_ceil (Real.log a / Real.log b)
  have he := (div_le_iff₀ hlog).mp hceil
  have hexp := Real.exp_le_exp.mpr he
  simpa only [Real.exp_log ha, Real.exp_nat_mul, Real.exp_log hb0] using hexp

/-- The first transverse threshold is reached within an explicit logarithmic number of steps. -/
theorem phasePath_first_crossing {δ s : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 1000000)
    (hs : s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50)) :
    ∃ j, j ≤ 2 + ⌈Real.log ((1 / 10 : ℝ) / ((16 / 1000000 : ℝ) * δ)) /
      Real.log (1009 / 1000 : ℝ)⌉₊ ∧ (1 / 10 : ℝ) ≤ (phasePath δ 1 s j).2 := by
  have hseed : 0 < (16 / 1000000 : ℝ) * δ := by positivity
  have hp := power_ceil_log_ge
    (show 0 < (1 / 10 : ℝ) / ((16 / 1000000 : ℝ) * δ) by positivity)
    (show (1 : ℝ) < 1009 / 1000 by norm_num)
  exact phasePath_crosses_of_power ⟨hδ0.le, hδ1⟩ hs _ ((div_le_iff₀ hseed).mp hp)

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem correctionY_abs_le_two (s x y : ℝ) :
    |Real.tanh x * tanhSlope y - Real.tanh s| ≤ 2 := by
  have hp := abs_mul_le_one (Real.abs_tanh_lt_one x).le
    (show |tanhSlope y| ≤ 1 by rw [abs_of_pos (tanhSlope_pos y)]; exact tanhSlope_le_one y)
  have ht := (Real.abs_tanh_lt_one s).le
  exact (abs_sub _ _).trans (by linarith)

theorem vertical_second_bound {x y : ℝ} (hx : -(3 / 100 : ℝ) ≤ x)
    (hy : y ∈ Set.Icc (0 : ℝ) (9 / 5)) : vertical x y ≤ -(19 / 500 : ℝ) * y := by
  have ht : -(3 / 100 : ℝ) ≤ Real.tanh x := by
    have h := (abs_le.mp (abs_tanh_le_abs (-(3 / 100 : ℝ)))).1
    have hm := monotone_tanh hx
    rw [Real.tanh_neg] at hm
    norm_num at h
    linarith
  have he0 := (Real.exp_pos (-y ^ 2)).le
  have he1 : Real.exp (-y ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
  have hm := mul_le_mul_of_nonneg_right ht he0
  have he : -(3 / 100 : ℝ) ≤ Real.tanh x * Real.exp (-y ^ 2) := by nlinarith
  have hmy := mul_le_mul_of_nonneg_right he hy.1
  have htan := tanh_phase_two_lower hy
  dsimp [vertical]
  nlinarith

theorem phaseStep_second_growth {δ s x y : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (hx : -(3 / 100 : ℝ) ≤ x)
    (hy : y ∈ Set.Icc (1 / 10 : ℝ) (9 / 5)) :
    (100037 / 100000 : ℝ) * y ≤ (phaseStep δ 1 s (x, y)).2 := by
  have hv := vertical_second_bound hx ⟨by linarith [hy.1], hy.2⟩
  have hc := mul_le_mul_of_nonneg_left (abs_le.mp (correctionY_abs_le_two s x y)).2 hδ.1
  dsimp [phaseStep, directionY]
  nlinarith [hδ.2, hy.1]

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem phaseStep_prethreshold_upper {δ s x y : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000))
    (hy : y ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    (phaseStep δ 1 s (x, y)).2 ≤ 13 / 100 := by
  have he0 := (Real.exp_pos (-y ^ 2)).le
  have he1 : Real.exp (-y ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
  have hm := mul_le_mul_of_nonneg_right (Real.tanh_lt_one x).le he0
  have hp : Real.tanh x * Real.exp (-y ^ 2) ≤ 1 := by linarith
  have hpy := mul_le_mul_of_nonneg_right hp hy.1
  have ht := (Real.tanh_lt_one y).le
  have hc := mul_le_mul_of_nonneg_left (abs_le.mp (correctionY_abs_le_two s x y)).1 hδ.1
  dsimp [phaseStep, directionY, vertical]
  nlinarith [hδ.2, hy.1, hy.2]

/-- The earliest height crossing enters the bounded second-phase rectangle. -/
theorem phasePath_first_entry {δ s : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 1000000)
    (hs : s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50)) :
    ∃ j, j ≤ 2 + ⌈Real.log ((1 / 10 : ℝ) / ((16 / 1000000 : ℝ) * δ)) /
      Real.log (1009 / 1000 : ℝ)⌉₊ ∧
      (phasePath δ 1 s j).1 ∈ Set.Icc (-(3 / 100 : ℝ)) (21 / 100) ∧
      (phasePath δ 1 s j).2 ∈ Set.Icc (1 / 10 : ℝ) (21 / 10) := by
  obtain ⟨J, hJ, hcross⟩ := phasePath_first_crossing hδ0 hδ1 hs
  have hex : ∃ j, (1 / 10 : ℝ) ≤ (phasePath δ 1 s j).2 := ⟨J, hcross⟩
  have hmin := Nat.find_min' hex hcross
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro he
    rw [he] at hspec
    norm_num [phasePath] at hspec
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hbefore (m : ℕ) (hm : m < k + 1) : (phasePath δ 1 s m).2 < 1 / 10 := by
    apply lt_of_not_ge
    exact Nat.find_min hex (by omega)
  have hr := phasePath_initial_region ⟨hδ0.le, hδ1⟩ hs k
    (fun m hm => (hbefore m (by omega)).le)
  have hstep := phaseStep_initial_region ⟨hδ0.le, hδ1⟩ hs hr.1
    ⟨hr.2, (hbefore k (by omega)).le⟩
  have hu := phaseStep_prethreshold_upper (s := s) (x := (phasePath δ 1 s k).1)
    ⟨hδ0.le, hδ1⟩ ⟨hr.2, (hbefore k (by omega)).le⟩
  change (phasePath δ 1 s (k + 1)).1 ∈ Set.Icc (-(3 / 100 : ℝ)) s ∧
    0 ≤ (phasePath δ 1 s (k + 1)).2 at hstep
  change (phasePath δ 1 s (k + 1)).2 ≤ 13 / 100 at hu
  rw [hk] at hspec
  refine ⟨k + 1, by omega, ⟨hstep.1.1, ?_⟩, ⟨hspec, ?_⟩⟩
  · linarith [hstep.1.2, hs.2]
  · linarith

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem directionY_derivative (δ s x y : ℝ) :
    HasDerivAt (fun z => directionY δ 1 s x z)
      (1 - 2 * tanhSlope y - 2 / 5 * (Real.tanh x * (1 - 2 * y ^ 2) * Real.exp (-y ^ 2)) -
        2 * δ * (Real.tanh x * Real.tanh y * tanhSlope y)) y := by
  have he := (((hasDerivAt_id y).pow 2).neg).exp
  have hv := ((hasDerivAt_id y).sub ((hasDerivAt_tanhSlope_value y).const_mul 2)).sub
    (((hasDerivAt_id y).mul he).const_mul (2 / 5 * Real.tanh x))
  have hc := (((hasDerivAt_tanhSlope y).const_mul (Real.tanh x)).sub_const
    (Real.tanh s)).const_mul δ
  convert hv.add hc using 1
  · funext z
    simp [directionY, vertical]
    ring
  · dsimp
    ring

theorem directionY_derivative_le {δ x y : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) (21 / 10)) :
    1 - 2 * tanhSlope y - 2 / 5 * (Real.tanh x * (1 - 2 * y ^ 2) * Real.exp (-y ^ 2)) -
        2 * δ * (Real.tanh x * Real.tanh y * tanhSlope y) ≤ 7 := by
  have hpoly : |1 - 2 * y ^ 2| ≤ 10 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hy.1, hy.2, sq_nonneg y]
  have ha : |Real.tanh x * (1 - 2 * y ^ 2)| ≤ 10 := by
    rw [abs_mul]
    simpa using mul_le_mul (Real.abs_tanh_lt_one x).le hpoly
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have he : |Real.exp (-y ^ 2)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
  have hb : |Real.tanh x * (1 - 2 * y ^ 2) * Real.exp (-y ^ 2)| ≤ 10 := by
    rw [abs_mul]
    simpa using mul_le_mul ha he (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 10)
  have hc := abs_mul_le_one (abs_mul_le_one (Real.abs_tanh_lt_one x).le
    (Real.abs_tanh_lt_one y).le)
    (show |tanhSlope y| ≤ 1 by rw [abs_of_pos (tanhSlope_pos y)]; exact tanhSlope_le_one y)
  have hm := mul_le_mul_of_nonneg_left (abs_le.mp hc).1 hδ.1
  nlinarith [(abs_le.mp hb).1, (tanhSlope_pos y).le, hδ.2]

theorem monotoneOn_phaseStep_y {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (s x : ℝ) :
    MonotoneOn (fun y => (phaseStep δ 1 s (x, y)).2) (Set.Icc (0 : ℝ) (21 / 10)) := by
  have hd (y : ℝ) := (hasDerivAt_id y).sub ((directionY_derivative δ s x y).div_const 100)
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) (21 / 10))
    ((continuous_iff_continuousAt.mpr (fun y => (hd y).continuousAt)).continuousOn)
    (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
  intro y hy
  rw [(hd y).deriv]
  have hb := directionY_derivative_le (x := x) hδ (interior_subset hy)
  linarith

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem directionX_right_boundary {δ y : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) :
    0 ≤ directionX δ 1 (21 / 100) y := by
  have he0 : 0 ≤ 1 - Real.exp (-y ^ 2) := by
    have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
    linarith
  have he1 : 1 - Real.exp (-y ^ 2) ≤ 1 := by linarith [Real.exp_pos (-y ^ 2)]
  have hb := mul_le_mul (tanhSlope_le_one (21 / 100)) he1 he0 (by norm_num : (0 : ℝ) ≤ 1)
  have hc := (abs_le.mp (abs_mul_le_one
    (show |tanhSlope (21 / 100 : ℝ)| ≤ 1 by
      rw [abs_of_pos (tanhSlope_pos _)]; exact tanhSlope_le_one _)
    (Real.abs_tanh_lt_one y).le)).1
  have hm := mul_le_mul_of_nonneg_left hc hδ.1
  dsimp [directionX, horizontal]
  nlinarith [hδ.2]

theorem exp_upper_height : Real.exp (-(21 / 10 : ℝ) ^ 2) ≤ 1 / 10 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 441 / 100) 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  have he : (10 : ℝ) ≤ Real.exp (441 / 100) := by linarith
  have hp : Real.exp (-(441 / 100 : ℝ)) * Real.exp (441 / 100 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-(441 / 100 : ℝ))).le
  norm_num only [show -(21 / 10 : ℝ) ^ 2 = -(441 / 100 : ℝ) by norm_num]
  nlinarith

theorem directionY_upper_boundary {δ s x : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (hx : x ≤ 21 / 100) :
    0 ≤ directionY δ 1 s x (21 / 10) := by
  have ht : Real.tanh x ≤ 21 / 100 := by
    have h := (abs_le.mp (abs_tanh_le_abs (21 / 100 : ℝ))).2
    have hm := monotone_tanh hx
    norm_num at h
    linarith
  have hp := mul_le_mul ht exp_upper_height
    (Real.exp_pos (-(21 / 10 : ℝ) ^ 2)).le (by norm_num : (0 : ℝ) ≤ 21 / 100)
  have hy := (Real.tanh_lt_one (21 / 10 : ℝ)).le
  have hc := mul_le_mul_of_nonneg_left (abs_le.mp (correctionY_abs_le_two s x (21 / 10))).1 hδ.1
  dsimp [directionY, vertical]
  nlinarith [hδ.2]

/-- Every rectangle with lower height between 0.1 and 1.8 is preserved by the update. -/
theorem phaseStep_rectangle {δ s x y a : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (ha : a ∈ Set.Icc (1 / 10 : ℝ) (9 / 5))
    (hx : x ∈ Set.Icc (-(3 / 100 : ℝ)) (21 / 100)) (hy : y ∈ Set.Icc a (21 / 10)) :
    (phaseStep δ 1 s (x, y)).1 ∈ Set.Icc (-(3 / 100 : ℝ)) (21 / 100) ∧
      (phaseStep δ 1 s (x, y)).2 ∈ Set.Icc a (21 / 10) := by
  have hd : δ ∈ Set.Icc (0 : ℝ) 1 := ⟨hδ.1, by linarith [hδ.2]⟩
  have hmx := monotone_phaseStep_x hd s y
  have hxl := hmx hx.1
  have hxr := hmx hx.2
  have hleft := directionX_left_boundary (y := y) hδ
  have hright := directionX_right_boundary (y := y) hδ
  have hmy := monotoneOn_phaseStep_y hd s x
  have hy' : y ∈ Set.Icc (0 : ℝ) (21 / 10) := ⟨by linarith [hy.1, ha.1], hy.2⟩
  have ha' : a ∈ Set.Icc (0 : ℝ) (21 / 10) := ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hyl := hmy ha' hy' hy.1
  have hyr := hmy hy' (show (21 / 10 : ℝ) ∈ Set.Icc 0 (21 / 10) by norm_num) hy.2
  have hg := phaseStep_second_growth (s := s) hδ hx.1 ha
  have hupper := directionY_upper_boundary (s := s) hδ hx.2
  dsimp [phaseStep] at hxl hxr hyl hyr hg ⊢
  exact ⟨⟨by linarith, by linarith⟩, ⟨by nlinarith [ha.1], by linarith⟩⟩

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem phasePath_stays_rectangle {δ s a : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (ha : a ∈ Set.Icc (1 / 10 : ℝ) (9 / 5))
    (j : ℕ) (hstart : (phasePath δ 1 s j).1 ∈ Set.Icc (-(3 / 100 : ℝ)) (21 / 100) ∧
      (phasePath δ 1 s j).2 ∈ Set.Icc a (21 / 10)) (n : ℕ) :
    (phasePath δ 1 s (j + n)).1 ∈ Set.Icc (-(3 / 100 : ℝ)) (21 / 100) ∧
      (phasePath δ 1 s (j + n)).2 ∈ Set.Icc a (21 / 10) := by
  induction n with
  | zero => simpa using hstart
  | succ n ih =>
    have h := phaseStep_rectangle (s := s) hδ ha ih.1 ih.2
    rw [show j + (n + 1) = (j + n) + 1 by omega]
    exact h

theorem second_growth_power : (18 : ℝ) ≤ (100037 / 100000 : ℝ) ^ 8000 := by
  have h := one_add_mul_le_pow (a := (37 / 100000 : ℝ)) (by norm_num) 100
  have h100 : (1037 / 1000 : ℝ) ≤ (100037 / 100000 : ℝ) ^ 100 := by
    convert h using 1 <;> norm_num
  have h1000 : (23 / 16 : ℝ) ≤ (100037 / 100000 : ℝ) ^ 1000 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1037 / 1000) h100 10
    have hc : (23 / 16 : ℝ) ≤ (1037 / 1000 : ℝ) ^ 10 := by norm_num
    exact hc.trans (by simpa only [← pow_mul] using hp)
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 23 / 16) h1000 8
  have hc : (18 : ℝ) ≤ (23 / 16 : ℝ) ^ 8 := by norm_num
  exact hc.trans (by simpa only [← pow_mul] using hp)

theorem phasePath_second_crossing {δ s : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (j : ℕ)
    (hstart : (phasePath δ 1 s j).1 ∈ Set.Icc (-(3 / 100 : ℝ)) (21 / 100) ∧
      (phasePath δ 1 s j).2 ∈ Set.Icc (1 / 10 : ℝ) (21 / 10)) :
    ∃ n, n ≤ 8000 ∧ (9 / 5 : ℝ) ≤ (phasePath δ 1 s (j + n)).2 := by
  have hr := phasePath_stays_rectangle hδ
    (show (1 / 10 : ℝ) ∈ Set.Icc (1 / 10) (9 / 5) by norm_num) j hstart
  by_contra h
  push Not at h
  have hg (n : ℕ) (hn : n ≤ 8000) :
      (100037 / 100000 : ℝ) ^ n * (1 / 10 : ℝ) ≤ (phasePath δ 1 s (j + n)).2 := by
    induction n with
    | zero => simpa using hstart.2.1
    | succ n ih =>
      have hp := ih (by omega)
      have hb := phaseStep_second_growth (s := s) hδ (hr n).1.1
        ⟨(hr n).2.1, (h n (by omega)).le⟩
      have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 100037 / 100000)
      change (100037 / 100000 : ℝ) * (phasePath δ 1 s (j + n)).2 ≤
        (phasePath δ 1 s ((j + n) + 1)).2 at hb
      rw [pow_succ, Nat.add_succ]
      nlinarith
  have he := hg 8000 le_rfl
  have hn := h 8000 le_rfl
  have hp := mul_le_mul_of_nonneg_right second_growth_power (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hl : (9 / 5 : ℝ) ≤ (phasePath δ 1 s (j + 8000)).2 := by
    convert hp.trans he using 1
    norm_num
  exact (not_lt_of_ge hl) hn

/-- At the common 8000-step deadline, the trajectory is permanently above height 1.8. -/
theorem phasePath_second_complete {δ s : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (j : ℕ)
    (hstart : (phasePath δ 1 s j).1 ∈ Set.Icc (-(3 / 100 : ℝ)) (21 / 100) ∧
      (phasePath δ 1 s j).2 ∈ Set.Icc (1 / 10 : ℝ) (21 / 10)) :
    (phasePath δ 1 s (j + 8000)).1 ∈ Set.Icc (-(3 / 100 : ℝ)) (21 / 100) ∧
      (phasePath δ 1 s (j + 8000)).2 ∈ Set.Icc (9 / 5 : ℝ) (21 / 10) := by
  obtain ⟨n, hn, hc⟩ := phasePath_second_crossing hδ j hstart
  have hr := phasePath_stays_rectangle hδ
    (show (1 / 10 : ℝ) ∈ Set.Icc (1 / 10) (9 / 5) by norm_num) j hstart n
  have hs := phasePath_stays_rectangle hδ
    (show (9 / 5 : ℝ) ∈ Set.Icc (1 / 10) (9 / 5) by norm_num)
    (j + n) ⟨hr.1, hc, hr.2.2⟩ (8000 - n)
  simpa only [Nat.add_assoc, Nat.add_sub_of_le hn] using hs

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem exp_high_height {y : ℝ} (hy : (9 / 5 : ℝ) ≤ y) : Real.exp (-y ^ 2) ≤ 1 / 25 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 81 / 25) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  have he : (25 : ℝ) ≤ Real.exp (81 / 25) := by linarith
  have hp : Real.exp (-(81 / 25 : ℝ)) * Real.exp (81 / 25 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-(81 / 25 : ℝ))).le
  have hb : Real.exp (-(81 / 25 : ℝ)) ≤ 1 / 25 := by nlinarith
  exact (Real.exp_le_exp.mpr (show -y ^ 2 ≤ -(81 / 25 : ℝ) by nlinarith)).trans hb

theorem directionX_return_left {δ y : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (hy : (9 / 5 : ℝ) ≤ y) :
    directionX δ 1 (4 / 25) y ≤ -(7 / 1000 : ℝ) := by
  have he := exp_high_height hy
  have hs := tanhSlope_lower (4 / 25 : ℝ)
  have he0 : 0 ≤ 1 - Real.exp (-y ^ 2) := by linarith
  have hp := mul_le_mul (show (609 / 625 : ℝ) ≤ tanhSlope (4 / 25) by norm_num at hs ⊢; exact hs)
    (show (24 / 25 : ℝ) ≤ 1 - Real.exp (-y ^ 2) by linarith)
    (by norm_num : (0 : ℝ) ≤ 24 / 25) (tanhSlope_pos (4 / 25 : ℝ)).le
  have hc := (abs_le.mp (abs_mul_le_one
    (show |tanhSlope (4 / 25 : ℝ)| ≤ 1 by
      rw [abs_of_pos (tanhSlope_pos _)]; exact tanhSlope_le_one _)
    (Real.abs_tanh_lt_one y).le)).2
  have hm := mul_le_mul_of_nonneg_left hc hδ.1
  dsimp [directionX, horizontal]
  nlinarith [hδ.2]

theorem directionX_return_right {δ y : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) :
    (57 / 10000 : ℝ) ≤ directionX δ 1 (9 / 50) y := by
  have ht : (17 / 100 : ℝ) ≤ Real.tanh (9 / 50) := by
    have h := tanh_cubic_lower (by norm_num : (0 : ℝ) ≤ 9 / 50)
    norm_num at h
    linarith
  have hs : tanhSlope (9 / 50 : ℝ) ≤ 9711 / 10000 := by
    dsimp [tanhSlope]
    nlinarith
  have he0 : 0 ≤ 1 - Real.exp (-y ^ 2) := by
    have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
    linarith
  have he1 : 1 - Real.exp (-y ^ 2) ≤ 1 := by linarith [Real.exp_pos (-y ^ 2)]
  have hp := mul_le_mul_of_nonneg_left he1 (tanhSlope_pos (9 / 50 : ℝ)).le
  have hc := (abs_le.mp (abs_mul_le_one
    (show |tanhSlope (9 / 50 : ℝ)| ≤ 1 by
      rw [abs_of_pos (tanhSlope_pos _)]; exact tanhSlope_le_one _)
    (Real.abs_tanh_lt_one y).le)).1
  have hm := mul_le_mul_of_nonneg_left hc hδ.1
  dsimp [directionX, horizontal]
  nlinarith [hδ.2]

theorem monotone_directionX {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (y : ℝ) :
    Monotone (fun x => directionX δ 1 x y) := by
  apply monotone_of_deriv_nonneg (fun x => (directionX_derivative δ x y).differentiableAt)
  intro x
  rw [(directionX_derivative δ x y).deriv]
  have ha : |Real.tanh x * tanhSlope x| ≤ 1 := abs_mul_le_one
    (Real.abs_tanh_lt_one x).le (by rw [abs_of_pos (tanhSlope_pos x)]; exact tanhSlope_le_one x)
  have he0 := (Real.exp_pos (-y ^ 2)).le
  have he1 : Real.exp (-y ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
  have he : |1 - Real.exp (-y ^ 2)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb := (abs_le.mp (abs_mul_le_one ha he)).1
  have hc := (abs_le.mp (abs_mul_le_one ha (Real.abs_tanh_lt_one y).le)).2
  have hm := mul_le_mul_of_nonneg_left hc hδ.1
  nlinarith [hδ.2]

theorem phaseStep_return_lower {δ s x y : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (hy : (9 / 5 : ℝ) ≤ y) :
    min (4 / 25 : ℝ) (x + 7 / 100000) ≤ (phaseStep δ 1 s (x, y)).1 := by
  have hb := directionX_return_left hδ hy
  by_cases hx : x ≤ 4 / 25
  · have hm := monotone_directionX hδ y hx
    have hp : x + 7 / 100000 ≤ (phaseStep δ 1 s (x, y)).1 := by
      dsimp [phaseStep]
      linarith
    exact (min_le_right _ _).trans hp
  · have hm := monotone_phaseStep_x
      (show δ ∈ Set.Icc (0 : ℝ) 1 from ⟨hδ.1, by linarith [hδ.2]⟩) s y (le_of_not_ge hx)
    have hp : (4 / 25 : ℝ) ≤ (phaseStep δ 1 s (x, y)).1 := by
      dsimp [phaseStep] at hm ⊢
      linarith
    exact (min_le_left _ _).trans hp

theorem phaseStep_return_upper {δ s x y : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) :
    (phaseStep δ 1 s (x, y)).1 ≤ max (9 / 50 : ℝ) (x - 57 / 1000000) := by
  have hb := directionX_return_right (y := y) hδ
  by_cases hx : (9 / 50 : ℝ) ≤ x
  · have hm := monotone_directionX hδ y hx
    have hp : (phaseStep δ 1 s (x, y)).1 ≤ x - 57 / 1000000 := by
      dsimp [phaseStep]
      linarith
    exact hp.trans (le_max_right _ _)
  · have hm := monotone_phaseStep_x
      (show δ ∈ Set.Icc (0 : ℝ) 1 from ⟨hδ.1, by linarith [hδ.2]⟩) s y (le_of_not_ge hx)
    have hp : (phaseStep δ 1 s (x, y)).1 ≤ (9 / 50 : ℝ) := by
      dsimp [phaseStep] at hm ⊢
      linarith
    exact hp.trans (le_max_left _ _)

end BirchNonIIDInstability

namespace BirchNonIIDInstability

theorem min_cap_add (a b c : ℝ) (hc : 0 ≤ c) :
    min a (min a b + c) = min a (b + c) := by
  by_cases h : b ≤ a
  · rw [min_eq_right h]
  · have hab : a ≤ b := le_of_not_ge h
    rw [min_eq_left hab, min_eq_left (by linarith), min_eq_left (by linarith)]

theorem max_cap_sub (a b c : ℝ) (hc : 0 ≤ c) :
    max a (max a b - c) = max a (b - c) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h]
  · have hba : b ≤ a := le_of_not_ge h
    rw [max_eq_left hba, max_eq_left (by linarith), max_eq_left (by linarith)]

theorem phasePath_return_bounds {δ s : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (j : ℕ)
    (hstart : (phasePath δ 1 s j).1 ∈ Set.Icc (-(3 / 100 : ℝ)) (21 / 100) ∧
      (phasePath δ 1 s j).2 ∈ Set.Icc (9 / 5 : ℝ) (21 / 10)) (n : ℕ) :
    min (4 / 25 : ℝ) (-(3 / 100 : ℝ) + (n : ℝ) * (7 / 100000)) ≤ (phasePath δ 1 s (j + n)).1 ∧
      (phasePath δ 1 s (j + n)).1 ≤ max (9 / 50 : ℝ) ((21 / 100 : ℝ) - (n : ℝ) * (57 / 1000000)) := by
  have hr := phasePath_stays_rectangle hδ
    (show (9 / 5 : ℝ) ∈ Set.Icc (1 / 10) (9 / 5) by norm_num) j hstart
  induction n with
  | zero => norm_num; exact ⟨hstart.1.1, hstart.1.2⟩
  | succ n ih =>
    have hl := phaseStep_return_lower (s := s) (x := (phasePath δ 1 s (j + n)).1) hδ (hr n).2.1
    have hu := phaseStep_return_upper (s := s) (x := (phasePath δ 1 s (j + n)).1)
      (y := (phasePath δ 1 s (j + n)).2) hδ
    change min (4 / 25 : ℝ) ((phasePath δ 1 s (j + n)).1 + 7 / 100000) ≤
      (phasePath δ 1 s ((j + n) + 1)).1 at hl
    change (phasePath δ 1 s ((j + n) + 1)).1 ≤
      max (9 / 50 : ℝ) ((phasePath δ 1 s (j + n)).1 - 57 / 1000000) at hu
    have hl' := (min_le_min_left (4 / 25 : ℝ)
      (add_le_add ih.1 (le_refl (7 / 100000 : ℝ)))).trans hl
    have hu' := hu.trans (max_le_max_left (9 / 50 : ℝ) (sub_le_sub_right ih.2 (57 / 1000000)))
    rw [min_cap_add _ _ _ (by norm_num)] at hl'
    rw [max_cap_sub _ _ _ (by norm_num)] at hu'
    have hL : -(3 / 100 : ℝ) + ((n + 1 : ℕ) : ℝ) * (7 / 100000) =
      (-(3 / 100 : ℝ) + (n : ℝ) * (7 / 100000)) + 7 / 100000 := by push_cast; ring
    have hU : (21 / 100 : ℝ) - ((n + 1 : ℕ) : ℝ) * (57 / 1000000) =
      ((21 / 100 : ℝ) - (n : ℝ) * (57 / 1000000)) - 57 / 1000000 := by push_cast; ring
    rw [show j + (n + 1) = (j + n) + 1 by omega, hL, hU]
    exact ⟨hl', hu'⟩

theorem phasePath_return_complete {δ s : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (j : ℕ)
    (hstart : (phasePath δ 1 s j).1 ∈ Set.Icc (-(3 / 100 : ℝ)) (21 / 100) ∧
      (phasePath δ 1 s j).2 ∈ Set.Icc (9 / 5 : ℝ) (21 / 10)) :
    (phasePath δ 1 s (j + 3000)).1 ∈ Set.Icc (4 / 25 : ℝ) (9 / 50) := by
  have h := phasePath_return_bounds hδ j hstart 3000
  norm_num at h
  exact h

theorem phasePath_return_after {δ s : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (j n : ℕ) (hn : 3000 ≤ n)
    (hstart : (phasePath δ 1 s j).1 ∈ Set.Icc (-(3 / 100 : ℝ)) (21 / 100) ∧
      (phasePath δ 1 s j).2 ∈ Set.Icc (9 / 5 : ℝ) (21 / 10)) :
    (phasePath δ 1 s (j + n)).1 ∈ Set.Icc (4 / 25 : ℝ) (9 / 50) := by
  have h := phasePath_return_bounds hδ j hstart n
  have hn' : (3000 : ℝ) ≤ n := by exact_mod_cast hn
  rw [min_eq_left (show (4 / 25 : ℝ) ≤ -(3 / 100 : ℝ) + (n : ℝ) * (7 / 100000) by linarith),
    max_eq_left (show (21 / 100 : ℝ) - (n : ℝ) * (57 / 1000000) ≤ 9 / 50 by linarith)] at h
  exact h

end BirchNonIIDInstability

namespace BirchNonIIDInstability

noncomputable def instabilityHorizon (δ : ℝ) : ℕ :=
  2 + ⌈Real.log ((1 / 10 : ℝ) / ((16 / 1000000 : ℝ) * δ)) /
    Real.log (1009 / 1000 : ℝ)⌉₊ + 11000

theorem phasePath_maps_anchor_interval {δ s : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 1000000)
    (hs : s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50)) :
    (phasePath δ 1 s (instabilityHorizon δ)).1 ∈ Set.Icc (4 / 25 : ℝ) (9 / 50) := by
  obtain ⟨j, hj, hentry⟩ := phasePath_first_entry hδ0 hδ1 hs
  have hhigh := phasePath_second_complete ⟨hδ0.le, hδ1⟩ j hentry
  let B := 2 + ⌈Real.log ((1 / 10 : ℝ) / ((16 / 1000000 : ℝ) * δ)) /
    Real.log (1009 / 1000 : ℝ)⌉₊
  have hjB : j ≤ B := hj
  have hr := phasePath_return_after ⟨hδ0.le, hδ1⟩ (j + 8000) ((B - j) + 3000)
    (by omega) hhigh
  have he : (j + 8000) + ((B - j) + 3000) = instabilityHorizon δ := by
    change (j + 8000) + ((B - j) + 3000) = B + 11000
    omega
  rwa [he] at hr

/-- A nonzero server anchor fixed by one full endpoint-averaging round of the scalar recurrence. -/
theorem phasePath_anchor_fixedPoint {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 1000000) :
    ∃ s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50),
      (phasePath δ 1 s (instabilityHorizon δ)).1 = s := by
  let T := fun s => (phasePath δ 1 s (instabilityHorizon δ)).1
  have hT : Continuous T := (continuous_phasePath δ 1 (instabilityHorizon δ)).fst
  have hlo := phasePath_maps_anchor_interval hδ0 hδ1
    (show (4 / 25 : ℝ) ∈ Set.Icc (4 / 25) (9 / 50) by norm_num)
  have hhi := phasePath_maps_anchor_interval hδ0 hδ1
    (show (9 / 50 : ℝ) ∈ Set.Icc (4 / 25) (9 / 50) by norm_num)
  have hmem : (0 : ℝ) ∈ Set.Icc ((4 / 25 : ℝ) - T (4 / 25)) ((9 / 50 : ℝ) - T (9 / 50)) := by
    exact ⟨by dsimp [T]; linarith [hlo.1], by dsimp [T]; linarith [hhi.2]⟩
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc (show (4 / 25 : ℝ) ≤ 9 / 50 by norm_num)
    (continuous_id.sub hT).continuousOn hmem
  exact ⟨s, hs, by dsimp [T] at he; linarith⟩

/-- Reflection turns the scalar fixed anchor into an exact two-client endpoint-mean fixed point. -/
theorem phasePath_mean_fixedPoint {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 1000000) :
    ∃ s ∈ Set.Icc (4 / 25 : ℝ) (9 / 50),
      (((phasePath δ 1 s (instabilityHorizon δ)).1 +
          (phasePath δ (-1) s (instabilityHorizon δ)).1) / 2,
        ((phasePath δ 1 s (instabilityHorizon δ)).2 +
          (phasePath δ (-1) s (instabilityHorizon δ)).2) / 2) = (s, 0) ∧
      (81 / 2500 : ℝ) ≤ horizontal s 0 ^ 2 + vertical s 0 ^ 2 := by
  obtain ⟨s, hs, hfix⟩ := phasePath_anchor_fixedPoint hδ0 hδ1
  have href := phasePath_reflection δ 1 s (instabilityHorizon δ)
  refine ⟨s, hs, ?_, ?_⟩
  · rw [href]
    dsimp [reflect]
    rw [hfix]
    apply Prod.ext <;> dsimp <;> ring
  · norm_num [horizontal, vertical]
    nlinarith [hs.1]

end BirchNonIIDInstability
