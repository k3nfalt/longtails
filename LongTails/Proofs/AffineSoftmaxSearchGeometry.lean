import LongTails.Proofs.AffineSoftmaxSearchTrace

namespace LongTails.Proofs.AffineSoftmaxSearchGeometry

lemma clamped_grid_step {floor cap : ℝ} (hf : 0 ≤ floor) (hc : 0 ≤ cap) (j : ℕ) :
    max floor (cap / 2 ^ (j + 1)) ≤ max floor (cap / 2 ^ j) ∧
      max floor (cap / 2 ^ j) ≤ 2 * max floor (cap / 2 ^ (j + 1)) := by
  rw [pow_succ, div_mul_eq_div_div]
  have hv : 0 ≤ cap / 2 ^ j := by positivity
  have hm : 0 ≤ max floor (cap / 2 ^ j / 2) := hf.trans (le_max_left _ _)
  constructor
  · exact max_le (le_max_left _ _) ((div_le_self hv (by norm_num : (1 : ℝ) ≤ 2)).trans (le_max_right _ _))
  · apply max_le
    · linarith [le_max_left floor (cap / 2 ^ j / 2)]
    · linarith [le_max_right floor (cap / 2 ^ j / 2)]

lemma halved_relative_width {lower upper : ℝ} (hlu : lower ≤ upper) (k : ℕ)
    (hw : upper - lower ≤ lower / 2 ^ k) :
    (lower + upper) / 2 - lower ≤ lower / 2 ^ (k + 1) ∧
      upper - (lower + upper) / 2 ≤ ((lower + upper) / 2) / 2 ^ (k + 1) := by
  have he : lower / (2 : ℝ) ^ (k + 1) = (lower / 2 ^ k) / 2 := by
    rw [pow_succ, div_mul_eq_div_div]
  have hl : (lower + upper) / 2 - lower ≤ lower / 2 ^ (k + 1) := by rw [he]; linarith
  refine ⟨hl, ?_⟩
  have hm : lower ≤ (lower + upper) / 2 := by linarith
  have hh := hl.trans (div_le_div_of_nonneg_right hm (by positivity : (0 : ℝ) ≤ 2 ^ (k + 1)))
  linarith

lemma interval_modulus_bound (d : ℝ → ℝ) {floor cap K lower upper a b : ℝ}
    (hf : 0 < floor) (hK : 0 ≤ K)
    (hl : floor ≤ lower) (hlu : lower ≤ upper) (hu : upper ≤ cap)
    (ha : a ∈ Set.Icc lower upper) (hb : b ∈ Set.Icc lower upper)
    (hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ K * |x - y| / min x y)
    (k : ℕ) (hw : upper - lower ≤ lower / 2 ^ k) :
    |d a - d b| ≤ K / 2 ^ k := by
  have hlpos : 0 < lower := hf.trans_le hl
  have habs : |a - b| ≤ upper - lower := by
    apply abs_le.mpr
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hmin : lower ≤ min a b := le_min ha.1 hb.1
  have hminpos : 0 < min a b := hlpos.trans_le hmin
  calc
    |d a - d b| ≤ K * |a - b| / min a b := hmod a ⟨hl.trans ha.1, ha.2.trans hu⟩
      b ⟨hl.trans hb.1, hb.2.trans hu⟩
    _ ≤ K * (upper - lower) / min a b := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left habs hK) hminpos.le
    _ ≤ K * (upper - lower) / lower := div_le_div_of_nonneg_left
      (mul_nonneg hK (sub_nonneg.mpr hlu)) hlpos hmin
    _ ≤ K * (lower / 2 ^ k) / lower := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw hK) hlpos.le
    _ = K / 2 ^ k := by field_simp

lemma narrow_bracket_midpoint (d : ℝ → ℝ) {floor cap K lower upper r : ℝ}
    (hf : 0 < floor) (hK : 0 ≤ K)
    (hl : floor ≤ lower) (hlu : lower ≤ upper) (hu : upper ≤ cap)
    (hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ K * |x - y| / min x y)
    (k : ℕ) (hw : upper - lower ≤ lower / 2 ^ k)
    (hs : K / 2 ^ k < r / 64)
    (hdl : 55 * r / 64 ≤ d lower) (hdu : d upper ≤ 57 * r / 64) :
    54 * r / 64 < d ((lower + upper) / 2) ∧ d ((lower + upper) / 2) < 58 * r / 64 := by
  have hm : (lower + upper) / 2 ∈ Set.Icc lower upper := by constructor <;> linarith
  have h1 := interval_modulus_bound d hf hK hl hlu hu hm ⟨le_rfl, hlu⟩ hmod k hw
  have h2 := interval_modulus_bound d hf hK hl hlu hu hm ⟨hlu, le_rfl⟩ hmod k hw
  have h1a := (abs_le.mp h1).1
  have h2a := (abs_le.mp h2).2
  constructor <;> linarith

lemma proximal_displacement_scaled_modulus {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E} {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    {μ : ℝ} (hμ : 0 < μ) (ν D G floor : ℝ) (y z : E) {u w : E}
    (hu : u ∈ C) (hw : w ∈ C)
    (humin : IsMinOn (LongTails.Proofs.RecursiveEnvelopeGeometry.regularized f μ y) C u)
    (hwmin : IsMinOn (LongTails.Proofs.RecursiveEnvelopeGeometry.regularized f ν z) C w)
    (hcenter : μ * ‖y - z‖ ≤ D * |μ - ν|) (hbound : ‖z - w‖ ≤ G / floor) :
    μ * |‖y - u‖ - ‖z - w‖| ≤ (2 * D + G / floor) * |μ - ν| := by
  have hp := LongTails.Proofs.AffineSoftmaxOuter.proximal_parameter_distance hf hg hμ ν y z hu hw humin hwmin
  have he : (y - u) - (z - w) = (y - z) - (u - w) := by module
  have hn := abs_norm_sub_norm_le (y - u) (z - w)
  rw [he] at hn
  have ht := hn.trans (norm_sub_le (y - z) (u - w))
  have hm := mul_le_mul_of_nonneg_left ht hμ.le
  have hb := mul_le_mul_of_nonneg_left hbound (abs_nonneg (μ - ν))
  nlinarith only [hp, hcenter, hm, hb]

lemma observed_crossing_lower {r d observed : ℝ}
    (he : |observed - min r d| ≤ r / 64) (hl : 7 * r / 8 ≤ observed) :
    55 * r / 64 ≤ d := by
  have h := (abs_le.mp he).2
  linarith [min_le_right r d]

lemma observed_reject_low {r d observed : ℝ} (hr : 0 < r)
    (he : |observed - min r d| ≤ r / 64) (hl : observed < 13 * r / 16) :
    d < 53 * r / 64 := by
  have h := (abs_le.mp he).1
  have hm : min r d < 53 * r / 64 := by linarith
  by_cases hd : d ≤ r
  · simpa only [min_eq_right hd] using hm
  · rw [min_eq_left (le_of_not_ge hd)] at hm
    linarith

lemma observed_reject_high {r d observed : ℝ}
    (he : |observed - min r d| ≤ r / 64) (hh : 15 * r / 16 < observed) :
    59 * r / 64 < d := by
  have h := (abs_le.mp he).2
  linarith [min_le_right r d]

lemma bracket_refinement (d : ℝ → ℝ) {r lower upper observed : ℝ}
    (hr : 0 < r) (hlu : lower ≤ upper) (k : ℕ)
    (hw : upper - lower ≤ lower / 2 ^ k)
    (hdl : 55 * r / 64 ≤ d lower) (hdu : d upper ≤ 57 * r / 64)
    (he : |observed - min r (d ((lower + upper) / 2))| ≤ r / 64) :
    (observed < 13 * r / 16 →
      55 * r / 64 ≤ d lower ∧ d ((lower + upper) / 2) ≤ 57 * r / 64 ∧
        (lower + upper) / 2 - lower ≤ lower / 2 ^ (k + 1)) ∧
    (15 * r / 16 < observed →
      55 * r / 64 ≤ d ((lower + upper) / 2) ∧ d upper ≤ 57 * r / 64 ∧
        upper - (lower + upper) / 2 ≤ ((lower + upper) / 2) / 2 ^ (k + 1)) := by
  have hh := halved_relative_width hlu k hw
  constructor
  · intro hlow
    have hd := observed_reject_low hr he hlow
    exact ⟨hdl, by linarith, hh.1⟩
  · intro hhigh
    have hd := observed_reject_high he hhigh
    exact ⟨by linarith, hdu, hh.2⟩

lemma active_bracket_step (d : ℝ → ℝ) (observe : ℕ → ℝ → ℝ)
    {r floor cap K lower upper : ℝ} (H i : ℕ)
    (hr : 0 < r) (hf : 0 < floor) (hK : 0 ≤ K)
    (hi : H < i) (hiend : i ≤ 2 * H + 8)
    (hl : floor ≤ lower) (hlu : lower ≤ upper) (hu : upper ≤ cap)
    (hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ K * |x - y| / min x y)
    (hw : upper - lower ≤ lower / 2 ^ (i - (H + 1)))
    (hs : K / 2 ^ (H + 7) < r / 64)
    (hdl : 55 * r / 64 ≤ d lower) (hdu : d upper ≤ 57 * r / 64)
    (he : |observe i ((lower + upper) / 2) - min r (d ((lower + upper) / 2))| ≤ r / 64) :
    (∃ answer, AffineSoftmaxSearchTrace.step observe r floor cap H i
        (AffineSoftmaxSearchTrace.bracket lower upper) = AffineSoftmaxSearchTrace.done answer ∧
      answer ∈ Set.Icc lower upper ∧ 51 * r / 64 ≤ d answer ∧ d answer ≤ 61 * r / 64) ∨
    (∃ lo up, AffineSoftmaxSearchTrace.step observe r floor cap H i
        (AffineSoftmaxSearchTrace.bracket lower upper) = AffineSoftmaxSearchTrace.bracket lo up ∧
      lower ≤ lo ∧ lo ≤ up ∧ up ≤ upper ∧
      55 * r / 64 ≤ d lo ∧ d up ≤ 57 * r / 64 ∧
      up - lo ≤ lo / 2 ^ (i + 1 - (H + 1))) := by
  have hmid : (lower + upper) / 2 ∈ Set.Icc lower upper := by constructor <;> linarith
  have hin : ¬ i ≤ H := by omega
  by_cases hend : 2 * H + 8 ≤ i
  · have hik : i - (H + 1) = H + 7 := by omega
    rw [hik] at hw
    have hm := narrow_bracket_midpoint d hf hK hl hlu hu hmod (H + 7) hw hs hdl hdu
    left
    refine ⟨(lower + upper) / 2, ?_, hmid, ?_, ?_⟩
    · simp [AffineSoftmaxSearchTrace.step, AffineSoftmaxSearchTrace.bracket, hin, hend]
    all_goals linarith
  · have hk : i + 1 - (H + 1) = (i - (H + 1)) + 1 := by omega
    have href := bracket_refinement d hr hlu (i - (H + 1)) hw hdl hdu he
    by_cases hlow : observe i ((lower + upper) / 2) < 13 * r / 16
    · right
      refine ⟨lower, (lower + upper) / 2, ?_, le_rfl, hmid.1, hmid.2,
        (href.1 hlow).1, (href.1 hlow).2.1, ?_⟩
      · simp [AffineSoftmaxSearchTrace.step, AffineSoftmaxSearchTrace.bracket, hin, hend, hlow]
      · simpa only [hk] using (href.1 hlow).2.2
    · by_cases hhigh : 15 * r / 16 < observe i ((lower + upper) / 2)
      · right
        refine ⟨(lower + upper) / 2, upper, ?_, hmid.1, hmid.2, le_rfl,
          (href.2 hhigh).1, (href.2 hhigh).2.1, ?_⟩
        · simp [AffineSoftmaxSearchTrace.step, AffineSoftmaxSearchTrace.bracket, hin, hend, hlow, hhigh]
        · simpa only [hk] using (href.2 hhigh).2.2
      · left
        have hd := AffineSoftmaxSearch.observed_displacement_certificate hr he
          (le_of_not_gt hlow) (le_of_not_gt hhigh)
        refine ⟨(lower + upper) / 2, ?_, hmid, hd.1, hd.2⟩
        simp [AffineSoftmaxSearchTrace.step, AffineSoftmaxSearchTrace.bracket, hin, hend, hlow, hhigh]

lemma scan_step_certificate (d : ℝ → ℝ) (observe : ℕ → ℝ → ℝ)
    {r floor cap previous : ℝ} (H i : ℕ) (hr : 0 < r)
    (hfc : floor ≤ cap) (hi : i ≤ H) (hcap : d cap ≤ r / 2)
    (hprev : d previous ≤ 57 * r / 64)
    (horder : max floor (cap / 2 ^ i) ≤ previous)
    (hwidth : previous ≤ 2 * max floor (cap / 2 ^ i))
    (hend : i = H → max floor (cap / 2 ^ i) = floor)
    (he : |observe i (max floor (cap / 2 ^ i)) - min r (d (max floor (cap / 2 ^ i)))| ≤ r / 64) :
    (AffineSoftmaxSearchTrace.step observe r floor cap H i
        (AffineSoftmaxSearchTrace.scan previous) = AffineSoftmaxSearchTrace.scan (max floor (cap / 2 ^ i)) ∧
      i < H ∧ d (max floor (cap / 2 ^ i)) ≤ 57 * r / 64) ∨
    (AffineSoftmaxSearchTrace.step observe r floor cap H i
        (AffineSoftmaxSearchTrace.scan previous) = AffineSoftmaxSearchTrace.bracket (max floor (cap / 2 ^ i)) previous ∧
      55 * r / 64 ≤ d (max floor (cap / 2 ^ i)) ∧
      max floor (cap / 2 ^ i) ≤ previous ∧
      previous - max floor (cap / 2 ^ i) ≤ max floor (cap / 2 ^ i) ∧
      d previous ≤ 57 * r / 64) ∨
    (AffineSoftmaxSearchTrace.step observe r floor cap H i
        (AffineSoftmaxSearchTrace.scan previous) = AffineSoftmaxSearchTrace.done floor ∧ d floor < r) := by
  by_cases hcross : 7 * r / 8 ≤ observe i (max floor (cap / 2 ^ i))
  · have hd := observed_crossing_lower he hcross
    have hiz : i ≠ 0 := by
      intro hz
      simp only [hz, pow_zero, div_one, max_eq_right hfc] at hd
      linarith
    right; left
    refine ⟨?_, hd, horder, by linarith, hprev⟩
    simp [AffineSoftmaxSearchTrace.step, AffineSoftmaxSearchTrace.scan, hi, hcross, hiz]
  · have hd := AffineSoftmaxSearch.observed_small_certificate hr he (lt_of_not_ge hcross)
    by_cases hiH : i = H
    · right; right
      refine ⟨?_, ?_⟩
      · subst H
        simp [AffineSoftmaxSearchTrace.step, AffineSoftmaxSearchTrace.scan, hcross]
      · rw [hend hiH] at hd
        linarith
    · left
      refine ⟨?_, by omega, hd.le⟩
      simp [AffineSoftmaxSearchTrace.step, AffineSoftmaxSearchTrace.scan, hi, hcross, hiH]

def Invariant (d : ℝ → ℝ) (r floor cap : ℝ) (H i : ℕ)
    (state : AffineSoftmaxSearchTrace.State) : Prop :=
  (∃ previous, state = AffineSoftmaxSearchTrace.scan previous ∧ i ≤ H ∧
    previous = (if i = 0 then cap else max floor (cap / 2 ^ (i - 1))) ∧
    d previous ≤ 57 * r / 64) ∨
  (∃ lower upper, state = AffineSoftmaxSearchTrace.bracket lower upper ∧
    floor ≤ lower ∧ lower ≤ upper ∧ upper ≤ cap ∧
    55 * r / 64 ≤ d lower ∧ d upper ≤ 57 * r / 64 ∧
    upper - lower ≤ lower / 2 ^ (i - (H + 1))) ∨
  (∃ answer, state = AffineSoftmaxSearchTrace.done answer ∧
    answer ∈ Set.Icc floor cap ∧
    ((answer = floor ∧ d answer < r) ∨
      (51 * r / 64 ≤ d answer ∧ d answer ≤ 61 * r / 64)))

lemma invariant_initial (d : ℝ → ℝ) {r cap : ℝ} (floor : ℝ) (H : ℕ)
    (hr : 0 < r) (hc : d cap ≤ r / 2) :
    Invariant d r floor cap H 0 (AffineSoftmaxSearchTrace.scan cap) := by
  left
  exact ⟨cap, rfl, Nat.zero_le H, by simp, by linarith⟩

lemma invariant_done_step (d : ℝ → ℝ) (observe : ℕ → ℝ → ℝ)
    (r floor cap : ℝ) (H i : ℕ) (answer : ℝ)
    (ha : answer ∈ Set.Icc floor cap)
    (hd : (answer = floor ∧ d answer < r) ∨
      (51 * r / 64 ≤ d answer ∧ d answer ≤ 61 * r / 64)) :
    Invariant d r floor cap H (i + 1)
      (AffineSoftmaxSearchTrace.step observe r floor cap H i (AffineSoftmaxSearchTrace.done answer)) := by
  rw [AffineSoftmaxSearchTrace.step_done]
  exact Or.inr (Or.inr ⟨answer, rfl, ha, hd⟩)

lemma invariant_bracket_step (d : ℝ → ℝ) (observe : ℕ → ℝ → ℝ)
    {r floor cap K lower upper : ℝ} (H i : ℕ)
    (hr : 0 < r) (hf : 0 < floor) (hK : 0 ≤ K) (hiend : i ≤ 2 * H + 8)
    (hl : floor ≤ lower) (hlu : lower ≤ upper) (hu : upper ≤ cap)
    (hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ K * |x - y| / min x y)
    (hw : upper - lower ≤ lower / 2 ^ (i - (H + 1)))
    (hs : K / 2 ^ (H + 7) < r / 64)
    (hdl : 55 * r / 64 ≤ d lower) (hdu : d upper ≤ 57 * r / 64)
    (he : H < i → |observe i ((lower + upper) / 2) - min r (d ((lower + upper) / 2))| ≤ r / 64) :
    Invariant d r floor cap H (i + 1)
      (AffineSoftmaxSearchTrace.step observe r floor cap H i (AffineSoftmaxSearchTrace.bracket lower upper)) := by
  by_cases hi : i ≤ H
  · have hk : i - (H + 1) = 0 := by omega
    have hk' : i + 1 - (H + 1) = 0 := by omega
    right; left
    refine ⟨lower, upper, ?_, hl, hlu, hu, hdl, hdu, ?_⟩
    · simp [AffineSoftmaxSearchTrace.step, AffineSoftmaxSearchTrace.bracket, hi]
    · simpa only [hk, hk'] using hw
  · have hit : H < i := by omega
    rcases active_bracket_step d observe H i hr hf hK hit hiend hl hlu hu hmod hw hs hdl hdu (he hit) with hd | hb
    · rcases hd with ⟨answer, heq, ha, h1, h2⟩
      right; right
      exact ⟨answer, heq, ⟨hl.trans ha.1, ha.2.trans hu⟩, Or.inr ⟨h1, h2⟩⟩
    · rcases hb with ⟨lo, up, heq, hlo, hlub, hup, hdlb, hdub, hwb⟩
      right; left
      exact ⟨lo, up, heq, hl.trans hlo, hlub, hup.trans hu, hdlb, hdub, hwb⟩

lemma invariant_scan_step (d : ℝ → ℝ) (observe : ℕ → ℝ → ℝ)
    {r floor cap previous : ℝ} (H i : ℕ) (hr : 0 < r) (hf : 0 < floor)
    (hfc : floor ≤ cap) (hi : i ≤ H) (hcap : d cap ≤ r / 2)
    (hprev : d previous ≤ 57 * r / 64)
    (hp : previous = (if i = 0 then cap else max floor (cap / 2 ^ (i - 1))))
    (hend : cap / 2 ^ H ≤ floor)
    (he : |observe i (max floor (cap / 2 ^ i)) - min r (d (max floor (cap / 2 ^ i)))| ≤ r / 64) :
    Invariant d r floor cap H (i + 1)
      (AffineSoftmaxSearchTrace.step observe r floor cap H i (AffineSoftmaxSearchTrace.scan previous)) := by
  have hc : 0 ≤ cap := hf.le.trans hfc
  have hcurrent : max floor (cap / 2 ^ i) ≤ cap := max_le hfc
    (div_le_self hc (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  have horder : max floor (cap / 2 ^ i) ≤ previous ∧ previous ≤ 2 * max floor (cap / 2 ^ i) := by
    by_cases hz : i = 0
    · simp only [hz, ite_true, pow_zero, div_one, max_eq_right hfc] at hp ⊢
      rw [hp]
      exact ⟨le_rfl, by linarith⟩
    · have hi' : i = (i - 1) + 1 := by omega
      rw [ite_eq_right hz] at hp
      rw [hp]
      simpa only [← hi'] using clamped_grid_step hf.le hc (i - 1)
  have hprange : previous ≤ cap := by
    rw [hp]
    split_ifs
    · exact le_rfl
    · exact max_le hfc (div_le_self hc (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  have hend' : i = H → max floor (cap / 2 ^ i) = floor := by
    intro hiH
    rw [hiH, max_eq_left hend]
  rcases scan_step_certificate d observe H i hr hfc hi hcap hprev horder.1 horder.2 hend' he with ha | hb | hd
  · rcases ha with ⟨heq, hit, hdc⟩
    left
    refine ⟨max floor (cap / 2 ^ i), heq, by omega, ?_, hdc⟩
    simp
  · rcases hb with ⟨heq, hdl, hlu, hw, hdu⟩
    right; left
    refine ⟨max floor (cap / 2 ^ i), previous, heq, le_max_left _ _, hlu, hprange, hdl, hdu, ?_⟩
    have hk : i + 1 - (H + 1) = 0 := by omega
    simpa only [hk, pow_zero, div_one] using hw
  · right; right
    exact ⟨floor, hd.1, ⟨le_rfl, hfc⟩, Or.inl ⟨rfl, hd.2⟩⟩

lemma invariant_step (d : ℝ → ℝ) (observe : ℕ → ℝ → ℝ)
    {r floor cap K : ℝ} (H i : ℕ) (state : AffineSoftmaxSearchTrace.State)
    (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap) (hK : 0 ≤ K)
    (hi : i ≤ 2 * H + 8) (hcap : d cap ≤ r / 2) (hend : cap / 2 ^ H ≤ floor)
    (hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ K * |x - y| / min x y)
    (hs : K / 2 ^ (H + 7) < r / 64)
    (hinv : Invariant d r floor cap H i state)
    (hscan : ∀ previous, state = AffineSoftmaxSearchTrace.scan previous →
      |observe i (max floor (cap / 2 ^ i)) - min r (d (max floor (cap / 2 ^ i)))| ≤ r / 64)
    (hbracket : ∀ lower upper, state = AffineSoftmaxSearchTrace.bracket lower upper → H < i →
      |observe i ((lower + upper) / 2) - min r (d ((lower + upper) / 2))| ≤ r / 64) :
    Invariant d r floor cap H (i + 1) (AffineSoftmaxSearchTrace.step observe r floor cap H i state) := by
  rcases hinv with hscaninv | hbracketinv | hdone
  · rcases hscaninv with ⟨previous, heq, hiH, hp, hdp⟩
    rw [heq]
    exact invariant_scan_step d observe H i hr hf hfc hiH hcap hdp hp hend (hscan previous heq)
  · rcases hbracketinv with ⟨lower, upper, heq, hl, hlu, hu, hdl, hdu, hw⟩
    rw [heq]
    exact invariant_bracket_step d observe H i hr hf hK hi hl hlu hu hmod hw hs hdl hdu
      (hbracket lower upper heq)
  · rcases hdone with ⟨answer, heq, ha, hd⟩
    rw [heq]
    exact invariant_done_step d observe r floor cap H i answer ha hd

lemma trajectory_invariant (d : ℝ → ℝ) (observe : ℕ → ℝ → ℝ)
    {r floor cap K : ℝ} (H n : ℕ)
    (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap) (hK : 0 ≤ K)
    (hn : n ≤ 2 * H + 9) (hcap : d cap ≤ r / 2) (hend : cap / 2 ^ H ≤ floor)
    (hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ K * |x - y| / min x y)
    (hs : K / 2 ^ (H + 7) < r / 64)
    (hscan : ∀ i < n, ∀ previous,
      AffineSoftmaxSearchTrace.trajectory observe r floor cap H i = AffineSoftmaxSearchTrace.scan previous →
      |observe i (max floor (cap / 2 ^ i)) - min r (d (max floor (cap / 2 ^ i)))| ≤ r / 64)
    (hbracket : ∀ i < n, ∀ lower upper,
      AffineSoftmaxSearchTrace.trajectory observe r floor cap H i = AffineSoftmaxSearchTrace.bracket lower upper → H < i →
      |observe i ((lower + upper) / 2) - min r (d ((lower + upper) / 2))| ≤ r / 64) :
    Invariant d r floor cap H n (AffineSoftmaxSearchTrace.trajectory observe r floor cap H n) := by
  induction n with
  | zero => exact invariant_initial d floor H hr hcap
  | succ n ih =>
    apply invariant_step d observe H n _ hr hf hfc hK (by omega) hcap hend hmod hs
    · exact ih (by omega) (fun i hi => hscan i (by omega)) (fun i hi => hbracket i (by omega))
    · exact hscan n (by omega)
    · exact hbracket n (by omega)

lemma invariant_done_certificate (d : ℝ → ℝ) (r floor cap : ℝ) (H i : ℕ) (answer : ℝ)
    (hi : Invariant d r floor cap H i (AffineSoftmaxSearchTrace.done answer)) :
    answer ∈ Set.Icc floor cap ∧
      ((answer = floor ∧ d answer < r) ∨ (51 * r / 64 ≤ d answer ∧ d answer ≤ 61 * r / 64)) := by
  rcases hi with ha | hb | hc
  · rcases ha with ⟨previous, heq, _⟩
    have hp := congrArg Prod.fst heq
    simp [AffineSoftmaxSearchTrace.done, AffineSoftmaxSearchTrace.scan] at hp
  · rcases hb with ⟨lower, upper, heq, _⟩
    have hp := congrArg Prod.fst heq
    simp [AffineSoftmaxSearchTrace.done, AffineSoftmaxSearchTrace.bracket] at hp
  · rcases hc with ⟨other, heq, ha, hd⟩
    have hp : answer = other := congrArg (fun s : AffineSoftmaxSearchTrace.State => s.2.1) heq
    simpa only [hp] using And.intro ha hd

open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxSearch

lemma searchPlan_certificate (d : ℝ → ℝ) {Q R : Type*}
    (probe : ℕ → ℝ → Program Q R ℝ) (reply : Q → R)
    {r floor cap K : ℝ} (H : ℕ)
    (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap) (hK : 0 ≤ K)
    (hcap : d cap ≤ r / 2) (hend : cap / 2 ^ H ≤ floor)
    (hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ K * |x - y| / min x y)
    (hs : K / 2 ^ (H + 7) < r / 64)
    (hscan : ∀ i < 2 * H + 9, ∀ previous,
      AffineSoftmaxSearchTrace.trajectory (fun j t => Program.eval reply (probe j t)) r floor cap H i =
        AffineSoftmaxSearchTrace.scan previous →
      |Program.eval reply (probe i (max floor (cap / 2 ^ i))) - min r (d (max floor (cap / 2 ^ i)))| ≤ r / 64)
    (hbracket : ∀ i < 2 * H + 9, ∀ lower upper,
      AffineSoftmaxSearchTrace.trajectory (fun j t => Program.eval reply (probe j t)) r floor cap H i =
        AffineSoftmaxSearchTrace.bracket lower upper → H < i →
      |Program.eval reply (probe i ((lower + upper) / 2)) - min r (d ((lower + upper) / 2))| ≤ r / 64) :
    let answer := Program.eval reply (searchPlan probe r floor cap H)
    answer ∈ Set.Icc floor cap ∧
      ((answer = floor ∧ d answer < r) ∨ (51 * r / 64 ≤ d answer ∧ d answer ≤ 61 * r / 64)) := by
  have hi := trajectory_invariant d (fun j t => Program.eval reply (probe j t)) H (2 * H + 9)
    hr hf hfc hK le_rfl hcap hend hmod hs hscan hbracket
  rw [AffineSoftmaxSearchTrace.trajectory_search_eq Q R probe reply r floor cap H] at hi
  exact invariant_done_certificate d r floor cap H (2 * H + 9) _ hi

end LongTails.Proofs.AffineSoftmaxSearchGeometry
