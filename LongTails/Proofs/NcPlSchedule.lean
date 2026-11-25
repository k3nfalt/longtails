import LongTails.Proofs.NcPlBlockPL

open scoped BigOperators

namespace LongTails.Proofs.NcPlSchedule

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlProfiles
open LongTails.Proofs.NcPlBlockPL

noncomputable def wt (N k : ℕ) : ℝ := max (1 / (N : ℝ)) ((1 / 4 : ℝ) ^ (N - k))

noncomputable def cum (N k : ℕ) : ℝ := ∑ i ∈ Finset.range k, wt N i

lemma wt_pos {N : ℕ} (k : ℕ) : 0 < wt N k :=
  lt_of_lt_of_le (by positivity) (le_max_right _ _)

lemma wt_le_one {N : ℕ} (hN : 0 < N) (k : ℕ) : wt N k ≤ 1 := by
  apply max_le
  · rw [div_le_one (by exact_mod_cast hN)]
    exact_mod_cast hN
  · exact pow_le_one₀ (by norm_num) (by norm_num)

lemma wt_ge {N : ℕ} (k : ℕ) : 1 / (N : ℝ) ≤ wt N k := le_max_left _ _

lemma wt_top (N : ℕ) (hN : 0 < N) : wt N N = 1 := by
  unfold wt
  rw [Nat.sub_self, pow_zero]
  apply max_eq_right
  rw [div_le_one (by exact_mod_cast hN)]
  exact_mod_cast hN

lemma wt_mono {N k : ℕ} (hk : k < N) : wt N k ≤ wt N (k + 1) := by
  unfold wt
  apply max_le_max le_rfl
  have e : N - k = (N - (k + 1)) + 1 := by omega
  rw [e, pow_succ]
  have : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (N - (k + 1)) := by positivity
  nlinarith

lemma wt_succ_le {N k : ℕ} (hk : k < N) : wt N (k + 1) ≤ 4 * wt N k := by
  unfold wt
  have e : N - k = (N - (k + 1)) + 1 := by omega
  have h1 : (1 / 4 : ℝ) ^ (N - (k + 1)) = 4 * (1 / 4 : ℝ) ^ (N - k) := by
    rw [e, pow_succ]; ring
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  apply max_le
  · have := le_max_left (1 / (N : ℝ)) ((1 / 4 : ℝ) ^ (N - k))
    linarith
  · rw [h1]
    have := le_max_right (1 / (N : ℝ)) ((1 / 4 : ℝ) ^ (N - k))
    linarith

lemma wt_sq {N k : ℕ} (hk : k < N) : wt N (k + 1) ≤ 16 * N * wt N k ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hw := wt_ge (N := N) k
  have hwp := wt_pos (N := N) k
  have e : N - k = (N - (k + 1)) + 1 := by omega
  have h1 : (1 / 4 : ℝ) ^ (N - (k + 1)) = 4 * (1 / 4 : ℝ) ^ (N - k) := by
    rw [e, pow_succ]; ring
  have hNw : 1 ≤ (N : ℝ) * wt N k := by
    have := mul_le_mul_of_nonneg_left hw hNpos.le
    rwa [mul_one_div_cancel hNpos.ne'] at this
  unfold wt at *
  apply max_le
  · have h2 : 1 / (N : ℝ) ≤ max (1 / (N : ℝ)) ((1 / 4 : ℝ) ^ (N - k)) := le_max_left _ _
    nlinarith [mul_pos hNpos hwp]
  · rw [h1]
    have h2 : (1 / 4 : ℝ) ^ (N - k) ≤ max (1 / (N : ℝ)) ((1 / 4 : ℝ) ^ (N - k)) := le_max_right _ _
    nlinarith [mul_pos hNpos hwp]

lemma geom_sum (N : ℕ) : ∑ k ∈ Finset.range N, (1 / 4 : ℝ) ^ (N - k) = (1 - (1 / 4 : ℝ) ^ N) / 3 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h : ∑ k ∈ Finset.range N, (1 / 4 : ℝ) ^ (N + 1 - k) =
        1 / 4 * ∑ k ∈ Finset.range N, (1 / 4 : ℝ) ^ (N - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have e : N + 1 - k = (N - k) + 1 := by
        have := Finset.mem_range.mp hk
        omega
      rw [e, pow_succ]
      ring
    rw [h, ih]
    have e2 : N + 1 - N = 1 := by omega
    rw [e2, pow_succ]
    ring

lemma cum_le {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : k ≤ N) : cum N k ≤ 4 / 3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : cum N k ≤ cum N N := by
    unfold cum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)
    · intro i _ _
      exact (wt_pos i).le
  have h2 : cum N N ≤ ∑ i ∈ Finset.range N, (1 / (N : ℝ) + (1 / 4 : ℝ) ^ (N - i)) := by
    unfold cum
    apply Finset.sum_le_sum
    intro i _
    unfold wt
    apply max_le
    · have : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (N - i) := by positivity
      linarith
    · have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      linarith
  rw [Finset.sum_add_distrib, geom_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one_div_cancel hNpos.ne'] at h2
  have h3 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ N := by positivity
  linarith

lemma cum_succ (N k : ℕ) : cum N (k + 1) = cum N k + wt N k := by
  unfold cum
  rw [Finset.sum_range_succ]

lemma cum_mono {N : ℕ} {k l : ℕ} (h : k ≤ l) : cum N k ≤ cum N l := by
  unfold cum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) h)
  · intro i _ _
    exact (wt_pos i).le

lemma cum_nonneg (N k : ℕ) : 0 ≤ cum N k :=
  Finset.sum_nonneg (fun i _ => (wt_pos i).le)

noncomputable def ramp (w u : ℝ) : ℝ := (rr u - rr (u - w)) / w

noncomputable def dramp (w u : ℝ) : ℝ := (pos u - pos (u - w)) / w

noncomputable def cap (z : ℝ) : ℝ := z - rr z / 2 + rr (z - 2) / 2

noncomputable def dcap (z : ℝ) : ℝ := 1 - pos z / 2 + pos (z - 2) / 2

lemma rr_hasDerivAt (x : ℝ) : HasDerivAt rr (pos x) x :=
  model_hasDerivAt rr pos (1 / 2) (fun a b => by
    have := rr_model a b
    linarith) x

lemma ramp_hasDerivAt (w u : ℝ) : HasDerivAt (ramp w) (dramp w u) u := by
  have h1 : HasDerivAt rr (pos u) u := rr_hasDerivAt u
  have h2 : HasDerivAt (rr ∘ fun x : ℝ => x - w) (pos (u - w) * 1) u :=
    HasDerivAt.comp u (rr_hasDerivAt (u - w)) ((hasDerivAt_id' u).sub_const w)
  have h := (h1.sub h2).div_const w
  have e : (pos u - pos (u - w) * 1) / w = dramp w u := by unfold dramp; ring
  rw [e] at h
  exact h

lemma cap_hasDerivAt (z : ℝ) : HasDerivAt cap (dcap z) z := by
  have h1 := (rr_hasDerivAt z).div_const 2
  have h2 : HasDerivAt (rr ∘ fun x : ℝ => x - 2) (pos (z - 2) * 1) z :=
    HasDerivAt.comp z (rr_hasDerivAt (z - 2)) ((hasDerivAt_id' z).sub_const 2)
  have h := ((hasDerivAt_id' z).sub h1).add (h2.div_const 2)
  have e : 1 - pos z / 2 + pos (z - 2) * 1 / 2 = dcap z := by unfold dcap; ring
  rw [e] at h
  exact h

lemma ramp_nonneg {w : ℝ} (hw : 0 < w) (u : ℝ) : 0 ≤ ramp w u := by
  unfold ramp
  apply div_nonneg _ hw.le
  simp only [rr, pos, max_def]
  split_ifs <;> nlinarith

lemma ramp_of_nonpos {w : ℝ} (hw : 0 < w) {u : ℝ} (hu : u ≤ 0) : ramp w u = 0 := by
  simp only [ramp, rr, pos_of_nonpos hu, pos_of_nonpos (by linarith : u - w ≤ 0)]
  simp

lemma dramp_of_nonpos {w : ℝ} (hw : 0 < w) {u : ℝ} (hu : u ≤ 0) : dramp w u = 0 := by
  simp only [dramp, pos_of_nonpos hu, pos_of_nonpos (by linarith : u - w ≤ 0)]
  simp

lemma ramp_of_ge {w : ℝ} (hw : 0 < w) {u : ℝ} (hu : w ≤ u) : ramp w u = u - w / 2 := by
  simp only [ramp, rr, pos_of_nonneg (by linarith : 0 ≤ u), pos_of_nonneg (by linarith : 0 ≤ u - w)]
  field_simp
  ring

lemma ramp_pos {w : ℝ} (hw : 0 < w) {u : ℝ} (hu : 0 < u) : 0 < ramp w u := by
  unfold ramp
  apply div_pos _ hw
  simp only [rr, pos, max_def]
  split_ifs <;> nlinarith

lemma ramp_le {w : ℝ} (hw : 0 < w) (u : ℝ) : ramp w u ≤ pos u := by
  unfold ramp
  rw [div_le_iff₀ hw]
  simp only [rr, pos, max_def]
  split_ifs <;> nlinarith

lemma dramp_nonneg {w : ℝ} (hw : 0 < w) (u : ℝ) : 0 ≤ dramp w u := by
  unfold dramp
  apply div_nonneg _ hw.le
  simp only [pos, max_def]
  split_ifs <;> linarith

lemma dramp_le_one {w : ℝ} (hw : 0 < w) (u : ℝ) : dramp w u ≤ 1 := by
  unfold dramp
  rw [div_le_one hw]
  simp only [pos, max_def]
  split_ifs <;> linarith

lemma cap_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ cap z := by
  simp only [cap, rr, pos_of_nonneg hz]
  simp only [pos, max_def]
  split_ifs <;> nlinarith

lemma cap_le_one (z : ℝ) : cap z ≤ 1 := by
  simp only [cap, rr, pos, max_def]
  split_ifs <;> nlinarith [sq_nonneg (z - 2)]

lemma cap_zero : cap 0 = 0 := by
  simp [cap, rr, pos]

lemma cap_pos {z : ℝ} (hz : 0 < z) : 0 < cap z := by
  simp only [cap, rr, pos_of_nonneg hz.le]
  simp only [pos, max_def]
  split_ifs <;> nlinarith

lemma cap_ge {z : ℝ} (hz : 0 ≤ z) : min 1 (z / 2) ≤ cap z := by
  simp only [cap, rr, pos_of_nonneg hz]
  rcases le_total z 2 with h | h
  · rw [pos_of_nonpos (by linarith : z - 2 ≤ 0)]
    apply (min_le_right _ _).trans
    nlinarith
  · rw [pos_of_nonneg (by linarith : 0 ≤ z - 2)]
    apply (min_le_left _ _).trans
    nlinarith

lemma cap_of_ge {z : ℝ} (hz : 2 ≤ z) : cap z = 1 := by
  simp only [cap, rr, pos_of_nonneg (by linarith : 0 ≤ z), pos_of_nonneg (by linarith : 0 ≤ z - 2)]
  ring

lemma dcap_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ dcap z := by
  simp only [dcap, pos_of_nonneg hz]
  simp only [pos, max_def]
  split_ifs <;> linarith

lemma dcap_le_one {z : ℝ} (hz : 0 ≤ z) : dcap z ≤ 1 := by
  simp only [dcap, pos_of_nonneg hz]
  simp only [pos, max_def]
  split_ifs <;> linarith

lemma dcap_lipschitz (a b : ℝ) : |dcap a - dcap b| ≤ |a - b| := by
  have h1 := pos_lipschitz a b
  have h2 := pos_lipschitz (a - 2) (b - 2)
  have e : a - 2 - (b - 2) = a - b := by ring
  rw [e] at h2
  have e2 : dcap a - dcap b = -(pos a - pos b) / 2 + (pos (a - 2) - pos (b - 2)) / 2 := by
    unfold dcap; ring
  rw [e2]
  have := abs_add_le (-(pos a - pos b) / 2) ((pos (a - 2) - pos (b - 2)) / 2)
  rw [abs_div, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
  linarith

lemma cap_mono {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : cap a ≤ cap b := by
  have hb : 0 ≤ b := le_trans ha h
  simp only [cap, rr, pos_of_nonneg ha, pos_of_nonneg hb]
  simp only [pos, max_def]
  split_ifs <;> nlinarith

lemma ramp_mono {w : ℝ} (hw : 0 < w) {a b : ℝ} (h : a ≤ b) : ramp w a ≤ ramp w b :=
  monotone_of_hasDerivAt_nonneg (ramp_hasDerivAt w) (fun x => dramp_nonneg hw x) h

lemma ramp_lipschitz {w : ℝ} (hw : 0 < w) (a b : ℝ) : |ramp w a - ramp w b| ≤ |a - b| := by
  have h := lipschitz_of_deriv (ramp w) (dramp w) 1 (ramp_hasDerivAt w)
    (fun z => by rw [abs_of_nonneg (dramp_nonneg hw z)]; exact dramp_le_one hw z) a b
  simpa using h

section Amplitudes

variable (N : ℕ)

noncomputable def amp (k : ℕ) (s : ℝ) : ℝ := cap (ramp (wt N k) (s - cum N k))

noncomputable def damp (k : ℕ) (s : ℝ) : ℝ :=
  dcap (ramp (wt N k) (s - cum N k)) * dramp (wt N k) (s - cum N k)

noncomputable def ampT (s : ℝ) : ℝ := cap (ramp 1 (s - cum N N))

noncomputable def dampT (s : ℝ) : ℝ := dcap (ramp 1 (s - cum N N)) * dramp 1 (s - cum N N)

noncomputable def smax : ℝ := cum N N + 5 / 2

variable {N}

lemma amp_hasDerivAt (k : ℕ) (s : ℝ) : HasDerivAt (amp N k) (damp N k s) s := by
  have h1 : HasDerivAt (ramp (wt N k) ∘ fun x : ℝ => x - cum N k)
      (dramp (wt N k) (s - cum N k) * 1) s :=
    HasDerivAt.comp s (ramp_hasDerivAt (wt N k) (s - cum N k))
      ((hasDerivAt_id' s).sub_const (cum N k))
  have h : HasDerivAt (cap ∘ (ramp (wt N k) ∘ fun x : ℝ => x - cum N k))
      (dcap (ramp (wt N k) (s - cum N k)) * (dramp (wt N k) (s - cum N k) * 1)) s :=
    HasDerivAt.comp s (cap_hasDerivAt (ramp (wt N k) (s - cum N k))) h1
  have e : dcap (ramp (wt N k) (s - cum N k)) * (dramp (wt N k) (s - cum N k) * 1) =
      damp N k s := by unfold damp; ring
  rw [e] at h
  exact h

lemma ampT_hasDerivAt (s : ℝ) : HasDerivAt (ampT N) (dampT N s) s := by
  have h1 : HasDerivAt (ramp 1 ∘ fun x : ℝ => x - cum N N) (dramp 1 (s - cum N N) * 1) s :=
    HasDerivAt.comp s (ramp_hasDerivAt 1 (s - cum N N)) ((hasDerivAt_id' s).sub_const (cum N N))
  have h : HasDerivAt (cap ∘ (ramp 1 ∘ fun x : ℝ => x - cum N N))
      (dcap (ramp 1 (s - cum N N)) * (dramp 1 (s - cum N N) * 1)) s :=
    HasDerivAt.comp s (cap_hasDerivAt (ramp 1 (s - cum N N))) h1
  have e : dcap (ramp 1 (s - cum N N)) * (dramp 1 (s - cum N N) * 1) = dampT N s := by
    unfold dampT; ring
  rw [e] at h
  exact h

lemma amp_nonneg (k : ℕ) (s : ℝ) : 0 ≤ amp N k s := cap_nonneg (ramp_nonneg (wt_pos k) _)

lemma amp_le_one (k : ℕ) (s : ℝ) : amp N k s ≤ 1 := cap_le_one _

lemma ampT_nonneg (s : ℝ) : 0 ≤ ampT N s := cap_nonneg (ramp_nonneg one_pos _)

lemma ampT_le_one (s : ℝ) : ampT N s ≤ 1 := cap_le_one _

lemma amp_of_le {k : ℕ} {s : ℝ} (h : s ≤ cum N k) : amp N k s = 0 := by
  rw [amp, ramp_of_nonpos (wt_pos k) (by linarith), cap_zero]

lemma damp_of_le {k : ℕ} {s : ℝ} (h : s ≤ cum N k) : damp N k s = 0 := by
  rw [damp, dramp_of_nonpos (wt_pos k) (by linarith), mul_zero]

lemma ampT_of_le {s : ℝ} (h : s ≤ cum N N) : ampT N s = 0 := by
  rw [ampT, ramp_of_nonpos one_pos (by linarith), cap_zero]

lemma dampT_of_le {s : ℝ} (h : s ≤ cum N N) : dampT N s = 0 := by
  rw [dampT, dramp_of_nonpos one_pos (by linarith), mul_zero]

lemma lt_of_amp_pos {k : ℕ} {s : ℝ} (h : 0 < amp N k s) : cum N k < s := by
  by_contra hc
  rw [amp_of_le (not_lt.mp hc)] at h
  exact lt_irrefl _ h

lemma lt_of_ampT_pos {s : ℝ} (h : 0 < ampT N s) : cum N N < s := by
  by_contra hc
  rw [ampT_of_le (not_lt.mp hc)] at h
  exact lt_irrefl _ h

lemma amp_lower {k : ℕ} {s : ℝ} (h : cum N k + wt N k ≤ s) :
    min 1 ((s - cum N k) / 4) ≤ amp N k s := by
  have hw := wt_pos (N := N) k
  have hr : ramp (wt N k) (s - cum N k) = s - cum N k - wt N k / 2 := ramp_of_ge hw (by linarith)
  have hr0 : 0 ≤ ramp (wt N k) (s - cum N k) := ramp_nonneg hw _
  have h1 := cap_ge hr0
  rw [amp]
  refine le_trans (min_le_min le_rfl ?_) h1
  rw [hr]
  linarith

lemma amp_anti {k l : ℕ} (hkl : k < l) (s : ℝ) : amp N l s ≤ amp N k s := by
  rcases le_or_gt s (cum N l) with h | h
  · rw [amp_of_le h]
    exact amp_nonneg k s
  · have hwk := wt_pos (N := N) k
    have hwl := wt_pos (N := N) l
    have hc : cum N k + wt N k ≤ cum N l := by
      rw [← cum_succ]
      exact cum_mono hkl
    have h1 : ramp (wt N l) (s - cum N l) ≤ pos (s - cum N l) := ramp_le hwl _
    rw [pos_of_nonneg (by linarith)] at h1
    have h2 : ramp (wt N k) (s - cum N k) = s - cum N k - wt N k / 2 :=
      ramp_of_ge hwk (by linarith)
    unfold amp
    apply cap_mono (ramp_nonneg hwl _)
    rw [h2]
    linarith

lemma ampT_le_amp {k : ℕ} (hk : k < N) (s : ℝ) : ampT N s ≤ amp N k s := by
  rcases le_or_gt s (cum N N) with h | h
  · rw [ampT_of_le h]
    exact amp_nonneg k s
  · have hwk := wt_pos (N := N) k
    have hc : cum N k + wt N k ≤ cum N N := by
      rw [← cum_succ]
      exact cum_mono hk
    have h1 : ramp 1 (s - cum N N) ≤ pos (s - cum N N) := ramp_le one_pos _
    rw [pos_of_nonneg (by linarith)] at h1
    have h2 : ramp (wt N k) (s - cum N k) = s - cum N k - wt N k / 2 :=
      ramp_of_ge hwk (by linarith)
    unfold amp ampT
    apply cap_mono (ramp_nonneg one_pos _)
    rw [h2]
    linarith

lemma damp_nonneg (k : ℕ) (s : ℝ) : 0 ≤ damp N k s :=
  mul_nonneg (dcap_nonneg (ramp_nonneg (wt_pos k) _)) (dramp_nonneg (wt_pos k) _)

lemma damp_le_one (k : ℕ) (s : ℝ) : damp N k s ≤ 1 :=
  (mul_le_mul (dcap_le_one (ramp_nonneg (wt_pos k) _)) (dramp_le_one (wt_pos k) _)
    (dramp_nonneg (wt_pos k) _) zero_le_one).trans_eq (one_mul 1)

lemma dampT_nonneg (s : ℝ) : 0 ≤ dampT N s :=
  mul_nonneg (dcap_nonneg (ramp_nonneg one_pos _)) (dramp_nonneg one_pos _)

lemma dampT_le_one (s : ℝ) : dampT N s ≤ 1 :=
  (mul_le_mul (dcap_le_one (ramp_nonneg one_pos _)) (dramp_le_one one_pos _)
    (dramp_nonneg one_pos _) zero_le_one).trans_eq (one_mul 1)

lemma amp_full {k : ℕ} (hk : k < N) {s : ℝ} (h : smax N ≤ s) : amp N k s = 1 := by
  have hw := wt_pos (N := N) k
  have hw1 := wt_le_one (Nat.zero_lt_of_lt hk) k
  have hc : cum N k + wt N k ≤ cum N N := by
    rw [← cum_succ]
    exact cum_mono hk
  unfold smax at h
  rw [amp, ramp_of_ge hw (by linarith)]
  exact cap_of_ge (by linarith)

lemma ampT_full {s : ℝ} (h : smax N ≤ s) : ampT N s = 1 := by
  unfold smax at h
  rw [ampT, ramp_of_ge one_pos (by linarith)]
  exact cap_of_ge (by linarith)

lemma wt_dramp (k : ℕ) (s : ℝ) :
    wt N k * dramp (wt N k) (s - cum N k) = pos (s - cum N k) - pos (s - cum N (k + 1)) := by
  have hw := wt_pos (N := N) k
  rw [dramp, mul_div_cancel₀ _ hw.ne', cum_succ]
  congr 2
  ring

lemma indicator_le (k : ℕ) {s : ℝ} (h : cum N (k + 1) < s) :
    wt N k ≤ pos (s - cum N k) - pos (s - cum N (k + 1)) := by
  have h1 : cum N k ≤ cum N (k + 1) := cum_mono (Nat.le_succ k)
  rw [pos_of_nonneg (by linarith), pos_of_nonneg (by linarith), cum_succ]
  linarith

lemma pos_diff_nonneg (k : ℕ) (s : ℝ) : 0 ≤ pos (s - cum N k) - pos (s - cum N (k + 1)) := by
  have h1 : cum N k ≤ cum N (k + 1) := cum_mono (Nat.le_succ k)
  simp only [pos, max_def]
  split_ifs <;> linarith

lemma telescope (s : ℝ) (J m : ℕ) (hJm : J ≤ m) :
    ∑ k ∈ Finset.range m, (if J ≤ k then pos (s - cum N k) - pos (s - cum N (k + 1)) else 0) =
      pos (s - cum N J) - pos (s - cum N m) := by
  induction m with
  | zero =>
    have : J = 0 := by omega
    subst this
    simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge m J with h | h
    · have hJ : J = m + 1 := by omega
      subst hJ
      have hz : ∑ k ∈ Finset.range m,
          (if m + 1 ≤ k then pos (s - cum N k) - pos (s - cum N (k + 1)) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have := Finset.mem_range.mp hk
        rw [ite_eq_right (by omega)]
      rw [hz, ite_eq_right (by omega)]
      simp
    · rw [ih h, ite_eq_left h]
      ring

end Amplitudes

section Dominance

variable {N : ℕ}

noncomputable def alphaSeq (N : ℕ) (s : ℝ) (k : ℕ) : ℝ := wt N k * amp N k s

noncomputable def rsq (N : ℕ) (k : ℕ) : ℝ := wt N (k + 1)

lemma alphaSeq_nonneg (s : ℝ) (k : ℕ) : 0 ≤ alphaSeq N s k :=
  mul_nonneg (wt_pos k).le (amp_nonneg k s)

lemma alphaSeq_le {k : ℕ} (hk : k < N) (s : ℝ) : alphaSeq N s k ≤ wt N (k + 1) := by
  have h1 := mul_le_mul_of_nonneg_left (amp_le_one (N := N) k s) (wt_pos (N := N) k).le
  rw [mul_one] at h1
  exact h1.trans (wt_mono hk)

lemma chat_pos_front {n : ℕ} {s b : ℝ} {j : ℕ} (hj : j ≤ n)
    (h : 0 < chat n (alphaSeq (n + 1) s) (ampT (n + 1) s * b) j) :
    cum (n + 1) j + wt (n + 1) j < s := by
  rw [← cum_succ]
  unfold chat at h
  split_ifs at h with hlt
  · have h2 : 0 < amp (n + 1) (j + 1) s := by
      by_contra hc
      have h0 : amp (n + 1) (j + 1) s = 0 := le_antisymm (not_lt.mp hc) (amp_nonneg _ _)
      rw [alphaSeq, h0, mul_zero] at h
      exact lt_irrefl _ h
    exact lt_of_amp_pos h2
  · have hjn : j = n := by omega
    subst hjn
    have h2 : 0 < ampT (j + 1) s := by
      by_contra hc
      have h0 : ampT (j + 1) s = 0 := le_antisymm (not_lt.mp hc) (ampT_nonneg _)
      rw [h0, zero_mul] at h
      exact lt_irrefl _ h
    exact lt_of_ampT_pos h2

lemma schedule_H1 {n : ℕ} {s b lam : ℝ} (hlam : lam = 1 / (2048 * ((n : ℝ) + 1)))
    {j : ℕ} (hj : j ≤ n) (h : 0 < chat n (alphaSeq (n + 1) s) (ampT (n + 1) s * b) j) :
    24 * lam * wt (n + 1) (j + 1) ≤ alphaSeq (n + 1) s j := by
  have hfront := chat_pos_front hj h
  have hw := wt_pos (N := n + 1) j
  have hw1 := wt_le_one (Nat.succ_pos n) j
  have hlow := amp_lower (N := n + 1) (k := j) hfront.le
  have hmin : wt (n + 1) j / 4 ≤ min 1 ((s - cum (n + 1) j) / 4) := by
    apply le_min
    · linarith
    · linarith
  have hA : wt (n + 1) j / 4 ≤ amp (n + 1) j s := hmin.trans hlow
  have hsq := wt_sq (N := n + 1) (k := j) (by omega)
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hsq
  have h1 : wt (n + 1) j * (wt (n + 1) j / 4) ≤ alphaSeq (n + 1) s j :=
    mul_le_mul_of_nonneg_left hA hw.le
  have h2 : 24 * lam * wt (n + 1) (j + 1) ≤ wt (n + 1) j * (wt (n + 1) j / 4) := by
    rw [hlam]
    have e : 24 * (1 / (2048 * ((n : ℝ) + 1))) * wt (n + 1) (j + 1) =
        3 * wt (n + 1) (j + 1) / (256 * ((n : ℝ) + 1)) := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

lemma tail_sum_le {n : ℕ} (s : ℝ) (J : ℕ) (hJ : J ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
      (if J ≤ k then (if k < n then alphaSeq (n + 1) s (k + 1) else 0) else 0) ≤
      amp (n + 1) J s * min (16 / 3) (4 * pos (s - cum (n + 1) J)) := by
  have hstep : ∀ k, k ∈ Finset.range (n + 1) →
      (if J ≤ k then (if k < n then alphaSeq (n + 1) s (k + 1) else 0) else 0) ≤
        amp (n + 1) J s * (4 * (if J ≤ k then
          (if k < n then min (wt (n + 1) k)
            (pos (s - cum (n + 1) k) - pos (s - cum (n + 1) (k + 1))) else 0) else 0)) := by
    intro k _
    by_cases h1 : J ≤ k
    · by_cases h2 : k < n
      · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h1, ite_eq_left h2]
        have hanti : amp (n + 1) (k + 1) s ≤ amp (n + 1) J s := amp_anti (by omega) s
        have hw := wt_succ_le (N := n + 1) (k := k) (by omega)
        have hwp := wt_pos (N := n + 1) (k + 1)
        have hA0 := amp_nonneg (N := n + 1) (k + 1) s
        have hAJ := amp_nonneg (N := n + 1) J s
        rcases le_or_gt s (cum (n + 1) (k + 1)) with hs | hs
        · rw [alphaSeq, amp_of_le hs, mul_zero]
          apply mul_nonneg hAJ
          apply mul_nonneg (by norm_num)
          exact le_min (wt_pos k).le (pos_diff_nonneg k s)
        · have hind := indicator_le (N := n + 1) k hs
          rw [min_eq_left hind, alphaSeq]
          calc wt (n + 1) (k + 1) * amp (n + 1) (k + 1) s
              ≤ wt (n + 1) (k + 1) * amp (n + 1) J s := mul_le_mul_of_nonneg_left hanti hwp.le
            _ ≤ 4 * wt (n + 1) k * amp (n + 1) J s := mul_le_mul_of_nonneg_right hw hAJ
            _ = amp (n + 1) J s * (4 * wt (n + 1) k) := by ring
      · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1, ite_eq_right h2]
        simp
    · rw [ite_eq_right h1, ite_eq_right h1]
      simp
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (amp_nonneg J s)
  have hb1 : ∑ k ∈ Finset.range (n + 1), (if J ≤ k then
      (if k < n then min (wt (n + 1) k)
        (pos (s - cum (n + 1) k) - pos (s - cum (n + 1) (k + 1))) else 0) else 0) ≤
      cum (n + 1) (n + 1) := by
    unfold cum
    apply Finset.sum_le_sum
    intro k _
    split_ifs
    · exact min_le_left _ _
    · exact (wt_pos k).le
    · exact (wt_pos k).le
  have hb2 : ∑ k ∈ Finset.range (n + 1), (if J ≤ k then
      (if k < n then min (wt (n + 1) k)
        (pos (s - cum (n + 1) k) - pos (s - cum (n + 1) (k + 1))) else 0) else 0) ≤
      pos (s - cum (n + 1) J) := by
    have ht := telescope (N := n + 1) s J (n + 1) (by omega)
    have hle : ∑ k ∈ Finset.range (n + 1), (if J ≤ k then
        (if k < n then min (wt (n + 1) k)
          (pos (s - cum (n + 1) k) - pos (s - cum (n + 1) (k + 1))) else 0) else 0) ≤
        ∑ k ∈ Finset.range (n + 1),
          (if J ≤ k then pos (s - cum (n + 1) k) - pos (s - cum (n + 1) (k + 1)) else 0) := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · exact min_le_right _ _
      · exact pos_diff_nonneg k s
      · exact le_rfl
    rw [ht] at hle
    have := pos_nonneg (s - cum (n + 1) (n + 1))
    linarith
  have hc := cum_le (Nat.succ_pos n) (le_refl (n + 1))
  apply le_min
  · linarith
  · linarith

lemma schedule_H2 {n : ℕ} {s b lam : ℝ} (hb : 0 ≤ b) (hb4 : b ≤ 4)
    (hlam : lam = 1 / (2048 * ((n : ℝ) + 1))) {J : ℕ} (hJ : J ≤ n)
    (h : 0 < chat n (alphaSeq (n + 1) s) (ampT (n + 1) s * b) J) :
    ∑ k ∈ Finset.range (n + 1),
      (if J ≤ k then chat n (alphaSeq (n + 1) s) (ampT (n + 1) s * b) k else 0) ≤
      alphaSeq (n + 1) s J ^ 2 / (lam * wt (n + 1) (J + 1)) := by
  have hfront := chat_pos_front hJ h
  have hw := wt_pos (N := n + 1) J
  have hw1 := wt_le_one (Nat.succ_pos n) J
  have hwJ1 := wt_pos (N := n + 1) (J + 1)
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlampos : 0 < lam := by rw [hlam]; positivity
  set A := amp (n + 1) J s with hA
  set u := s - cum (n + 1) J with hu
  have hu0 : 0 < u := by rw [hu]; linarith
  have hAlow : min 1 (u / 4) ≤ A := amp_lower (N := n + 1) (k := J) hfront.le
  have hA0 : 0 ≤ A := amp_nonneg J s
  have hA1 : A ≤ 1 := amp_le_one J s
  have hsplit : ∀ k, k ∈ Finset.range (n + 1) →
      (if J ≤ k then chat n (alphaSeq (n + 1) s) (ampT (n + 1) s * b) k else 0) =
        (if J ≤ k then (if k < n then alphaSeq (n + 1) s (k + 1) else 0) else 0) +
          (if k = n then ampT (n + 1) s * b else 0) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    unfold chat
    by_cases h1 : J ≤ k
    · by_cases h2 : k < n
      · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h1, ite_eq_left h2, ite_eq_right (by omega), add_zero]
      · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1, ite_eq_right h2, ite_eq_left (by omega), zero_add]
    · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right (by omega), add_zero]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hlast : ∑ k ∈ Finset.range (n + 1), (if k = n then ampT (n + 1) s * b else 0) =
      ampT (n + 1) s * b := by
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) n (fun _ => ampT (n + 1) s * b),
      ite_eq_left (Finset.mem_range.mpr (Nat.lt_succ_self n))]
  rw [hlast]
  have htail := tail_sum_le (n := n) s J hJ
  rw [← hA, pos_of_nonneg hu0.le] at htail
  have hT0 : 0 ≤ ampT (n + 1) s := ampT_nonneg s
  have hTle : ampT (n + 1) s * b ≤ 64 * A * A := by
    rcases le_or_gt s (cum (n + 1) (n + 1)) with hs | hs
    · rw [ampT_of_le hs, zero_mul]
      positivity
    · have hTA : ampT (n + 1) s ≤ A := by
        rcases Nat.lt_or_ge J (n + 1) with hlt | hge
        · exact ampT_le_amp hlt s
        · omega
      have hquarter : 1 / 4 ≤ u := by
        have hc : cum (n + 1) J + wt (n + 1) n ≤ cum (n + 1) (n + 1) := by
          rw [cum_succ]
          have := cum_mono (N := n + 1) hJ
          linarith
        have hwn : 1 / 4 ≤ wt (n + 1) n := by
          unfold wt
          refine le_trans ?_ (le_max_right _ _)
          have e : n + 1 - n = 1 := by omega
          rw [e, pow_one]
        rw [hu]
        linarith
      have hA16 : 1 / 16 ≤ A := by
        refine le_trans ?_ hAlow
        apply le_min
        · norm_num
        · linarith
      calc ampT (n + 1) s * b ≤ A * 4 := mul_le_mul hTA hb4 hb hA0
        _ ≤ 64 * A * A := by nlinarith
  have hmain : A * min (16 / 3) (4 * u) + 64 * A * A ≤ 128 * A ^ 2 := by
    rcases le_total 4 u with h4 | h4
    · have hAeq : A = 1 := by
        apply le_antisymm hA1
        refine le_trans ?_ hAlow
        apply le_min le_rfl
        linarith
      rw [hAeq]
      have := min_le_left (16 / 3 : ℝ) (4 * u)
      nlinarith
    · have hAu : u / 4 ≤ A := by
        refine le_trans ?_ hAlow
        apply le_min
        · linarith
        · exact le_rfl
      have := min_le_right (16 / 3 : ℝ) (4 * u)
      nlinarith [mul_le_mul_of_nonneg_left this hA0]
  have hsq := wt_sq (N := n + 1) (k := J) (by omega)
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hsq
  have hden : 128 * A ^ 2 ≤ alphaSeq (n + 1) s J ^ 2 / (lam * wt (n + 1) (J + 1)) := by
    rw [le_div_iff₀ (by positivity), hlam, alphaSeq, ← hA]
    have e : 128 * A ^ 2 * (1 / (2048 * ((n : ℝ) + 1)) * wt (n + 1) (J + 1)) =
        A ^ 2 * wt (n + 1) (J + 1) / (16 * ((n : ℝ) + 1)) := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)]
    have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
    nlinarith [mul_le_mul_of_nonneg_left hsq hA2]
  linarith

end Dominance

end LongTails.Proofs.NcPlSchedule
