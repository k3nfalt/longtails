import LongTails.Proofs.GradientOnlyWitness

namespace LongTails.Proofs.GradientOnlyEpoch

open scoped RealInnerProductSpace
open LongTails.Algorithms.GradientOnlyGuarded LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.GradientOnlyAgd LongTails.Proofs.GradientOnlyTests
open LongTails.Proofs.GradientOnlyGeometry LongTails.Proofs.GradientOnlyWitness

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

structure Bounds (t : Tuning) (L₁ L₃ Δ : ℝ) : Prop where
  valid : Valid t
  L₁_nonneg : 0 ≤ L₁
  L₃_pos : 0 < L₃
  L_eq : t.L = L₁ + 2 * t.α
  τ_eq : t.τ = t.α / 32
  m_eq : t.m = 16
  R_sq : t.R ^ 2 = t.α / (441 * L₃)
  η_nonneg : 0 ≤ t.η
  η_sq : t.η ^ 2 = t.α / (16 * L₃)
  q_eq : t.q = t.α ^ 2 / (4096 * L₃)
  ε_pos : 0 < t.ε
  ε_sq : t.ε ^ 2 = t.α ^ 3 / (8 * L₃)
  N_pos : 1 ≤ t.N
  horizon : (1 - t.a) ^ t.N * Δ ≤ t.ε ^ 2 / (200 * t.L)

omit [FiniteDimensional ℝ E] in
lemma passes_self (t : Tuning) (c u G : E) (r : Fin t.m × Fin 2 → E) : passes t c u u G r := by
  unfold passes pairValue surrogateOf
  simp

omit [FiniteDimensional ℝ E] in
lemma ne_of_fail {t : Tuning} {c u v G : E} {r : Fin t.m × Fin 2 → E}
    (h : ¬ passes t c u v G r) : u ≠ v := by
  rintro rfl
  exact h (passes_self t c u G r)

omit [FiniteDimensional ℝ E] in
lemma ys_momentum' (t : Tuning) (hv : Valid t) (g : E → E) (c : E) (j : ℕ) (hj : j ≤ t.N) :
    ys t g c j = xs t g c j + ((1 - t.a) / (1 + t.a)) • (xs t g c j - xs t g c (j - 1)) := by
  cases j with
  | zero => simp [ys_zero t hv g c, xs_zero]
  | succ j => simpa using ys_momentum t hv g c j (by omega)

lemma theta_bounds (t : Tuning) (hv : Valid t) :
    0 ≤ (1 - t.a) / (1 + t.a) ∧ (1 - t.a) / (1 + t.a) ≤ 1 :=
  ⟨div_nonneg (by linarith [hv.a_le]) (by linarith [hv.a_nonneg]),
    (div_le_one (by linarith [hv.a_nonneg])).mpr (by linarith [hv.a_nonneg])⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma pair_small {t : Tuning} {L₁ L₃ Δ : ℝ} (hb : Bounds t L₁ L₃ Δ) {u v c : E}
    (hu : ‖u - c‖ ≤ 3 * t.R) (hv : ‖v - c‖ ≤ 3 * t.R) :
    L₃ * ‖u - v‖ ^ 4 / (t.m : ℝ) ^ 3 ≤ t.τ * ‖u - v‖ ^ 2 := by
  have hR := hb.valid.R_nonneg
  have hd : ‖u - v‖ ≤ 6 * t.R := by
    calc
      _ = ‖(u - c) - (v - c)‖ := by congr 1; abel
      _ ≤ ‖u - c‖ + ‖v - c‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hd2 : ‖u - v‖ ^ 2 ≤ 36 * t.R ^ 2 := by nlinarith [norm_nonneg (u - v)]
  rw [hb.m_eq, hb.τ_eq]
  have hR2 := hb.R_sq
  have hα := hb.valid.α_pos
  have hL := hb.L₃_pos
  have h4 : ‖u - v‖ ^ 4 = ‖u - v‖ ^ 2 * ‖u - v‖ ^ 2 := by ring
  rw [h4]
  have hn : 0 ≤ ‖u - v‖ ^ 2 := sq_nonneg _
  have hkey : L₃ * ‖u - v‖ ^ 2 ≤ 36 * t.α / 441 := by
    have := mul_le_mul_of_nonneg_left hd2 hL.le
    rw [hR2] at this
    have he : L₃ * (36 * (t.α / (441 * L₃))) = 36 * t.α / 441 := by field_simp
    linarith
  have : L₃ * (‖u - v‖ ^ 2 * ‖u - v‖ ^ 2) / ((16 : ℕ) : ℝ) ^ 3 ≤
      (36 * t.α / 441) * ‖u - v‖ ^ 2 / 4096 := by
    rw [show L₃ * (‖u - v‖ ^ 2 * ‖u - v‖ ^ 2) = (L₃ * ‖u - v‖ ^ 2) * ‖u - v‖ ^ 2 by ring]
    norm_num
    gcongr
  calc
    _ ≤ (36 * t.α / 441) * ‖u - v‖ ^ 2 / 4096 := this
    _ ≤ t.α / 32 * ‖u - v‖ ^ 2 := by nlinarith

section Semantic

variable {f : E → ℝ}

lemma close_of_exit (t : Tuning) (c : E) {k : ℕ}
    (hk : k < exitIndex t c (agd t (gradient f) c)) : ‖xs t (gradient f) c k - c‖ ≤ t.R := by
  have h := firstTrue_not (fun k => t.R < ‖stateX (agd t (gradient f) c) k - c‖) (t.N + 1) k hk
  push Not at h
  simpa only [stateX_agd] using h

lemma ys_close_of_exit (t : Tuning) (hv : Valid t) (c : E) {k : ℕ}
    (hk : k < exitIndex t c (agd t (gradient f) c)) : ‖ys t (gradient f) c k - c‖ ≤ 3 * t.R := by
  cases k with
  | zero =>
    rw [ys_zero t hv]
    simp only [sub_self, norm_zero]
    linarith [hv.R_nonneg]
  | succ k =>
    have hE := firstTrue_le (fun k => t.R < ‖stateX (agd t (gradient f) c) k - c‖) (t.N + 1)
    have hk' : k + 1 < exitIndex t c (agd t (gradient f) c) := hk
    unfold exitIndex at hk'
    exact ys_close t hv (gradient f) c k (by omega) (close_of_exit t c hk) (close_of_exit t c (by omega))

lemma hasGradient_of {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) : HasGradientAt f (gradient f x) x :=
  (hf.differentiable (by norm_num) x).hasGradientAt

lemma pass_to_supports {t : Tuning} {L₁ L₃ Δ : ℝ} (hb : Bounds t L₁ L₃ Δ) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L₃ * ‖x - y‖) {c u v G : E}
    (hu : ‖u - c‖ ≤ 3 * t.R) (hv : ‖v - c‖ ≤ 3 * t.R)
    (hp : passes t c u v G (fun j => gradient f (nodes v u t.m j))) : supports f t c u v G := by
  have hm : 0 < t.m := by rw [hb.m_eq]; norm_num
  exact pass_supports t hp (pair_error hf hb.L₃_pos.le hT t hm c u v G) (pair_small hb hu hv)

lemma fail_to_deficit {t : Tuning} {L₁ L₃ Δ : ℝ} (hb : Bounds t L₁ L₃ Δ) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L₃ * ‖x - y‖) {c u v : E}
    (hu : ‖u - c‖ ≤ 3 * t.R) (hv : ‖v - c‖ ≤ 3 * t.R)
    (hp : ¬ passes t c u v (regGrad t.α c v (gradient f v)) (fun j => gradient f (nodes v u t.m j))) :
    f u - f v - ⟪gradient f v, u - v⟫ ≤ -t.α * ‖u - v‖ ^ 2 / 2 := by
  have hm : 0 < t.m := by rw [hb.m_eq]; norm_num
  exact fail_deficit t hp (pair_error hf hb.L₃_pos.le hT t hm c u v _) (pair_small hb hu hv)
    hb.valid.μ_eq hb.τ_eq hb.valid.α_pos.le

lemma rA_eq (t : Tuning) (c : E) (k : Fin t.N) (i : Fin 2) :
    (fun j => gradient f (nodesA t c (agd t (gradient f) c) ((k, i), j))) =
      fun j => gradient f (nodes (ys t (gradient f) c k)
        (if i = 0 then xs t (gradient f) c k else c) t.m j) := by
  funext j
  simp only [nodesA, pairsA, stateY_agd, stateX_agd]

lemma stepA_supports {t : Tuning} {L₁ L₃ Δ : ℝ} (hb : Bounds t L₁ L₃ Δ) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L₃ * ‖x - y‖) (c : E) (n : ℕ)
    (hn : n ≤ horizonIndex t c (agd t (gradient f) c))
    (hno : ∀ k < n, ¬ failA t c (agd t (gradient f) c)
      (fun j => gradient f (nodesA t c (agd t (gradient f) c) j)) k) :
    ∀ k < n, ∀ i : Fin 2,
      supports f t c (if i = 0 then xs t (gradient f) c k else c) (ys t (gradient f) c k)
        (regGrad t.α c (ys t (gradient f) c k) (gradient f (ys t (gradient f) c k))) := by
  intro k hk i
  have hv := hb.valid
  have hLne : t.L ≠ 0 := hv.L_pos.ne'
  have hTE : horizonIndex t c (agd t (gradient f) c) ≤ exitIndex t c (agd t (gradient f) c) :=
    min_le_left _ _
  have hTN : horizonIndex t c (agd t (gradient f) c) ≤ t.N := min_le_right _ _
  have hkN : k < t.N := by omega
  have hkE : k < exitIndex t c (agd t (gradient f) c) := by omega
  have hpass : passes t c (if i = 0 then xs t (gradient f) c k else c) (ys t (gradient f) c k)
      (regGrad t.α c (ys t (gradient f) c k) (gradient f (ys t (gradient f) c k)))
      (fun j => gradient f (nodes (ys t (gradient f) c k)
        (if i = 0 then xs t (gradient f) c k else c) t.m j)) := by
    by_contra hc
    apply hno k hk
    refine ⟨hkN, i, ?_⟩
    rw [rA_eq (f := f) t c ⟨k, hkN⟩ i]
    simpa only [pairsA, stateY_agd, stateX_agd, stateG_agd t (gradient f) c hLne k hkN] using hc
  have hu : ‖(if i = 0 then xs t (gradient f) c k else c) - c‖ ≤ 3 * t.R := by
    split_ifs
    · linarith [close_of_exit (f := f) t c hkE, hv.R_nonneg]
    · simp only [sub_self, norm_zero]; linarith [hv.R_nonneg]
  exact pass_to_supports hb hf hT hu (ys_close_of_exit t hv c hkE) hpass

lemma center_descent {t : Tuning} {L₁ L₃ Δ : ℝ} (hb : Bounds t L₁ L₃ Δ) (hf : ContDiff ℝ 3 f)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L₃ * ‖x - y‖) (c : E) (n : ℕ)
    (hn : n ≤ horizonIndex t c (agd t (gradient f) c))
    (hno : ∀ k < n, ¬ failA t c (agd t (gradient f) c)
      (fun j => gradient f (nodesA t c (agd t (gradient f) c) j)) k) :
    ∀ j ≤ n, regValue f t.α c (xs t (gradient f) c j) ≤ f c := by
  intro j hj
  have hv := hb.valid
  have hLne : t.L ≠ 0 := hv.L_pos.ne'
  have hT' : horizonIndex t c (agd t (gradient f) c) ≤ exitIndex t c (agd t (gradient f) c) :=
    min_le_left _ _
  have hTN : horizonIndex t c (agd t (gradient f) c) ≤ t.N := min_le_right _ _
  have hsup := fun k (hk : k < j) => stepA_supports hb hf hT c n hn hno k (by omega)
  have hh := prop_one (f := f) (g := gradient f) t (hasGradient_of hf) hlip hv.α_pos.le hv.L_pos
    (by rw [hb.L_eq]) (by rw [hv.μ_eq]; linarith [hv.α_pos]) hv.a_nonneg hv.a_le hv.tune c c j (by omega)
    (fun k hk => by simpa using hsup k hk 0) (fun k hk => by simpa using hsup k hk 1)
  have hc : regValue f t.α c c = f c := by simp [regValue]
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, add_zero] at hh
  linarith

end Semantic

section Witness

variable {f : E → ℝ}

omit [FiniteDimensional ℝ E] in
lemma escape_dist {η R : ℝ} {u v c : E} (hη : 0 ≤ η) (hne : u ≠ v)
    (hu : ‖u - c‖ ≤ R) (hv : ‖v - c‖ ≤ R) (i : Fin 4) :
    ‖escapePoints η u v i - c‖ ≤ R + η := by
  have hn : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hs : ‖(η / ‖u - v‖) • (u - v)‖ = η := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hη, abs_of_pos hn]
    field_simp
  set w := (η / ‖u - v‖) • (u - v) with hw
  have h0 : ‖escapePoints η u v 0 - c‖ ≤ R + η := by
    rw [show escapePoints η u v 0 - c = (u - c) + w by simp [escapePoints, hw]; abel]
    exact (norm_add_le _ _).trans (by rw [hs]; linarith)
  have h1 : ‖escapePoints η u v 1 - c‖ ≤ R + η := by
    rw [show escapePoints η u v 1 - c = (u - c) - w by simp [escapePoints, hw]; abel]
    exact (norm_sub_le _ _).trans (by rw [hs]; linarith)
  have h2 : ‖escapePoints η u v 2 - c‖ ≤ R + η := by
    rw [show escapePoints η u v 2 - c = (v - c) + w by simp [escapePoints, hw]; abel]
    exact (norm_add_le _ _).trans (by rw [hs]; linarith)
  have h3 : ‖escapePoints η u v 3 - c‖ ≤ R + η := by
    rw [show escapePoints η u v 3 - c = (v - c) - w by simp [escapePoints, hw]; abel]
    exact (norm_sub_le _ _).trans (by rw [hs]; linarith)
  fin_cases i
  exacts [h0, h1, h2, h3]

lemma witness_progress {t : Tuning} {L₁ L₃ Δ : ℝ} (hb : Bounds t L₁ L₃ Δ) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L₃ * ‖x - y‖)
    (c : E) (states : ℕ → E × E) (j : ℕ) (u : E)
    (hx : f (stateX states j) ≤ f c) (hp : f (stateX states (j - 1)) ≤ f c) (hu : f u ≤ f c)
    (hxc : ‖stateX states j - c‖ ≤ t.R) (hpc : ‖stateX states (j - 1) - c‖ ≤ t.R)
    (huc : ‖u - c‖ ≤ 3 * t.R) (hvc : ‖stateY t states j - c‖ ≤ 3 * t.R)
    (hvx : stateY t states j = stateX states j +
      ((1 - t.a) / (1 + t.a)) • (stateX states j - stateX states (j - 1)))
    (hne : u ≠ stateY t states j)
    (hdef : f u - f (stateY t states j) - ⟪gradient f (stateY t states j), u - stateY t states j⟫ ≤
      -t.α * ‖u - stateY t states j‖ ^ 2 / 2) :
    f (choose t c (escapeCandidates t states ⟨j, u, stateY t states j⟩)
      (fun i => gradient f (nodes c (escapeCandidates t states ⟨j, u, stateY t states j⟩ i.1) t.m i.2))) ≤
      f c - t.α ^ 2 / (8192 * L₃) := by
  have hv := hb.valid
  have hR := hv.R_nonneg
  have hα := hv.α_pos
  have hL₃ := hb.L₃_pos
  have hη := hb.η_nonneg
  set x := stateX states j
  set pr := stateX states (j - 1)
  set v := stateY t states j
  obtain ⟨hθ0, hθ1⟩ := theta_bounds t hv
  have huv : ‖u - v‖ ≤ 6 * t.R := by
    calc
      _ = ‖(u - c) - (v - c)‖ := by congr 1; abel
      _ ≤ ‖u - c‖ + ‖v - c‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hshort : 3 * L₃ * ‖u - v‖ ^ 2 ≤ t.α / 4 := by
    have h2 : ‖u - v‖ ^ 2 ≤ 36 * t.R ^ 2 := by nlinarith [norm_nonneg (u - v)]
    rw [hb.R_sq] at h2
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 3 * L₃)
    have he : 3 * L₃ * (36 * (t.α / (441 * L₃))) = 108 * t.α / 441 := by field_simp; ring
    linarith
  have hηsq : L₃ * t.η ^ 2 ≤ t.α / 16 := by
    rw [hb.η_sq]
    field_simp
    rfl
  have hstep : ‖x - pr‖ ≤ 2 * t.R := by
    calc
      _ = ‖(x - c) - (pr - c)‖ := by congr 1; abel
      _ ≤ ‖x - c‖ + ‖pr - c‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hbudget : 14 * t.q + 384 * L₃ * t.R ^ 4 ≤ t.α * t.η ^ 2 / 4 := by
    rw [hb.q_eq, show t.R ^ 4 = (t.R ^ 2) ^ 2 by ring, hb.R_sq, hb.η_sq]
    field_simp
    nlinarith [sq_nonneg t.α]
  obtain ⟨i, hi⟩ := witness_candidates hf hL₃.le hT hα.le (by rw [hb.q_eq]; positivity) hθ0 hθ1
    x pr u v hvx hx hp hu hne hdef hshort hηsq hstep hR hbudget
  have hE := escape_dist (c := c) hη hne (R := 3 * t.R) huc hvc
  have hc0 : ‖(1 / 2 : ℝ) • (x + pr) - c‖ ≤ 5 * t.R + t.η := by
    rw [show (1 / 2 : ℝ) • (x + pr) - c = (1 / 2 : ℝ) • (x - c) + (1 / 2 : ℝ) • (pr - c) by module]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hc1 : ‖(-2 : ℝ) • x + (3 : ℝ) • pr - c‖ ≤ 5 * t.R + t.η := by
    rw [show (-2 : ℝ) • x + (3 : ℝ) • pr - c = (-2 : ℝ) • (x - c) + (3 : ℝ) • (pr - c) by module]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    norm_num
    linarith
  have hD : ∀ k : Fin 6, ‖escapeCandidates t states ⟨j, u, v⟩ k - c‖ ≤ 5 * t.R + t.η := by
    intro k
    fin_cases k
    exacts [hc0, hc1, (hE 0).trans (by linarith), (hE 1).trans (by linarith),
      (hE 2).trans (by linarith), (hE 3).trans (by linarith)]
  have hm : (t.m : ℝ) = 16 := by rw [hb.m_eq]; norm_num
  have hmpos : 0 < t.m := by rw [hb.m_eq]; norm_num
  set e := L₃ * (2 * (25 * t.R ^ 2 + t.η ^ 2)) ^ 2 / 4096
  have herr : ∀ k, |surrogateOf (fun jj => gradient f (nodes c (escapeCandidates t states ⟨j, u, v⟩
      (k, jj).1) t.m (k, jj).2)) c (escapeCandidates t states ⟨j, u, v⟩ k) -
      (f (escapeCandidates t states ⟨j, u, v⟩ k) - f c)| ≤ e := by
    intro k
    have hs := LongTails.Proofs.GradientQuadrature.surrogate_error hf hL₃.le hT c (escapeCandidates t states ⟨j, u, v⟩ k) hmpos
    rw [← surrogateOf_nodes] at hs
    refine hs.trans ?_
    have hd := hD k
    have hd2 : ‖escapeCandidates t states ⟨j, u, v⟩ k - c‖ ^ 2 ≤ 2 * (25 * t.R ^ 2 + t.η ^ 2) := by
      have h0 : 0 ≤ ‖escapeCandidates t states ⟨j, u, v⟩ k - c‖ := norm_nonneg _
      nlinarith [sq_nonneg (5 * t.R - t.η)]
    have hd4 : ‖escapeCandidates t states ⟨j, u, v⟩ k - c‖ ^ 4 ≤ (2 * (25 * t.R ^ 2 + t.η ^ 2)) ^ 2 := by
      rw [show ‖escapeCandidates t states ⟨j, u, v⟩ k - c‖ ^ 4 =
        (‖escapeCandidates t states ⟨j, u, v⟩ k - c‖ ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ (sq_nonneg _) hd2 2
    rw [hm]
    have := mul_le_mul_of_nonneg_left hd4 hL₃.le
    norm_num
    show _ ≤ L₃ * (2 * (25 * t.R ^ 2 + t.η ^ 2)) ^ 2 / 4096
    linarith
  have he_val : e = L₃ * (2 * (25 * (t.α / (441 * L₃)) + t.α / (16 * L₃))) ^ 2 / 4096 := by
    simp only [e, hb.R_sq, hb.η_sq]
  have hQ : 0 < t.α ^ 2 / (4096 * L₃) := by positivity
  have he' : e = (1682 / 7056) ^ 2 * (t.α ^ 2 / (4096 * L₃)) := by
    rw [he_val]
    field_simp
    ring
  have heq : e < t.q := by
    rw [he', hb.q_eq]
    nlinarith
  have hprog := choose_progress (f := f) t c (escapeCandidates t states ⟨j, u, v⟩)
    (fun i => gradient f (nodes c (escapeCandidates t states ⟨j, u, v⟩ i.1) t.m i.2)) heq herr
    ⟨i, by simpa [escapeCandidates] using hi⟩
  have hfin : t.q - 2 * e ≥ t.α ^ 2 / (8192 * L₃) := by
    have hh : t.α ^ 2 / (8192 * L₃) = (t.α ^ 2 / (4096 * L₃)) / 2 := by field_simp; ring
    rw [he', hb.q_eq, hh]
    nlinarith
  linarith

end Witness

section Main

variable {f : E → ℝ}

omit [FiniteDimensional ℝ E] in
lemma reg_lipschitz' {g : E → E} {L₁ α : ℝ} (hα : 0 ≤ α)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L₁ * ‖x - y‖) (c x y : E) :
    ‖regGrad α c x (g x) - regGrad α c y (g y)‖ ≤ (L₁ + 2 * α) * ‖x - y‖ := by
  have he : regGrad α c x (g x) - regGrad α c y (g y) = (g x - g y) + (2 * α) • (x - y) := by
    unfold regGrad
    module
  rw [he]
  calc
    _ ≤ ‖g x - g y‖ + ‖(2 * α) • (x - y)‖ := norm_add_le _ _
    _ ≤ L₁ * ‖x - y‖ + 2 * α * ‖x - y‖ := by
      gcongr
      · exact hlip x y
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ = _ := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma regValue_ge (α : ℝ) (hα : 0 ≤ α) (c x : E) : f x ≤ regValue f α c x := by
  unfold regValue
  have : 0 ≤ α * ‖x - c‖ ^ 2 := by positivity
  linarith

lemma stall_close {t : Tuning} {L₁ L₃ Δ : ℝ} (hb : Bounds t L₁ L₃ Δ)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖) (c : E)
    (hEx : t.N < exitIndex t c (agd t (gradient f) c)) :
    ‖stall t c (agd t (gradient f) c) (gradient f (stateX (agd t (gradient f) c) t.N)) - c‖ ≤
      3 * t.R := by
  have hv := hb.valid
  have hL := hv.L_pos
  have hN := hb.N_pos
  have h1 : ‖xs t (gradient f) c 1 - c‖ ≤ t.R := close_of_exit t c (by omega)
  have hNc : ‖xs t (gradient f) c t.N - c‖ ≤ t.R := close_of_exit t c (by omega)
  have hx1 : xs t (gradient f) c 1 = c - t.L⁻¹ • gradient f c := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, xs_succ t (gradient f) c 0 (by omega), ys_zero t hv]
    simp [gradientStep, regGrad]
  have hgc : ‖gradient f c‖ ≤ t.L * t.R := by
    rw [hx1, show c - t.L⁻¹ • gradient f c - c = -(t.L⁻¹ • gradient f c) by abel, norm_neg,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] at h1
    have := mul_le_mul_of_nonneg_left h1 hL.le
    field_simp at this ⊢
    linarith
  have hFc : regGrad t.α c c (gradient f c) = gradient f c := by simp [regGrad]
  have hlipF := reg_lipschitz' hv.α_pos.le hlip c (xs t (gradient f) c t.N) c
  rw [hFc, ← hb.L_eq] at hlipF
  have hFN : ‖regGrad t.α c (xs t (gradient f) c t.N) (gradient f (xs t (gradient f) c t.N))‖ ≤
      2 * t.L * t.R := by
    calc
      _ ≤ ‖regGrad t.α c (xs t (gradient f) c t.N) (gradient f (xs t (gradient f) c t.N)) -
            gradient f c‖ + ‖gradient f c‖ := norm_le_norm_sub_add _ _
      _ ≤ t.L * ‖xs t (gradient f) c t.N - c‖ + t.L * t.R := add_le_add hlipF hgc
      _ ≤ t.L * t.R + t.L * t.R := by gcongr
      _ = _ := by ring
  unfold stall gradientStep
  simp only [stateX_agd]
  calc
    _ = ‖(xs t (gradient f) c t.N - c) - t.L⁻¹ • regGrad t.α c (xs t (gradient f) c t.N)
          (gradient f (xs t (gradient f) c t.N))‖ := by congr 1; abel
    _ ≤ ‖xs t (gradient f) c t.N - c‖ + ‖t.L⁻¹ • regGrad t.α c (xs t (gradient f) c t.N)
          (gradient f (xs t (gradient f) c t.N))‖ := norm_sub_le _ _
    _ ≤ t.R + t.L⁻¹ * (2 * t.L * t.R) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
      gcongr
    _ = 3 * t.R := by field_simp; ring

end Main

end LongTails.Proofs.GradientOnlyEpoch
