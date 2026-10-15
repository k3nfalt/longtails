import LongTails.Proofs.OnlineMetricRun

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {w : Fin d → ℝ} {μ fstar : ℝ}
  {xstar x0 : EuclideanSpace ℝ (Fin d)} {b0 : Fin d → ℝ}

lemma weight_pos (s : Core d) : 0 < weight s := by
  unfold weight; have := stepScale_pos s; positivity

lemma extrapolate_apply (s : Core d) (hA : 0 ≤ s.A) (i : Fin d) :
    (s.A + weight s) * extrapolate s i = s.A * s.x i + weight s * s.z i := by
  have ha := weight_pos s
  simp only [extrapolate, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp

lemma sum_scaled (s : Core d) (g : EuclideanSpace ℝ (Fin d)) :
    ∑ i, stepScale s * metric s i * g i ^ 2 = stepScale s * ∑ i, metric s i * g i ^ 2 := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

lemma inv_continue {s : Core d} {n : ℕ} (H : Hyp f w μ fstar xstar) (_hd : 1 ≤ (d : ℝ))
    (I : Inv f w μ fstar x0 b0 s n)
    (hacc : f (trialPoint s (extrapolate s) (gradient f (extrapolate s))) ≤
      f (extrapolate s) - (∑ i, stepScale s * metric s i *
        gradient f (extrapolate s) i ^ 2) / 2)
    (hhalf : ¬ (f (trialPoint s (extrapolate s) (gradient f (extrapolate s))) - fstar ≤
      (s.fs - fstar) / 2)) :
    Inv f w μ fstar x0 b0
      { s with
        x := trialPoint s (extrapolate s) (gradient f (extrapolate s))
        z := s.z - weight s • scale (metric s) (gradient f (extrapolate s))
        A := s.A + weight s
        k := s.k + 1 } (n + 1) := by
  set y := extrapolate s
  set g := gradient f y
  set xp := trialPoint s y g
  have ha := weight_pos s
  have hθ := stepScale_pos s
  have hθa : weight s ^ 2 ≤ stepScale s * (s.A + weight s) := by
    have hl := I.A_lower
    unfold weight
    have hk : (0 : ℝ) ≤ s.k := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hl hθ.le]
  refine ⟨I.stage, I.box_ge, I.box_pow, I.band0, I.band1, I.phi, I.fs, I.halving, ?_, ?_, ?_,
    ?_, I.cuts, I.certified, I.prev, ?_⟩
  · intro u
    have hstep := metric_agd_step (f := f) H.conv (P := metric s)
      (metric_pos H.w_pos I.box_ge) I.A_nonneg ha hθa (x := s.x) (z := s.z) (u := u) (y := y)
      (xp := xp) (zp := s.z - weight s • scale (metric s) g)
      (fun i => extrapolate_apply s I.A_nonneg i)
      (fun i => by simp [scale]; exact Or.inl (Or.inl rfl))
      (by rw [sum_scaled] at hacc; exact hacc)
    have := I.pot u
    show (s.A + weight s) * (f xp - f u) +
        (∑ i, ((s.z - weight s • scale (metric s) g) i - u i) ^ 2 / metric s i) / 2 ≤
      (∑ i, (s.xs i - u i) ^ 2 / metric s i) / 2
    linarith
  · show 0 ≤ s.A + weight s; linarith [I.A_nonneg]
  · show stepScale s * (((s.k + 1 : ℕ) : ℝ) * (((s.k + 1 : ℕ) : ℝ) + 1)) / 4 ≤ s.A + weight s
    have hl := I.A_lower
    unfold weight
    push_cast
    nlinarith
  · intro _
    show (s.fs - fstar) / 2 < f xp - fstar
    push Not at hhalf; exact hhalf
  · obtain ⟨Xc, X0, X0', X1, X1', nc, n0, n1, ndrop, hep, hd1, hd2, hXc, hL0, hL1, hn⟩ :=
      I.ledger
    refine ⟨Xc, X0, X0', X1, X1', nc, n0, n1, ndrop, hep, hd1, hd2, hXc, hL0, hL1, ?_⟩
    show ((n + 1 : ℕ) : ℝ) ≤ _ + ((((s.k + 1 : ℕ) : ℝ)) + (s.cuts.length : ℝ))
    simp only [prevSteps] at hn ⊢
    push_cast
    linarith

lemma inv_cut {s : Core d} {n : ℕ} (H : Hyp f w μ fstar xstar) (_hd : 1 ≤ (d : ℝ))
    (I : Inv f w μ fstar x0 b0 s n)
    (hfail : ¬ (f (trialPoint s (extrapolate s) (gradient f (extrapolate s))) ≤
      f (extrapolate s) - (∑ i, stepScale s * metric s i *
        gradient f (extrapolate s) i ^ 2) / 2))
    (hbox : ¬ (2 * d * cutLevel (fun i => stepScale s * metric s i) (f (extrapolate s))
        (f (trialPoint s (extrapolate s) (gradient f (extrapolate s))))
        (gradient f (extrapolate s))
        (gradient f (trialPoint s (extrapolate s) (gradient f (extrapolate s)))) <
      ∑ i, cutVector (gradient f (extrapolate s))
        (gradient f (trialPoint s (extrapolate s) (gradient f (extrapolate s)))) i * s.b i)) :
    Inv f w μ fstar x0 b0
      { s with
        cuts := (fun i => 2 * cutVector (gradient f (extrapolate s))
            (gradient f (trialPoint s (extrapolate s) (gradient f (extrapolate s)))) i * s.b i /
          cutLevel (fun i => stepScale s * metric s i) (f (extrapolate s))
            (f (trialPoint s (extrapolate s) (gradient f (extrapolate s))))
            (gradient f (extrapolate s))
            (gradient f (trialPoint s (extrapolate s) (gradient f (extrapolate s))))) ::
          s.cuts } (n + 1) := by
  set y := extrapolate s
  set g := gradient f y
  set q : Fin d → ℝ := fun i => stepScale s * metric s i
  set xp := trialPoint s y g
  set g' := gradient f xp
  set ap := cutVector g g'
  set c := cutLevel q (f y) (f xp) g g'
  have hxp : xp = y - scale q g := rfl
  have hvalid := cut_valid H.w_pos H.smooth H.conv y q
  rw [← hxp] at hvalid
  have hq : ∀ i, 0 ≤ q i := fun i =>
    mul_nonneg (stepScale_pos s).le (metric_pos H.w_pos I.box_ge i).le
  have hexc : c < ∑ i, ap i * q i := by
    apply cut_exceeds hq
    push Not at hfail
    have e : ∑ i, q i * g i ^ 2 = ∑ i, stepScale s * metric s i * g i ^ 2 := rfl
    rw [e]; exact hfail
  have hap : ∀ i, 0 ≤ ap i := fun i => cutVector_nonneg g g' i
  have hwpos := H.w_pos
  have hc0 : 0 ≤ c := le_trans (Finset.sum_nonneg fun i _ => div_nonneg (hap i) (hwpos i).le)
    hvalid
  have hcpos : 0 < c := by
    rcases eq_or_lt_of_le hc0 with h | h
    · exfalso
      have hz : ∀ i, ap i = 0 := by
        intro i
        have hsum : ∑ i, ap i / w i ≤ 0 := h ▸ hvalid
        have hnn : ∀ j ∈ Finset.univ, 0 ≤ ap j / w j := fun j _ => div_nonneg (hap j) (hwpos j).le
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp
          (le_antisymm hsum (Finset.sum_nonneg hnn)) i (Finset.mem_univ _)
        rcases div_eq_zero_iff.mp this with h1 | h1
        · exact h1
        · exact absurd h1 (hwpos i).ne'
      simp [hz] at hexc
      linarith
    · exact h
  push Not at hbox
  set a : Fin d → ℝ := fun i => 2 * ap i * s.b i / c
  have hbpos : ∀ i, 0 < s.b i := fun i =>
    lt_of_lt_of_le (by have := hwpos i; positivity) (I.box_ge i)
  have ha0 : ∀ i, 0 ≤ a i := fun i => by
    have := hap i; have := hbpos i; positivity
  have hasum : ∑ i, a i ≤ 4 * d := by
    simp only [a]
    rw [← Finset.sum_div, div_le_iff₀ hcpos]
    have : ∑ i, 2 * ap i * s.b i = 2 * ∑ i, ap i * s.b i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]; linarith
  have har : ∑ i, a i * (1 / w i / (2 * s.b i)) ≤ 1 := by
    have e : ∑ i, a i * (1 / w i / (2 * s.b i)) = (∑ i, ap i / w i) / c := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [a]
      have := hbpos i; have := hwpos i
      field_simp
    rw [e, div_le_one hcpos]; exact hvalid
  have hcv : 2 / stepScale s < cutValue a s.φ := by
    have e : cutValue a s.φ = 2 / c * ∑ i, ap i * metric s i := by
      rw [cutValue, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [a, metric]; ring
    have e2 : ∑ i, ap i * q i = stepScale s * ∑ i, ap i * metric s i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [q]; ring
    rw [e2] at hexc
    rw [e]
    have hθ := stepScale_pos s
    rw [div_lt_iff₀ hθ]
    have : 2 / c * (stepScale s * ∑ i, ap i * metric s i) = 2 * ((stepScale s *
        ∑ i, ap i * metric s i) / c) := by ring
    have h2 : 1 < (stepScale s * ∑ i, ap i * metric s i) / c := by
      rw [one_lt_div hcpos]; exact hexc
    nlinarith
  have hss : stepScale { s with cuts := a :: s.cuts } = stepScale s / 2 := by
    unfold stepScale; simp [pow_succ]; ring
  refine ⟨I.stage, I.box_ge, I.box_pow, I.band0, I.band1, I.phi, I.fs, I.halving, I.pot,
    I.A_nonneg, ?_, I.not_halved, ?_, ?_, I.prev, ?_⟩
  · rw [hss]; have := I.A_lower; have := stepScale_pos s
    have hk : (0 : ℝ) ≤ s.k * (s.k + 1) := by positivity
    show stepScale s / 2 * (s.k * (s.k + 1)) / 4 ≤ s.A
    nlinarith
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨ha0, hasum, har⟩
    · exact I.cuts b hb
  · rw [hss]
    have hθ := stepScale_pos s
    have hb := (bestCut_spec (a :: s.cuts) s.φ).2.1 a List.mem_cons_self
    show 1 / (stepScale s / 2) ≤ (bestCut (a :: s.cuts) s.φ).1
    have e : 1 / (stepScale s / 2) = 2 / stepScale s := by field_simp
    rw [e]; linarith
  · obtain ⟨Xc, X0, X0', X1, X1', nc, n0, n1, ndrop, hep, hd1, hd2, hXc, hL0, hL1, hn⟩ :=
      I.ledger
    refine ⟨Xc, X0, X0', X1, X1', nc, n0, n1, ndrop, hep, hd1, hd2, hXc, hL0, hL1, ?_⟩
    show ((n + 1 : ℕ) : ℝ) ≤ _ + ((s.k : ℝ) + ((a :: s.cuts).length : ℝ))
    simp only [List.length_cons]
    simp only [prevSteps] at hn ⊢
    push_cast
    linarith

end OracleTemplate.OnlineMetricAccelerated
