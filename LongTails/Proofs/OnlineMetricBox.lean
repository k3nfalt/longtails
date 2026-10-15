import LongTails.Proofs.OnlineMetricStep

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {w : Fin d → ℝ} {μ fstar : ℝ}
  {xstar x0 : EuclideanSpace ℝ (Fin d)} {b0 : Fin d → ℝ}

lemma inv_box [NeZero d] {s : Core d} {n : ℕ} (H : Hyp f w μ fstar xstar) (hd : 1 ≤ (d : ℝ))
    (I : Inv f w μ fstar x0 b0 s n)
    (_hfail : ¬ (f (trialPoint s (extrapolate s) (gradient f (extrapolate s))) ≤
      f (extrapolate s) - (∑ i, stepScale s * metric s i *
        gradient f (extrapolate s) i ^ 2) / 2))
    (hbox : 2 * d * cutLevel (fun i => stepScale s * metric s i) (f (extrapolate s))
        (f (trialPoint s (extrapolate s) (gradient f (extrapolate s))))
        (gradient f (extrapolate s))
        (gradient f (trialPoint s (extrapolate s) (gradient f (extrapolate s)))) <
      ∑ i, cutVector (gradient f (extrapolate s))
        (gradient f (trialPoint s (extrapolate s) (gradient f (extrapolate s)))) i * s.b i) :
    Inv f w μ fstar x0 b0
      { s with
        b := Function.update s.b (cutIndex s (gradient f (extrapolate s))
            (gradient f (trialPoint s (extrapolate s) (gradient f (extrapolate s)))))
          (s.b (cutIndex s (gradient f (extrapolate s))
            (gradient f (trialPoint s (extrapolate s) (gradient f (extrapolate s))))) / 2)
        learner0 := freshLearner d
        learner1 := freshLearner d
        seg := s.seg + 1
        φ := (freshLearner d).φ
        x := s.xs
        z := s.xs
        A := 0
        k := 0
        cuts := [] } (n + 1) := by
  set y := extrapolate s
  set g := gradient f y
  set q : Fin d → ℝ := fun i => stepScale s * metric s i
  set xp := trialPoint s y g
  set g' := gradient f xp
  set ap := cutVector g g'
  set c := cutLevel q (f y) (f xp) g g'
  set j := cutIndex s g g'
  have hxp : xp = y - scale q g := rfl
  have hvalid := cut_valid H.w_pos H.smooth H.conv y q
  rw [← hxp] at hvalid
  have hap : ∀ i, 0 ≤ ap i := fun i => cutVector_nonneg g g' i
  have hwpos := H.w_pos
  have hc0 : 0 ≤ c := le_trans (Finset.sum_nonneg fun i _ => div_nonneg (hap i) (hwpos i).le)
    hvalid
  have hj : ∀ i, ap i * s.b i ≤ ap j * s.b j := fun i =>
    (Classical.choose_spec (Finset.exists_max_image Finset.univ
      (fun i => cutVector g g' i * s.b i) Finset.univ_nonempty)).2 i (Finset.mem_univ _)
  have hjbig : 2 * c < ap j * s.b j := by
    have hsum : ∑ i, ap i * s.b i ≤ d * (ap j * s.b j) := by
      calc ∑ i, ap i * s.b i ≤ ∑ _i : Fin d, ap j * s.b j := Finset.sum_le_sum fun i _ => hj i
        _ = d * (ap j * s.b j) := by simp
    have : 2 * d * c < d * (ap j * s.b j) := lt_of_lt_of_le hbox hsum
    have hdpos : (0 : ℝ) < d := by linarith
    nlinarith
  have hbpos : ∀ i, 0 < s.b i := fun i =>
    lt_of_lt_of_le (by have := hwpos i; positivity) (I.box_ge i)
  have hapj : 0 < ap j := by
    by_contra h
    have : ap j = 0 := le_antisymm (not_lt.mp h) (hap j)
    rw [this] at hjbig; linarith
  have hjw : ap j / w j ≤ c := by
    refine le_trans ?_ hvalid
    exact Finset.single_le_sum (fun i _ => div_nonneg (hap i) (hwpos i).le) (Finset.mem_univ j)
  have hhalf : 1 / w j ≤ s.b j / 2 := by
    have h1 : 1 / w j = (ap j / w j) / ap j := by field_simp
    rw [h1, div_le_iff₀ hapj]
    nlinarith
  obtain ⟨m, hm, hseg⟩ := I.box_pow
  have hκ := kappaRoot_ge_one H.μ_pos H.μ_le
  have hk := I.k_le H hd
  have hcl := I.cuts_len hd
  have hD := bandWidth_pos hd
  have hF := lossCap_nonneg (d := d) H.μ_pos
  refine ⟨I.stage, ?_, ?_, ⟨fun i => fresh_band hd i, le_rfl⟩, ⟨fun i => fresh_band hd i, le_rfl⟩,
    ?_, I.fs, I.halving, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show 1 / w i ≤ Function.update s.b j (s.b j / 2) i
    by_cases hij : i = j
    · rw [hij]; simpa using hhalf
    · rw [Function.update_of_ne hij]; exact I.box_ge i
  · refine ⟨Function.update m j (m j + 1), ?_, ?_⟩
    · intro i
      show Function.update s.b j (s.b j / 2) i = b0 i / 2 ^ (Function.update m j (m j + 1) i)
      by_cases hij : i = j
      · rw [hij]; simp only [Function.update_self]; rw [hm j, pow_succ]; field_simp
      · rw [Function.update_of_ne hij, Function.update_of_ne hij]; exact hm i
    · show s.seg + 1 = ∑ i, Function.update m j (m j + 1) i
      rw [Finset.sum_update_of_mem (Finset.mem_univ j), hseg,
        ← Finset.add_sum_erase _ _ (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase]
      ring
  · show (freshLearner d).φ = (learnerFor _ s.ep).φ
    unfold learnerFor; split_ifs <;> rfl
  · intro u
    show (0 : ℝ) * (f s.xs - f u) + _ ≤ _
    simp
  · show stepScale { s with cuts := ([] : List (Fin d → ℝ)) } * (((0 : ℕ) : ℝ) * ((0 : ℕ) + 1)) / 4 ≤ 0
    simp
  · intro h; exact absurd h (by norm_num)
  · intro a ha; simp at ha
  · show 1 / stepScale { s with cuts := ([] : List (Fin d → ℝ)) } ≤ (bestCut [] _).1
    simp [stepScale, bestCut]
  · have hp := I.prev
    unfold PrevOK at hp ⊢
    cases hR : s.prev with
    | none => rw [hR] at hp; exact hp
    | some R =>
      rw [hR] at hp
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
      refine ⟨h1, h2, h3, h4, h5, h6, by show R.seg ≤ s.seg + 1; omega, ?_, h9, h10⟩
      intro h; exfalso; change R.seg = s.seg + 1 at h; omega
  · obtain ⟨Xc, X0, X0', X1, X1', nc, n0, n1, ndrop, hep, hd1, hd2, hXc, hL0, hL1, hn⟩ :=
      I.ledger
    have hc0' := ledger_close hD hF hL0
    have hc1' := ledger_close hD hF hL1
    refine ⟨Xc + X0 + X1, 0, 0, 0, 0, nc + n0 + n1, 0, 0, ndrop, ?_, ?_, ?_, ?_,
      fresh_ledger _ _ _ _, fresh_ledger _ _ _ _, ?_⟩
    · show s.ep = _; rw [hep]; simp
    · cases hR : s.prev with
      | none => simp only [prevSeg, hR] at hd1 ⊢; omega
      | some R => simp only [prevSeg, hR] at hd1 ⊢; omega
    · cases hR : s.prev with
      | none => simp only [prevSeg, hR] at hd2 ⊢; omega
      | some R => simp only [prevSeg, hR] at hd2 ⊢; omega
    · show Xc + X0 + X1 ≤ 24 * kappaRoot μ * ((nc + n0 + n1 : ℕ) : ℝ) +
        ((s.seg + 1 : ℕ) : ℝ) * (9 / 2 * bandWidth d ^ 2 * lossCap d μ)
      push_cast
      nlinarith
    · show ((n + 1 : ℕ) : ℝ) ≤ (((nc + n0 + n1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ)) *
          (1 + logTwo d) + (Xc + X0 + X1) + 0 + 0 + ndrop * (runCap d μ + 1 + logTwo d) +
          prevSteps s + ((s.seg + 1 : ℕ) : ℝ) * (runCap d μ + 2 + logTwo d) +
          (((0 : ℕ) : ℝ) + (([] : List (Fin d → ℝ)).length : ℝ))
      push_cast
      simp only [List.length_nil, Nat.cast_zero, add_zero]
      nlinarith

end OracleTemplate.OnlineMetricAccelerated
