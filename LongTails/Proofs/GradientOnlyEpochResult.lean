import LongTails.Proofs.GradientOnlyEpoch

namespace LongTails.Proofs.GradientOnlyEpochResult

open scoped RealInnerProductSpace
open LongTails.Algorithms.GradientOnlyGuarded LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.GradientOnlyAgd LongTails.Proofs.GradientOnlyTests
open LongTails.Proofs.GradientOnlyGeometry LongTails.Proofs.GradientOnlyWitness
open LongTails.Proofs.GradientOnlyEpoch

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def epochResult (t : Tuning) (g : E → E) (c : E) : Verdict E :=
  finalize t c (agd t g c)
    (verdict t c (agd t g c) (g (stateX (agd t g c) t.N))
      (fun j => g (nodesA t c (agd t g c) j))
      (fun j => g (nodesB t c (agd t g c) (g (stateX (agd t g c) t.N)) j)))
    (fun j => g (nodesC t c (agd t g c)
      (verdict t c (agd t g c) (g (stateX (agd t g c) t.N))
        (fun j => g (nodesA t c (agd t g c) j))
        (fun j => g (nodesB t c (agd t g c) (g (stateX (agd t g c) t.N)) j))) j))

variable {f : E → ℝ}

lemma no_fail_zero {t : Tuning} (hv : Valid t) (c : E)
    (rA : (Fin t.N × Fin 2) × (Fin t.m × Fin 2) → E) :
    ¬ failA t c (agd t (gradient f) c) rA 0 := by
  rintro ⟨h, i, hp⟩
  apply hp
  have hx : stateX (agd t (gradient f) c) 0 = c := rfl
  have hy : stateY t (agd t (gradient f) c) 0 = c := ys_zero t hv (gradient f) c
  simp only [pairsA, hx, hy]
  split_ifs <;> exact passes_self t c c _ _

theorem epoch_result {t : Tuning} {L₁ L₃ Δ : ℝ} (hb : Bounds t L₁ L₃ Δ) (hf : ContDiff ℝ 3 f)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L₃ * ‖x - y‖)
    (x0 c : E) (hgap : ∀ x, f x0 - f x ≤ Δ) (hc : f c ≤ f x0) :
    (∃ x, epochResult t (gradient f) c = .finished x ∧ ‖gradient f x‖ ≤ t.ε) ∨
      (∃ c', epochResult t (gradient f) c = .moved c' ∧ f c' ≤ f c - t.α ^ 2 / (8192 * L₃)) := by
  have hv := hb.valid
  have hLne : t.L ≠ 0 := hv.L_pos.ne'
  have hα := hv.α_pos
  have hL₃ := hb.L₃_pos
  have hR := hv.R_nonneg
  have hTE : horizonIndex t c (agd t (gradient f) c) ≤ exitIndex t c (agd t (gradient f) c) :=
    min_le_left _ _
  have hTN : horizonIndex t c (agd t (gradient f) c) ≤ t.N := min_le_right _ _
  have hgain_le : ∀ D, t.α ^ 2 / (441 * L₃) ≤ D → t.α ^ 2 / (8192 * L₃) ≤ D := by
    intro D hD
    have : t.α ^ 2 / (8192 * L₃) ≤ t.α ^ 2 / (441 * L₃) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    linarith
  unfold epochResult
  generalize hV : verdict t c (agd t (gradient f) c) (gradient f (stateX (agd t (gradient f) c) t.N))
    (fun j => gradient f (nodesA t c (agd t (gradient f) c) j))
    (fun j => gradient f (nodesB t c (agd t (gradient f) c)
      (gradient f (stateX (agd t (gradient f) c) t.N)) j)) = V
  unfold verdict at hV
  dsimp only at hV
  split_ifs at hV with h1 h2 h3 h4 h5 <;> subst hV
  · right
    refine ⟨_, rfl, ?_⟩
    have hfail := firstTrue_spec _ _ h1
    have hno := firstTrue_not (failA t c (agd t (gradient f) c)
      (fun j => gradient f (nodesA t c (agd t (gradient f) c) j))) (horizonIndex t c (agd t (gradient f) c))
    set j := firstTrue (failA t c (agd t (gradient f) c)
      (fun j => gradient f (nodesA t c (agd t (gradient f) c) j))) (horizonIndex t c (agd t (gradient f) c))
    have hdesc := center_descent hb hf hlip hT c j h1.le hno
    have hj1 : 1 ≤ j := by
      by_contra hj
      have hj0 : j = 0 := by omega
      rw [hj0] at hfail
      exact no_fail_zero hv c _ hfail
    have hjE : j < exitIndex t c (agd t (gradient f) c) := by omega
    have hjN : j < t.N := by omega
    have hxv : f (xs t (gradient f) c j) ≤ f c :=
      (regValue_ge t.α hα.le c _).trans (hdesc j le_rfl)
    have hpv : f (xs t (gradient f) c (j - 1)) ≤ f c :=
      (regValue_ge t.α hα.le c _).trans (hdesc (j - 1) (by omega))
    have hxc : ‖xs t (gradient f) c j - c‖ ≤ t.R := close_of_exit t c hjE
    have hpc : ‖xs t (gradient f) c (j - 1) - c‖ ≤ t.R := close_of_exit t c (by omega)
    have hyc : ‖ys t (gradient f) c j - c‖ ≤ 3 * t.R := ys_close_of_exit t hv c hjE
    obtain ⟨u, hu_eq, hu_fail, hu_close, hu_val⟩ : ∃ u, candidate t c (agd t (gradient f) c)
        (fun j => gradient f (nodesA t c (agd t (gradient f) c) j)) j = u ∧
        ¬ passes t c u (ys t (gradient f) c j)
          (regGrad t.α c (ys t (gradient f) c j) (gradient f (ys t (gradient f) c j)))
          (fun jj => gradient f (nodes (ys t (gradient f) c j) u t.m jj)) ∧
        ‖u - c‖ ≤ 3 * t.R ∧ f u ≤ f c := by
      unfold candidate
      split_ifs with hacc
      · obtain ⟨h, hp⟩ := hacc
        refine ⟨_, rfl, ?_, by change ‖xs t (gradient f) c j - c‖ ≤ 3 * t.R; linarith, hxv⟩
        have := rA_eq (f := f) t c ⟨j, h⟩ 0
        simp only [↓reduceIte] at this
        rw [this] at hp
        simpa only [stateY_agd, stateX_agd, stateG_agd t (gradient f) c hLne j hjN, ↓reduceIte] using hp
      · obtain ⟨h, i, hp⟩ := hfail
        have hi : i = 1 := by
          by_contra hi1
          have hi0 : i = 0 := by fin_cases i <;> simp_all
          subst hi0
          exact hacc ⟨h, by simpa [pairsA] using hp⟩
        subst hi
        refine ⟨c, rfl, ?_, by simp; linarith, le_rfl⟩
        have := rA_eq (f := f) t c ⟨j, h⟩ 1
        simp only [show (1 : Fin 2) ≠ 0 from by decide, ite_false] at this
        rw [this] at hp
        simpa only [pairsA, show (1 : Fin 2) ≠ 0 from by decide, ite_false, stateY_agd,
          stateG_agd t (gradient f) c hLne j hjN] using hp
    have hne : u ≠ ys t (gradient f) c j := ne_of_fail hu_fail
    have hdef := fail_to_deficit hb hf hT hu_close hyc hu_fail
    have hwp := witness_progress hb hf hT c (agd t (gradient f) c) j u hxv hpv hu_val hxc hpc
      hu_close hyc (ys_momentum' t hv (gradient f) c j (by omega)) hne hdef
    rw [hu_eq]
    simpa [finalize, targets, nodesC] using hwp
  · right
    refine ⟨_, rfl, ?_⟩
    have hT_eq : horizonIndex t c (agd t (gradient f) c) = exitIndex t c (agd t (gradient f) c) :=
      min_eq_left h2
    have hfA : firstTrue (failA t c (agd t (gradient f) c)
        (fun j => gradient f (nodesA t c (agd t (gradient f) c) j)))
        (horizonIndex t c (agd t (gradient f) c)) = horizonIndex t c (agd t (gradient f) c) := by
      have := firstTrue_le (failA t c (agd t (gradient f) c)
        (fun j => gradient f (nodesA t c (agd t (gradient f) c) j))) (horizonIndex t c (agd t (gradient f) c))
      omega
    have hno := firstTrue_not (failA t c (agd t (gradient f) c)
      (fun j => gradient f (nodesA t c (agd t (gradient f) c) j))) (horizonIndex t c (agd t (gradient f) c))
    rw [hfA] at hno
    have hdesc := center_descent hb hf hlip hT c _ le_rfl hno _ le_rfl
    have hexit := firstTrue_spec (fun k => t.R < ‖stateX (agd t (gradient f) c) k - c‖) (t.N + 1)
      (by unfold exitIndex at h2; omega)
    try simp only [finalize]
    rw [hT_eq]
    change t.R < ‖xs t (gradient f) c (exitIndex t c (agd t (gradient f) c)) - c‖ at hexit
    rw [hT_eq] at hdesc
    unfold regValue at hdesc
    have hRR : t.R ^ 2 < ‖xs t (gradient f) c (exitIndex t c (agd t (gradient f) c)) - c‖ ^ 2 := by
      nlinarith
    have hαR : t.α * t.R ^ 2 = t.α ^ 2 / (441 * L₃) := by rw [hb.R_sq]; field_simp
    have h441 := hgain_le _ le_rfl
    have hαRR := mul_le_mul_of_nonneg_left hRR.le hα.le
    change f (xs t (gradient f) c (exitIndex t c (agd t (gradient f) c))) ≤ _
    linarith
  · left
    exact ⟨_, rfl, h3⟩
  · right
    refine ⟨_, rfl, ?_⟩
    have hEx : t.N < exitIndex t c (agd t (gradient f) c) := by omega
    have hT_eq : horizonIndex t c (agd t (gradient f) c) = t.N := min_eq_right (by omega)
    have hfA : firstTrue (failA t c (agd t (gradient f) c)
        (fun j => gradient f (nodesA t c (agd t (gradient f) c) j)))
        (horizonIndex t c (agd t (gradient f) c)) = horizonIndex t c (agd t (gradient f) c) := by
      have := firstTrue_le (failA t c (agd t (gradient f) c)
        (fun j => gradient f (nodesA t c (agd t (gradient f) c) j))) (horizonIndex t c (agd t (gradient f) c))
      omega
    have hno := firstTrue_not (failA t c (agd t (gradient f) c)
      (fun j => gradient f (nodesA t c (agd t (gradient f) c) j))) (horizonIndex t c (agd t (gradient f) c))
    rw [hfA] at hno
    have hdesc := center_descent hb hf hlip hT c _ le_rfl hno _ le_rfl
    rw [hT_eq] at hdesc
    try simp only [finalize]
    push Not at h3
    set x := xs t (gradient f) c t.N
    change ‖regGrad t.α c x (gradient f x)‖ ≤ t.ε / 10 at h4
    change t.ε < ‖gradient f x‖ at h3
    have hsplit : gradient f x = regGrad t.α c x (gradient f x) - (2 * t.α) • (x - c) := by
      simp [regGrad]
    have hgx : ‖gradient f x‖ ≤ ‖regGrad t.α c x (gradient f x)‖ + 2 * t.α * ‖x - c‖ := by
      calc
        _ = ‖regGrad t.α c x (gradient f x) - (2 * t.α) • (x - c)‖ := by rw [← hsplit]
        _ ≤ _ := (norm_sub_le _ _).trans (by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)])
    have hdist : 0.45 * t.ε / t.α ≤ ‖x - c‖ := by
      rw [div_le_iff₀ hα]
      nlinarith
    have hε := hb.ε_pos
    have hsq : (0.45 * t.ε / t.α) ^ 2 ≤ ‖x - c‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hdist 2
    unfold regValue at hdesc
    have hε2 := hb.ε_sq
    have hval : t.α * (0.45 * t.ε / t.α) ^ 2 = 0.2025 * t.α ^ 2 / (8 * L₃) := by
      field_simp
      rw [hε2]
      field_simp
      ring
    have hfin : t.α ^ 2 / (8192 * L₃) ≤ 0.2025 * t.α ^ 2 / (8 * L₃) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg t.α]
    have := mul_le_mul_of_nonneg_left hsq hα.le
    try simp only [stateX_agd]
    all_goals nlinarith
  · right
    refine ⟨_, rfl, ?_⟩
    have hEx : t.N < exitIndex t c (agd t (gradient f) c) := by omega
    have hT_eq : horizonIndex t c (agd t (gradient f) c) = t.N := min_eq_right (by omega)
    have hfA : firstTrue (failA t c (agd t (gradient f) c)
        (fun j => gradient f (nodesA t c (agd t (gradient f) c) j)))
        (horizonIndex t c (agd t (gradient f) c)) = horizonIndex t c (agd t (gradient f) c) := by
      have := firstTrue_le (failA t c (agd t (gradient f) c)
        (fun j => gradient f (nodesA t c (agd t (gradient f) c) j))) (horizonIndex t c (agd t (gradient f) c))
      omega
    have hno := firstTrue_not (failA t c (agd t (gradient f) c)
      (fun j => gradient f (nodesA t c (agd t (gradient f) c) j))) (horizonIndex t c (agd t (gradient f) c))
    rw [hfA] at hno
    have hdesc := center_descent hb hf hlip hT c _ le_rfl hno
    rw [hT_eq] at hdesc
    have hfail := firstTrue_spec _ _ h5
    set w := stall t c (agd t (gradient f) c) (gradient f (stateX (agd t (gradient f) c) t.N))
    set j := firstTrue (failB t c (agd t (gradient f) c) (gradient f (stateX (agd t (gradient f) c) t.N))
      (fun j => gradient f (nodesB t c (agd t (gradient f) c)
        (gradient f (stateX (agd t (gradient f) c) t.N)) j))) t.N
    obtain ⟨h, hp⟩ := hfail
    have hjE : j < exitIndex t c (agd t (gradient f) c) := by omega
    have hwc : ‖w - c‖ ≤ 3 * t.R := stall_close hb hlip c hEx
    have hyc : ‖ys t (gradient f) c j - c‖ ≤ 3 * t.R := ys_close_of_exit t hv c hjE
    have hp' : ¬ passes t c w (ys t (gradient f) c j)
        (regGrad t.α c (ys t (gradient f) c j) (gradient f (ys t (gradient f) c j)))
        (fun jj => gradient f (nodes (ys t (gradient f) c j) w t.m jj)) := by
      simpa only [nodesB, stateY_agd, stateG_agd t (gradient f) c hLne j h5] using hp
    have hne : w ≠ ys t (gradient f) c j := ne_of_fail hp'
    have hdef := fail_to_deficit hb hf hT hwc hyc hp'
    have hwv : f w ≤ f c := by
      have hd := reg_descent hα.le hv.L_pos (by rw [hb.L_eq]) (hasGradient_of hf) hlip c
        (xs t (gradient f) c t.N)
      have h0 := hdesc t.N le_rfl
      have hge := regValue_ge (f := f) t.α hα.le c w
      have hn : 0 ≤ ‖regGrad t.α c (xs t (gradient f) c t.N)
          (gradient f (xs t (gradient f) c t.N))‖ ^ 2 / (2 * t.L) := by
        have := hv.L_pos; positivity
      simp only [w, stall, stateX_agd] at hge ⊢
      linarith
    have hxv : f (xs t (gradient f) c j) ≤ f c :=
      (regValue_ge t.α hα.le c _).trans (hdesc j (by omega))
    have hpv : f (xs t (gradient f) c (j - 1)) ≤ f c :=
      (regValue_ge t.α hα.le c _).trans (hdesc (j - 1) (by omega))
    have hxc : ‖xs t (gradient f) c j - c‖ ≤ t.R := close_of_exit t c hjE
    have hpc : ‖xs t (gradient f) c (j - 1) - c‖ ≤ t.R := close_of_exit t c (by omega)
    have hwp := witness_progress hb hf hT c (agd t (gradient f) c) j w hxv hpv hwv hxc hpc
      hwc hyc (ys_momentum' t hv (gradient f) c j (by omega)) hne hdef
    simpa [finalize, targets, nodesC] using hwp
  · exfalso
    have hEx : t.N < exitIndex t c (agd t (gradient f) c) := by omega
    have hT_eq : horizonIndex t c (agd t (gradient f) c) = t.N := min_eq_right (by omega)
    have hfA : firstTrue (failA t c (agd t (gradient f) c)
        (fun j => gradient f (nodesA t c (agd t (gradient f) c) j)))
        (horizonIndex t c (agd t (gradient f) c)) = horizonIndex t c (agd t (gradient f) c) := by
      have := firstTrue_le (failA t c (agd t (gradient f) c)
        (fun j => gradient f (nodesA t c (agd t (gradient f) c) j))) (horizonIndex t c (agd t (gradient f) c))
      omega
    have hno := firstTrue_not (failA t c (agd t (gradient f) c)
      (fun j => gradient f (nodesA t c (agd t (gradient f) c) j))) (horizonIndex t c (agd t (gradient f) c))
    rw [hfA] at hno
    have hsupA := stepA_supports hb hf hT c _ le_rfl hno
    rw [hT_eq] at hsupA
    set w := stall t c (agd t (gradient f) c) (gradient f (stateX (agd t (gradient f) c) t.N))
    have hfB : firstTrue (failB t c (agd t (gradient f) c) (gradient f (stateX (agd t (gradient f) c) t.N))
        (fun j => gradient f (nodesB t c (agd t (gradient f) c)
          (gradient f (stateX (agd t (gradient f) c) t.N)) j))) t.N = t.N := by
      have := firstTrue_le (failB t c (agd t (gradient f) c) (gradient f (stateX (agd t (gradient f) c) t.N))
        (fun j => gradient f (nodesB t c (agd t (gradient f) c)
          (gradient f (stateX (agd t (gradient f) c) t.N)) j))) t.N
      omega
    have hnoB := firstTrue_not (failB t c (agd t (gradient f) c) (gradient f (stateX (agd t (gradient f) c) t.N))
        (fun j => gradient f (nodesB t c (agd t (gradient f) c)
          (gradient f (stateX (agd t (gradient f) c) t.N)) j))) t.N
    rw [hfB] at hnoB
    have hwc : ‖w - c‖ ≤ 3 * t.R := stall_close hb hlip c hEx
    have hsupB : ∀ k < t.N, supports f t c w (ys t (gradient f) c k)
        (regGrad t.α c (ys t (gradient f) c k) (gradient f (ys t (gradient f) c k))) := by
      intro k hk
      have hkE : k < exitIndex t c (agd t (gradient f) c) := by omega
      have hpass : passes t c w (ys t (gradient f) c k)
          (regGrad t.α c (ys t (gradient f) c k) (gradient f (ys t (gradient f) c k)))
          (fun jj => gradient f (nodes (ys t (gradient f) c k) w t.m jj)) := by
        by_contra hc
        exact hnoB k hk ⟨hk, by simpa only [nodesB, stateY_agd, stateG_agd t (gradient f) c hLne k hk] using hc⟩
      exact pass_to_supports hb hf hT hwc (ys_close_of_exit t hv c hkE) hpass
    have hprop := prop_one (f := f) (g := gradient f) t (hasGradient_of hf) hlip hα.le hv.L_pos
      (by rw [hb.L_eq]) (by rw [hv.μ_eq]; linarith) hv.a_nonneg hv.a_le hv.tune c w t.N le_rfl
      (fun k hk => by simpa using hsupA k hk 0) hsupB
    have hd := reg_descent hα.le hv.L_pos (by rw [hb.L_eq]) (hasGradient_of hf) hlip c
      (xs t (gradient f) c t.N)
    have hwdef : w = gradientStep t.L (xs t (gradient f) c t.N)
        (regGrad t.α c (xs t (gradient f) c t.N) (gradient f (xs t (gradient f) c t.N))) := rfl
    rw [← hwdef] at hd
    have hbr : regValue f t.α c c - regValue f t.α c w + t.μ / 2 * ‖w - c‖ ^ 2 ≤ Δ := by
      unfold regValue
      rw [hv.μ_eq]
      have := hgap w
      have hn : 0 ≤ ‖w - c‖ ^ 2 := sq_nonneg _
      simp only [sub_self, norm_zero]
      nlinarith
    have hpow : 0 ≤ (1 - t.a) ^ t.N := pow_nonneg (sub_nonneg.mpr hv.a_le) _
    have hchain := mul_le_mul_of_nonneg_left hbr hpow
    have hhor := hb.horizon
    push Not at h4
    change t.ε / 10 < ‖regGrad t.α c (xs t (gradient f) c t.N)
      (gradient f (xs t (gradient f) c t.N))‖ at h4
    have hG2 : (t.ε / 10) ^ 2 < ‖regGrad t.α c (xs t (gradient f) c t.N)
        (gradient f (xs t (gradient f) c t.N))‖ ^ 2 := by
      have := hb.ε_pos
      nlinarith
    have hL := hv.L_pos
    have key : ‖regGrad t.α c (xs t (gradient f) c t.N) (gradient f (xs t (gradient f) c t.N))‖ ^ 2 /
        (2 * t.L) ≤ t.ε ^ 2 / (200 * t.L) := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at key
    nlinarith

end LongTails.Proofs.GradientOnlyEpochResult
