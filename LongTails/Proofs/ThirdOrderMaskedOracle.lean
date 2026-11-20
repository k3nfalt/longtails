import LongTails.Proofs.RelativeHessianExposure
import LongTails.Proofs.AbcHardOracle
import LongTails.Proofs.ThirdOrderChainLipschitz

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.ThirdOrderMaskedOracle

open LongTails.Proofs.RelativeHessianSimulation (axes axes_inner axes_orthonormal)
open LongTails.Proofs.RelativeHessianOracle (prefixFunction rawPrefix partial_smooth rawPrefix_smooth
  partial_prefix partial_jet_outside full_jet_outside jet_prequery_bounded jet)
open LongTails.Proofs.RelativeHessianLocalized (radius radius_pos)
open LongTails.Proofs.RelativeHessianArctan (coefficient)
open LongTails.Proofs.RelativeHessianGeometry (edge edge_smooth edge_eq)
open LongTails.Proofs.AbcHardOracle (coin unif Scale toUnit coin_integral coin_sq_integral
  coin_integrable coin_measurable setOf_le_measurable)

variable {d n : ℕ}

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def stage (π : Fin (n + 1) ↪ Fin d) (w : Space d) : ℕ :=
  Finset.univ.sup (fun i : Fin (n + 1) => if 1 / 20 < |w (π i)| then i.val + 1 else 0)

noncomputable def stageUpTo (r : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d) : ℕ :=
  Finset.univ.sup (fun i : Fin (n + 1) => if i.val < r ∧ 1 / 20 < |w (π i)| then i.val + 1 else 0)

lemma small_of_stage (π : Fin (n + 1) ↪ Fin d) (w : Space d) (i : Fin (n + 1))
    (hi : stage π w ≤ i.val) : |w (π i)| ≤ 1 / 20 := by
  by_contra h
  push Not at h
  have hle : (if 1 / 20 < |w (π i)| then i.val + 1 else 0) ≤ stage π w :=
    Finset.le_sup (f := fun i : Fin (n + 1) => if 1 / 20 < |w (π i)| then i.val + 1 else 0)
      (Finset.mem_univ i)
  rw [ite_eq_left h] at hle
  omega

lemma stage_le (π : Fin (n + 1) ↪ Fin d) (w : Space d) : stage π w ≤ n + 1 := by
  apply Finset.sup_le
  intro i _
  split_ifs <;> omega

lemma stageUpTo_le (r : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d) : stageUpTo r π w ≤ r := by
  apply Finset.sup_le
  intro i _
  split_ifs with h <;> omega

lemma stageUpTo_eq (r : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d)
    (h : ∀ i : Fin (n + 1), r ≤ i.val → |w (π i)| ≤ 1 / 20) : stageUpTo r π w = stage π w := by
  unfold stageUpTo stage
  congr 1
  funext i
  by_cases hi : i.val < r
  · simp only [hi, true_and]
  · have := h i (by omega)
    simp only [hi, false_and, ↓reduceIte, show ¬ (1 / 20 : ℝ) < |w (π i)| by linarith]

lemma stageUpTo_congr (r : ℕ) (π ρ : Fin (n + 1) ↪ Fin d) (w : Space d)
    (h : ∀ i : Fin (n + 1), i.val < r → π i = ρ i) : stageUpTo r π w = stageUpTo r ρ w := by
  unfold stageUpTo
  congr 1
  funext i
  by_cases hi : i.val < r
  · rw [h i hi]
  · simp only [hi, false_and, ↓reduceIte]

noncomputable def partGrad (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (w : Space d) : Space d :=
  gradient (prefixFunction (axes π) r) w

noncomputable def hardValue (π : Fin (n + 1) ↪ Fin d) : Space d → ℝ :=
  RelativeHessianLocalized.value (axes π)

noncomputable def hardGrad (π : Fin (n + 1) ↪ Fin d) (w : Space d) : Space d :=
  gradient (hardValue π) w

lemma partGrad_prefix (π ρ : Fin (n + 1) ↪ Fin d) (r : ℕ) (w : Space d)
    (h : ∀ k : Fin (n + 1), k.val < r + 1 → π k = ρ k) : partGrad π r w = partGrad ρ r w := by
  unfold partGrad
  rw [partial_prefix (axes π) (axes ρ) r (fun j hj => by simp only [axes, h j hj])]

lemma quadratic_grad (w : Space d) :
    gradient (FullGeneralizedSmoothZeroQuery.quadratic coefficient (0 : Space d)) w =
      coefficient • w := RelativeHessianGuard.quadratic_gradient coefficient w

lemma partGrad_outside (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (w : Space d)
    (hw : 2 * radius n ≤ ‖w‖) : partGrad π r w = coefficient • w := by
  have h := congrArg (fun z => z.2.1) (partial_jet_outside (axes π) r w hw)
  simp only [jet] at h
  rw [partGrad, h, quadratic_grad]

lemma hardGrad_outside (π : Fin (n + 1) ↪ Fin d) (w : Space d)
    (hw : 2 * radius n ≤ ‖w‖) : hardGrad π w = coefficient • w := by
  have h := congrArg (fun z => z.2.1) (full_jet_outside (axes π) w hw)
  simp only [jet] at h
  rw [hardGrad, hardValue, h, quadratic_grad]

lemma hardGrad_eq_part (π : Fin (n + 1) ↪ Fin d) (s : ℕ) (w : Space d)
    (h : ‖w‖ ≤ 2 * radius n → ∀ i : Fin (n + 1), s ≤ i.val → i.val < n → |w (π i)| ≤ 1 / 20) :
    hardGrad π w = partGrad π s w := by
  have hj := jet_prequery_bounded (axes π) s w (fun hx i hi => by
    rw [axes_inner]
    have := h hx i.castSucc (by simpa using hi) (by simp)
    linarith)
  have hg := congrArg (fun z => z.2.1) hj
  simp only [jet] at hg
  exact hg

lemma rawPrefix_step {m : ℕ} (v : Fin (m + 1) → Space d) (hn : ∀ i, ‖v i‖ ≤ 1) (s : ℕ) :
    ∃ e : Space d → ℝ, ContDiff ℝ 3 e ∧ (∀ x, |e x| ≤ 4) ∧ (∀ x, ‖gradient e x‖ ≤ 2 ^ 50) ∧
      ∀ x, rawPrefix v s x = rawPrefix v (s - 1) x + e x := by
  have hzero : ∃ e : Space d → ℝ, ContDiff ℝ 3 e ∧ (∀ x, |e x| ≤ 4) ∧
      (∀ x, ‖gradient e x‖ ≤ 2 ^ 50) ∧ ∀ x, e x = 0 := by
    refine ⟨fun _ => 0, contDiff_const, fun x => by norm_num, fun x => ?_, fun x => rfl⟩
    have : gradient (fun _ : Space d => (0 : ℝ)) x = 0 := by
      have h : HasGradientAt (fun _ : Space d => (0 : ℝ)) (0 : Space d) x := by
        rw [hasGradientAt_iff_hasFDerivAt]
        simpa using hasFDerivAt_const (0 : ℝ) x
      exact h.gradient
    rw [this, norm_zero]
    positivity
  rcases Nat.eq_zero_or_pos s with hs | hs
  · obtain ⟨e, h1, h2, h3, h4⟩ := hzero
    refine ⟨e, h1, h2, h3, fun x => ?_⟩
    subst hs
    simp [h4 x]
  · obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    by_cases hk : k < m
    · refine ⟨edge (v (⟨k, hk⟩ : Fin m).castSucc) (v (⟨k, hk⟩ : Fin m).succ), edge_smooth _ _,
        fun x => ?_, fun x => (RelativeHessianChainBounds.edge_bounds _ _ x (hn _) (hn _)).1,
        fun x => ?_⟩
      · rw [edge_eq, abs_le]
        have := RelativeHessianChain.link_bounds ⟪v (⟨k, hk⟩ : Fin m).castSucc, x⟫
          ⟪v (⟨k, hk⟩ : Fin m).succ, x⟫
        constructor <;> linarith [Real.pi_lt_four, this.1, this.2]
      · unfold rawPrefix
        rw [add_assoc]
        congr 1
        have hsplit : ∀ i : Fin m, (if i.val < k + 1 then edge (v i.castSucc) (v i.succ) x else 0) =
            (if i.val < k then edge (v i.castSucc) (v i.succ) x else 0) +
              (if i = (⟨k, hk⟩ : Fin m) then edge (v i.castSucc) (v i.succ) x else 0) := by
          intro i
          by_cases h1 : i.val < k
          · have h2 : i ≠ (⟨k, hk⟩ : Fin m) := fun h => by rw [h] at h1; simp at h1
            simp [h1, h2, Nat.lt_succ_of_lt h1]
          · by_cases h2 : i = (⟨k, hk⟩ : Fin m)
            · subst h2; simp
            · have h3 : ¬ i.val < k + 1 := by
                intro h
                exact h2 (Fin.ext (by simp; omega))
              simp [h1, h2, h3]
        simp_rw [hsplit]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (⟨k, hk⟩ : Fin m)]
        simp
    · obtain ⟨e, h1, h2, h3, h4⟩ := hzero
      refine ⟨e, h1, h2, h3, fun x => ?_⟩
      rw [h4 x, add_zero]
      unfold rawPrefix
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have hi := i.isLt
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]

lemma secret_bound (π : Fin (n + 1) ↪ Fin d) (s : ℕ) (w : Space d) :
    ‖partGrad π s w - partGrad π (s - 1) w‖ ≤ 2 ^ 51 := by
  have hv := axes_orthonormal π
  obtain ⟨e, he, hval, hgrad, hstep⟩ := rawPrefix_step (axes π) (fun i => (hv.norm_eq_one i).le) s
  have hcs := RelativeHessianCutoffSpatial.smooth (E := Space d) (radius n)
  have hfun : prefixFunction (axes π) s = fun y => 1 * prefixFunction (axes π) (s - 1) y +
      1 * (RelativeHessianCutoffSpatial.value (radius n) y * e y) := by
    funext y
    unfold prefixFunction
    rw [hstep y]
    ring
  have hg := ThirdOrderAffineCalculus.combination_gradient (partial_smooth (axes π) (s - 1))
    (hcs.mul he) 1 1 w
  unfold partGrad
  rw [hfun, hg, one_smul, one_smul, add_sub_cancel_left,
    ProductCompositionJets.product_gradient hcs he]
  obtain ⟨hc0, hc1, -, -, -⟩ := ThirdOrderChainLipschitz.cutoff_small (E := Space d) n w
  have hN : (1 : ℝ) / (n + 1 : ℕ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast Nat.succ_pos n)]; exact_mod_cast Nat.succ_pos n
  calc _ ≤ ‖RelativeHessianCutoffSpatial.value (radius n) w • gradient e w‖ +
        ‖e w • gradient (RelativeHessianCutoffSpatial.value (radius n)) w‖ := norm_add_le _ _
    _ = |RelativeHessianCutoffSpatial.value (radius n) w| * ‖gradient e w‖ +
        |e w| * ‖gradient (RelativeHessianCutoffSpatial.value (radius n)) w‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * 2 ^ 50 + 4 * 1 := add_le_add (mul_le_mul hc0 (hgrad w) (norm_nonneg _) (by norm_num))
        (mul_le_mul (hval w) (hc1.trans hN) (norm_nonneg _) (by norm_num))
    _ ≤ 2 ^ 51 := by norm_num

lemma partGrad_continuous (π : Fin (n + 1) ↪ Fin d) (r : ℕ) : Continuous (partGrad π r) :=
  (LongTails.Proofs.GradientDependentLocal.gradient_contDiff_two (partial_smooth (axes π) r)).continuous

lemma hardGrad_continuous (π : Fin (n + 1) ↪ Fin d) : Continuous (hardGrad π) :=
  (LongTails.Proofs.GradientDependentLocal.gradient_contDiff_two
    (RelativeHessianLocalized.smooth (axes π))).continuous

lemma hardGrad_lower (π : Fin (n + 1) ↪ Fin d) (w : Space d)
    (h : ‖w‖ ≤ 2 * radius n → |w (π (Fin.last n))| ≤ 1 / 20) : 7 / 10 ≤ ‖hardGrad π w‖ := by
  unfold hardGrad hardValue
  by_cases hw : ‖w‖ ≤ 2 * radius n
  · apply RelativeHessianLocalized.hidden_gradient (axes_orthonormal π)
    refine ⟨Fin.last n, ?_⟩
    rw [axes_inner]
    linarith [h hw]
  · have hr := radius_pos n
    have hg := RelativeHessianLocalized.outside_gradient (axes_orthonormal π) w (by linarith)
    have hR := RelativeHessianLocalized.radius_large n
    linarith

noncomputable def objective (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) : ℝ :=
  S.a * hardValue π (toUnit S x0 x)

noncomputable def objGrad (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) : Space d :=
  (S.a / S.lam) • hardGrad π (toUnit S x0 x)

noncomputable def knownPart (S : Scale) (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (x0 x : Space d) :
    Space d :=
  (S.a / S.lam) • partGrad π (m - 1) (toUnit S x0 x)

noncomputable def fullPart (S : Scale) (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (x0 x : Space d) :
    Space d :=
  (S.a / S.lam) • partGrad π m (toUnit S x0 x)

noncomputable def reply (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d)
    (ω : ℝ) : Space d :=
  knownPart S π (stage π (toUnit S x0 x)) x0 x +
    coin q ω • (objGrad S π x0 x - knownPart S π (stage π (toUnit S x0 x)) x0 x)

lemma objGrad_eq_full (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    objGrad S π x0 x = fullPart S π (stage π (toUnit S x0 x)) x0 x := by
  unfold objGrad fullPart
  rw [hardGrad_eq_part π (stage π (toUnit S x0 x)) (toUnit S x0 x)
    (fun _ i hi _ => small_of_stage π _ i hi)]

lemma secret_norm (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    ‖objGrad S π x0 x - knownPart S π (stage π (toUnit S x0 x)) x0 x‖ ≤ 2 ^ 51 * (S.a / S.lam) := by
  rw [objGrad_eq_full, fullPart, knownPart, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (by have := S.ha; have := S.hlam; positivity), mul_comm]
  exact mul_le_mul_of_nonneg_right (secret_bound π _ _)
    (by have := S.ha; have := S.hlam; positivity)

lemma reply_integral (S : Scale) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    ∫ ω, reply S q π x0 x ω ∂unif = objGrad S π x0 x := by
  unfold reply
  rw [integral_add (integrable_const _) ((coin_integrable _).smul_const _), integral_const,
    probReal_univ, one_smul, integral_smul_const, coin_integral _ hq0 hq1, one_smul]
  abel

lemma reply_integrable (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    Integrable (reply S q π x0 x) unif := by
  unfold reply
  exact (integrable_const _).add ((coin_integrable _).smul_const _)

lemma reply_variance (S : Scale) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    ∫ ω, ‖reply S q π x0 x ω - objGrad S π x0 x‖ ^ 2 ∂unif =
      (1 / q - 1) * ‖objGrad S π x0 x - knownPart S π (stage π (toUnit S x0 x)) x0 x‖ ^ 2 := by
  set m := stage π (toUnit S x0 x)
  set v := objGrad S π x0 x - knownPart S π m x0 x
  have he : (fun ω => ‖reply S q π x0 x ω - objGrad S π x0 x‖ ^ 2) =
      fun ω => (coin q ω - 1) ^ 2 * ‖v‖ ^ 2 := by
    funext ω
    have : reply S q π x0 x ω - objGrad S π x0 x = (coin q ω - 1) • v := by
      simp only [reply, v, m, sub_smul, one_smul]
      abel
    rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [he, integral_mul_const, coin_sq_integral _ hq0 hq1]

lemma reply_variance_integrable (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x0 x : Space d) :
    Integrable (fun ω => ‖reply S q π x0 x ω - objGrad S π x0 x‖ ^ 2) unif := by
  set m := stage π (toUnit S x0 x)
  set v := objGrad S π x0 x - knownPart S π m x0 x
  have he : (fun ω => ‖reply S q π x0 x ω - objGrad S π x0 x‖ ^ 2) =
      fun ω => Set.indicator {ω | ω ≤ q} (fun _ => ((1 / q - 1) ^ 2 - 1) * ‖v‖ ^ 2) ω +
        ‖v‖ ^ 2 := by
    funext ω
    have : reply S q π x0 x ω - objGrad S π x0 x = (coin q ω - 1) • v := by
      simp only [reply, v, m, sub_smul, one_smul]
      abel
    rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp only [coin, Set.indicator, Set.mem_ofPred_eq]
    split_ifs <;> ring
  rw [he]
  exact ((integrable_const _).indicator (setOf_le_measurable _)).add (integrable_const _)

end LongTails.Proofs.ThirdOrderMaskedOracle
