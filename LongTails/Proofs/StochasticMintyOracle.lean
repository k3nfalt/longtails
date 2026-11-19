import LongTails.Proofs.MintyChainGeometry
import LongTails.Proofs.AbcHardContinuity

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.StochasticMintyOracle

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Proofs.MintyChainGeometry
open LongTails.Proofs.AbcHardOracle (coin unif coin_integral coin_sq_integral coin_integrable
  coin_measurable setOf_le_measurable)

variable {d k : ℕ}

lemma lift_congr_support (π ρ : Fin (k + 1) ↪ Fin d) (c : Fin (k + 1) → ℝ)
    (h : ∀ j, c j ≠ 0 → π j = ρ j) : lift π c = lift ρ c := by
  ext i
  change (∑ j, if π j = i then c j else 0) = ∑ j, if ρ j = i then c j else 0
  apply Finset.sum_congr rfl
  intro j _
  by_cases hc : c j = 0
  · simp [hc]
  · rw [h j hc]

noncomputable def known (κ r : ℝ) (π : Fin (k + 1) ↪ Fin d) (m : ℕ)
    (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  lift π (fun j => if j.val < m then coef κ r π v j else 0)

noncomputable def stage (r : ℝ) (π : Fin (k + 1) ↪ Fin d) (v : EuclideanSpace ℝ (Fin d)) : ℕ :=
  Finset.univ.sup (fun j : Fin (k + 1) => if r / 4 < |v (π j)| then j.val + 1 else 0)

noncomputable def stageUpTo (r : ℝ) (π : Fin (k + 1) ↪ Fin d) (m : ℕ)
    (v : EuclideanSpace ℝ (Fin d)) : ℕ :=
  Finset.univ.sup (fun j : Fin (k + 1) => if j.val < m ∧ r / 4 < |v (π j)| then j.val + 1 else 0)

noncomputable def reply (κ r B q : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (u : EuclideanSpace ℝ (Fin d)) (ω : ℝ) : EuclideanSpace ℝ (Fin d) :=
  known κ r π (stage r π (ball B u)) (ball B u) +
    coin q ω • (chain κ r π (ball B u) - known κ r π (stage r π (ball B u)) (ball B u)) +
    κ • (u - ball B u)

noncomputable def simReply (κ r B q : ℝ) (π : Fin (k + 1) ↪ Fin d) (m : ℕ)
    (u : EuclideanSpace ℝ (Fin d)) (ω : ℝ) : EuclideanSpace ℝ (Fin d) :=
  known κ r π (stageUpTo r π m (ball B u)) (ball B u) +
    (if stageUpTo r π m (ball B u) < m then
      coin q ω • (known κ r π (stageUpTo r π m (ball B u) + 1) (ball B u) -
        known κ r π (stageUpTo r π m (ball B u)) (ball B u))
    else 0) +
    κ • (u - ball B u)

lemma known_prefix (κ r : ℝ) (π ρ : Fin (k + 1) ↪ Fin d) (m t : ℕ) (hm : m ≤ t)
    (h : ∀ j : Fin (k + 1), j.val < t → π j = ρ j) (v : EuclideanSpace ℝ (Fin d)) :
    known κ r π m v = known κ r ρ m v := by
  unfold known
  have hc : (fun j : Fin (k + 1) => if j.val < m then coef κ r π v j else 0) =
      fun j => if j.val < m then coef κ r ρ v j else 0 := by
    funext j
    split_ifs with hj
    · exact coef_prefix κ r π ρ (m - 1) (fun j' hj' => h j' (by omega)) v j (by omega)
    · rfl
  rw [hc]
  apply lift_congr_support
  intro j hj
  by_cases hjm : j.val < m
  · exact h j (by omega)
  · simp [hjm] at hj

lemma stageUpTo_congr (r : ℝ) (π ρ : Fin (k + 1) ↪ Fin d) (m : ℕ) (v : EuclideanSpace ℝ (Fin d))
    (h : ∀ j : Fin (k + 1), j.val < m → π j = ρ j) :
    stageUpTo r π m v = stageUpTo r ρ m v := by
  unfold stageUpTo
  congr 1
  funext j
  by_cases hj : j.val < m
  · rw [h j hj]
  · simp only [hj, false_and, ↓reduceIte]

lemma small_of_stage (r : ℝ) (π : Fin (k + 1) ↪ Fin d) (v : EuclideanSpace ℝ (Fin d))
    (j : Fin (k + 1)) (hj : stage r π v ≤ j.val) : |v (π j)| ≤ r / 4 := by
  by_contra h
  push Not at h
  have hle : (if r / 4 < |v (π j)| then j.val + 1 else 0) ≤ stage r π v :=
    Finset.le_sup (f := fun j : Fin (k + 1) => if r / 4 < |v (π j)| then j.val + 1 else 0)
      (Finset.mem_univ j)
  rw [ite_eq_left h] at hle
  omega

lemma stage_le (r : ℝ) (π : Fin (k + 1) ↪ Fin d) (v : EuclideanSpace ℝ (Fin d)) :
    stage r π v ≤ k + 1 := by
  apply Finset.sup_le
  intro j _
  split_ifs <;> omega

lemma stageUpTo_le (r : ℝ) (π : Fin (k + 1) ↪ Fin d) (m : ℕ) (v : EuclideanSpace ℝ (Fin d)) :
    stageUpTo r π m v ≤ m := by
  apply Finset.sup_le
  intro j _
  split_ifs with h <;> omega

lemma stageUpTo_eq (r : ℝ) (π : Fin (k + 1) ↪ Fin d) (m : ℕ) (v : EuclideanSpace ℝ (Fin d))
    (h : ∀ j : Fin (k + 1), m ≤ j.val → |v (π j)| ≤ r / 4) :
    stageUpTo r π m v = stage r π v := by
  unfold stageUpTo stage
  congr 1
  funext j
  by_cases hj : j.val < m
  · simp only [hj, true_and]
  · have := h j (by omega)
    simp only [hj, false_and, ↓reduceIte, show ¬ r / 4 < |v (π j)| by linarith]

lemma coef_zero_beyond (κ r : ℝ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (s : ℕ)
    (hs : ∀ j : Fin (k + 1), s ≤ j.val → |v (π j)| ≤ r / 4) (j : Fin (k + 1))
    (hj : s + 1 ≤ j.val) : coef κ r π v j = 0 := by
  cases j using Fin.cases with
  | zero => simp at hj
  | succ i =>
    have hi := hs i.castSucc (by simp only [Fin.val_castSucc, Fin.val_succ] at hj ⊢; omega)
    unfold coef act
    simp only [Fin.cases_succ]
    rw [ramp_of_le κ r _ hr ((le_abs_self _).trans hi), zero_mul]

lemma chain_eq_known (κ r : ℝ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (s : ℕ)
    (hs : ∀ j : Fin (k + 1), s ≤ j.val → |v (π j)| ≤ r / 4) :
    chain κ r π v = known κ r π (s + 1) v := by
  unfold chain known
  congr 1
  funext j
  split_ifs with hj
  · rfl
  · exact coef_zero_beyond κ r hr π v s hs j (by omega)

lemma known_full (κ r : ℝ) (π : Fin (k + 1) ↪ Fin d) (m : ℕ) (hm : k + 1 ≤ m)
    (v : EuclideanSpace ℝ (Fin d)) : known κ r π m v = chain κ r π v := by
  unfold known chain
  congr 1
  funext j
  rw [ite_eq_left (by omega)]

lemma coef_abs_le (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (v : EuclideanSpace ℝ (Fin d)) (j : Fin (k + 1)) : |coef κ r π v j| ≤ κ * r := by
  unfold coef
  rw [abs_mul, abs_of_nonneg (act_nonneg κ r hκ π v j)]
  exact mul_le_mul (act_le κ r hκ π v j) (clip_abs_le r _ hr.le) (abs_nonneg _) hκ

lemma frontier_norm_sq (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (v : EuclideanSpace ℝ (Fin d)) :
    ‖chain κ r π v - known κ r π (stage r π v) v‖ ^ 2 ≤ κ ^ 2 * r ^ 2 := by
  set s := stage r π v
  rw [chain_eq_known κ r hr π v s (fun j hj => small_of_stage r π v j hj), known, known, lift_sub,
    norm_lift_sq]
  have hterm (j : Fin (k + 1)) : ((if j.val < s + 1 then coef κ r π v j else 0) -
      (if j.val < s then coef κ r π v j else 0)) ^ 2 ≤
      if j.val = s then κ ^ 2 * r ^ 2 else 0 := by
    have hb := coef_abs_le κ r hκ hr π v j
    have hb2 : coef κ r π v j ^ 2 ≤ κ ^ 2 * r ^ 2 := by
      rw [← sq_abs, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    by_cases h1 : j.val < s
    · rw [ite_eq_left (by omega), ite_eq_left h1, sub_self, zero_pow two_ne_zero]
      split_ifs <;> positivity
    · by_cases h2 : j.val = s
      · rw [ite_eq_left (by omega), ite_eq_right h1, sub_zero, ite_eq_left h2]
        exact hb2
      · rw [ite_eq_right (by omega), ite_eq_right h1, sub_self, ite_eq_right h2]
        norm_num
  refine (Finset.sum_le_sum (fun j _ => hterm j)).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun j : Fin (k + 1) => j.val = s)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact Fin.ext (by omega)
  have hc' : ((Finset.univ.filter (fun j : Fin (k + 1) => j.val = s)).card : ℝ) ≤ 1 := by
    exact_mod_cast hc
  nlinarith [sq_nonneg (κ * r), mul_pow κ r 2]

lemma reply_sub_field (κ r B q : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (u : EuclideanSpace ℝ (Fin d)) (ω : ℝ) :
    reply κ r B q π u ω - field κ r B π u = (coin q ω - 1) •
      (chain κ r π (ball B u) - known κ r π (stage r π (ball B u)) (ball B u)) := by
  simp only [reply, field, sub_smul, one_smul]
  abel

lemma reply_integrable (κ r B q : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : EuclideanSpace ℝ (Fin d)) :
    Integrable (reply κ r B q π u) unif := by
  unfold reply
  exact ((integrable_const _).add ((coin_integrable _).smul_const _)).add (integrable_const _)

lemma reply_integral (κ r B q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (π : Fin (k + 1) ↪ Fin d)
    (u : EuclideanSpace ℝ (Fin d)) :
    ∫ ω, reply κ r B q π u ω ∂unif = field κ r B π u := by
  unfold reply field
  rw [integral_add ((integrable_const _).add ((coin_integrable _).smul_const _))
      (integrable_const _),
    integral_add (integrable_const _) ((coin_integrable _).smul_const _), integral_const,
    integral_const, probReal_univ, one_smul, one_smul, integral_smul_const,
    coin_integral _ hq0 hq1, one_smul]
  abel

lemma reply_variance (κ r B q : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (π : Fin (k + 1) ↪ Fin d) (u : EuclideanSpace ℝ (Fin d)) :
    ∫ ω, ‖reply κ r B q π u ω - field κ r B π u‖ ^ 2 ∂unif ≤ (1 / q - 1) * (κ ^ 2 * r ^ 2) := by
  set V := chain κ r π (ball B u) - known κ r π (stage r π (ball B u)) (ball B u)
  have he : (fun ω => ‖reply κ r B q π u ω - field κ r B π u‖ ^ 2) =
      fun ω => (coin q ω - 1) ^ 2 * ‖V‖ ^ 2 := by
    funext ω
    rw [reply_sub_field, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [he, integral_mul_const, coin_sq_integral _ hq0 hq1]
  have hq : 0 ≤ 1 / q - 1 := by
    rw [sub_nonneg, le_div_iff₀ hq0, one_mul]
    exact hq1
  exact mul_le_mul_of_nonneg_left (frontier_norm_sq κ r hκ hr π (ball B u)) hq

lemma reply_variance_integrable (κ r B q : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (u : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ω => ‖reply κ r B q π u ω - field κ r B π u‖ ^ 2) unif := by
  set V := chain κ r π (ball B u) - known κ r π (stage r π (ball B u)) (ball B u)
  have he : (fun ω => ‖reply κ r B q π u ω - field κ r B π u‖ ^ 2) =
      fun ω => Set.indicator {ω | ω ≤ q} (fun _ => ((1 / q - 1) ^ 2 - 1) * ‖V‖ ^ 2) ω +
        ‖V‖ ^ 2 := by
    funext ω
    rw [reply_sub_field, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp only [coin, Set.indicator, Set.mem_ofPred_eq]
    split_ifs <;> ring
  rw [he]
  exact ((integrable_const _).indicator (setOf_le_measurable _)).add (integrable_const _)

lemma known_lipschitz (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d) (m : ℕ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    ‖known κ r π m u - known κ r π m v‖ ≤ 5 * κ * ‖u - v‖ := by
  unfold known
  rw [lift_sub, ← sq_le_sq₀ (norm_nonneg _) (by positivity), norm_lift_sq]
  refine le_trans ?_ ((coef_sq_sum κ r hκ hr π u v).trans_eq (by ring))
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_rfl
  · nlinarith [sq_nonneg (coef κ r π u j - coef κ r π v j)]

lemma known_continuous (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d) (m : ℕ) :
    Continuous (known κ r π m) := by
  apply LipschitzWith.continuous (K := ⟨5 * κ, by positivity⟩)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  exact known_lipschitz κ r hκ hr π m u v

lemma chain_continuous (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d) :
    Continuous (chain κ r π) := by
  apply LipschitzWith.continuous (K := ⟨5 * κ, by positivity⟩)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  exact chain_lipschitz κ r hκ hr π u v

lemma ball_continuous (B : ℝ) (hB : 0 < B) : Continuous (ball (E := EuclideanSpace ℝ (Fin d)) B) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  exact ball_lipschitz B hB u v

lemma stage_measurable (r B : ℝ) (hB : 0 < B) (π : Fin (k + 1) ↪ Fin d) :
    Measurable (fun u : EuclideanSpace ℝ (Fin d) => stage r π (ball B u)) := by
  have hne : (Finset.univ : Finset (Fin (k + 1))).Nonempty := Finset.univ_nonempty
  have he : (fun u : EuclideanSpace ℝ (Fin d) => stage r π (ball B u)) = Finset.univ.sup' hne
      (fun (j : Fin (k + 1)) (u : EuclideanSpace ℝ (Fin d)) =>
        if r / 4 < |ball B u (π j)| then j.val + 1 else 0) := by
    funext u
    rw [Finset.sup'_apply, Finset.sup'_eq_sup]
    rfl
  rw [he]
  apply Finset.measurable_sup'
  intro j _
  apply Measurable.ite _ measurable_const measurable_const
  apply measurableSet_lt measurable_const
  have hc : Continuous (fun u : EuclideanSpace ℝ (Fin d) => |ball B u (π j)|) :=
    continuous_abs.comp ((PiLp.continuous_apply 2 _ (π j)).comp (ball_continuous B hB))
  exact hc.measurable

lemma reply_measurable (κ r B q : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (hB : 0 < B)
    (π : Fin (k + 1) ↪ Fin d) :
    Measurable (Function.uncurry (reply κ r B q π)) := by
  let G : (EuclideanSpace ℝ (Fin d) × ℝ) × ℕ → EuclideanSpace ℝ (Fin d) := fun p =>
    known κ r π p.2 (ball B p.1.1) +
      coin q p.1.2 • (chain κ r π (ball B p.1.1) - known κ r π p.2 (ball B p.1.1)) +
      κ • (p.1.1 - ball B p.1.1)
  have hG : Measurable G := by
    apply measurable_from_prod_countable_left
    intro m
    have hb : Continuous (fun z : EuclideanSpace ℝ (Fin d) × ℝ => ball B z.1) :=
      (ball_continuous B hB).comp continuous_fst
    have hk : Measurable (fun z : EuclideanSpace ℝ (Fin d) × ℝ => known κ r π m (ball B z.1)) :=
      ((known_continuous κ r hκ hr π m).comp hb).measurable
    have hc : Measurable (fun z : EuclideanSpace ℝ (Fin d) × ℝ => chain κ r π (ball B z.1)) :=
      ((chain_continuous κ r hκ hr π).comp hb).measurable
    have hq : Measurable (fun z : EuclideanSpace ℝ (Fin d) × ℝ => coin q z.2) :=
      (coin_measurable q).comp measurable_snd
    have hw : Measurable (fun z : EuclideanSpace ℝ (Fin d) × ℝ => κ • (z.1 - ball B z.1)) :=
      ((continuous_fst.sub hb).const_smul κ).measurable
    exact (hk.add (hq.smul (hc.sub hk))).add hw
  have he : Function.uncurry (reply κ r B q π) =
      G ∘ (fun z : EuclideanSpace ℝ (Fin d) × ℝ => (z, stage r π (ball B z.1))) := by
    funext z
    rfl
  rw [he]
  exact hG.comp (measurable_id.prodMk ((stage_measurable r B hB π).comp measurable_fst))

lemma simReply_prefix (κ r B q : ℝ) (π ρ : Fin (k + 1) ↪ Fin d) (m : ℕ)
    (u : EuclideanSpace ℝ (Fin d)) (ω : ℝ) (h : ∀ j : Fin (k + 1), j.val < m → π j = ρ j) :
    simReply κ r B q π m u ω = simReply κ r B q ρ m u ω := by
  have hs := stageUpTo_congr r π ρ m (ball B u) h
  have hle := stageUpTo_le r ρ m (ball B u)
  unfold simReply
  rw [hs, known_prefix κ r π ρ _ m hle h]
  split_ifs with hlt
  · rw [known_prefix κ r π ρ _ m (by omega) h]
  · rfl

lemma reply_eq_simReply (κ r B q : ℝ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (u : EuclideanSpace ℝ (Fin d)) (m m' : ℕ) (hm : m ≤ m') (ω : ℝ)
    (hsmall : ∀ j : Fin (k + 1), m ≤ j.val → |ball B u (π j)| ≤ r / 4)
    (hcoin : m' = m → k + 1 ≤ m ∨ q < ω) :
    reply κ r B q π u ω = simReply κ r B q π m' u ω := by
  have hsm' : ∀ j : Fin (k + 1), m' ≤ j.val → |ball B u (π j)| ≤ r / 4 :=
    fun j hj => hsmall j (by omega)
  have hst : stageUpTo r π m' (ball B u) = stage r π (ball B u) :=
    stageUpTo_eq r π m' (ball B u) hsm'
  have hstage : stage r π (ball B u) ≤ m := by
    rw [← stageUpTo_eq r π m (ball B u) hsmall]
    exact stageUpTo_le r π m (ball B u)
  have hchain := chain_eq_known κ r hr π (ball B u) (stage r π (ball B u))
    (fun j hj => small_of_stage r π (ball B u) j hj)
  unfold simReply reply
  rw [hst]
  by_cases hlt : stage r π (ball B u) < m'
  · rw [ite_eq_left hlt, hchain]
  · rw [ite_eq_right hlt, add_zero]
    have heq : stage r π (ball B u) = m := by omega
    rcases hcoin (by omega) with hfull | hω
    · rw [known_full κ r π _ (by omega) (ball B u), sub_self, smul_zero, add_zero]
    · have hc0 : coin q ω = 0 := by
        unfold coin
        rw [ite_eq_right (not_le.mpr hω)]
      rw [hc0, zero_smul, add_zero]

end LongTails.Proofs.StochasticMintyOracle
