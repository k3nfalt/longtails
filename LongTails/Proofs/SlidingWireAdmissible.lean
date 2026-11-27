import LongTails.Setups.HighDimensionalSlidingStochasticComposite
import LongTails.Proofs.SlidingWireGap
import LongTails.Proofs.QuasarHardAdmissible

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingWireAdmissible

open LongTails.Proofs.SlidingLowerChain (Point)

open OracleTemplate LongTails.Setups.HighDimensionalSlidingStochasticComposite
open SlidingWireChain SlidingWireLocal SlidingWireSplit SlidingWireConvex SlidingWireSim
open SlidingWireGap SlidingLowerOracle SmoothConvexFiniteGeometry SmoothConvexFiniteWall
open QuasarCoinLaw QuasarHardAdmissible FrontierChainProfiles FrontierChain FrontierChainGeometry

variable {d k : ℕ}

lemma objDiv_gradient (r : ℕ) (δ : ℝ) {Λ : ℝ} (π : Fin (k + 1) ↪ Fin d) (x : Point d) :
    HasGradientAt (fun v => obj r δ π v / Λ) (Λ⁻¹ • field r δ π x) x := by
  have h := obj_gradient r δ π x
  rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
  rw [show (fun v => obj r δ π v / Λ) = fun v => Λ⁻¹ * obj r δ π v from
    funext fun v => div_eq_inv_mul _ _]
  refine (h.const_mul Λ⁻¹).congr_fderiv ?_
  ext v
  simp [InnerProductSpace.toDual_apply_apply]

lemma field_norm (r : ℕ) (δ : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : Point d) :
    ‖field r δ π u‖ ≤ 1 + 2 * ((r : ℝ) ^ 2 + 23) * (k + 1) := by
  rw [SlidingWireChain.field_decomposition]
  have hc : ∀ l : ℕ, ∀ s t : ℝ, |linkL r δ l s t| ≤ (r : ℝ) ^ 2 + 23 ∧
      |linkR r δ l s t| ≤ (r : ℝ) ^ 2 + 23 := by
    intro l s t
    have hcb := coef_bounds r l
    have hsp := spS_abs δ (stretch r l s t)
    unfold linkL linkR
    split_ifs
    · have h1 := edgeLeft_bounds s t
      have h2 := edgeRight_bounds s t
      have hr : 0 ≤ (r : ℝ) ^ 2 := by positivity
      constructor <;> rw [abs_le] <;> constructor <;> linarith
    · constructor
      · rw [abs_mul]; nlinarith [abs_nonneg (cA r l), abs_nonneg (spS δ (stretch r l s t))]
      · rw [abs_mul]; nlinarith [abs_nonneg (cB r l), abs_nonneg (spS δ (stretch r l s t))]
  have hC : (0 : ℝ) ≤ (r : ℝ) ^ 2 + 23 := by positivity
  have h1 := scatter_norm_le (Fin.castSuccEmb.trans π)
    (fun i => linkL r δ i.val (u (π i.castSucc)) (u (π i.succ))) hC (fun i => (hc _ _ _).1)
  have h2 := scatter_norm_le ((Fin.succEmb k).trans π)
    (fun i => linkR r δ i.val (u (π i.castSucc)) (u (π i.succ))) hC (fun i => (hc _ _ _).2)
  have hs : Real.sqrt k ≤ k + 1 := by
    have := Real.sqrt_le_sqrt (show (k : ℝ) ≤ (k + 1) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at this
  have h0 : ‖-(potentialSlope (u (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ))‖ ≤ 1 := by
    rw [norm_neg, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have := potentialSlope_bounds (u (π 0))
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  calc _ ≤ _ := norm_add₃_le
    _ ≤ 1 + ((r : ℝ) ^ 2 + 23) * Real.sqrt k + ((r : ℝ) ^ 2 + 23) * Real.sqrt k := by
        gcongr
    _ ≤ _ := by nlinarith

structure WVal (q : Params) (T : ℕ) (W : WScale) : Prop where
  gap : GapHyp W T
  ell : W.ℓ = q.ℓ
  Λ_lip : 8 * ((W.r : ℝ) ^ 2 + 7) ^ 2 + 1026 ≤ W.Λ
  R_field : 1 + 2 * ((W.r : ℝ) ^ 2 + 23) * ((T * (W.r ^ 2 + 2) : ℕ) + 1) ≤ W.R
  smooth_L : q.ℓ + W.a / W.s ^ 2 * (512 * W.Λ) ≤ q.L
  gap_Δ : W.a * (4 + 4 * T) ≤ q.Δ

lemma wG_lipschitz (q : Params) (T : ℕ) (W : WScale) (hV : WVal q T W)
    (π : Fin (T * (W.r ^ 2 + 2) + 1) ↪ Fin d) (x y : Point d) :
    ‖wG W.r W.δ W.R W.Λ π x - wG W.r W.δ W.R W.Λ π y‖ ≤ 512 * W.Λ * ‖x - y‖ := by
  have hG := hV.gap
  have hΛ0 : 0 < W.Λ := by linarith [hG.Λ_ge]
  have hR0 : 0 < W.R := by linarith [hG.R_one]
  rw [wG_eq _ _ _ hΛ0, wG_eq _ _ _ hΛ0, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hΛ0]
  have h := localized_lipschitz W.R hR0 (fun v => obj W.r W.δ π v / W.Λ)
    (fun v => W.Λ⁻¹ • field W.r W.δ π v) (fun z => objDiv_gradient W.r W.δ π z)
    (fun a b => by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛ0)]
      have := field_lipschitz W.r W.δ π a b
      rw [inv_mul_le_iff₀ hΛ0]
      nlinarith [hV.Λ_lip, norm_nonneg (a - b)])
    (fun z => by
      have hp := pobj_upper W.r hG.δ_nonneg π (T * (W.r ^ 2 + 2) + 1) z
      rw [← obj_eq_pobj] at hp
      have hR := hG.R_big
      rcases le_or_gt (obj W.r W.δ π z) 0 with h | h
      · have : obj W.r W.δ π z / W.Λ ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hΛ0.le
        nlinarith [sq_nonneg ‖z‖, sq_nonneg W.R]
      · rw [div_le_iff₀ hΛ0]
        nlinarith [sq_nonneg ‖z‖, sq_nonneg W.R, hG.Λ_ge])
    (fun z => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛ0)]
      have := field_norm W.r W.δ π z
      have h1 : W.Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hG.Λ_ge
      have h2 : 0 ≤ ‖field W.r W.δ π z‖ := norm_nonneg _
      calc W.Λ⁻¹ * ‖field W.r W.δ π z‖ ≤ 1 * ‖field W.r W.δ π z‖ :=
            mul_le_mul_of_nonneg_right h1 h2
        _ ≤ ‖z‖ + W.R := by linarith [hV.R_field, norm_nonneg z]) x y
  nlinarith [h, hΛ0]


noncomputable def wireInstance (q : Params) (W : WScale) {T : ℕ}
    (π : Fin (T * (W.r ^ 2 + 2) + 1) ↪ Fin q.d) : spec.Instance q :=
  ⟨fB q.ℓ, hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0⟩

noncomputable def wireOracle (q : Params) (W : WScale) {T : ℕ}
    (π : Fin (T * (W.r ^ 2 + 2) + 1) ↪ Fin q.d) :
    Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)) 2 where
  Seed := fun _ => Bool
  law := coinPath 1 zero_le_one le_rfl
  answer := fun _ qq _ => if qq.1 = 0 then gradient (fB q.ℓ) qq.2
    else gradient (hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0) qq.2

lemma fB_grad_eq (ℓ : ℝ) (x : Point d) : gradient (fB ℓ) x = (-ℓ) • x := (fB_gradient ℓ x).gradient

lemma hB_grad_eq (q : Params) (T : ℕ) (W : WScale) (hV : WVal q T W)
    (π : Fin (T * (W.r ^ 2 + 2) + 1) ↪ Fin q.d) (x : EuclideanSpace ℝ (Fin q.d)) :
    gradient (hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0) x =
      (W.a / W.s) • wG W.r W.δ W.R W.Λ π (rescale W.s q.x0 x) + q.ℓ • x :=
  (hB_gradient W.a W.s q.ℓ W.r (by linarith [hV.gap.R_one]) (by linarith [hV.gap.Λ_ge]) π q.x0 x).gradient

lemma wF_zero (r : ℕ) {δ R Λ : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R) (hΛ : 1 ≤ Λ) {T : ℕ}
    (hRk : 8 + 8 * ((T * (r ^ 2 + 2) : ℕ) : ℝ) ≤ R ^ 2)
    (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d) : wF r δ R Λ π 0 ≤ 0 := by
  have hs := obj_split r δ π 0
  have hg := SlidingLowerInstance.gateObj_zero ((gEmb r T).trans π)
  have hsp : springObj r δ π 0 = 0 := by
    unfold springObj
    apply Finset.sum_eq_zero
    intro l _
    split_ifs
    · rfl
    · simp only [PiLp.zero_apply, stretch, mul_zero, add_zero]
      exact (sp_flat (by simp [hδ])).1
  have hob : obj r δ π 0 ≤ 0 := by
    rw [hs, hg, hsp]
    linarith [(potential_bounds 0).1]
  unfold wF localized
  have hΛ0 : 0 < Λ := by linarith
  have he := (smoothMax_eq_left (R ^ 2) (obj r δ π 0 / Λ) (wall R (0 : Point d)) (by positivity) (by
    unfold wall
    simp only [norm_zero]
    have h1 := SlidingWireLocal.obj_lower r (δ := δ) π 0
    have h2 : -(4 + 4 * ((T * (r ^ 2 + 2) : ℕ) : ℝ)) / Λ ≤ obj r δ π 0 / Λ :=
      div_le_div_of_nonneg_right h1 hΛ0.le
    have h3 : -(4 + 4 * ((T * (r ^ 2 + 2) : ℕ) : ℝ)) ≤ -(4 + 4 * ((T * (r ^ 2 + 2) : ℕ) : ℝ)) / Λ := by
      rw [le_div_iff₀ hΛ0]
      have : (0 : ℝ) ≤ 4 + 4 * ((T * (r ^ 2 + 2) : ℕ) : ℝ) := by positivity
      nlinarith
    nlinarith)).1
  rw [he]
  have : obj r δ π 0 / Λ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hob hΛ0.le
  nlinarith


lemma wF_lower (r : ℕ) {δ R Λ : ℝ} (hR : 0 < R) (hΛ : 1 ≤ Λ) {T : ℕ}
    (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d) (u : Point d) :
    -(4 + 4 * (T : ℝ)) ≤ wF r δ R Λ π u := by
  have hs := obj_split r δ π u
  have hg := SlidingLowerInstance.gateObj_lower ((gEmb r T).trans π) u
  have hsp : 0 ≤ springObj r δ π u := by
    unfold springObj
    apply Finset.sum_nonneg
    intro l _
    split_ifs
    · rfl
    · exact sp_nonneg _ _
  have hob : -(4 + 4 * (T : ℝ)) ≤ obj r δ π u := by rw [hs]; linarith
  have hl := localized_ge R hR (fun v => obj r δ π v / Λ) u
  have hΛ0 : 0 < Λ := by linarith
  unfold wF
  have : obj r δ π u ≤ Λ * localized R (fun v => obj r δ π v / Λ) u := by
    have := mul_le_mul_of_nonneg_left hl hΛ0.le
    rwa [mul_div_cancel₀ _ hΛ0.ne'] at this
  linarith

lemma wire_admissible (q : Params) (T : ℕ) (W : WScale) (hV : WVal q T W)
    (π : Fin (T * (W.r ^ 2 + 2) + 1) ↪ Fin q.d) :
    spec.admissible q (wireInstance q W π) (wireOracle q W π) := by
  have hG := hV.gap
  have hR0 : 0 < W.R := by linarith [hG.R_one]
  have hΛ0 : 0 < W.Λ := by linarith [hG.Λ_ge]
  have hℓ : 0 < q.ℓ := by rw [← hV.ell]; exact hG.ℓ_pos
  refine ⟨fun x _ => gradient (hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0) x,
    coinLaw 1 zero_le_one le_rfl, coinPath 1 zero_le_one le_rfl,
    coinPath_iid zero_le_one le_rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (fB_gradient q.ℓ x).differentiableAt.hasGradientAt
  · intro x y
    change ‖gradient (fB q.ℓ) x - gradient (fB q.ℓ) y‖ ≤ q.ℓ * ‖x - y‖
    rw [fB_grad_eq, fB_grad_eq, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hℓ]
  · apply LongTails.Proofs.SharpChainLowerBound.convexOn_of_subgradient _
      (fun x => (W.a / W.s) • wG W.r W.δ W.R W.Λ π (rescale W.s q.x0 x) + q.ℓ • x)
    intro x y
    change hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0 x + _ ≤ hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0 y
    have h := F_weak W hG π q.x0 x y
    rw [hV.ell] at h
    unfold hB
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [real_inner_smul_left] at h
    have e : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫ + ‖y - x‖ ^ 2 := by
      have : y = x + (y - x) := by abel
      conv_lhs => rw [this]
      rw [norm_add_sq_real]
    have e2 : q.ℓ / 2 * ‖y‖ ^ 2 =
        q.ℓ / 2 * ‖x‖ ^ 2 + q.ℓ * ⟪x, y - x⟫ + q.ℓ / 2 * ‖y - x‖ ^ 2 := by
      rw [e]; ring
    linarith
  · intro x
    exact (hB_gradient W.a W.s q.ℓ W.r hR0 hΛ0 π q.x0 x).differentiableAt.hasGradientAt
  · intro x y
    change ‖gradient (hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0) x -
      gradient (hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0) y‖ ≤ q.L * ‖x - y‖
    rw [hB_grad_eq q T W hV, hB_grad_eq q T W hV]
    have h1 := scaled_lipschitz hG.a_nonneg hG.s_pos (wG_lipschitz q T W hV π) q.x0 x y
    have h2 : ‖q.ℓ • x - q.ℓ • y‖ = q.ℓ * ‖x - y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
    calc _ = ‖((W.a / W.s) • wG W.r W.δ W.R W.Λ π (rescale W.s q.x0 x) -
          (W.a / W.s) • wG W.r W.δ W.R W.Λ π (rescale W.s q.x0 y)) + (q.ℓ • x - q.ℓ • y)‖ := by
          congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ ≤ W.a / W.s ^ 2 * (512 * W.Λ) * ‖x - y‖ + q.ℓ * ‖x - y‖ := by rw [h2]; linarith
      _ ≤ q.L * ‖x - y‖ := by nlinarith [hV.smooth_L, norm_nonneg (x - y)]
  · refine ⟨-(W.a * (4 + 4 * (T : ℝ))), fun x => ?_, ?_⟩
    · change -(W.a * (4 + 4 * (T : ℝ))) ≤ fB q.ℓ x + hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0 x
      rw [← hV.ell, F_eq]
      have := wF_lower W.r (δ := W.δ) hR0 hG.Λ_ge π (rescale W.s q.x0 x)
      nlinarith [hG.a_nonneg]
    · change fB q.ℓ q.x0 + hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0 q.x0 - -(W.a * (4 + 4 * (T : ℝ))) ≤ q.Δ
      rw [← hV.ell, F_eq]
      have h0 : rescale W.s q.x0 q.x0 = 0 := by simp [rescale]
      rw [h0]
      have := wF_zero W.r hG.δ_nonneg hR0 hG.Λ_ge hG.R_k π
      nlinarith [hG.a_nonneg, hV.gap_Δ]
  · apply measurable_from_prod_countable_left
    intro b
    have hc : Continuous (gradient (hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0)) := by
      apply LipschitzWith.continuous (K := ⟨W.a / W.s ^ 2 * (512 * W.Λ) + q.ℓ, by
        have := hG.a_nonneg; have := hG.s_pos; positivity⟩)
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, dist_eq_norm, hB_grad_eq q T W hV, hB_grad_eq q T W hV]
      have h1 := scaled_lipschitz hG.a_nonneg hG.s_pos (wG_lipschitz q T W hV π) q.x0 x y
      have h2 : ‖q.ℓ • x - q.ℓ • y‖ = q.ℓ * ‖x - y‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
      calc _ = ‖((W.a / W.s) • wG W.r W.δ W.R W.Λ π (rescale W.s q.x0 x) -
            (W.a / W.s) • wG W.r W.δ W.R W.Λ π (rescale W.s q.x0 y)) + (q.ℓ • x - q.ℓ • y)‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ ≤ (W.a / W.s ^ 2 * (512 * W.Λ) + q.ℓ) * ‖x - y‖ := by
            rw [h2]; nlinarith [norm_nonneg (x - y)]
    have e1 : (toGeneral q).measurableE =
        LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace q.d :=
      (toGeneral q).borelE.measurable_eq.trans
        (LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace q.d).measurable_eq.symm
    exact hc.measurable.mono e1.ge e1.le
  · intro x
    exact coin_integrable zero_le_one le_rfl _
  · intro x
    rw [coin_integral]
    simp
    rfl
  · intro x
    exact coin_integrable zero_le_one le_rfl _
  · intro x
    rw [coin_integral]
    have hx : gradient (wireInstance q W π).h x =
        gradient (hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0) x := rfl
    simp
    rw [hx, sub_self, norm_zero]
    nlinarith [sq_nonneg q.σ]

lemma answer_eqB (q : Params) (T : ℕ) (W : WScale) (hV : WVal q T W)
    (π : Fin (T * (W.r ^ 2 + 2) + 1) ↪ Fin q.d) (β : ℕ → Bool) :
    ∀ history qq, (wireOracle q W π).answer history qq (β history.length) =
      trueB W q.x0 π (β history.length) qq := by
  intro history qq
  unfold trueB
  change (if qq.1 = 0 then gradient (fB q.ℓ) qq.2
    else gradient (hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0) qq.2) = _
  rw [fB_grad_eq, hB_grad_eq q T W hV, hV.ell]

end LongTails.Proofs.SlidingWireAdmissible
