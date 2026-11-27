import LongTails.Proofs.SlidingWireGeometry
import LongTails.Proofs.SmoothConvexFiniteWall

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingWireLocal

open LongTails.Proofs.SlidingLowerChain (Point)

open SlidingWireChain SlidingWireGeometry FrontierChainProfiles FrontierChain
open SmoothConvexFiniteGeometry SmoothConvexFiniteWall QuasarHardProfiles

variable {d k : ℕ}

lemma spS_mul_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (e : ℝ) : 0 ≤ spS δ e * e := by
  unfold spS
  rcases le_total 0 e with h | h
  · rw [rampSlope_of_nonpos (by linarith : -e - δ ≤ 0), sub_zero]
    exact mul_nonneg (rampSlope_nonneg _) h
  · rw [rampSlope_of_nonpos (by linarith : e - δ ≤ 0), zero_sub]
    nlinarith [rampSlope_nonneg (-e - δ)]

lemma gateSlope_mul (s : ℝ) : |gateSlope s * s| ≤ 4 := by
  rcases le_or_gt (|s|) 1 with h | h
  · rw [abs_mul]
    have := gateSlope_bounds s
    have h4 : |gateSlope s| ≤ 4 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (gateSlope s), abs_nonneg s]
  · rcases lt_abs.mp h with h1 | h1
    · have : gateSlope s = 0 := by
        unfold gateSlope
        rw [rampSlope_of_ge (by linarith), rampSlope_of_ge (by linarith)]
        ring
      simp [this]
    · have : gateSlope s = 0 := (gate_flat (by linarith)).2
      simp [this]

lemma potentialSlope_mul (t : ℝ) : |potentialSlope t * t| ≤ 3 := by
  rcases le_or_gt (|t|) 3 with h | h
  · rw [abs_mul]
    have := potentialSlope_bounds t
    have h1 : |potentialSlope t| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (potentialSlope t), abs_nonneg t]
  · rcases lt_abs.mp h with h1 | h1
    · have : potentialSlope t = 0 := by
        unfold potentialSlope
        rw [rampSlope_of_ge (by linarith), rampSlope_of_ge (by linarith)]
        ring
      simp [this]
    · have : potentialSlope t = 0 := by
        unfold potentialSlope
        rw [rampSlope_of_nonpos (by linarith), rampSlope_of_nonpos (by linarith)]
        ring
      simp [this]

lemma gate_radial (s t : ℝ) : -38 ≤ edgeLeft s t * s + edgeRight s t * t := by
  have h1 := gateSlope_mul s
  have h2 := gateSlope_mul (-s)
  have h3 := potentialSlope_mul t
  have h4 := potentialSlope_mul (-t)
  have p1 := potential_bounds t
  have p2 := potential_bounds (-t)
  have g1 := gate_bounds s
  have g2 := gate_bounds (-s)
  have k1 : |(gateSlope (-s) * -s) * potential (-t)| ≤ 16 := by
    rw [abs_mul, abs_of_nonneg p2.1]
    nlinarith [abs_nonneg (gateSlope (-s) * -s)]
  have k2 : |(gateSlope s * s) * potential t| ≤ 16 := by
    rw [abs_mul, abs_of_nonneg p1.1]
    nlinarith [abs_nonneg (gateSlope s * s)]
  have k3 : |gate (-s) * (potentialSlope (-t) * -t)| ≤ 3 := by
    rw [abs_mul, abs_of_nonneg g2.1]
    nlinarith [abs_nonneg (potentialSlope (-t) * -t)]
  have k4 : |gate s * (potentialSlope t * t)| ≤ 3 := by
    rw [abs_mul, abs_of_nonneg g1.1]
    nlinarith [abs_nonneg (potentialSlope t * t)]
  have e : edgeLeft s t * s + edgeRight s t * t =
      (gateSlope (-s) * -s) * potential (-t) - (gateSlope s * s) * potential t +
        gate (-s) * (potentialSlope (-t) * -t) - gate s * (potentialSlope t * t) := by
    unfold edgeLeft edgeRight; ring
  rw [e]
  linarith [neg_abs_le ((gateSlope (-s) * -s) * potential (-t)),
    le_abs_self ((gateSlope s * s) * potential t),
    neg_abs_le (gate (-s) * (potentialSlope (-t) * -t)),
    le_abs_self (gate s * (potentialSlope t * t))]

lemma link_radial (r : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (l : ℕ) (s t : ℝ) :
    -38 ≤ linkL r δ l s t * s + linkR r δ l s t * t := by
  unfold linkL linkR
  split_ifs
  · exact gate_radial s t
  · have := spS_mul_nonneg hδ (stretch r l s t)
    have e : cA r l * spS δ (stretch r l s t) * s + cB r l * spS δ (stretch r l s t) * t =
        spS δ (stretch r l s t) * stretch r l s t := by unfold stretch; ring
    rw [e]
    linarith

lemma field_radial (r : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (π : Fin (k + 1) ↪ Fin d) (u : Point d) :
    -(3 + 38 * k) ≤ ⟪field r δ π u, u⟫ := by
  rw [field_inner]
  have h0 := abs_le.mp (potentialSlope_mul (u (π 0)))
  have hs : -(38 * (k : ℝ)) ≤ ∑ i : Fin k,
      (linkL r δ i.val (u (π i.castSucc)) (u (π i.succ)) * u (π i.castSucc) +
        linkR r δ i.val (u (π i.castSucc)) (u (π i.succ)) * u (π i.succ)) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
      link_radial r hδ i.val (u (π i.castSucc)) (u (π i.succ)))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  nlinarith

lemma obj_lower (r : ℕ) {δ : ℝ} (π : Fin (k + 1) ↪ Fin d) (u : Point d) :
    -(4 + 4 * k) ≤ obj r δ π u := by
  unfold obj
  have h0 := (potential_bounds (u (π 0))).2
  have hs : -(4 * (k : ℝ)) ≤ ∑ i : Fin k, link r δ i.val (u (π i.castSucc)) (u (π i.succ)) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
      (show -4 ≤ link r δ i.val (u (π i.castSucc)) (u (π i.succ)) by
        unfold link
        split_ifs
        · exact (edge_bounds _ _).1
        · linarith [sp_nonneg δ (stretch r i.val (u (π i.castSucc)) (u (π i.succ)))]))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  linarith

noncomputable def wF (r : ℕ) (δ R Λ : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : Point d) : ℝ :=
  Λ * localized R (fun v => obj r δ π v / Λ) u

noncomputable def wG (r : ℕ) (δ R Λ : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : Point d) : Point d :=
  weight (R ^ 2) (obj r δ π u / Λ) (wall R u) • field r δ π u +
    (1 - weight (R ^ 2) (obj r δ π u / Λ) (wall R u)) • ((4 * Λ) • u)

lemma wG_eq (r : ℕ) (δ R : ℝ) {Λ : ℝ} (hΛ : 0 < Λ) (π : Fin (k + 1) ↪ Fin d) (u : Point d) :
    wG r δ R Λ π u = Λ • localizedField R (fun v => obj r δ π v / Λ) (fun v => Λ⁻¹ • field r δ π v) u := by
  ext j
  simp only [wG, localizedField, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp

lemma wF_gradient (r : ℕ) (δ : ℝ) {R Λ : ℝ} (hR : 0 < R) (hΛ : 0 < Λ) (π : Fin (k + 1) ↪ Fin d)
    (u : Point d) : HasGradientAt (wF r δ R Λ π) (wG r δ R Λ π u) u := by
  have hf : ∀ x, HasGradientAt (fun v => obj r δ π v / Λ) (Λ⁻¹ • field r δ π x) x := by
    intro x
    have h := (obj_gradient r δ π x)
    rw [show (fun v => obj r δ π v / Λ) = fun v => Λ⁻¹ * obj r δ π v from
      funext fun v => div_eq_inv_mul _ _]
    exact SlidingLowerChain.grad_const_mul Λ⁻¹ h
  have hl := localized_gradient R hR (fun v => obj r δ π v / Λ) (fun x => Λ⁻¹ • field r δ π x) hf u
  rw [wG_eq r δ R hΛ π u]
  exact SlidingLowerChain.grad_const_mul Λ hl

lemma weight_one (r : ℕ) (δ : ℝ) {R Λ : ℝ} (hR : 0 < R) (hΛ : 1 ≤ Λ)
    (hRk : 8 + 8 * (k : ℝ) ≤ R ^ 2) (π : Fin (k + 1) ↪ Fin d) (u : Point d) (hu : ‖u‖ ≤ R) :
    weight (R ^ 2) (obj r δ π u / Λ) (wall R u) = 1 := by
  apply (smoothMax_eq_left _ _ _ (by positivity) _).2
  have h1 := obj_lower r (δ := δ) π u
  have h2 : -(4 + 4 * (k : ℝ)) ≤ obj r δ π u / Λ := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have h3 : ‖u‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
  unfold wall
  nlinarith

lemma wG_lower (r : ℕ) (hr : 1 ≤ r) {δ : ℝ} (hδ : 0 ≤ δ) (hrδ : r * δ ≤ 1 / 4) {T : ℕ}
    {R Λ : ℝ} (hR : 0 < R) (hΛ : 1 ≤ Λ)
    (hRk : 8 + 8 * ((T * (r ^ 2 + 2) : ℕ) : ℝ) ≤ R ^ 2)
    (hRG : 320 * (4 + 38 * ((T * (r ^ 2 + 2) : ℕ) : ℝ)) ≤ R)
    (π : Fin (T * (r ^ 2 + 2) + 1) ↪ Fin d) (u : Point d)
    (htail : |u (π (Fin.last _))| < 1) :
    1 / 320 ≤ ‖wG r δ R Λ π u‖ := by
  set lw := weight (R ^ 2) (obj r δ π u / Λ) (wall R u) with hlw
  have hlw0 : 0 ≤ lw := weight_nonneg _ _ _
  have hlw1 : lw ≤ 1 := weight_le_one _ _ _
  set t := 4 * Λ * (1 - lw) with ht
  have ht0 : 0 ≤ t := by rw [ht]; nlinarith
  have hwG : wG r δ R Λ π u = lw • field r δ π u + t • u := by
    simp only [wG, ← hlw, ht, smul_smul]
    ring_nf
  have hrad := field_radial r hδ π u
  by_cases hc : 1 / 2 ≤ lw ∧ t * ‖u‖ ≤ 1 / 160
  · obtain ⟨hlwh, htu⟩ := hc
    rcases wire_deficient r hr δ hδ hrδ π u htail with ⟨v, hv, hgv⟩ | ⟨a, ha, hpos, hneg⟩
    · have hin : ⟪wG r δ R Λ π u, v⟫ ≤ -(1 / 16) := by
        rw [hwG, inner_add_left, real_inner_smul_left, real_inner_smul_left]
        have h1 : |⟪u, v⟫| ≤ ‖u‖ * 10 :=
          (abs_real_inner_le_norm u v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
        have h2 : t * ⟪u, v⟫ ≤ 10 / 160 := by
          have := abs_le.mp h1
          nlinarith
        nlinarith
      have hcs := abs_real_inner_le_norm (wG r δ R Λ π u) v
      have := neg_abs_le ⟪wG r δ R Λ π u, v⟫
      have hvn := norm_nonneg v
      by_contra hneg
      push Not at hneg
      have : ‖wG r δ R Λ π u‖ * ‖v‖ ≤ 1 / 320 * 10 :=
        mul_le_mul hneg.le hv hvn (by norm_num)
      linarith
    · have hcomp : |wG r δ R Λ π u a| ≤ ‖wG r δ R Λ π u‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (wG r δ R Λ π u) a
      rw [hwG] at hcomp ⊢
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hcomp
      rcases le_abs'.mp ha with hn | hp
      · have := hneg hn
        have : lw * field r δ π u a + t * u a ≤ -(1 / 2) := by nlinarith
        have := neg_abs_le (lw * field r δ π u a + t * u a)
        linarith
      · have := hpos hp
        have : 1 / 2 ≤ lw * field r δ π u a + t * u a := by nlinarith
        have := le_abs_self (lw * field r δ π u a + t * u a)
        linarith
  · have hout : R < ‖u‖ := by
      by_contra hle
      push Not at hle
      have h1 := weight_one r δ hR hΛ hRk π u hle
      rw [← hlw] at h1
      apply hc
      refine ⟨by rw [h1]; norm_num, ?_⟩
      rw [ht, h1]
      simp
    have hu0 : 0 < ‖u‖ := lt_trans hR hout
    have hrad2 : ⟪wG r δ R Λ π u, u⟫ ≥ -(3 + 38 * ((T * (r ^ 2 + 2) : ℕ) : ℝ)) + t * ‖u‖ ^ 2 := by
      rw [hwG, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      nlinarith
    have hcs := abs_real_inner_le_norm (wG r δ R Λ π u) u
    have hle := le_abs_self ⟪wG r δ R Λ π u, u⟫
    have key : 1 / 320 * ‖u‖ ≤ -(3 + 38 * ((T * (r ^ 2 + 2) : ℕ) : ℝ)) + t * ‖u‖ ^ 2 := by
      rcases not_and_or.mp hc with h | h
      · push Not at h
        have ht2 : 2 ≤ t := by rw [ht]; nlinarith
        nlinarith
      · push Not at h
        nlinarith
    by_contra hneg
    push Not at hneg
    have : ‖wG r δ R Λ π u‖ * ‖u‖ < 1 / 320 * ‖u‖ := mul_lt_mul_of_pos_right hneg hu0
    linarith

end LongTails.Proofs.SlidingWireLocal
