import LongTails.Algorithms.HiddenPotential
import LongTails.Proofs.HiddenDecompositionEnergy
import LongTails.Proofs.AcceleratedBiasedStochastic

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.HiddenPotential

open BiasedStochasticGradient StochasticGradient HeavyTailedMarkovGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma inner_energy_step (F : E → E) {f : E → ℝ} {L D R b β : ℝ}
    (hL : 0 ≤ L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (anchor center u : E)
    (herror : ∀ y, ‖y - center‖ ≤ R →
      ‖gradient f y - (F y + β • (y - anchor))‖ ≤ b)
    (x z : E) (hx : ‖x - center‖ ≤ R) (hz : ‖z - center‖ ≤ R)
    (hu : ‖u - center‖ ≤ R) (k : ℕ) :
    let y := Gradient.acceleratedQuery (k, x, z)
    let next := projectedUpdate D R center k (x, z) (F y + β • (y - anchor))
    acceleratedEnergy f D u (k + 1) next ≤
      acceleratedEnergy f D u k (x, z) + 4 * R * (((k : ℝ) + 1) / 2) * b := by
  have hs := HiddenDecompositionEnergy.bounded_error_step hL hD hLD hR hc hg hlip
    center x z u
    (F (Gradient.acceleratedQuery (k, x, z)) +
      β • (Gradient.acceleratedQuery (k, x, z) - anchor))
    hz hu
    (A := (k : ℝ) * ((k : ℝ) + 1) / 4)
    (a := ((k : ℝ) + 1) / 2)
    (by positivity) (by positivity) (by positivity)
    (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
    (herror _ (query_ball hx hz k))
  have hw : ((k : ℝ) + 1) * ((k : ℝ) + 1 + 1) / 4 =
      (k : ℝ) * ((k : ℝ) + 1) / 4 + ((k : ℝ) + 1) / 2 := by ring
  simpa only [acceleratedEnergy, acceleratedWeight, projectedUpdate,
    Gradient.acceleratedQuery, Nat.cast_add, Nat.cast_one, hw, div_div] using hs

lemma inner_energy_bound (F : E → E) {f : E → ℝ} {L D R b β : ℝ}
    (hL : 0 ≤ L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (anchor center u : E)
    (herror : ∀ y, ‖y - center‖ ≤ R →
      ‖gradient f y - (F y + β • (y - anchor))‖ ≤ b)
    (hu : ‖u - center‖ ≤ R) (T k : ℕ) (x z : E)
    (hx : ‖x - center‖ ≤ R) (hz : ‖z - center‖ ≤ R) :
    acceleratedEnergy f D u (k + T) (innerRun F β D R anchor center T k (x, z)) ≤
      acceleratedEnergy f D u k (x, z) +
        4 * R * b * (acceleratedWeight (k + T) - acceleratedWeight k) := by
  induction T generalizing k x z with
  | zero => simp [innerRun]
  | succ T ih =>
      let y := Gradient.acceleratedQuery (k, x, z)
      let next := projectedUpdate D R center k (x, z) (F y + β • (y - anchor))
      have hn := projectedUpdate_ball (D := D) (z := z) hR hx k (F y + β • (y - anchor))
      have hs := inner_energy_step F hL hD hLD hR hc hg hlip
        anchor center u herror x z hx hz hu k
      have hi := ih (k + 1) next.1 next.2 hn.1 hn.2
      have hw : acceleratedWeight (k + 1) - acceleratedWeight k = ((k : ℝ) + 1) / 2 := by
        simp only [acceleratedWeight, Nat.cast_add, Nat.cast_one]
        ring
      have hk : k + (T + 1) = k + 1 + T := by omega
      rw [innerRun, hk]
      change acceleratedEnergy f D u (k + 1 + T)
        (innerRun F β D R anchor center T (k + 1) next) ≤ _
      change acceleratedEnergy f D u (k + 1) next ≤ _ at hs
      have hid : 4 * R * (((k : ℝ) + 1) / 2) * b +
          4 * R * b * (acceleratedWeight (k + 1 + T) - acceleratedWeight (k + 1)) =
          4 * R * b * (acceleratedWeight (k + 1 + T) - acceleratedWeight k) := by
        rw [← hw]
        ring
      linarith

lemma inner_gap_bound (F : E → E) {f : E → ℝ} {L D R b β : ℝ}
    (hL : 0 ≤ L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (anchor center u : E)
    (herror : ∀ y, ‖y - center‖ ≤ R →
      ‖gradient f y - (F y + β • (y - anchor))‖ ≤ b)
    (hu : ‖u - center‖ ≤ R) (T : ℕ) (hT : 0 < T) :
    f (innerRun F β D R anchor center T 0 (center, center)).1 - f u ≤
      2 * D * R ^ 2 / ((T : ℝ) * ((T : ℝ) + 1)) + 4 * R * b := by
  have hs := inner_energy_bound F hL hD hLD hR hc hg hlip
    anchor center u herror hu T 0 center center (by simpa using hR) (by simpa using hR)
  simp only [zero_add, acceleratedEnergy, acceleratedWeight, Nat.cast_zero,
    zero_mul, zero_add, zero_div, sub_zero] at hs
  have hnorm : ‖center - u‖ ^ 2 ≤ R ^ 2 := by
    rw [norm_sub_rev]
    nlinarith [norm_nonneg (u - center)]
  have hn := mul_nonneg (le_of_lt (half_pos hD))
    (sq_nonneg ‖(innerRun F β D R anchor center T 0 (center, center)).2 - u‖)
  have hd : 0 < (T : ℝ) * ((T : ℝ) + 1) := by positivity
  apply (mul_le_mul_iff_of_pos_right hd).mp
  have he : (2 * D * R ^ 2 / ((T : ℝ) * ((T : ℝ) + 1)) + 4 * R * b) *
      ((T : ℝ) * ((T : ℝ) + 1)) =
      2 * D * R ^ 2 + 4 * R * b * ((T : ℝ) * ((T : ℝ) + 1)) := by
    field_simp
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hnorm hD.le]

lemma inner_radius_contraction (F : E → E) {f : E → ℝ} {L D R b β m : ℝ}
    (hL : 0 ≤ L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R)
    (hm : 0 < m) (hb : b ≤ m * R / 256)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (anchor center u : E)
    (herror : ∀ y, ‖y - center‖ ≤ R →
      ‖gradient f y - (F y + β • (y - anchor))‖ ≤ b)
    (hlower : ∀ x, m / 2 * ‖x - u‖ ^ 2 - b * ‖x - u‖ ≤ f x - f u)
    (hu : ‖u - center‖ ≤ R) (T : ℕ) (hT : 0 < T)
    (hsteps : 128 * D ≤ m * ((T : ℝ) * ((T : ℝ) + 1))) :
    ‖(innerRun F β D R anchor center T 0 (center, center)).1 - u‖ ≤ R / 2 := by
  have hs := inner_gap_bound F hL hD hLD hR hc hg hlip anchor center u herror hu T hT
  have hd : 0 < (T : ℝ) * ((T : ℝ) + 1) := by positivity
  have hterm : 2 * D * R ^ 2 / ((T : ℝ) * ((T : ℝ) + 1)) ≤ m * R ^ 2 / 64 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsteps (sq_nonneg R)]
  have herr : 4 * R * b ≤ m * R ^ 2 / 64 := by
    nlinarith [mul_le_mul_of_nonneg_left hb hR]
  exact HiddenDecompositionEnergy.radius_contraction hm hR (norm_nonneg _) hb
    (hlower _) (by linarith)

lemma hidden_inner_contraction (F : E → E) (φ : E → ℝ) {μ L s β D R : ℝ}
    (hL : 0 ≤ L) (hs : 0 ≤ s) (hβ : 0 ≤ β) (hD : 0 < D)
    (hLD : 2 * (L + β) ≤ D) (hR : 0 ≤ R)
    (hm : 0 < μ + β - s) (hsmall : 256 * s ≤ μ + β - s)
    (hg : ∀ x, HasGradientAt φ (gradient φ x) x)
    (hlip : ∀ x y, ‖gradient φ x - gradient φ y‖ ≤ L * ‖x - y‖)
    (hstrong : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hresidual : ∀ x y,
      ‖(F x - gradient φ x) - (F y - gradient φ y)‖ ≤ s * ‖x - y‖)
    (anchor center u : E) (hroot : F u + β • (u - anchor) = 0)
    (hu : ‖u - center‖ ≤ R) (T : ℕ) (hT : 0 < T)
    (hsteps : 128 * D ≤ (μ + β - s) * ((T : ℝ) * ((T : ℝ) + 1))) :
    ‖(innerRun F β D R anchor center T 0 (center, center)).1 - u‖ ≤ R / 2 := by
  let S := fun x => F x - gradient φ x
  let f := fun x => φ x + β / 2 * ‖x - anchor‖ ^ 2 + ⟪S center, x⟫
  let G := fun x => gradient φ x + β • (x - anchor) + S center
  have hgf : ∀ x, HasGradientAt f (G x) x :=
    HiddenDecompositionEnergy.regularized_potential_gradient hg β anchor (S center)
  have hgrad : ∀ x, gradient f x = G x := fun x => (hgf x).gradient
  have hcurv : ∀ x y, (μ + β - s) * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫ := by
    intro x y
    have h := HiddenDecompositionEnergy.regularized_curvature F (gradient φ) S μ β s
      (by intro z; dsimp [S]; abel) hstrong hresidual anchor x y
    simpa only [G, add_sub_add_right_eq_sub] using h
  have hfc := HiddenDecompositionEnergy.strongly_monotone_gradient_convex hgf hcurv hm.le
  have hfl : ∀ x y, ‖gradient f x - gradient f y‖ ≤ (L + β) * ‖x - y‖ := by
    intro x y
    rw [hgrad, hgrad]
    have he : G x - G y = (gradient φ x - gradient φ y) + β • (x - y) := by
      dsimp [G]
      module
    rw [he]
    calc
      _ ≤ ‖gradient φ x - gradient φ y‖ + ‖β • (x - y)‖ := norm_add_le _ _
      _ ≤ L * ‖x - y‖ + β * ‖x - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ]
        linarith [hlip x y]
      _ = _ := by ring
  have herr : ∀ y, ‖y - center‖ ≤ R →
      ‖gradient f y - (F y + β • (y - anchor))‖ ≤ s * R := by
    intro y hy
    rw [hgrad]
    have he : G y - (F y + β • (y - anchor)) = S center - S y := by
      dsimp [G, S]
      abel
    rw [he, norm_sub_rev]
    exact (hresidual y center).trans (mul_le_mul_of_nonneg_left hy hs)
  have hgu : ‖G u‖ ≤ s * R := by
    have h := herr u hu
    simpa only [hgrad, hroot, sub_zero] using h
  have hlower : ∀ x, (μ + β - s) / 2 * ‖x - u‖ ^ 2 -
      (s * R) * ‖x - u‖ ≤ f x - f u := by
    intro x
    have h := HiddenDecompositionEnergy.strongly_monotone_gradient_support hgf hcurv u x
    have hi : -((s * R) * ‖x - u‖) ≤ ⟪G u, x - u⟫ := by
      have hn := abs_real_inner_le_norm (G u) (x - u)
      have hb := mul_le_mul_of_nonneg_right hgu (norm_nonneg (x - u))
      have := neg_abs_le ⟪G u, x - u⟫
      linarith
    linarith
  apply inner_radius_contraction F (f := f) (add_nonneg hL hβ) hD hLD hR hm
    (by nlinarith [mul_le_mul_of_nonneg_right hsmall hR]) hfc
    (fun x => by rw [hgrad]; exact hgf x) hfl anchor center u herr hlower hu T hT hsteps

omit [CompleteSpace E] in
lemma stage_distance (F : E → E) (β D : ℝ) (T : ℕ) (anchor u : E)
    (hinner : ∀ R center, 0 ≤ R → ‖center - u‖ ≤ R →
      ‖(innerRun F β D R anchor center T 0 (center, center)).1 - u‖ ≤ R / 2)
    (H : ℕ) {R : ℝ} (hR : 0 ≤ R) (center : E) (hu : ‖center - u‖ ≤ R) :
    ‖stageRun F β D T anchor H R center - u‖ ≤ R / 2 ^ H := by
  induction H generalizing R center with
  | zero => simpa [stageRun] using hu
  | succ H ih =>
      have hi := ih (by positivity : 0 ≤ R / 2) _
        (hinner R center hR hu)
      simpa only [stageRun, pow_succ, div_div, mul_comm (2 : ℝ)] using hi

omit [CompleteSpace E] in
lemma outer_distance (F : E → E) (β D q : ℝ) (T H : ℕ) (u : E)
    (hq : 0 ≤ q)
    (hstage : ∀ R anchor, 0 ≤ R → ‖anchor - u‖ ≤ R →
      ‖stageRun F β D T anchor H R anchor - u‖ ≤ q * R)
    (N : ℕ) {R : ℝ} (hR : 0 ≤ R) (anchor : E) (hu : ‖anchor - u‖ ≤ R) :
    ‖outerRun F β D q T H N R anchor - u‖ ≤ q ^ N * R := by
  induction N generalizing R anchor with
  | zero => simpa [outerRun] using hu
  | succ N ih =>
      have hi := ih (mul_nonneg hq hR) _ (hstage R anchor hR hu)
      simpa only [outerRun, pow_succ, mul_assoc] using hi

lemma hidden_stage_contraction (F : E → E) (φ : E → ℝ) {μ L s β D R : ℝ}
    (hμ : 0 < μ) (hL : 0 ≤ L) (hs : 0 ≤ s) (hβ : 0 ≤ β) (hD : 0 < D)
    (hLD : 2 * (L + β) ≤ D) (hR : 0 ≤ R)
    (hm : 0 < μ + β - s) (hsmall : 256 * s ≤ μ + β - s)
    (hg : ∀ x, HasGradientAt φ (gradient φ x) x)
    (hlip : ∀ x y, ‖gradient φ x - gradient φ y‖ ≤ L * ‖x - y‖)
    (hstrong : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hresidual : ∀ x y,
      ‖(F x - gradient φ x) - (F y - gradient φ y)‖ ≤ s * ‖x - y‖)
    (anchor xstar : E) (hroot : F xstar = 0)
    (hu : ‖anchor - xstar‖ ≤ R) (T H : ℕ) (hT : 0 < T)
    (hsteps : 128 * D ≤ (μ + β - s) * ((T : ℝ) * ((T : ℝ) + 1)))
    (hH : (1 : ℝ) / 2 ^ H ≤ μ / (2 * (μ + β))) :
    ‖stageRun F β D T anchor H R anchor - xstar‖ ≤
      (1 - μ / (2 * (μ + β))) * R := by
  have hFl : ∀ x y, ‖F x - F y‖ ≤ (L + s) * ‖x - y‖ := by
    intro x y
    have he : F x - F y = (gradient φ x - gradient φ y) +
        ((F x - gradient φ x) - (F y - gradient φ y)) := by abel
    rw [he]
    have hn := norm_add_le (gradient φ x - gradient φ y)
      ((F x - gradient φ x) - (F y - gradient φ y))
    nlinarith [hlip x y, hresidual x y]
  obtain ⟨u, huroot⟩ := HiddenDecompositionEnergy.regularized_root_exists F
    hμ (add_nonneg hL hs) hβ hstrong hFl anchor
  have hinit : ‖anchor - u‖ ≤ R := by
    rw [norm_sub_rev]
    exact (HiddenDecompositionEnergy.proximal_displacement F hμ hβ hstrong
      anchor u xstar huroot hroot).trans hu
  have hi := stage_distance F β D T anchor u
    (fun r center hr hc => hidden_inner_contraction F φ hL hs hβ hD hLD hr hm hsmall
      hg hlip hstrong hresidual anchor center u huroot (by rwa [norm_sub_rev])
      T hT hsteps) H hR anchor hinit
  have hp := HiddenDecompositionEnergy.proximal_root_distance F hμ hβ hstrong
    anchor u xstar huroot hroot
  have hβratio : 0 ≤ β / (μ + β) := by positivity
  have hpp := hp.trans (mul_le_mul_of_nonneg_left hu hβratio)
  have hrad : R / 2 ^ H ≤ μ / (2 * (μ + β)) * R := by
    have hh := mul_le_mul_of_nonneg_right hH hR
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hh
  have he : μ / (2 * (μ + β)) + β / (μ + β) =
      1 - μ / (2 * (μ + β)) := by
    field_simp [ne_of_gt (show 0 < μ + β by positivity)]
    ring
  have hn := norm_sub_le_norm_sub_add_norm_sub (stageRun F β D T anchor H R anchor) u xstar
  have heR := congrArg (fun t : ℝ => t * R) he
  nlinarith

lemma hidden_outer_convergence (F : E → E) (φ : E → ℝ) {μ L s β D R : ℝ}
    (hμ : 0 < μ) (hL : 0 ≤ L) (hs : 0 ≤ s) (hβ : 0 ≤ β) (hD : 0 < D)
    (hLD : 2 * (L + β) ≤ D) (hR : 0 ≤ R)
    (hm : 0 < μ + β - s) (hsmall : 256 * s ≤ μ + β - s)
    (hg : ∀ x, HasGradientAt φ (gradient φ x) x)
    (hlip : ∀ x y, ‖gradient φ x - gradient φ y‖ ≤ L * ‖x - y‖)
    (hstrong : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫)
    (hresidual : ∀ x y,
      ‖(F x - gradient φ x) - (F y - gradient φ y)‖ ≤ s * ‖x - y‖)
    (x0 xstar : E) (hroot : F xstar = 0)
    (hu : ‖x0 - xstar‖ ≤ R) (T H N : ℕ) (hT : 0 < T)
    (hsteps : 128 * D ≤ (μ + β - s) * ((T : ℝ) * ((T : ℝ) + 1)))
    (hH : (1 : ℝ) / 2 ^ H ≤ μ / (2 * (μ + β))) :
    ‖outerRun F β D (1 - μ / (2 * (μ + β))) T H N R x0 - xstar‖ ≤
      (1 - μ / (2 * (μ + β))) ^ N * R := by
  have hq : 0 ≤ 1 - μ / (2 * (μ + β)) := by
    rw [sub_nonneg, div_le_one (by positivity : 0 < 2 * (μ + β))]
    linarith
  exact outer_distance F β D _ T H xstar hq
    (fun r anchor hr ha => hidden_stage_contraction F φ hμ hL hs hβ hD hLD hr hm hsmall
      hg hlip hstrong hresidual anchor xstar hroot ha T H hT hsteps hH) N hR x0 hu

end OracleTemplate.HiddenPotential
