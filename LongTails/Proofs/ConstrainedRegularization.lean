import LongTails.Proofs.ConstrainedAnchoredStep
import LongTails.Proofs.StronglyMonotoneZero
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

open Set Metric Filter Topology
open scoped RealInnerProductSpace

namespace OracleTemplate.ConstrainedMonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma regularized_root_nonexpansive {F : E → E} {X : Set E} {r : ℝ} (hr : 0 < r)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) {a b p q : E}
    (hp : p ∈ X) (hq : q ∈ X)
    (hnp : Normal X p (-(F p + r • (p - a))))
    (hnq : Normal X q (-(F q + r • (q - b)))) : ‖p - q‖ ≤ ‖a - b‖ := by
  have hm := hmono p q
  have hn := normal_monotone hp hq hnp hnq
  have he : -(F p + r • (p - a)) - -(F q + r • (q - b)) =
      -(F p - F q) + r • (a - b) - r • (p - q) := by module
  rw [he, inner_sub_left, inner_add_left, inner_neg_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at hn
  have hf : ‖p - q‖ ^ 2 ≤ ⟪a - b, p - q⟫ := by
    by_contra hh
    have hh := lt_of_not_ge hh
    nlinarith [mul_pos hr (sub_pos.mpr hh)]
  have hi := real_inner_le_norm (a - b) (p - q)
  by_contra hh
  have hh := lt_of_not_ge hh
  nlinarith [norm_nonneg (p - q), norm_nonneg (a - b)]

lemma Proj.firm {X : Set E} {P : E → E} (hP : Proj X P) (x y : E) :
    ‖P x - P y‖ ^ 2 ≤ ⟪x - y, P x - P y⟫ := by
  have h1 := hP.var x (P y) (hP.mem y)
  have h2 := hP.var y (P x) (hP.mem x)
  rw [show P y - P x = -(P x - P y) by abel, inner_neg_right] at h1
  have he : x - y = (x - P x) - (y - P y) + (P x - P y) := by abel
  rw [he, inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq]
  linarith

lemma Proj.lipschitz {X : Set E} {P : E → E} (hP : Proj X P) : LipschitzWith 1 P := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h1 := hP.firm x y
  have h2 := real_inner_le_norm (x - y) (P x - P y)
  by_contra hh
  have hh := lt_of_not_ge hh
  nlinarith [norm_nonneg (x - y), norm_nonneg (P x - P y)]

lemma Proj.complement_monotone {X : Set E} {P : E → E} (hP : Proj X P) (x y : E) :
    0 ≤ ⟪(x - P x) - (y - P y), x - y⟫ := by
  have hl := hP.lipschitz.dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hl
  have hi := real_inner_le_norm (P x - P y) (x - y)
  have he : (x - P x) - (y - P y) = (x - y) - (P x - P y) := by abel
  rw [he, inner_sub_left, real_inner_self_eq_norm_sq]
  nlinarith [mul_le_mul_of_nonneg_right hl (norm_nonneg (x - y))]

lemma Proj.fixed {X : Set E} {P : E → E} (hP : Proj X P) {a : E} (ha : a ∈ X) : P a = a := by
  have ht := hP.dist_le a ha
  rw [sub_self, norm_zero] at ht
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ht (norm_nonneg _)))

lemma Proj.closed {X : Set E} {P : E → E} (hP : Proj X P) : IsClosed X := by
  have he : X = {x | P x = x} := by
    ext x
    exact ⟨hP.fixed, fun hx => hx ▸ hP.mem x⟩
  rw [he]
  exact isClosed_eq hP.lipschitz.continuous continuous_id

lemma Proj.penalized_zero [FiniteDimensional ℝ E] {X : Set E} {P H : E → E}
    (hP : Proj X P) (hc : Continuous H) {μ : ℝ} (hμ : 0 < μ)
    (hmono : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪H x - H y, x - y⟫)
    {a : E} (ha : a ∈ X) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ p, H p + τ • (p - P p) = 0 ∧ ‖p - a‖ ≤ ‖H a‖ / μ := by
  let G := fun x => H x + τ • (x - P x)
  have hGc : Continuous G := hc.add (continuous_const.smul (continuous_id.sub hP.lipschitz.continuous))
  have hGm (x y : E) : μ * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫ := by
    have he : G x - G y = (H x - H y) + τ • ((x - P x) - (y - P y)) := by
      dsimp [G]
      module
    rw [he, inner_add_left, real_inner_smul_left]
    have := mul_nonneg hτ (hP.complement_monotone x y)
    linarith [hmono x y]
  obtain ⟨p, hp⟩ := StronglyMonotoneZero.exists_zero hGc hμ hGm
  refine ⟨p, hp, ?_⟩
  have hm := hGm p a
  have hGa : G a = H a := by simp [G, hP.fixed ha]
  rw [hp, hGa, zero_sub, inner_neg_left] at hm
  have hi := real_inner_le_norm (-H a) (p - a)
  rw [inner_neg_left, norm_neg] at hi
  apply (le_div_iff₀ hμ).mpr
  by_contra hh
  have hh := lt_of_not_ge hh
  have hn : 0 < ‖p - a‖ := by
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) (norm_nonneg (p - a))
    rw [hz, zero_mul] at hh
    exact (not_lt_of_ge (norm_nonneg _)) hh
  nlinarith [mul_pos hn (sub_pos.mpr hh)]

lemma Proj.exists_variational [FiniteDimensional ℝ E] {X : Set E} {P H : E → E}
    (hP : Proj X P) (hc : Continuous H) {μ : ℝ} (hμ : 0 < μ)
    (hmono : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪H x - H y, x - y⟫)
    {a : E} (ha : a ∈ X) : ∃ p ∈ X, Normal X p (-H p) := by
  choose z hz hbound using fun n : ℕ => hP.penalized_zero hc hμ hmono ha
    (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hball : ∀ n, z n ∈ closedBall a (‖H a‖ / μ) := by
    intro n
    rw [mem_closedBall, dist_eq_norm]
    exact hbound n
  obtain ⟨p, _, φ, hφ, hlim⟩ := (isCompact_closedBall a (‖H a‖ / μ)).tendsto_subseq hball
  have hHlim := (hc.tendsto p).comp hlim
  have hPlim := (hP.lipschitz.continuous.tendsto p).comp hlim
  have hinv : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hpen (n : ℕ) : ((n : ℝ) + 1) • (z n - P (z n)) = -H (z n) :=
    eq_neg_of_add_eq_zero_right (hz n)
  have hdis (n : ℕ) : z n - P (z n) = (1 / ((n : ℝ) + 1)) • (-H (z n)) := by
    rw [← hpen, smul_smul, one_div_mul_cancel (by positivity : (n : ℝ) + 1 ≠ 0), one_smul]
  have hzero : Tendsto (fun n => z (φ n) - P (z (φ n))) atTop (𝓝 (0 : E)) := by
    simp_rw [hdis]
    simpa using hinv.smul hHlim.neg
  have hfix : P p = p := by
    have he := tendsto_nhds_unique (hlim.sub hPlim) hzero
    exact (sub_eq_zero.mp he).symm
  refine ⟨p, hfix ▸ hP.mem p, ?_⟩
  intro w hw
  have hnormal (n : ℕ) : ⟪-H (z n), w - P (z n)⟫ ≤ 0 := by
    rw [← hpen, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hP.var (z n) w hw)
  have hi : Tendsto (fun n => ⟪-H (z (φ n)), w - P (z (φ n))⟫) atTop
      (𝓝 ⟪-H p, w - P p⟫) := hHlim.neg.inner (tendsto_const_nhds.sub hPlim)
  have hout := le_of_tendsto hi (Filter.Eventually.of_forall (fun n => hnormal (φ n)))
  simpa [hfix] using hout

lemma Proj.exists_regularized [FiniteDimensional ℝ E] {X : Set E} {P F : E → E}
    (hP : Proj X P) (hc : Continuous F)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    {a : E} (ha : a ∈ X) {r : ℝ} (hr : 0 < r) (c : E) :
    ∃ p ∈ X, Normal X p (-(F p + r • (p - c))) := by
  apply hP.exists_variational (hc.add (continuous_const.smul (continuous_id.sub continuous_const))) hr
    (a := a) ?_ ha
  intro x y
  change r * ‖x - y‖ ^ 2 ≤ ⟪(F x + r • (x - c)) - (F y + r • (y - c)), x - y⟫
  have he : (F x + r • (x - c)) - (F y + r • (y - c)) = (F x - F y) + r • (x - y) := by module
  rw [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  linarith [hmono x y]

noncomputable def regularizedRoot [FiniteDimensional ℝ E] {X : Set E} {P F : E → E}
    (hP : Proj X P) (hc : Continuous F)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    {a : E} (ha : a ∈ X) {r : ℝ} (hr : 0 < r) (c : E) : E :=
  Classical.choose (hP.exists_regularized hc hmono ha hr c)

lemma regularizedRoot_spec [FiniteDimensional ℝ E] {X : Set E} {P F : E → E}
    (hP : Proj X P) (hc : Continuous F)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    {a : E} (ha : a ∈ X) {r : ℝ} (hr : 0 < r) (c : E) :
    let p := regularizedRoot hP hc hmono ha hr c
    p ∈ X ∧ Normal X p (-(F p + r • (p - c))) :=
  Classical.choose_spec (hP.exists_regularized hc hmono ha hr c)

lemma regularizedRoot_continuous [FiniteDimensional ℝ E] {X : Set E} {P F : E → E}
    (hP : Proj X P) (hc : Continuous F)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    {a : E} (ha : a ∈ X) {r : ℝ} (hr : 0 < r) :
    Continuous (regularizedRoot hP hc hmono ha hr) := by
  have hl : LipschitzWith 1 (regularizedRoot hP hc hmono ha hr) := by
    apply LipschitzWith.of_dist_le_mul
    intro c d
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    have hc' := regularizedRoot_spec hP hc hmono ha hr c
    have hd' := regularizedRoot_spec hP hc hmono ha hr d
    exact regularized_root_nonexpansive hr hmono hc'.1 hd'.1 hc'.2 hd'.2
  exact hl.continuous

lemma regularized_root_transport {F : E → E} {X : Set E} {r : ℝ} (hr : 0 < r)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) {c w p q : E}
    (hp : p ∈ X) (hq : q ∈ X)
    (hnp : Normal X p (-(F p + r • (p - c))))
    (hnq : Normal X q (-(F q + (2 * r) • (q - (1 / 2 : ℝ) • (c + w))))) :
    ‖q - p‖ ≤ ‖w - p‖ / 2 ∧ ‖q - w‖ ≤ ‖w - p‖ ∧
      ‖(2 * r) • (q - (1 / 2 : ℝ) • (c + w)) - r • (p - c)‖ ≤ 2 * r * ‖w - p‖ := by
  have hm := hmono q p
  have hn := normal_monotone hq hp hnq hnp
  have he : -(F q + (2 * r) • (q - (1 / 2 : ℝ) • (c + w))) - -(F p + r • (p - c)) =
      -(F q - F p) + r • (w - p) - (2 * r) • (q - p) := by module
  rw [he, inner_sub_left, inner_add_left, inner_neg_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at hn
  have hf : 2 * ‖q - p‖ ^ 2 ≤ ⟪w - p, q - p⟫ := by
    by_contra hh
    have hh := lt_of_not_ge hh
    nlinarith [mul_pos hr (sub_pos.mpr hh)]
  have hn : ‖q - p‖ ≤ ‖w - p‖ / 2 := by
    have hi := real_inner_le_norm (w - p) (q - p)
    by_contra hh
    have hh := lt_of_not_ge hh
    nlinarith [norm_nonneg (w - p), norm_nonneg (q - p)]
  refine ⟨hn, ?_, ?_⟩
  · have he' : q - w = (q - p) - (w - p) := by abel
    have hi : ⟪q - p, w - p⟫ = ⟪w - p, q - p⟫ := real_inner_comm _ _
    have hs := norm_sub_sq_real (q - p) (w - p)
    rw [← he', hi] at hs
    nlinarith [sq_nonneg ‖q - p‖, norm_nonneg (q - w), norm_nonneg (w - p)]
  · have he' : (2 * r) • (q - (1 / 2 : ℝ) • (c + w)) - r • (p - c) =
        (2 * r) • (q - p) - r • (w - p) := by module
    rw [he']
    have ht := norm_sub_le ((2 * r) • (q - p)) (r • (w - p))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * r), abs_of_pos hr] at ht
    nlinarith

lemma regularized_root_distance {F : E → E} {X : Set E} {r : ℝ} (hr : 0 < r)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) {c p q : E}
    (hp : p ∈ X) (hq : q ∈ X) (hnp : Normal X p (-(F p + r • (p - c))))
    (hnq : Normal X q (-F q)) : ‖p - q‖ ≤ ‖c - q‖ ∧ ‖p - c‖ ≤ ‖c - q‖ := by
  have hnq' : Normal X q (-(F q + r • (q - q))) := by simpa using hnq
  have hd := regularized_root_nonexpansive hr hmono hp hq hnp hnq'
  refine ⟨hd, ?_⟩
  have hm := hmono p q
  have hn := normal_monotone hp hq hnp hnq
  have he : -(F p + r • (p - c)) - -F q = -(F p - F q) - r • (p - c) := by module
  rw [he, inner_sub_left, inner_neg_left, real_inner_smul_left] at hn
  have hi : ⟪p - c, p - q⟫ ≤ 0 := by
    by_contra hh
    have hh := lt_of_not_ge hh
    nlinarith [mul_pos hr hh]
  have he' : c - q = (p - q) - (p - c) := by abel
  have hs := norm_sub_sq_real (p - q) (p - c)
  rw [← he', real_inner_comm (p - c) (p - q)] at hs
  nlinarith [sq_nonneg ‖p - q‖, norm_nonneg (p - c), norm_nonneg (c - q)]

lemma operator_normal_bound {F : E → E} {L0 L1 h D : ℝ}
    (hF : GeneralizedMonotone.Hyp F L0 L1) {X : Set E} {x q ξ : E}
    (hx : x ∈ X) (hq : q ∈ X) (hnx : Normal X x ξ) (hnq : Normal X q (-F q))
    (hh : 0 < h) (hcap : L1 * h ≤ 1 / 2) (hD : ‖x - q‖ ≤ D) :
    h * ‖F x‖ ≤ h * ‖F q‖ + ‖F x + ξ‖ * D +
      2 * (L0 + L1 * ‖F q‖) * h * (D + h) := by
  have ho := one_point hF x q hh hcap
  have hn := normal_monotone hx hq hnx hnq
  rw [sub_neg_eq_add, inner_add_left] at hn
  have hi : ⟪F x - F q, x - q⟫ ≤ ⟪F x + ξ, x - q⟫ := by
    rw [inner_sub_left, inner_add_left]
    linarith
  have hcs := real_inner_le_norm (F x + ξ) (x - q)
  have hnF : ‖F x‖ ≤ ‖F x - F q‖ + ‖F q‖ := by
    simpa using norm_add_le (F x - F q) (F q)
  have hmul := mul_le_mul_of_nonneg_left hnF hh.le
  have hdist := mul_le_mul_of_nonneg_left hD (norm_nonneg (F x + ξ))
  have hL : 0 ≤ 2 * (L0 + L1 * ‖F q‖) * h := by
    have := hF.L0_pos
    have := hF.L1_nonneg
    positivity
  have hdist' := mul_le_mul_of_nonneg_left hD hL
  nlinarith

lemma regularized_strong_vi {F : E → E} {X : Set E} {r : ℝ}
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) {p y c : E}
    (hnp : Normal X p (-(F p + r • (p - c)))) (hy : y ∈ X) :
    r * ‖y - p‖ ^ 2 ≤ ⟪F y + r • (y - c), y - p⟫ := by
  have hn := hnp y hy
  rw [inner_neg_left] at hn
  have hm := hmono y p
  have he : F y + r • (y - c) = (F y - F p) + (F p + r • (p - c)) + r • (y - p) := by module
  rw [he, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  linarith

lemma regularized_local_bound {F : E → E} {L0 L1 r C : ℝ}
    (hF : GeneralizedMonotone.Hyp F L0 L1) (hr : 0 ≤ r) (c x y : E)
    (hx : ‖x - c‖ ≤ C) (hcap : L1 * ‖x - y‖ ≤ 1 / 2) :
    ‖(F y + r • (y - c)) - (F x + r • (x - c))‖ ≤
      2 * (L0 + r + L1 * r * C + L1 * ‖F x + r • (x - c)‖) * ‖x - y‖ := by
  have hl := hF.local x y (by linarith)
  have hnorm : ‖F x‖ ≤ ‖F x + r • (x - c)‖ + r * C := by
    have ht := norm_sub_le (F x + r • (x - c)) (r • (x - c))
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] at ht
    have := mul_le_mul_of_nonneg_left hx hr
    linarith
  have he : (F y + r • (y - c)) - (F x + r • (x - c)) = (F y - F x) + r • (y - x) := by module
  rw [he]
  have ht := norm_add_le (F y - F x) (r • (y - x))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, norm_sub_rev y x, norm_sub_rev (F y) (F x)] at ht
  have hFdiff : ‖F x - F y‖ ≤ 2 * (L0 + L1 * ‖F x‖) * ‖x - y‖ := by
    have hn := norm_nonneg (F x - F y)
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hcap)]
  have hL1 := hF.L1_nonneg
  have hmul := mul_le_mul_of_nonneg_left hnorm hL1
  have hmul' := mul_le_mul_of_nonneg_right hmul (norm_nonneg (x - y))
  nlinarith [mul_nonneg hr (norm_nonneg (x - y))]

lemma Proj.eq_of_normal {X : Set E} {P : E → E} (hP : Proj X P) {p z : E}
    (hp : p ∈ X) (hn : Normal X p (z - p)) : P z = p := by
  have h1 := hP.var z p hp
  have h2 := hn (P z) (hP.mem z)
  rw [show p - P z = -(P z - p) by abel, inner_neg_right] at h1
  have he : z - p = (z - P z) + (P z - p) := by abel
  rw [he, inner_add_left, real_inner_self_eq_norm_sq] at h2
  have hz : ‖P z - p‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖P z - p‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

lemma Proj.root_fixed {X : Set E} {P H : E → E} (hP : Proj X P) {p : E}
    (hp : p ∈ X) (hn : Normal X p (-H p)) {γ : ℝ} (hγ : 0 ≤ γ) :
    P (p - γ • H p) = p := by
  apply hP.eq_of_normal hp
  intro w hw
  have ht := hn w hw
  rw [inner_neg_left] at ht
  rw [show p - γ • H p - p = -(γ • H p) by abel, inner_neg_left, real_inner_smul_left]
  nlinarith [mul_nonneg hγ (neg_nonpos.mp ht)]

lemma Proj.noisy_root_distance {X : Set E} {P H : E → E} (hP : Proj X P) {p : E}
    (hp : p ∈ X) (hn : Normal X p (-H p)) {γ : ℝ} (hγ : 0 ≤ γ) (x e : E) :
    ‖P (x - γ • (H x + e)) - p‖ ≤ ‖x - p‖ + γ * ‖H x - H p‖ + γ * ‖e‖ := by
  have hl := hP.lipschitz.dist_le_mul (x - γ • (H x + e)) (p - γ • H p)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, hP.root_fixed hp hn hγ] at hl
  have he : (x - γ • (H x + e)) - (p - γ • H p) = (x - p) - γ • (H x - H p) - γ • e := by module
  rw [he] at hl
  have h1 := norm_sub_le ((x - p) - γ • (H x - H p)) (γ • e)
  have h2 := norm_sub_le (x - p) (γ • (H x - H p))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ] at h1 h2
  linarith

lemma Proj.regularized_residual_certificate {X : Set E} {P F : E → E} (hP : Proj X P)
    {p c x e : E} {r γ K ε : ℝ} (hp : p ∈ X)
    (hn : Normal X p (-(F p + r • (p - c)))) (hr : 0 ≤ r) (hγ : 0 < γ)
    (hε : 0 ≤ ε) (hK : 0 ≤ K) (hγK : γ * K ≤ 1) (hγr : γ * r ≤ 1)
    (hxp : ‖x - p‖ ≤ γ * ε / 32) (he : ‖e‖ ≤ ε / 32)
    (hbias : r * ‖p - c‖ ≤ ε / 4)
    (hlocal : ‖(F x + r • (x - c)) - (F p + r • (p - c))‖ ≤ K * ‖x - p‖)
    (hfinish : let y := P (x - γ • (F x + r • (x - c) + e));
      ‖F y - F x‖ ≤ K * ‖y - x‖) :
    let y := P (x - γ • (F x + r • (x - c) + e))
    y ∈ X ∧ ∃ ξ, Normal X y ξ ∧ ‖F y + ξ‖ ≤ ε := by
  dsimp only at hfinish ⊢
  let H := fun z => F z + r • (z - c)
  let y := P (x - γ • (H x + e))
  have hy := hP.noisy_root_distance (H := H) hp hn hγ.le x e
  have hdist : ‖y - p‖ ≤ 3 * γ * ε / 32 := by
    have h1 := mul_le_mul_of_nonneg_left hlocal hγ.le
    have h2 := mul_le_mul_of_nonneg_right hγK (norm_nonneg (x - p))
    have h3 := mul_le_mul_of_nonneg_left he hγ.le
    change ‖y - p‖ ≤ _ at hy
    nlinarith
  have hD : ‖x - y‖ ≤ γ * ε / 8 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub x p y
    rw [norm_sub_rev p y] at ht
    linarith
  have hFbound : ‖F y - F x‖ ≤ ε / 8 := by
    change ‖F y - F x‖ ≤ K * ‖y - x‖ at hfinish
    rw [norm_sub_rev y x] at hfinish
    have h1 := mul_le_mul_of_nonneg_left hD hK
    have h2 := mul_le_mul_of_nonneg_right hγK hε
    nlinarith
  have hrbound : r * ‖x - c‖ ≤ 9 * ε / 32 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub x p c
    have h1 := mul_le_mul_of_nonneg_left ht hr
    have h2 := mul_le_mul_of_nonneg_left hxp hr
    have h3 := mul_le_mul_of_nonneg_right hγr hε
    nlinarith
  let ξ := γ⁻¹ • (x - γ • (H x + e) - y)
  refine ⟨hP.mem _, ξ, hP.normal _ hγ, ?_⟩
  have hξ : ξ = γ⁻¹ • (x - y) - (H x + e) := by
    dsimp [ξ]
    rw [show x - γ • (H x + e) - y = (x - y) - γ • (H x + e) by abel,
      smul_sub, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
  have hid : F y + ξ = ((F y - F x) - r • (x - c)) + γ⁻¹ • (x - y) - e := by
    rw [hξ]
    dsimp [H]
    abel
  rw [hid]
  have h1 := norm_sub_le (((F y - F x) - r • (x - c)) + γ⁻¹ • (x - y)) e
  have h2 := norm_add_le ((F y - F x) - r • (x - c)) (γ⁻¹ • (x - y))
  have h3 := norm_sub_le (F y - F x) (r • (x - c))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hγ.le)] at h2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] at h3
  have hinv : γ⁻¹ * ‖x - y‖ ≤ ε / 8 := by
    rw [← div_eq_inv_mul, div_le_iff₀ hγ]
    nlinarith
  linarith

end OracleTemplate.ConstrainedMonotone
