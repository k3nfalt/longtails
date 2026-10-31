import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import LongTails.Proofs.ProjectedClippedStability
import LongTails.Proofs.ConstrainedRegularization

open scoped RealInnerProductSpace

namespace LongTails.Proofs.GapNoiseTwoCenter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma weighted_drift (F : E → E) (x p a s : E) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : r * ‖x - p‖ ^ 2 ≤ ⟪F x + r • (x - a), x - p⟫)
    (hs : 0 ≤ ⟪F s, x - s⟫) :
    r / 2 * ‖x - p‖ ^ 2 + t * ⟪F x - F s, x - s⟫ -
      t ^ 2 * r / 2 * ‖p - a + (p - s)‖ ^ 2 -
      t * r * (‖p - a‖ * ‖p - s‖) ≤
      (1 - t) * ⟪F x + r • (x - a), x - p⟫ +
        t * ⟪F x + r • (x - a), x - s⟫ := by
  have he : ⟪x - a, x - s⟫ = ‖x - p‖ ^ 2 +
      ⟪x - p, p - a + (p - s)⟫ + ⟪p - a, p - s⟫ := by
    rw [show x - a = (x - p) + (p - a) by abel,
      show x - s = (x - p) + (p - s) by abel]
    simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm (p - a) (x - p)]
    ring
  have hcross := real_inner_le_norm (-(x - p)) (p - a + (p - s))
  have hbase := real_inner_le_norm (-(p - a)) (p - s)
  simp only [inner_neg_left, norm_neg] at hcross hbase
  have hp' := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr ht1)
  have hs' := mul_nonneg ht hs
  have hc := mul_le_mul_of_nonneg_left hcross (mul_nonneg ht hr)
  have hb := mul_le_mul_of_nonneg_left hbase (mul_nonneg ht hr)
  have hy := mul_nonneg hr (sq_nonneg (‖x - p‖ - t * ‖p - a + (p - s)‖))
  simp only [inner_add_left, real_inner_smul_left] at hp' ⊢
  rw [inner_sub_left (F x) (F s)]
  rw [he]
  nlinarith

lemma reference_distance (p a s : E) :
    ‖p - s‖ ^ 2 ≤ ‖p - a + (p - s)‖ ^ 2 + 2 * (‖p - a‖ * ‖p - s‖) := by
  have h := real_inner_le_norm (-(p - a)) (p - s)
  simp only [inner_neg_left, norm_neg] at h
  rw [norm_add_sq_real]
  nlinarith [sq_nonneg ‖p - a‖]

lemma shifted_distance (x p s : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖x - (p + t • (s - p))‖ ^ 2 / 2 - t ^ 2 * ‖p - s‖ ^ 2 ≤ ‖x - p‖ ^ 2 := by
  have h := norm_sub_le (x - p) (t • (s - p))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, norm_sub_rev s p] at h
  have he : x - p - t • (s - p) = x - (p + t • (s - p)) := by abel
  rw [he] at h
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖x - p‖ - t * ‖p - s‖)]

lemma shifted_margin (p c s : E) {t d : ℝ} (ht : 0 ≤ t)
    (hp : ‖p - c‖ ≤ d) (hs : t * ‖p - s‖ ≤ d) :
    ‖p + t • (s - p) - c‖ ≤ 2 * d := by
  have h := norm_add_le (p - c) (t • (s - p))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, norm_sub_rev s p] at h
  have he : p + t • (s - p) - c = (p - c) + t • (s - p) := by abel
  rw [he]
  linarith

lemma centered_drift (F : E → E) (x p a s : E) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hp : r * ‖x - p‖ ^ 2 ≤ ⟪F x + r • (x - a), x - p⟫)
    (hs : 0 ≤ ⟪F s, x - s⟫) :
    r / 4 * ‖x - (p + t • (s - p))‖ ^ 2 + t * ⟪F x - F s, x - s⟫ -
      t ^ 2 * r * ‖p - a + (p - s)‖ ^ 2 -
      2 * t * r * (‖p - a‖ * ‖p - s‖) ≤
      ⟪F x + r • (x - a), x - (p + t • (s - p))⟫ := by
  have hd := weighted_drift F x p a s hr ht (by linarith) hp hs
  have he : (1 - t) * ⟪F x + r • (x - a), x - p⟫ +
      t * ⟪F x + r • (x - a), x - s⟫ =
      ⟪F x + r • (x - a), x - (p + t • (s - p))⟫ := by
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
    ring
  rw [he] at hd
  have hdist := mul_le_mul_of_nonneg_left (shifted_distance x p s ht) (by positivity : 0 ≤ r / 2)
  have href := mul_le_mul_of_nonneg_left (reference_distance p a s)
    (by positivity : 0 ≤ t ^ 2 * r / 2)
  have hnonneg : 0 ≤ r * (‖p - a‖ * ‖p - s‖) := by positivity
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have htbound := mul_le_mul_of_nonneg_right ht2 hnonneg
  nlinarith

lemma past_projection_energy {X : Set E} {P : E → E}
    (hP : OracleTemplate.ConstrainedMonotone.Proj X P)
    (w z previous h e : E) (hz : z ∈ X) {η S V : ℝ} (hη : 0 ≤ η)
    (hlocal : η ^ 2 * ‖previous - (h + e)‖ ^ 2 ≤
      (‖w - P (w - η • previous)‖ ^ 2 + S) / 16 + 3 * η ^ 2 * V) :
    let x := P (w - η • previous)
    let y := P (w - η • (h + e))
    ‖y - z‖ ^ 2 + ‖y - x‖ ^ 2 / 4 ≤
      ‖w - z‖ ^ 2 - 7 / 8 * ‖w - x‖ ^ 2 + S / 8 -
        2 * η * ⟪h, x - z⟫ - 2 * η * ⟪e, x - z⟫ + 6 * η ^ 2 * V := by
  dsimp only
  set x := P (w - η • previous)
  set y := P (w - η • (h + e))
  have hp := hP.extragradient_energy hz w previous (h + e) η
  change ‖y - z‖ ^ 2 ≤ ‖w - z‖ ^ 2 - ‖w - x‖ ^ 2 - ‖y - x‖ ^ 2 -
    2 * η * ⟪h + e, x - z⟫ + 2 * η * ⟪previous - (h + e), y - x⟫ at hp
  have hi := mul_le_mul_of_nonneg_left
    (real_inner_le_norm (previous - (h + e)) (y - x)) hη
  have hy := sq_nonneg (‖y - x‖ - 2 * η * ‖previous - (h + e)‖)
  rw [inner_add_left] at hp
  change η ^ 2 * ‖previous - (h + e)‖ ^ 2 ≤
    (‖w - x‖ ^ 2 + S) / 16 + 3 * η ^ 2 * V at hlocal
  nlinarith [sq_nonneg ‖y - x‖]

lemma projected_pair_distance {X : Set E} {P : E → E}
    (hP : OracleTemplate.ConstrainedMonotone.Proj X P)
    (w g previous : E) {η : ℝ} (hη : 0 ≤ η) :
    ‖P (w - η • g) - P (w - η • previous)‖ ≤ η * (‖g‖ + ‖previous‖) := by
  have hp := hP.lipschitz.dist_le_mul (w - η • g) (w - η • previous)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hp
  have he : w - η • g - (w - η • previous) = η • (previous - g) := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at hp
  have hn := mul_le_mul_of_nonneg_left (norm_sub_le previous g) hη
  linarith

lemma past_predictor_distance {X : Set E} {P : E → E}
    (hP : OracleTemplate.ConstrainedMonotone.Proj X P)
    (w g previous : E) {η ηnext radius : ℝ} (hη : 0 ≤ η) (hnext : 0 ≤ ηnext)
    (hg : η * ‖g‖ ≤ radius) (hold : η * ‖previous‖ ≤ 2 * radius)
    (hgrowth : ηnext ≤ 2 * η) :
    let y := P (w - η • g)
    ‖P (y - ηnext • g) - P (w - η • previous)‖ ≤ 5 * radius := by
  dsimp only
  have hp := projected_pair_distance hP w g previous hη
  have hm := hP.dist_le (P (w - η • g) - ηnext • g) (hP.mem (w - η • g))
  have he : P (w - η • g) - ηnext • g - P (w - η • g) = -(ηnext • g) := by abel
  rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnext] at hm
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (P (P (w - η • g) - ηnext • g)) (P (w - η • g)) (P (w - η • previous))
  have hh := mul_le_mul_of_nonneg_right hgrowth (norm_nonneg g)
  nlinarith

lemma shifted_coercivity (H : E → E) (x p s : E) {h B t : ℝ}
    (ht : 0 ≤ t) (hshift : t * ‖p - s‖ ≤ h / 2)
    (hc : h * ‖H x‖ ≤ h * B + ⟪H x, x - p⟫) :
    h / 2 * ‖H x‖ - h * B ≤ ⟪H x, x - (p + t • (s - p))⟫ := by
  have hi := real_inner_le_norm (H x) (s - p)
  rw [norm_sub_rev s p] at hi
  have hi' := mul_le_mul_of_nonneg_left hi ht
  have hs := mul_le_mul_of_nonneg_right hshift (norm_nonneg (H x))
  have he : ⟪H x, x - (p + t • (s - p))⟫ =
      ⟪H x, x - p⟫ - t * ⟪H x, s - p⟫ := by
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
    ring
  rw [he]
  nlinarith

lemma doubled_step_scale {η Dold Dnew cap a δ : ℝ}
    (hD : 0 ≤ Dnew) (hold : a ≤ η * Dold)
    (hvariation : η * Dold - η * Dnew ≤ δ)
    (hslack : 2 * δ ≤ a) (hcap : a ≤ cap * Dnew) :
    a ≤ min (2 * η) cap * Dnew := by
  rw [min_mul_of_nonneg _ _ hD]
  apply le_min
  · nlinarith
  · exact hcap

lemma norm_scaled_drift {η S v a α Q D κ c J : ℝ}
    (hη : 0 ≤ η) (hS : 0 ≤ S) (ha : 0 ≤ a) (hα : 0 ≤ α)
    (hQ : 0 ≤ Q) (hκ : 0 ≤ κ) (hQD : Q ≤ D)
    (hstep : a ≤ η * (S + v)) (hoffset : 2 * c ≤ S)
    (hscale : α * D ≤ S * κ) (hstrong : α * Q ≤ J)
    (hcoercive : κ * (v - c) ≤ J) :
    a * α * Q ≤ 4 * S * η * J := by
  have hJ : 0 ≤ J := (mul_nonneg hα hQ).trans hstrong
  have hαQ : α * Q ≤ S * κ :=
    (mul_le_mul_of_nonneg_left hQD hα).trans hscale
  by_cases hv : v ≤ S
  · have hηS : a ≤ 2 * η * S := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hηS (mul_nonneg hα hQ)
    have h2 := mul_le_mul_of_nonneg_left hstrong (by positivity : 0 ≤ 2 * η * S)
    nlinarith [mul_nonneg (mul_nonneg hS hη) hJ]
  · have hvS : S ≤ v := le_of_lt (lt_of_not_ge hv)
    have hv0 : 0 ≤ v := hS.trans hvS
    have hηv : a ≤ 2 * η * v := by nlinarith
    have hκv : κ * v ≤ 2 * J := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hηv hκ
    have h2 := mul_le_mul_of_nonneg_left hκv hη
    have h3 : a * κ ≤ 4 * η * J := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 hS
    have h5 := mul_le_mul_of_nonneg_left hαQ ha
    nlinarith

lemma uniform_norm_scaled_drift {η S b h H B r Q D J : ℝ}
    (hη : 0 ≤ η) (hS : 0 < S) (hb : 0 < b) (hh : 0 < h) (hr : 0 ≤ r)
    (hQ : 0 ≤ Q) (hQD : Q ≤ D)
    (hstep : 1 / 262144 ≤ η * (2 * S + b * H))
    (hoffset : 2 * b * B ≤ S) (hscale : r * b * D ≤ 4 * S * h)
    (hstrong : r / 4 * Q ≤ J) (hcoercive : h / 2 * H - h * B ≤ J) :
    r / (2 ^ 25 * S) * Q ≤ η * J := by
  have hsc : r / 4 * D ≤ (2 * S) * (h / (2 * b)) := by
    rw [← mul_div_assoc, le_div_iff₀ (by positivity : 0 < 2 * b)]
    nlinarith
  have hco : h / (2 * b) * (b * H - 2 * b * B) ≤ J := by
    have he : h / (2 * b) * (b * H - 2 * b * B) = h / 2 * H - h * B := by
      field_simp
    rw [he]
    exact hcoercive
  have h := norm_scaled_drift hη (by positivity : 0 ≤ 2 * S)
    (by norm_num : (0 : ℝ) ≤ 1 / 262144) (by positivity : 0 ≤ r / 4)
    hQ (by positivity : 0 ≤ h / (2 * b)) hQD hstep (by nlinarith) hsc hstrong hco
  have hJ : 0 ≤ J := (mul_nonneg (by positivity) hQ).trans hstrong
  have hn := mul_nonneg hS.le (mul_nonneg hη hJ)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2 ^ 25 * S)]
  nlinarith

lemma gap_near_reference (F : E → E) (x p s : E) {L N d R : ℝ}
    (hL : 0 ≤ L) (hN : 0 ≤ N) (hd : ‖x - p‖ ≤ d) (hR : ‖p - s‖ ≤ R)
    (hlocal : ‖F x - F p‖ ≤ L * ‖x - p‖) (href : ‖F p - F s‖ ≤ N) :
    ⟪F x - F s, x - s⟫ ≤ ⟪F p - F s, p - s⟫ + L * d * (R + d) + N * d := by
  have hd0 := (norm_nonneg (x - p)).trans hd
  have hR0 := (norm_nonneg (p - s)).trans hR
  have he : ⟪F x - F s, x - s⟫ = ⟪F p - F s, p - s⟫ +
      ⟪F x - F p, x - s⟫ + ⟪F p - F s, x - p⟫ := by
    rw [show F x - F s = (F x - F p) + (F p - F s) by abel,
      inner_add_left, show x - s = (x - p) + (p - s) by abel]
    simp only [inner_add_right]
    ring
  have hxs : ‖x - s‖ ≤ R + d := by
    have := norm_sub_le_norm_sub_add_norm_sub x p s
    linarith
  have hl : ‖F x - F p‖ ≤ L * d := hlocal.trans (mul_le_mul_of_nonneg_left hd hL)
  have h1 := (real_inner_le_norm (F x - F p) (x - s)).trans
    (mul_le_mul hl hxs (norm_nonneg _) (by positivity))
  have h2 := (real_inner_le_norm (F p - F s) (x - p)).trans
    (mul_le_mul href hd (norm_nonneg _) hN)
  rw [he]
  linarith

lemma past_predictor_root_distance {X : Set E} {P H : E → E}
    (hP : OracleTemplate.ConstrainedMonotone.Proj X P) {p : E}
    (hp : p ∈ X) (hn : OracleTemplate.ConstrainedMonotone.Normal X p (-H p))
    (w previous e : E) {η : ℝ} (hη : 0 ≤ η) :
    ‖P (w - η • (H previous + e)) - p‖ ≤
      ‖w - p‖ + η * ‖H previous - H p‖ + η * ‖e‖ := by
  have hl := hP.lipschitz.dist_le_mul (w - η • (H previous + e)) (p - η • H p)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, hP.root_fixed hp hn hη] at hl
  have he : w - η • (H previous + e) - (p - η • H p) =
      (w - p) - η • (H previous - H p) - η • e := by module
  rw [he] at hl
  have h1 := norm_sub_le ((w - p) - η • (H previous - H p)) (η • e)
  have h2 := norm_sub_le (w - p) (η • (H previous - H p))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at h1 h2
  linarith

lemma positive_curvature_envelope {L0 L1 G R : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hG : 0 ≤ G) (hR : 0 < R) :
    let b := L1 + L0 / (G + L0 * R)
    0 < b ∧ b * R ≤ 1 + L1 * R ∧ L0 + b * G ≤ 2 * L0 + L1 * G := by
  dsimp only
  have hd : 0 < G + L0 * R := by positivity
  have hr : L0 / (G + L0 * R) * R ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hd]
    linarith
  have hg : L0 / (G + L0 * R) * G ≤ L0 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    exact mul_le_mul_of_nonneg_left (by nlinarith : G ≤ G + L0 * R) h0.le
  exact ⟨by positivity, by nlinarith, by nlinarith⟩

lemma past_augmented_energy {X : Set E} {P : E → E}
    (hP : OracleTemplate.ConstrainedMonotone.Proj X P)
    (w z previous previousPoint h e previousError : E) (hz : z ∈ X)
    {η ηold : ℝ} (hη : 0 ≤ η) (hgrowth : η ≤ 2 * ηold)
    (hlocal : η ^ 2 * ‖previous - (h + e)‖ ^ 2 ≤
      (‖w - P (w - η • previous)‖ ^ 2 + ‖w - previousPoint‖ ^ 2) / 16 +
        3 * η ^ 2 * (‖previousError‖ ^ 2 + ‖e‖ ^ 2)) :
    let x := P (w - η • previous)
    let y := P (w - η • (h + e))
    ‖y - z‖ ^ 2 + ‖y - x‖ ^ 2 / 4 + 24 * η ^ 2 * ‖e‖ ^ 2 ≤
      ‖w - z‖ ^ 2 + ‖w - previousPoint‖ ^ 2 / 4 +
        24 * ηold ^ 2 * ‖previousError‖ ^ 2 -
        7 / 8 * ‖w - x‖ ^ 2 - ‖w - previousPoint‖ ^ 2 / 8 -
        2 * η * ⟪h, x - z⟫ - 2 * η * ⟪e, x - z⟫ + 30 * η ^ 2 * ‖e‖ ^ 2 := by
  dsimp only
  have hp := past_projection_energy hP w z previous h e hz hη hlocal
  dsimp only at hp
  have hs := pow_le_pow_left₀ hη hgrowth 2
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖previousError‖)
  nlinarith

omit [InnerProductSpace ℝ E] in
lemma local_oracle_difference (previous current oldError error : E) {η d s : ℝ}
    (hη : 0 ≤ η) (hlocal : η * ‖previous - current‖ ≤ (d + s) / 16) :
    η ^ 2 * ‖previous + oldError - (current + error)‖ ^ 2 ≤
      (d ^ 2 + s ^ 2) / 16 + 3 * η ^ 2 * (‖oldError‖ ^ 2 + ‖error‖ ^ 2) := by
  have he : previous + oldError - (current + error) =
      (previous - current) + (oldError - error) := by abel
  have hn := norm_add_le (previous - current) (oldError - error)
  have ho := norm_sub_le oldError error
  have ht : η * ‖previous + oldError - (current + error)‖ ≤
      η * ‖previous - current‖ + η * ‖oldError‖ + η * ‖error‖ := by
    rw [he]
    have h := mul_le_mul_of_nonneg_left hn hη
    have h' := mul_le_mul_of_nonneg_left ho hη
    linarith
  have hsq := pow_le_pow_left₀ (mul_nonneg hη (norm_nonneg _)) ht 2
  have hlsq := pow_le_pow_left₀ (mul_nonneg hη (norm_nonneg _)) hlocal 2
  nlinarith [sq_nonneg (η * ‖previous - current‖ - η * ‖oldError‖),
    sq_nonneg (η * ‖previous - current‖ - η * ‖error‖),
    sq_nonneg (η * ‖oldError‖ - η * ‖error‖), sq_nonneg (d - s), sq_nonneg d, sq_nonneg s]

end LongTails.Proofs.GapNoiseTwoCenter
