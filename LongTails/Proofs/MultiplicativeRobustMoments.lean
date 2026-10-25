import LongTails.Proofs.MultiplicativeRobustConfidence
import LongTails.Proofs.MultiplicativeRobustClipping

open MeasureTheory
open LongTails.Proofs.HilbertSmallMoments

namespace OracleTemplate.MultiplicativeRobustEstimator

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] in
lemma normalized_oracle_moments {X : Ω → E} (hX : Measurable X) (u : E)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hi : Integrable X P)
    (hpi : Integrable (fun ω => ‖X ω-u‖ ^ p) P)
    (hm : (∫ ω, ‖X ω-u‖ ^ p ∂P) ≤ (‖u‖/65536)^p) :
    (∫ ω, ‖X ω-u‖ ∂P) ≤ ‖u‖/65536 ∧
    (∫ ω, ‖X ω‖ ∂P) ≤ 2*‖u‖ ∧
    Integrable (fun ω => ‖X ω‖ ^ p) P ∧
    (∫ ω, ‖X ω‖ ^ p ∂P) ≤ 4*‖u‖^p := by
  have hei : Integrable (fun ω => ‖X ω-u‖) P := (hi.sub (integrable_const u)).norm
  have hfirst := first_power_from_moment hp (by positivity : 0 ≤ ‖u‖/65536) hei hpi hm
  have hraw : (∫ ω, ‖X ω‖ ∂P) ≤ 2*‖u‖ := by
    have h := integral_mono hi.norm (hei.add (integrable_const ‖u‖)) (fun ω => by
      simpa only [Pi.add_apply, sub_add_cancel] using norm_add_le (X ω-u) u)
    simp only [Pi.add_apply] at h
    rw [integral_add hei (integrable_const ‖u‖)] at h
    simp only [integral_const, probReal_univ, one_smul] at h
    linarith [norm_nonneg u]
  have hrawi : Integrable (fun ω => ‖X ω‖ ^ p) P := by
    have h := integrable_add_power (hX.sub measurable_const) measurable_const hp hp2
      hpi (integrable_const (‖u‖^p))
    simpa only [Pi.sub_apply, sub_add_cancel] using h
  refine ⟨hfirst, hraw, hrawi, ?_⟩
  have hb (ω : Ω) : ‖X ω‖^p ≤ 2*(‖X ω-u‖^p+‖u‖^p) := by
    simpa only [sub_add_cancel] using addition_power_bound (X ω-u) u hp hp2
  have h := integral_mono hrawi ((hpi.add (integrable_const (‖u‖^p))).const_mul 2) hb
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add hpi (integrable_const (‖u‖^p))] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  have hm' : (∫ ω, ‖X ω-u‖^p ∂P) ≤ ‖u‖^p := hm.trans
    (Real.rpow_le_rpow (by positivity) (by nlinarith [norm_nonneg u]) (by linarith))
  linarith

omit [InnerProductSpace ℝ E] in
lemma normalized_pilot_small_power {X : Ω → E} (hX : Measurable X) (u : E)
    (hi : Integrable (fun ω => ‖X ω-u‖) P)
    (hm : (∫ ω, ‖X ω-u‖ ∂P) ≤ ‖u‖/65536) (n : ℕ) (hn : 8 ≤ n+1)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Integrable (fun ξ : Fin (n+1) → Ω => ‖medoid (fun i => X (ξ i))‖^q)
      (Measure.pi fun _ => P) ∧
    (∫ ξ : Fin (n+1) → Ω, ‖medoid (fun i => X (ξ i))‖^q
      ∂Measure.pi (fun _ => P)) ≤ 2*‖u‖^q := by
  have hd : Measurable (fun ξ : Fin (n+1) → Ω => medoid (fun i => X (ξ i))) :=
    measurable_medoid.comp (Measurable.of_eval (fun i => hX.comp (measurable_pi_apply i)))
  have he := normalized_medoid_second_moment hX u hi hm n hn
  have hs := second_moment_translate hd u he.1
  exact small_power_bound_from_second hd hq hq1 (norm_nonneg _) hs.1
    (by nlinarith [he.2, hs.2, sq_nonneg ‖u‖])

lemma normalized_mirror_second_moment {X : Ω → E} (hX : Measurable X) (u : E)
    {p Λ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hΛ : 1 ≤ Λ) (hi : Integrable X P)
    (hpi : Integrable (fun ω => ‖X ω-u‖ ^ p) P)
    (hm : (∫ ω, ‖X ω-u‖ ^ p ∂P) ≤ (‖u‖/65536)^p) (n : ℕ) (hn : 8 ≤ n+1) :
    Integrable (fun w : (Fin (n+1) → Ω) × Ω =>
      ‖clip (4*Λ*‖medoid (fun i => X (w.1 i))‖) (X w.2)‖^2)
      ((Measure.pi fun _ => P).prod P) ∧
    (∫ w : (Fin (n+1) → Ω) × Ω,
      ‖clip (4*Λ*‖medoid (fun i => X (w.1 i))‖) (X w.2)‖^2
      ∂(Measure.pi fun _ => P).prod P) ≤ 32*Λ^(2-p)*‖u‖^2 := by
  let Q := Measure.pi (fun _ : Fin (n+1) => P)
  let d : (Fin (n+1) → Ω) → E := fun ξ => medoid (fun i => X (ξ i))
  have hd : Measurable d :=
    measurable_medoid.comp (Measurable.of_eval (fun i => hX.comp (measurable_pi_apply i)))
  have ho := normalized_oracle_moments hX u hp hp2 hi hpi hm
  have hmom := normalized_pilot_small_power hX u (hi.sub (integrable_const u)).norm
    ho.1 n hn (show 0 ≤ 2-p by linarith) (show 2-p ≤ 1 by linarith)
  have he (ξ : Fin (n+1) → Ω) : (4*Λ*‖d ξ‖)^(2-p) =
      (4*Λ)^(2-p)*‖d ξ‖^(2-p) :=
    Real.mul_rpow (by positivity) (norm_nonneg _)
  have hRi : Integrable (fun ξ => (4*Λ*‖d ξ‖)^(2-p)) Q := by
    simp_rw [he]
    exact hmom.1.const_mul _
  have h := random_clip_second_moment (R := fun ξ => 4*Λ*‖d ξ‖)
    (measurable_const.mul hd.norm) hX (fun _ => by positivity)
    (by linarith : 0 ≤ p) hp2 hRi ho.2.2.1
  refine ⟨h.1, h.2.trans ?_⟩
  simp_rw [he]
  rw [integral_const_mul]
  have hfour : (4*Λ)^(2-p) ≤ 4*Λ^(2-p) := by
    rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ Λ)]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (show 2-p ≤ 1 by linarith)
  have hnorm : ‖u‖^(2-p)*‖u‖^p = ‖u‖^2 := by
    rw [← Real.rpow_add' (norm_nonneg u) (by linarith : 2-p+p ≠ 0)]
    simp only [sub_add_cancel, Real.rpow_two]
  calc
    _ ≤ ((4*Λ)^(2-p)*(2*‖u‖^(2-p))) * (4*‖u‖^p) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmom.2 (by positivity)) ho.2.2.2
        (integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg _) _)) (by positivity)
    _ ≤ (4*Λ^(2-p)*(2*‖u‖^(2-p))) * (4*‖u‖^p) := by gcongr
    _ = 32*Λ^(2-p)*(‖u‖^(2-p)*‖u‖^p) := by ring
    _ = _ := by rw [hnorm]

lemma normalized_bias_algebra {p g Λ : ℝ} (hp : 1 ≤ p) (hg : 0 < g) (hΛ : 1 ≤ Λ) :
    (g/65536)^p / (Λ*g)^(p-1) + (Λ^(1-p)/64)*(2*g) ≤ Λ^(1-p)/16*g := by
  have hΛpos : 0 < Λ := by linarith
  have hdelta : (1/65536 : ℝ)^p ≤ 1/65536 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
      (by norm_num : (0 : ℝ) < 1/65536) (by norm_num : (1/65536 : ℝ) ≤ 1) hp
  have hgpow : g^p/g^(p-1) = g := by
    rw [← Real.rpow_sub hg]
    simp
  have hΛpow : Λ^(1-p) = 1/Λ^(p-1) := by
    rw [show 1-p = -(p-1) by ring, Real.rpow_neg hΛpos.le, one_div]
  have he : (g/65536)^p/(Λ*g)^(p-1) = (1/65536 : ℝ)^p*g*Λ^(1-p) := by
    calc
      _ = (1/65536 : ℝ)^p*(g^p/g^(p-1))/Λ^(p-1) := by
        rw [show g/65536 = (1/65536)*g by ring,
          Real.mul_rpow (by norm_num) hg.le, Real.mul_rpow hΛpos.le hg.le]
        ring
      _ = _ := by rw [hgpow, hΛpow]; ring
  rw [he]
  have hb := mul_le_mul_of_nonneg_right hdelta
    (show 0 ≤ g*Λ^(1-p) by positivity)
  have hn : 0 ≤ g*Λ^(1-p) := by positivity
  nlinarith

lemma normalized_mirror_bias {X : Ω → E} (hX : Measurable X) (u : E)
    {p Λ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hΛ : 1 ≤ Λ) (hu : 0 < ‖u‖)
    (hi : Integrable X P) (hmean : ∫ ω, X ω ∂P = u)
    (hpi : Integrable (fun ω => ‖X ω-u‖ ^ p) P)
    (hm : (∫ ω, ‖X ω-u‖ ^ p ∂P) ≤ (‖u‖/65536)^p) (n : ℕ)
    (hbad : (Measure.pi fun _ : Fin (n+1) => P).real
      {ξ | ‖u‖/2 < ‖medoid (fun i => X (ξ i))-u‖} ≤ Λ^(1-p)/64) :
    Integrable (fun w : (Fin (n+1) → Ω) × Ω =>
      clip (4*Λ*‖medoid (fun i => X (w.1 i))‖) (X w.2))
      ((Measure.pi fun _ => P).prod P) ∧
    ‖(∫ w : (Fin (n+1) → Ω) × Ω,
      clip (4*Λ*‖medoid (fun i => X (w.1 i))‖) (X w.2)
      ∂(Measure.pi fun _ => P).prod P)-u‖ ≤ Λ^(1-p)/16*‖u‖ := by
  let Q := Measure.pi (fun _ : Fin (n+1) => P)
  let d : (Fin (n+1) → Ω) → E := fun ξ => medoid (fun i => X (ξ i))
  let B := {ξ | ‖u‖/2 < ‖d ξ-u‖}
  have hd : Measurable d :=
    measurable_medoid.comp (Measurable.of_eval (fun i => hX.comp (measurable_pi_apply i)))
  have hB : MeasurableSet B := measurableSet_lt measurable_const ((hd.sub measurable_const).norm)
  have hgood (ξ : Fin (n+1) → Ω) (hb : ξ ∉ B) : 2*Λ*‖u‖ ≤ 4*Λ*‖d ξ‖ := by
    have he : ‖d ξ-u‖ ≤ ‖u‖/2 := le_of_not_gt hb
    have ht := norm_sub_norm_le u (d ξ)
    rw [norm_sub_rev u (d ξ)] at ht
    have hl : ‖u‖ ≤ 2*‖d ξ‖ := by linarith
    nlinarith
  have h := random_clip_bias (Q := Q) (R := fun ξ => 4*Λ*‖d ξ‖)
    (measurable_const.mul hd.norm) hX (fun _ => by positivity) hp
    (by positivity : 0 < 2*Λ*‖u‖) u (by nlinarith) hi hmean hpi hB hgood
  refine ⟨h.1, h.2.trans ?_⟩
  have ho := normalized_oracle_moments hX u hp hp2 hi hpi hm
  rw [show 2*Λ*‖u‖/2 = Λ*‖u‖ by ring]
  apply (add_le_add
    (div_le_div_of_nonneg_right hm (Real.rpow_nonneg (by positivity) _))
    (mul_le_mul hbad ho.2.1 (integral_nonneg (fun ω => norm_nonneg _)) (by positivity))).trans
  exact normalized_bias_algebra hp hu hΛ

end OracleTemplate.MultiplicativeRobustEstimator
