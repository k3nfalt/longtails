import LongTails.Proofs.LogisticCloudCone
import LongTails.Proofs.LogisticCloudDispersion

open LongTails.Proofs.LogisticCloudCone
open LongTails.Proofs.LogisticCloudDispersion

namespace LongTails.Proofs.LogisticCloudDrift

structure Scales where
  a : ℝ
  μ : ℝ
  β : ℝ
  η : ℝ
  ha : 0 < a
  ha' : a ≤ 1/16
  hμ : 0 < μ
  hμ' : μ ≤ 1/10
  hβ : 4/5 ≤ β
  hβ' : β ≤ 1
  hη : 0 < η
  tune : η * (a + μ) ≤ 1 / 2^48

noncomputable def drift (s : Scales) (x : Point) (D : ℝ) : ℝ :=
  s.η/2 * (Real.sigmoid (-(x.p*x.q)) -
    (1+s.μ*s.a)*Real.sigmoid ((1+s.μ*s.a)*x.p*x.q-D))

noncomputable def weight (s : Scales) (x : Point) (D : ℝ) : ℝ :=
  s.η/2*s.μ*Real.sigmoid ((1+s.μ*s.a)*x.p*x.q-D)

lemma sigmoid_gap {x y : ℝ} (h : y ≤ x) : Real.sigmoid x - Real.sigmoid y ≤ (x-y)/4 := by
  obtain ⟨t, ⟨_, ht⟩, he⟩ := sigmoid_secant x y
  nlinarith [mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr h)]

lemma coefficients (s : Scales) (x : Point) (D : ℝ)
    (hx : Cone s.a x) (hq : x.q ≤ 0) (hD : 0 ≤ D)
    (hD' : D ≤ 8*s.μ*(amplitude x)^2) (hH : (amplitude x)^2 ≤ 2^32*s.a) :
    let h := drift s x D
    let l := weight s x D
    |h| ≤ 1/2 ∧ -(5/4)*s.a*(s.β*l) ≤ h ∧ 0 ≤ l ∧ 2*l ≤ s.η*s.μ ∧
      (s.η*s.μ/16 ≤ s.β*l ∨ s.η*s.μ ≤ h) := by
  intro h l
  obtain ⟨hH₀, hpH, _⟩ := amplitude_bounds hx
  obtain ⟨hp, haQ, _, _, _⟩ := hx
  have hη := s.hη
  have hμ := s.hμ
  have ha := s.ha
  have hτ : s.μ*s.a ≤ 1/16 := by
    nlinarith [mul_le_mul s.hμ' s.ha' ha.le (by norm_num : (0:ℝ) ≤ 1/10)]
  let A := Real.sigmoid (-(x.p*x.q))
  let B := Real.sigmoid ((1+s.μ*s.a)*x.p*x.q-D)
  have hneg := mul_nonpos_of_nonneg_of_nonpos hp.le hq
  have hz := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1+s.μ*s.a by positivity) hneg
  have hA : 1/2 ≤ A := by simpa [A] using Real.sigmoid_le (neg_nonneg.mpr hneg)
  have hB : B ≤ 1/2 := by
    apply (Real.sigmoid_le (show (1+s.μ*s.a)*x.p*x.q-D ≤ 0 by linarith only [hz,hD])).trans
    norm_num
  have hB₀ : 0 ≤ B := Real.sigmoid_nonneg _
  have he : h = s.η/2*(A-(1+s.μ*s.a)*B) := rfl
  have le : l = s.η/2*s.μ*B := rfl
  have hl : 0 ≤ l := le.symm ▸ (by positivity)
  have hbound := mul_le_mul_of_nonneg_left hB (show 0 ≤ s.η*s.μ by positivity)
  have hlo : -s.a*l ≤ h := by
    rw [he,le]
    nlinarith only [mul_le_mul_of_nonneg_left (hB.trans hA) hη.le]
  have hμt : s.η*s.μ ≤ 1/2^48 := by linarith [s.tune, mul_nonneg hη.le ha.le]
  have hap : s.η*s.a ≤ 1/2^48 := by linarith [s.tune, mul_nonneg hη.le hμ.le]
  have hsq := mul_le_mul hpH hpH hp.le (by positivity)
  have hq' := mul_le_mul_of_nonneg_left haQ hp.le
  have hargs : (1+s.μ*s.a)*x.p*x.q-D ≤ -(x.p*x.q) := by linarith only [hz,hneg,hD]
  have hgap := sigmoid_gap hargs
  change A-B ≤ _ at hgap
  have hτpq := mul_le_mul_of_nonpos_right (show s.μ*s.a ≤ 1 by linarith) hneg
  have hab : A-B ≤ 12*s.a*(amplitude x)^2 + D/4 := by
    nlinarith only [hgap,hτpq,hq',mul_le_mul_of_nonneg_left hsq ha.le]
  have hsum : A-B ≤ 12*(s.a+s.μ)*(amplitude x)^2 := by
    nlinarith only [hab,hD',mul_nonneg hμ.le (sq_nonneg (amplitude x))]
  have hhigh := mul_le_mul_of_nonneg_left hsum hη.le
  have hprod := mul_le_mul_of_nonneg_right s.tune (sq_nonneg (amplitude x))
  have hextra := mul_nonneg (mul_nonneg (mul_nonneg hη.le hμ.le) ha.le) hB₀
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, ?_, hl, by linarith [le], ?_⟩
  · nlinarith only [hlo,le,hbound,hμt,mul_le_mul_of_nonneg_left s.ha' hl,
      mul_nonneg hη.le hμ.le]
  · nlinarith only [he,hhigh,hprod,hH,s.ha',hextra]
  · nlinarith only [hlo,mul_le_mul_of_nonneg_right s.hβ (mul_nonneg ha.le hl)]
  · rcases le_or_gt (1/4 : ℝ) B with hb | hb
    · left
      have hb' := mul_le_mul s.hβ hb (by norm_num : (0:ℝ) ≤ 1/4)
        (by linarith [s.hβ] : 0 ≤ s.β)
      rw [le]
      nlinarith only [mul_le_mul_of_nonneg_left hb' (mul_nonneg hη.le hμ.le),
        mul_nonneg hη.le hμ.le]
    · right
      have H := mul_le_mul (show 1+s.μ*s.a ≤ 17/16 by linarith) hb.le hB₀
        (by norm_num : (0:ℝ) ≤ 17/16)
      nlinarith only [he,mul_le_mul_of_nonneg_left H hη.le,
        mul_le_mul_of_nonneg_left hA hη.le,mul_le_mul_of_nonneg_left s.hμ' hη.le,hη.le]

lemma high_drift (s : Scales) (x : Point) (D : ℝ) (hp : 0 ≤ x.p) (hq : x.q ≤ 0)
    (hD : 256*(s.μ*s.a) ≤ D) : 6*s.η*s.μ*s.a ≤ drift s x D := by
  let τ := s.μ*s.a
  have ha := s.ha
  have hμ := s.hμ
  have hτ : 0 ≤ τ := mul_nonneg hμ.le ha.le
  have ht : τ ≤ 1/100 := by
    dsimp [τ]
    nlinarith [mul_le_mul s.hμ' s.ha' ha.le (by norm_num : (0:ℝ) ≤ 1/10)]
  have hnon := mul_nonpos_of_nonneg_of_nonpos hp hq
  have hlow := Real.sigmoid_le (neg_nonneg.mpr hnon)
  rw [Real.sigmoid_zero] at hlow
  let z := (1+τ)*x.p*x.q-D
  have hz : z ≤ -D := by
    dsimp [z]
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1+τ by linarith) hnon]
  have hD₀ : 0 ≤ D := by change 256*τ ≤ D at hD; linarith
  have hden : 0 < 2+D := by linarith
  have hB : Real.sigmoid z ≤ 1/(2+D) := by
    rw [Real.sigmoid_def, ← one_div]
    apply one_div_le_one_div_of_le hden
    linarith [Real.add_one_le_exp (-z)]
  have hfrac : (1+τ)/(2+D) ≤ 1/2-12*τ := by
    apply (div_le_iff₀ hden).mpr
    have hD' : 256*τ ≤ D := hD
    nlinarith only [mul_le_mul_of_nonneg_left hD' (show 0 ≤ 1/2-12*τ by linarith),
      mul_nonneg hτ (sub_nonneg.mpr ht), hτ]
  have HH := mul_le_mul_of_nonneg_left hB (show 0 ≤ 1+τ by linarith)
  rw [mul_one_div] at HH
  rw [mul_assoc (6*s.η)]
  change 6*s.η*τ ≤ s.η/2*(Real.sigmoid (-(x.p*x.q))-(1+τ)*Real.sigmoid z)
  nlinarith only [mul_le_mul_of_nonneg_left (HH.trans hfrac) s.hη.le,
    mul_le_mul_of_nonneg_left hlow s.hη.le]

end LongTails.Proofs.LogisticCloudDrift
