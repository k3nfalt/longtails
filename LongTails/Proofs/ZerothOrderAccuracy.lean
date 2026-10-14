import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import LongTails.Proofs.AcceleratedBiasedStochastic
import LongTails.Proofs.AcceleratedComparator
import LongTails.Proofs.ZerothOrderEstimator
import LongTails.Proofs.ZerothOrderGridEstimator
import LongTails.Proofs.ZerothOrderSmoothing

section

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma min_bandwidth_noise {A C L σ : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hL : 0 < L) (hσ : 0 ≤ σ) :
    0 < min A (σ/L+C) ∧ σ^2/min A (σ/L+C) ≤ σ^2/A+L*σ := by
  have hB : 0 < σ/L+C := by positivity
  refine ⟨lt_min hA hB, ?_⟩
  have hratio : σ^2/(σ/L+C) ≤ L*σ := by
    apply (div_le_iff₀ hB).mpr
    have he : L*σ*(σ/L+C) = σ^2+L*σ*C := by field_simp
    rw [he]
    exact le_add_of_nonneg_right (by positivity)
  by_cases h : A ≤ σ/L+C
  · rw [min_eq_left h]
    linarith [mul_nonneg hL.le hσ]
  · rw [min_eq_right (le_of_not_ge h)]
    have hn : 0 ≤ σ^2/A := by positivity
    linarith

lemma min_bandwidth_variance {A C L σ d : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hL : 0 < L) (hσ : 0 ≤ σ) (hd : 0 ≤ d) :
    44*L^2*d*min A (σ/L+C)+2*d*σ^2/min A (σ/L+C) ≤
      46*L*d*σ+44*L^2*d*C+2*d*σ^2/A := by
  have ht := mul_le_mul_of_nonneg_left (min_le_right A (σ/L+C))
    (show 0 ≤ 44*L^2*d by positivity)
  have hn := mul_le_mul_of_nonneg_left (min_bandwidth_noise hA hC hL hσ).2
    (show 0 ≤ 2*d by positivity)
  have he : 44*L^2*d*(σ/L+C)+2*d*(σ^2/A+L*σ) =
      46*L*d*σ+44*L^2*d*C+2*d*σ^2/A := by field_simp; ring
  calc
    _ ≤ 44*L^2*d*(σ/L+C)+2*d*(σ^2/A+L*σ) := by
      convert add_le_add ht hn using 1; ring
    _ = _ := he

lemma smoothed_acceleration_tuning {L R ε v : ℝ} {K : ℕ}
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hv : 0 ≤ v)
    (hK : 0 < K) (hdet : 16 * L * R ^ 2 / ε ≤ (K : ℝ) ^ 2)
    (hnoise : 512 * v * R ^ 2 / ε ^ 2 ≤ K) :
    let D := 2 * L + 32 * (K : ℝ) * v / ε
    2 * D * R ^ 2 / ((K : ℝ) * (K + 1)) +
      4 * R * (ε / (32 * R)) + 4 * K * v / D + ε/4 ≤ ε := by
  let D := 2 * L + 32 * (K : ℝ) * v / ε
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hD : 0 < D := by dsimp [D]; positivity
  have hd := (div_le_iff₀ hε).mp hdet
  have hv' := (div_le_iff₀ (sq_pos_of_pos hε)).mp hnoise
  have hi : 2 * D * R ^ 2 / ((K : ℝ) * (K + 1)) ≤ 3 * ε / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < (K : ℝ) * (K + 1))).mpr
    have hh : 2 * D * R ^ 2 = 4 * L * R ^ 2 + 64 * K * v * R ^ 2 / ε := by
      dsimp [D]
      ring
    rw [hh]
    have hnv : 64 * K * v * R ^ 2 / ε ≤ ε * (K : ℝ) ^ 2 / 8 := by
      apply (div_le_iff₀ hε).mpr
      have := mul_le_mul_of_nonneg_left hv' hKr.le
      nlinarith
    nlinarith
  have hb : 4 * R * (ε / (32 * R)) = ε / 8 := by field_simp; ring
  have hn : 4 * K * v / D ≤ ε / 8 := by
    apply (div_le_iff₀ hD).mpr
    have he : ε / 8 * D = ε * L / 4 + 4 * K * v := by
      dsimp [D]
      field_simp
      ring
    rw [he]
    nlinarith [mul_pos hε hL]
  change 2 * D * R ^ 2 / ((K : ℝ) * (K + 1)) + _ + _ + ε/4 ≤ ε
  linarith

lemma grid_variance_budget {L R σ ε d v : ℝ} {K : ℕ}
    (hL : 0 < L) (hσ : 0 ≤ σ) (hε : 0 < ε) (hd : 0 ≤ d)
    (hv : v ≤ 46*L*d*σ+44*L*ε/(256*(Real.sqrt (L*R^2/ε)+1))+8*L*d^2*σ^2/ε)
    (hK : 128*Real.sqrt (L*R^2/ε)+32768*L*d*R^2*σ/ε^2+8192*L*d^2*R^2*σ^2/ε^3+1 ≤ K) :
    16*L*R^2/ε ≤ (K:ℝ)^2 ∧ 512*v*R^2/ε^2 ≤ K := by
  let a := Real.sqrt (L*R^2/ε)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a^2 = L*R^2/ε := Real.sq_sqrt (by positivity)
  have h1 : 0 ≤ 32768*L*d*R^2*σ/ε^2 := by positivity
  have h2 : 0 ≤ 8192*L*d^2*R^2*σ^2/ε^3 := by positivity
  have hak : 4*a ≤ (K:ℝ) := by change 128*a+_+_+1 ≤ _ at hK; linarith
  have hdet : 16*L*R^2/ε ≤ (K:ℝ)^2 := by
    have hh := mul_self_le_mul_self (show 0 ≤ 4*a by positivity) hak
    calc
      _ = 16*a^2 := by rw [ha2]; ring
      _ ≤ _ := by nlinarith only [hh]
  have hfloor : 512*(44*L*ε/(256*(a+1)))*R^2/ε^2 ≤ 88*a := by
    have he : 512*(44*L*ε/(256*(a+1)))*R^2/ε^2 = 88*(L*R^2/ε)/(a+1) := by field_simp; ring
    rw [he,← ha2]
    apply (div_le_iff₀ (by positivity : 0 < a+1)).mpr
    nlinarith
  have hv' := mul_le_mul_of_nonneg_right hv (show 0 ≤ 512*R^2/ε^2 by positivity)
  have he : (46*L*d*σ+44*L*ε/(256*(a+1))+8*L*d^2*σ^2/ε)*(512*R^2/ε^2) =
      23552*L*d*R^2*σ/ε^2+512*(44*L*ε/(256*(a+1)))*R^2/ε^2+4096*L*d^2*R^2*σ^2/ε^3 := by ring
  change v*(512*R^2/ε^2) ≤ _ at hv'
  rw [he] at hv'
  refine ⟨hdet, ?_⟩
  have hsmall1 : 23552*L*d*R^2*σ/ε^2 ≤ 32768*L*d*R^2*σ/ε^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hL.le hd) (sq_nonneg R)) hσ]
  have hsmall2 : 4096*L*d^2*R^2*σ^2/ε^3 ≤ 8192*L*d^2*R^2*σ^2/ε^3 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hL.le (sq_nonneg d)) (sq_nonneg R)) (sq_nonneg σ)]
  change 128*a+_+_+1 ≤ _ at hK
  have heleft : v*(512*R^2/ε^2) = 512*v*R^2/ε^2 := by ring
  rw [heleft] at hv'
  linarith

lemma grid_bandwidth_bounds {L R σ ε d : ℝ}
    (hL : 0 < L) (hσ : 0 ≤ σ) (hε : 0 < ε) (hd : 0 < d) :
    let h := Real.sqrt (min (ε/(4*L*d)) (σ/L+ε/(256*L*d*(Real.sqrt (L*R^2/ε)+1))))
    0 < h ∧ L*d*h^2/2 ≤ ε/4 ∧
      2*d*σ^2/h^2+44*d*L^2*h^2 ≤
        46*L*d*σ+44*L*ε/(256*(Real.sqrt (L*R^2/ε)+1))+8*L*d^2*σ^2/ε := by
  let a := Real.sqrt (L*R^2/ε)
  let A := ε/(4*L*d)
  let C := ε/(256*L*d*(a+1))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have ht := (min_bandwidth_noise hA hC hL hσ).1
  have hs : (Real.sqrt (min A (σ/L+C)))^2 = min A (σ/L+C) := Real.sq_sqrt ht.le
  change 0 < Real.sqrt (min A (σ/L+C)) ∧ _
  refine ⟨Real.sqrt_pos.mpr ht, ?_, ?_⟩
  · change L*d*(Real.sqrt (min A (σ/L+C)))^2/2 ≤ ε/4
    rw [hs]
    have hb := mul_le_mul_of_nonneg_left (min_le_left A (σ/L+C)) (show 0 ≤ L*d by positivity)
    have he : L*d*A = ε/4 := by dsimp [A]; field_simp
    rw [he] at hb
    linarith
  · change 2*d*σ^2/(Real.sqrt (min A (σ/L+C)))^2+44*d*L^2*(Real.sqrt (min A (σ/L+C)))^2 ≤ _
    rw [hs]
    have hb := min_bandwidth_variance hA hC hL hσ hd.le
    have he : 46*L*d*σ+44*L^2*d*C+2*d*σ^2/A =
        46*L*d*σ+44*L*ε/(256*(a+1))+8*L*d^2*σ^2/ε := by
      dsimp [A,C]
      field_simp
      ring
    rw [he] at hb
    convert hb using 1; ring

lemma grid_accuracy_tuning {L R σ ε : ℝ} {d : ℕ}
    (hd : 0 < d) (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    let h := Real.sqrt (min (ε/(4*L*d)) (σ/L+ε/(256*L*d*(Real.sqrt (L*R^2/ε)+1))))
    let m := max 1 ⌈64*R*L*h*Real.sqrt d/ε⌉₊
    let v := 2*(d:ℝ)*σ^2/h^2+44*(d:ℝ)*L^2*h^2
    let K := max 1 ⌈128*Real.sqrt (L*R^2/ε)+32768*L*d*R^2*σ/ε^2+8192*L*d^2*R^2*σ^2/ε^3+1⌉₊
    let D := 2*L+32*(K:ℝ)*v/ε
    0 < h ∧ 0 < m ∧ 0 < K ∧ 2*L ≤ D ∧
      2*D*R^2/((K:ℝ)*(K+1))+8*R*L*h*Real.sqrt d/m+4*K*v/D+L*d*h^2/2 ≤ ε := by
  let h := Real.sqrt (min (ε/(4*L*d)) (σ/L+ε/(256*L*d*(Real.sqrt (L*R^2/ε)+1))))
  let m := max 1 ⌈64*R*L*h*Real.sqrt d/ε⌉₊
  let v := 2*(d:ℝ)*σ^2/h^2+44*(d:ℝ)*L^2*h^2
  let K := max 1 ⌈128*Real.sqrt (L*R^2/ε)+32768*L*d*R^2*σ/ε^2+8192*L*d^2*R^2*σ^2/ε^3+1⌉₊
  let D := 2*L+32*(K:ℝ)*v/ε
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hb := grid_bandwidth_bounds (R := R) hL hσ hε hdr
  change 0 < h ∧ L*d*h^2/2 ≤ ε/4 ∧ v ≤ _ at hb
  have hm : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hmreal : (0:ℝ) < m := by exact_mod_cast hm
  have hmceil : 64*R*L*h*Real.sqrt d/ε ≤ (m:ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hKceil : 128*Real.sqrt (L*R^2/ε)+32768*L*d*R^2*σ/ε^2+8192*L*d^2*R^2*σ^2/ε^3+1 ≤ (K:ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hbudget := grid_variance_budget hL hσ hε hdr.le hb.2.2 hKceil
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hbias : 2*L*h*Real.sqrt d/m ≤ ε/(32*R) := by
    apply (div_le_div_iff₀ hmreal (by positivity : 0 < 32*R)).mpr
    have hh := (div_le_iff₀ hε).mp hmceil
    nlinarith only [hh]
  have ht := smoothed_acceleration_tuning hL hR hε hv hK hbudget.1 hbudget.2
  change 0 < h ∧ 0 < m ∧ 0 < K ∧ 2*L ≤ D ∧ _
  refine ⟨hb.1,hm,hK,?_,?_⟩
  · dsimp [D]
    exact le_add_of_nonneg_right (by positivity)
  · have hmul := mul_le_mul_of_nonneg_left hbias (show 0 ≤ 4*R by positivity)
    change 2*D*R^2/((K:ℝ)*(K+1))+4*R*(ε/(32*R))+4*K*v/D+ε/4 ≤ ε at ht
    have he : 4*R*(2*L*h*Real.sqrt d/m) = 8*R*L*h*Real.sqrt d/m := by ring
    rw [he] at hmul
    linarith [hb.2.1]

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma smoothing_accuracy_transfer {E Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f F : E → ℝ} {out : Ω → E} {u : E}
    {δ B : ℝ} (hi : Integrable (fun ω => f (out ω)-f u) P)
    (hI : Integrable (fun ω => F (out ω)-F u) P)
    (hlower : ∀ ω, f (out ω) ≤ F (out ω)) (hupper : F u ≤ f u+δ)
    (hbound : (∫ ω, F (out ω)-F u ∂P) ≤ B) :
    (∫ ω, f (out ω)-f u ∂P) ≤ B+δ := by
  have h := integral_mono hi (hI.add (integrable_const δ))
    (fun ω => show f (out ω)-f u ≤ F (out ω)-F u+δ by
      linarith [hlower ω])
  simp only [Pi.add_apply] at h
  rw [integral_add hI (integrable_const δ)] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith

end OracleTemplate.ZerothOrder

end

section

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma biased_acceleration_tuning {L R ε v : ℝ} {K : ℕ}
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hv : 0 ≤ v)
    (hK : 0 < K) (hdet : 16 * L * R ^ 2 / ε ≤ (K : ℝ) ^ 2)
    (hnoise : 512 * v * R ^ 2 / ε ^ 2 ≤ K) :
    let D := 2 * L + 32 * (K : ℝ) * v / ε
    2 * D * R ^ 2 / ((K : ℝ) * (K + 1)) +
      4 * R * (ε / (32 * R)) + 4 * K * v / D ≤ ε := by
  let D := 2 * L + 32 * (K : ℝ) * v / ε
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hD : 0 < D := by dsimp [D]; positivity
  have hd := (div_le_iff₀ hε).mp hdet
  have hv' := (div_le_iff₀ (sq_pos_of_pos hε)).mp hnoise
  have hi : 2 * D * R ^ 2 / ((K : ℝ) * (K + 1)) ≤ 3 * ε / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < (K : ℝ) * (K + 1))).mpr
    have hh : 2 * D * R ^ 2 = 4 * L * R ^ 2 + 64 * K * v * R ^ 2 / ε := by
      dsimp [D]
      ring
    rw [hh]
    have hnv : 64 * K * v * R ^ 2 / ε ≤ ε * (K : ℝ) ^ 2 / 8 := by
      apply (div_le_iff₀ hε).mpr
      have := mul_le_mul_of_nonneg_left hv' hKr.le
      nlinarith
    nlinarith
  have hb : 4 * R * (ε / (32 * R)) = ε / 8 := by field_simp; ring
  have hn : 4 * K * v / D ≤ ε / 8 := by
    apply (div_le_iff₀ hD).mpr
    have he : ε / 8 * D = ε * L / 4 + 4 * K * v := by
      dsimp [D]
      field_simp
      ring
    rw [he]
    nlinarith [mul_pos hε hL]
  change 2 * D * R ^ 2 / ((K : ℝ) * (K + 1)) + _ + _ ≤ ε
  linarith

lemma zeroth_order_tuning {L R σ ε : ℝ} {d : ℕ}
    (hd : 0 < d) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) :
    let h := ε / (16 * L * R * Real.sqrt d)
    let v := 2048 * L ^ 2 * R ^ 2 * (d : ℝ) ^ 2 * σ ^ 2 / ε ^ 2 + ε ^ 2 / (512 * R ^ 2)
    let K := max 1 ⌈Real.sqrt (16 * L * R ^ 2 / ε) + 1048576 * L ^ 2 * R ^ 4 * (d : ℝ) ^ 2 * σ ^ 2 / ε ^ 4 + 1⌉₊
    let D := 2 * L + 32 * (K : ℝ) * v / ε
    0 < h ∧ 2 * L ≤ D ∧
      L * h * Real.sqrt d / 2 = ε / (32 * R) ∧
      8 * (d : ℝ) * σ ^ 2 / h ^ 2 + d * L ^ 2 * h ^ 2 / 2 = v ∧
      2 * D * R ^ 2 / ((K : ℝ) * (K + 1)) +
        4 * R * (ε / (32 * R)) + 4 * K * v / D ≤ ε := by
  let h := ε / (16 * L * R * Real.sqrt d)
  let v := 2048 * L ^ 2 * R ^ 2 * (d : ℝ) ^ 2 * σ ^ 2 / ε ^ 2 + ε ^ 2 / (512 * R ^ 2)
  let K := max 1 ⌈Real.sqrt (16 * L * R ^ 2 / ε) + 1048576 * L ^ 2 * R ^ 4 * (d : ℝ) ^ 2 * σ ^ 2 / ε ^ 4 + 1⌉₊
  let D := 2 * L + 32 * (K : ℝ) * v / ε
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq : (Real.sqrt (d : ℝ)) ^ 2 = d := Real.sq_sqrt hdr.le
  have hsq4 : (Real.sqrt (d : ℝ)) ^ 4 = (d : ℝ) ^ 2 := by
    calc
      _ = ((Real.sqrt (d : ℝ)) ^ 2) ^ 2 := by ring
      _ = (d : ℝ) ^ 2 := by rw [hsq]
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdr
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hceil : Real.sqrt (16 * L * R ^ 2 / ε) +
      1048576 * L ^ 2 * R ^ 4 * (d : ℝ) ^ 2 * σ ^ 2 / ε ^ 4 + 1 ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hp : 0 ≤ 1048576 * L ^ 2 * R ^ 4 * (d : ℝ) ^ 2 * σ ^ 2 / ε ^ 4 := by positivity
  have hdet : 16 * L * R ^ 2 / ε ≤ (K : ℝ) ^ 2 := by
    have hh : 0 ≤ 16 * L * R ^ 2 / ε := by positivity
    nlinarith [Real.sq_sqrt hh, Real.sqrt_nonneg (16 * L * R ^ 2 / ε)]
  have hn : 512 * v * R ^ 2 / ε ^ 2 =
      1048576 * L ^ 2 * R ^ 4 * (d : ℝ) ^ 2 * σ ^ 2 / ε ^ 4 + 1 := by
    dsimp [v]
    field_simp
    ring
  change 0 < h ∧ 2 * L ≤ D ∧ _ ∧ _ ∧ _
  refine ⟨by dsimp [h]; positivity,
    by dsimp [D]; exact le_add_of_nonneg_right (by positivity), ?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    rw [hsq4, hsq]
    ring
  · apply biased_acceleration_tuning hL hR hε hv hK hdet
    rw [hn]
    linarith [Real.sqrt_nonneg (16 * L * R ^ 2 / ε)]

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open BiasedStochasticGradient HeavyTailedMarkovGradient
open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

lemma grid_projected_rate {d m : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {p : Measure Ω}
    {Q : Measure (Fin d × Bool → Ω)} [IsProbabilityMeasure Q] {σ L D R h : ℝ}
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω-f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω-f x)^2 ∂p) ≤ σ^2)
    (hm : 0 < m) (hL : 0 < L) (hD : 0 < D) (hLD : 2*L ≤ D) (hR : 0 ≤ R) (hh : 0 < h)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x0 u : Point d) (hmin : IsMinOn f univ u) (hu : ‖u-x0‖ ≤ R) (K : ℕ) (hK : 0 < K) :
    letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
    let q := (PMF.uniformOfFintype (Fin d → Fin m)).toMeasure.prod Q
    let out := fun ξ => (projectedRun (gridOracle (m := m) g h) D R x0 K 0 x0 x0 ξ).1
    Integrable (fun ξ => f (out ξ)-f u) (Measure.pi fun _ : Fin K => q) ∧
      (∫ ξ, f (out ξ)-f u ∂Measure.pi (fun _ : Fin K => q)) ≤
        2*D*R^2/((K:ℝ)*(K+1))+8*R*L*h*Real.sqrt d/m+
        4*K*(2*(d:ℝ)*σ^2/h^2+44*(d:ℝ)*L^2*h^2)/D+L*(d:ℝ)*h^2/2 := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  let q := (PMF.uniformOfFintype (Fin d → Fin m)).toMeasure.prod Q
  let out := fun ξ => (projectedRun (gridOracle (m := m) g h) D R x0 K 0 x0 x0 ξ).1
  have hgs (x : Point d) : HasGradientAt (gridSmooth f h m) (gradient (gridSmooth f h m) x) x := by
    rw [grid_smoothing_gradient hg h x]
    exact grid_smoothing_hasGradient hg h x
  have hls (x y : Point d) : ‖gradient (gridSmooth f h m) x-gradient (gridSmooth f h m) y‖ ≤ L*‖x-y‖ := by
    rw [grid_smoothing_gradient hg h x,grid_smoothing_gradient hg h y]
    exact grid_smoothing_lipschitz hm hlip h x y
  have hmoment (x : Point d) : Integrable (fun s => ‖gradient (gridSmooth f h m) x-gridOracle g h x s‖^2) q ∧
      (∫ s, ‖gradient (gridSmooth f h m) x-gridOracle g h x s‖^2 ∂q) ≤ 2*(d:ℝ)*σ^2/h^2+44*(d:ℝ)*L^2*h^2 := by
    have he := gridOracle_error_moment hmap hgm hgi hvi hv hm hL.le hh hc hg hlip x
    rw [grid_smoothing_gradient hg h x]
    simpa only [norm_sub_rev] using he
  have hr := comparator_expected_rate hL hD hLD hR
    (show 0 ≤ 2*L*h*Real.sqrt d/m by positivity)
    (show 0 ≤ 2*(d:ℝ)*σ^2/h^2+44*(d:ℝ)*L^2*h^2 by positivity)
    (grid_smoothing_convex hc h) hgs hls
    (measurable_gridOracle (m := m) hgm h)
    (fun x => (gridOracle_integral (m := m) hmap hgm hgi hmean h x).1)
    (gridOracle_bias hmap hgm hgi hmean hm hL.le hh hc hg hlip)
    (fun x => (hmoment x).1) (fun x => (hmoment x).2)
    x0 u (fun x hx => grid_smoothing_comparator_gap hm hL hR hh.le hc hg hlip hmin hu hx)
    hu K hK
  have ho : Measurable out :=
    ((measurable_projectedRun (measurable_gridOracle (m := m) hgm h) D R x0 K 0).comp
      (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin K → ((Fin d → Fin m) × (Fin d × Bool → Ω)) => ((x0,x0),ξ)))).fst
  have hf : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)).measurable
  have hball (ξ) : ‖out ξ-x0‖ ≤ R :=
    (projectedRun_ball (gridOracle (m := m) g h) D hR x0 K 0 x0 x0 (by simpa) (by simpa) ξ).1
  have hi : Integrable (fun ξ => f (out ξ)-f u) (Measure.pi fun _ : Fin K => q) := by
    apply Integrable.of_bound ((hf.comp ho).sub_const _).aestronglyMeasurable (2*L*R^2)
    apply Filter.Eventually.of_forall
    intro ξ
    have hh' := smooth_gap_ball hL hR hg hlip hmin hu (hball ξ)
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hh'.1] using hh'.2
  have he := smoothing_accuracy_transfer hi hr.1
    (fun ξ => by have hs := (grid_smoothing_gap hm hL.le hh.le hc hg hlip (out ξ)).1; linarith)
    (show gridSmooth f h m u ≤ f u+L*(d:ℝ)*h^2/2 by
      have hs := (grid_smoothing_gap hm hL.le hh.le hc hg hlip u).2; linarith) hr.2
  refine ⟨hi, ?_⟩
  convert he using 1; ring

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open BiasedStochasticGradient

lemma finite_difference_accuracy {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {f : Point d → ℝ} {g : Point d → Ω → ℝ} {p : Measure Ω} [IsProbabilityMeasure p]
    {L R σ ε : ℝ} (hd : 0 < d) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x)^2 ∂p) ≤ σ^2)
    (x0 u : Point d) (hm : IsMinOn f univ u) (hu : ‖x0-u‖ ≤ R) :
    let h := ε / (16 * L * R * Real.sqrt d)
    let v := 2048 * L ^ 2 * R ^ 2 * (d : ℝ) ^ 2 * σ ^ 2 / ε ^ 2 + ε ^ 2 / (512 * R ^ 2)
    let K := max 1 ⌈Real.sqrt (16 * L * R ^ 2 / ε) + 1048576 * L ^ 2 * R ^ 4 * (d : ℝ) ^ 2 * σ ^ 2 / ε ^ 4 + 1⌉₊
    let D := 2 * L + 32 * (K : ℝ) * v / ε
    Integrable (fun ξ => f (projectedRun (estimate g h) D R x0 K 0 x0 x0 ξ).1 - f u)
      (Measure.pi fun _ : Fin K => Measure.pi fun _ : Fin d × Bool => p) ∧
    (∫ ξ, f (projectedRun (estimate g h) D R x0 K 0 x0 x0 ξ).1 - f u
      ∂Measure.pi (fun _ : Fin K => Measure.pi fun _ : Fin d × Bool => p)) ≤ ε := by
  dsimp only
  let h := ε / (16 * L * R * Real.sqrt d)
  let v := 2048 * L ^ 2 * R ^ 2 * (d : ℝ) ^ 2 * σ ^ 2 / ε ^ 2 + ε ^ 2 / (512 * R ^ 2)
  let K := max 1 ⌈Real.sqrt (16 * L * R ^ 2 / ε) + 1048576 * L ^ 2 * R ^ 4 * (d : ℝ) ^ 2 * σ ^ 2 / ε ^ 4 + 1⌉₊
  let D := 2 * L + 32 * (K : ℝ) * v / ε
  let Q := Measure.pi (fun _ : Fin d × Bool => p)
  have ht := zeroth_order_tuning (σ := σ) hd hL hR hε
  change 0 < h ∧ 2*L ≤ D ∧ _ ∧ _ = v ∧ _ at ht
  have hmap (j : Fin d × Bool) : MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p :=
    measurePreserving_eval (fun _ : Fin d × Bool => p) j
  have hmom := estimate_error_moment hmap hgm hgi hvi hv ht.1 hc hg hlip
  have hr := projected_expected_rate hL (lt_of_lt_of_le (by linarith) ht.2.1) ht.2.1 hR.le
    (show 0 ≤ ε/(32*R) by positivity) (show 0 ≤ v by dsimp [v]; positivity)
    hc hg hlip (measurable_estimate hgm h)
    (fun x => (estimate_integral hmap hgi hmean h x).1)
    (fun x => by rw [(estimate_integral hmap hgi hmean h x).2, norm_sub_rev, ← ht.2.2.1]; exact difference_bias hL.le ht.1 hc hg hlip x)
    (fun x => by simpa only [norm_sub_rev] using (hmom x).1)
    (fun x => by simpa only [norm_sub_rev] using ((hmom x).2.trans_eq ht.2.2.2.1))
    x0 u hm (by simpa only [norm_sub_rev] using hu) K
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  exact ⟨hr.1, hr.2.trans ht.2.2.2.2⟩

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open BiasedStochasticGradient

lemma grid_accuracy {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {f : Point d → ℝ} {g : Point d → Ω → ℝ} {p : Measure Ω} [IsProbabilityMeasure p]
    {L R σ ε : ℝ} (hd : 0 < d) (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ) (hε : 0 < ε)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω-f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω-f x)^2 ∂p) ≤ σ^2)
    (x0 u : Point d) (hmin : IsMinOn f univ u) (hu : ‖u-x0‖ ≤ R) :
    let h := Real.sqrt (min (ε/(4*L*d)) (σ/L+ε/(256*L*d*(Real.sqrt (L*R^2/ε)+1))))
    let m := max 1 ⌈64*R*L*h*Real.sqrt d/ε⌉₊
    letI : Nonempty (Fin m) := ⟨⟨0,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩⟩
    let v := 2*(d:ℝ)*σ^2/h^2+44*(d:ℝ)*L^2*h^2
    let K := max 1 ⌈128*Real.sqrt (L*R^2/ε)+32768*L*d*R^2*σ/ε^2+8192*L*d^2*R^2*σ^2/ε^3+1⌉₊
    let D := 2*L+32*(K:ℝ)*v/ε
    let q := (PMF.uniformOfFintype (Fin d → Fin m)).toMeasure.prod (Measure.pi fun _ : Fin d × Bool => p)
    Integrable (fun ξ => f (projectedRun (gridOracle (m := m) g h) D R x0 K 0 x0 x0 ξ).1-f u)
      (Measure.pi fun _ : Fin K => q) ∧
      (∫ ξ, f (projectedRun (gridOracle (m := m) g h) D R x0 K 0 x0 x0 ξ).1-f u
        ∂Measure.pi (fun _ : Fin K => q)) ≤ ε := by
  let h := Real.sqrt (min (ε/(4*L*d)) (σ/L+ε/(256*L*d*(Real.sqrt (L*R^2/ε)+1))))
  let m := max 1 ⌈64*R*L*h*Real.sqrt d/ε⌉₊
  let : Nonempty (Fin m) := ⟨⟨0,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩⟩
  let v := 2*(d:ℝ)*σ^2/h^2+44*(d:ℝ)*L^2*h^2
  let K := max 1 ⌈128*Real.sqrt (L*R^2/ε)+32768*L*d*R^2*σ/ε^2+8192*L*d^2*R^2*σ^2/ε^3+1⌉₊
  let D := 2*L+32*(K:ℝ)*v/ε
  have ht := grid_accuracy_tuning hd hL hR hσ hε
  change 0 < h ∧ 0 < m ∧ 0 < K ∧ 2*L ≤ D ∧ _ at ht
  have hmap (j : Fin d × Bool) : MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j)
      (Measure.pi fun _ : Fin d × Bool => p) p := measurePreserving_eval _ j
  have hr := grid_projected_rate hmap hgm hgi hmean hvi hv ht.2.1 hL
    (lt_of_lt_of_le (by linarith : 0 < 2*L) ht.2.2.2.1) ht.2.2.2.1 hR.le ht.1 hc hg hlip
    x0 u hmin hu K ht.2.2.1
  exact ⟨hr.1,hr.2.trans ht.2.2.2.2⟩

end OracleTemplate.ZerothOrder

end


section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticGradient

open LongTails.Setups.StochasticSmoothAndConvex

noncomputable def coupledWeight (M : ℝ) (k : ℕ) : ℝ := (k:ℝ)*((k:ℝ)+1)/(2*M)

noncomputable def coupledNoiseCost (M v : ℝ) (k : ℕ) : ℝ := (k:ℝ)*((k:ℝ)+1)*v/M^2

lemma coupledWeight_succ (M : ℝ) (k : ℕ) :
    coupledWeight M (k+1)=coupledWeight M k+((k:ℝ)+1)/M := by
  unfold coupledWeight
  push_cast
  ring

lemma coupledNoiseCost_mono {M v : ℝ} (hv : 0 ≤ v) {k l : ℕ} (hkl : k ≤ l) :
    coupledNoiseCost M v k ≤ coupledNoiseCost M v l := by
  have h : (k:ℝ) ≤ l := by exact_mod_cast hkl
  have hh : (k:ℝ)*((k:ℝ)+1) ≤ (l:ℝ)*((l:ℝ)+1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k,Nat.cast_nonneg (α := ℝ) l]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh hv) (sq_nonneg M)

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def coupledEnergy (f : E → ℝ) (M c : ℝ) (u : E) (k : ℕ) (s : E × E) : ℝ :=
  coupledWeight M k*(f s.1-c)+‖s.2-u‖^2/2

lemma coupled_query_identity {M : ℝ} (hM : 0 < M) (k : ℕ) (x z : E) :
    (coupledWeight M k+((k:ℝ)+1)/M) • Gradient.acceleratedQuery (k,x,z) =
      coupledWeight M k • x+(((k:ℝ)+1)/M) • z := by
  have hden : (k:ℝ)*((k:ℝ)+1)/4+((k:ℝ)+1)/2 ≠ 0 := ne_of_gt (by positivity)
  unfold coupledWeight Gradient.acceleratedQuery
  match_scalars
  all_goals field_simp [hden,hM.ne']; ring

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma measurable_coupledUpdate (M θ : ℝ) (k : ℕ) :
    Measurable (fun v : (E × E) × E => coupledUpdate M θ k v.1 v.2) := by
  unfold coupledUpdate Gradient.acceleratedQuery
  fun_prop

lemma measurable_coupledRun {g : E → Ω → E} (hG : Measurable (Function.uncurry g))
    (M θ : ℝ) (K k : ℕ) :
    Measurable (fun v : (E × E) × (Fin K → Ω) => coupledRun g M θ K k v.1.1 v.1.2 v.2) := by
  induction K generalizing k with
  | zero => exact measurable_fst
  | succ K ih =>
    have hy : Measurable (fun v : (E × E) × (Fin (K+1) → Ω) => Gradient.acceleratedQuery (k,v.1.1,v.1.2)) := by
      dsimp only [Gradient.acceleratedQuery]
      exact (measurable_fst.fst.const_smul (_ : ℝ)).add (measurable_fst.snd.const_smul (_ : ℝ))
    have hr := hG.comp (hy.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    have hn := (measurable_coupledUpdate M θ k).comp (measurable_fst.prodMk hr)
    exact (ih (k+1)).comp (hn.prodMk (Measurable.of_eval (fun i =>
      (measurable_pi_apply i.succ).comp measurable_snd)))

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma measurable_coupledEnergy {f : E → ℝ} (hf : Measurable f) (M c : ℝ) (u : E) (k : ℕ) :
    Measurable (coupledEnergy f M c u k) := by
  unfold coupledEnergy
  fun_prop

variable [CompleteSpace E]

omit [SecondCountableTopology E] in
lemma coupled_energy_step {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L M θ v c δ : ℝ}
    (hL : 0 ≤ L) (hM : 0 < M) (hθ : 0 ≤ θ) (hv : 0 ≤ v) (hLM : 2*L*θ^2 ≤ M)
    (hc : ConvexOn ℝ univ f) (hd : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hlo : ∀ x, c ≤ f x)
    (hG : Measurable (Function.uncurry g)) (hGi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p)=gradient f x)
    (hG2 : ∀ x, Integrable (fun ω => ‖g x ω‖^2) p)
    (hmoment : ∀ x, (∫ ω, ‖g x ω‖^2 ∂p) ≤ θ*‖gradient f x‖^2+v)
    (x z u : E) (hu : f u-c ≤ δ) (k : ℕ) :
    let y := Gradient.acceleratedQuery (k,x,z)
    let step := fun ω => coupledUpdate M θ k (x,z) (g y ω)
    Integrable (fun ω => coupledEnergy f M c u (k+1) (step ω)) p ∧
      (∫ ω, coupledEnergy f M c u (k+1) (step ω) ∂p) ≤
        coupledEnergy f M c u k (x,z)+((k:ℝ)+1)/M*δ+coupledNoiseCost M v (k+1) := by
  intro y step
  have hGm : Measurable (g y) := hG.comp (measurable_const.prodMk measurable_id)
  have hparam := coupled_parameters hM hθ (Nat.cast_nonneg k) hLM
  have hs := coupled_lower_energy_step hL (show 0 ≤ coupledWeight M k by unfold coupledWeight; positivity)
    (show 0 ≤ ((k:ℝ)+1)/M by positivity) hc hd hlip hlo x z y u (coupled_query_identity hM k x z)
    (g y) hGm (hGi y) (hmean y) (hG2 y) (hmoment y) hparam.1
  have he : (fun ω => coupledEnergy f M c u (k+1) (step ω)) =
      fun ω => (coupledWeight M k+((k:ℝ)+1)/M)*(f (y-(2*θ/M) • g y ω)-c)+
        ‖z-(((k:ℝ)+1)/M) • g y ω-u‖^2/2 := by
    funext ω
    simp only [coupledEnergy,coupledWeight_succ,step,coupledUpdate,y]
  rw [he]
  refine ⟨hs.1,?_⟩
  have hu' := mul_le_mul_of_nonneg_left hu (show 0 ≤ ((k:ℝ)+1)/M by positivity)
  have hv' := mul_le_mul_of_nonneg_right hparam.2 hv
  have hcost : ((k:ℝ)+1)*((k:ℝ)+2)/M^2*v=coupledNoiseCost M v (k+1) := by
    unfold coupledNoiseCost
    push_cast
    ring
  rw [hcost] at hv'
  exact hs.2.trans (add_le_add (add_le_add (le_refl _) hu') hv')

omit [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] in
omit [MeasurableSpace E] in
lemma coupledEnergy_nonneg {f : E → ℝ} {M c : ℝ} (hM : 0 ≤ M)
    (hlo : ∀ x, c ≤ f x) (u : E) (k : ℕ) (s : E × E) :
    0 ≤ coupledEnergy f M c u k s := by
  unfold coupledEnergy coupledWeight
  exact add_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (hlo _))) (by positivity)

lemma coupled_energy_bound {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L M θ v c δ : ℝ}
    (hL : 0 ≤ L) (hM : 0 < M) (hθ : 0 ≤ θ) (hv : 0 ≤ v) (hLM : 2*L*θ^2 ≤ M)
    (hc : ConvexOn ℝ univ f) (hd : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hlo : ∀ x, c ≤ f x)
    (hG : Measurable (Function.uncurry g)) (hGi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p)=gradient f x)
    (hG2 : ∀ x, Integrable (fun ω => ‖g x ω‖^2) p)
    (hmoment : ∀ x, (∫ ω, ‖g x ω‖^2 ∂p) ≤ θ*‖gradient f x‖^2+v)
    (u : E) (hu : f u-c ≤ δ) (K k : ℕ) (x z : E) :
    Integrable (fun ξ => coupledEnergy f M c u (k+K) (coupledRun g M θ K k x z ξ))
      (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, coupledEnergy f M c u (k+K) (coupledRun g M θ K k x z ξ)
      ∂Measure.pi (fun _ : Fin K => p)) ≤
      coupledEnergy f M c u k (x,z)+(coupledWeight M (k+K)-coupledWeight M k)*δ+
        K*coupledNoiseCost M v (k+K) := by
  have hf : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).measurable
  induction K generalizing k x z with
  | zero => simp [coupledRun]
  | succ K ih =>
    let q := Measure.pi (fun _ : Fin K => p)
    let y := Gradient.acceleratedQuery (k,x,z)
    let step := fun ω => coupledUpdate M θ k (x,z) (g y ω)
    let C := (coupledWeight M (k+(K+1))-coupledWeight M (k+1))*δ+
      (K:ℝ)*coupledNoiseCost M v (k+(K+1))
    let B := fun ω => coupledEnergy f M c u (k+1) (step ω)+C
    let F := fun w : Ω × (Fin K → Ω) => coupledEnergy f M c u (k+(K+1))
      (coupledRun g M θ (K+1) k x z (Fin.cons w.1 w.2))
    have hmp : Measurable (fun ξ : Fin (K+1) → Ω => coupledEnergy f M c u (k+(K+1))
        (coupledRun g M θ (K+1) k x z ξ)) :=
      (measurable_coupledEnergy hf M c u _).comp
        ((measurable_coupledRun hG M θ (K+1) k).comp
          (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin (K+1) → Ω => ((x,z),ξ))))
    have hcons := cons_measurePreserving p K
    have hFm : Measurable F := hmp.comp hcons.measurable
    have hFeq (ω : Ω) : (fun ξ => F (ω,ξ)) = fun ξ => coupledEnergy f M c u (k+1+K)
        (coupledRun g M θ K (k+1) (step ω).1 (step ω).2 ξ) := by
      funext ξ
      simp only [F,coupledRun,Fin.cons_zero,Fin.cons_succ,step,y]
      congr 1
      omega
    have hstep := coupled_energy_step hL hM hθ hv hLM hc hd hlip hlo hG hGi hmean hG2 hmoment x z u hu k
    have hBint : Integrable B p := hstep.1.add (integrable_const C)
    have hsection : ∀ ω, Integrable (fun ξ => F (ω,ξ)) q := by
      intro ω
      rw [hFeq]
      exact (ih (k+1) (step ω).1 (step ω).2).1
    have hbound : ∀ ω, (∫ ξ, F (ω,ξ) ∂q) ≤ B ω := by
      intro ω
      rw [hFeq]
      simpa only [B,C,show k+1+K=k+(K+1) by omega,add_assoc] using
        (ih (k+1) (step ω).1 (step ω).2).2
    have hnonneg : ∀ w, 0 ≤ F w := fun w => coupledEnergy_nonneg hM.le hlo u _ _
    have hint : Integrable (fun ω => ∫ ξ, ‖F (ω,ξ)‖ ∂q) p := by
      apply hBint.mono_nonneg hFm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun ω => integral_nonneg (fun ξ => norm_nonneg _))
      · exact Filter.Eventually.of_forall (fun ω => by
          simpa only [Real.norm_eq_abs,abs_of_nonneg (hnonneg _)] using hbound ω)
    have hFi : Integrable F (p.prod q) := (integrable_prod_iff hFm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection,hint⟩
    have hi : Integrable (fun ξ => coupledEnergy f M c u (k+(K+1)) (coupledRun g M θ (K+1) k x z ξ))
        (Measure.pi fun _ : Fin (K+1) => p) :=
      (hcons.integrable_comp hmp.aestronglyMeasurable).mp hFi
    refine ⟨hi,?_⟩
    calc
      _ = ∫ w, F w ∂p.prod q := by
        rw [← hcons.map_eq,integral_map hcons.measurable.aemeasurable hmp.aestronglyMeasurable]
      _ = ∫ ω, ∫ ξ, F (ω,ξ) ∂q ∂p := integral_prod F hFi
      _ ≤ ∫ ω, B ω ∂p := integral_mono hFi.integral_prod_left hBint hbound
      _ = (∫ ω, coupledEnergy f M c u (k+1) (step ω) ∂p)+C := by
        rw [integral_add hstep.1 (integrable_const C)]
        simp only [integral_const,probReal_univ,one_smul]
        rfl
      _ ≤ coupledEnergy f M c u k (x,z)+((k:ℝ)+1)/M*δ+coupledNoiseCost M v (k+1)+C :=
        add_le_add hstep.2 (le_refl C)
      _ ≤ _ := by
        have hnoise := coupledNoiseCost_mono (M := M) hv (show k+1 ≤ k+(K+1) by omega)
        dsimp [C]
        rw [coupledWeight_succ M k]
        push_cast
        nlinarith only [hnoise]

end OracleTemplate.StochasticGradient

end


section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticGradient

open LongTails.Setups.StochasticSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Ω : Type} [MeasurableSpace Ω]

lemma coupled_expected_rate {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L M θ v c δ R : ℝ}
    (hL : 0 ≤ L) (hM : 0 < M) (hθ : 0 ≤ θ) (hv : 0 ≤ v) (hLM : 2*L*θ^2 ≤ M)
    (hR : 0 ≤ R) (hc : ConvexOn ℝ univ f) (hd : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hlo : ∀ x, c ≤ f x)
    (hG : Measurable (Function.uncurry g)) (hGi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p)=gradient f x)
    (hG2 : ∀ x, Integrable (fun ω => ‖g x ω‖^2) p)
    (hmoment : ∀ x, (∫ ω, ‖g x ω‖^2 ∂p) ≤ θ*‖gradient f x‖^2+v)
    (x0 u : E) (hu : f u-c ≤ δ) (hxu : ‖x0-u‖ ≤ R) {K : ℕ} (hK : 0 < K) :
    Integrable (fun ξ => f (coupledRun g M θ K 0 x0 x0 ξ).1-c) (Measure.pi fun _ : Fin K => p) ∧
      (∫ ξ, f (coupledRun g M θ K 0 x0 x0 ξ).1-c ∂Measure.pi (fun _ : Fin K => p)) ≤
        M*R^2/((K:ℝ)*((K:ℝ)+1))+δ+2*K*v/M := by
  let q := Measure.pi (fun _ : Fin K => p)
  let A := coupledWeight M K
  let F := fun ξ : Fin K → Ω => f (coupledRun g M θ K 0 x0 x0 ξ).1-c
  let H := fun ξ : Fin K → Ω => coupledEnergy f M c u K (coupledRun g M θ K 0 x0 x0 ξ)
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have hA : 0 < A := by dsimp [A,coupledWeight]; positivity
  have hE := coupled_energy_bound hL hM hθ hv hLM hc hd hlip hlo hG hGi hmean hG2 hmoment u hu K 0 x0 x0
  have hEi : Integrable H q := by simpa only [Nat.zero_add] using hE.1
  have hEb : (∫ ξ, H ξ ∂q) ≤ ‖x0-u‖^2/2+A*δ+K*coupledNoiseCost M v K := by
    simpa only [H,q,A,Nat.zero_add,coupledEnergy,coupledWeight,Nat.cast_zero,zero_mul,zero_div,zero_add,sub_zero] using hE.2
  have hf : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).measurable
  have hr := (measurable_coupledRun hG M θ K 0).comp
    (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin K → Ω => ((x0,x0),ξ)))
  have hFm : Measurable F := (hf.comp hr.fst).sub_const c
  have hFnonneg (ξ : Fin K → Ω) : 0 ≤ F ξ := sub_nonneg.mpr (hlo _)
  have hFH (ξ : Fin K → Ω) : F ξ ≤ H ξ/A := by
    apply (le_div_iff₀ hA).mpr
    dsimp [F,H,coupledEnergy,A]
    nlinarith [sq_nonneg ‖(coupledRun g M θ K 0 x0 x0 ξ).2-u‖]
  have hFi : Integrable F q := (hEi.div_const A).mono_nonneg hFm.aestronglyMeasurable
    (Filter.Eventually.of_forall hFnonneg) (Filter.Eventually.of_forall hFH)
  refine ⟨hFi,?_⟩
  have hi := integral_mono hFi (hEi.div_const A) hFH
  rw [integral_div] at hi
  have hn : ‖x0-u‖^2 ≤ R^2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hxu
  have hb : (∫ ξ, H ξ ∂q) ≤ R^2/2+A*δ+K*coupledNoiseCost M v K := by linarith
  calc
    _ ≤ (∫ ξ, H ξ ∂q)/A := hi
    _ ≤ (R^2/2+A*δ+K*coupledNoiseCost M v K)/A := div_le_div_of_nonneg_right hb hA.le
    _ = _ := by
      dsimp [A,coupledWeight,coupledNoiseCost]
      field_simp [hM.ne',hKr.ne',show (K:ℝ)+1 ≠ 0 from ne_of_gt (by positivity)]


end OracleTemplate.StochasticGradient

end


section

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma twoPoint_variance_bound {L σ ε d R : ℝ}
    (hL : 0 < L) (hσ : 0 ≤ σ) (hε : 0 < ε) (hd : 0 < d) :
    let h := Real.sqrt (min (ε/(4*L)) (σ/L+ε/(128*L*d*(Real.sqrt (L*R^2/ε)+1))))
    0 < h ∧ L*h^2/2 ≤ ε/8 ∧
      10*d^2*L^2*h^2+d^2*σ^2/h^2 ≤
        11*L*d^2*σ+10*L*d*ε/(128*(Real.sqrt (L*R^2/ε)+1))+4*L*d^2*σ^2/ε := by
  let a := Real.sqrt (L*R^2/ε)
  let A := ε/(4*L)
  let C := ε/(128*L*d*(a+1))
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C,a]; positivity
  have ht := min_bandwidth_noise hA hC hL hσ
  have hs : (Real.sqrt (min A (σ/L+C)))^2=min A (σ/L+C) := Real.sq_sqrt ht.1.le
  refine ⟨Real.sqrt_pos.mpr ht.1,?_,?_⟩
  · rw [hs]
    have hb := mul_le_mul_of_nonneg_left (min_le_left A (σ/L+C)) hL.le
    have he : L*A=ε/4 := by dsimp [A]; field_simp
    rw [he] at hb
    linarith
  · rw [hs]
    have hb := mul_le_mul_of_nonneg_left (min_le_right A (σ/L+C)) (show 0 ≤ 10*d^2*L^2 by positivity)
    have hn := mul_le_mul_of_nonneg_left ht.2 (sq_nonneg d)
    have he : 10*d^2*L^2*(σ/L+C)+d^2*(σ^2/A+L*σ) =
        11*L*d^2*σ+10*L*d*ε/(128*(a+1))+4*L*d^2*σ^2/ε := by
      dsimp [A,C]
      field_simp; ring
    change _ ≤ 11*L*d^2*σ+10*L*d*ε/(128*(a+1))+4*L*d^2*σ^2/ε
    rw [← he]
    convert add_le_add hb hn using 1; ring

lemma twoPoint_variance_budget {L R σ ε d v : ℝ} {K : ℕ}
    (hL : 0 < L) (hσ : 0 ≤ σ) (hε : 0 < ε) (hd : 0 ≤ d)
    (hv : v ≤ 11*L*d^2*σ+10*L*d*ε/(128*(Real.sqrt (L*R^2/ε)+1))+4*L*d^2*σ^2/ε)
    (hK : 64*d*Real.sqrt (L*R^2/ε)+512*L*d^2*R^2*σ/ε^2+256*L*d^2*R^2*σ^2/ε^3+1 ≤ K) :
    1024*L*d^2*R^2/ε ≤ (K:ℝ)^2 ∧ 32*v*R^2/ε^2 ≤ K := by
  let a := Real.sqrt (L*R^2/ε)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a^2=L*R^2/ε := Real.sq_sqrt (by positivity)
  have h1 : 0 ≤ 512*L*d^2*R^2*σ/ε^2 := by positivity
  have h2 : 0 ≤ 256*L*d^2*R^2*σ^2/ε^3 := by positivity
  have hak : 32*d*a ≤ (K:ℝ) := by change 64*d*a+_+_+1 ≤ _ at hK; nlinarith
  have hdet : 1024*L*d^2*R^2/ε ≤ (K:ℝ)^2 := by
    have hh := mul_self_le_mul_self (show 0 ≤ 32*d*a by positivity) hak
    have he : 1024*L*d^2*R^2/ε=(32*d*a)^2 := by rw [mul_pow,mul_pow,ha2]; ring
    rw [he]
    nlinarith only [hh]
  have hfloor : 32*(10*L*d*ε/(128*(a+1)))*R^2/ε^2 ≤ (5/2:ℝ)*d*a := by
    have he : 32*(10*L*d*ε/(128*(a+1)))*R^2/ε^2=(5/2:ℝ)*d*(L*R^2/ε)/(a+1) := by field_simp; ring
    rw [he,← ha2]
    apply (div_le_iff₀ (by positivity : 0 < a+1)).mpr
    nlinarith [mul_nonneg hd ha]
  have hv' := mul_le_mul_of_nonneg_right hv (show 0 ≤ 32*R^2/ε^2 by positivity)
  have he : (11*L*d^2*σ+10*L*d*ε/(128*(a+1))+4*L*d^2*σ^2/ε)*(32*R^2/ε^2) =
      352*L*d^2*R^2*σ/ε^2+32*(10*L*d*ε/(128*(a+1)))*R^2/ε^2+128*L*d^2*R^2*σ^2/ε^3 := by ring
  change v*(32*R^2/ε^2) ≤ _ at hv'
  rw [he] at hv'
  have hn1 : 352*L*d^2*R^2*σ/ε^2 ≤ 512*L*d^2*R^2*σ/ε^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hL.le (sq_nonneg d)) (sq_nonneg R)) hσ]
  have hn2 : 128*L*d^2*R^2*σ^2/ε^3 ≤ 256*L*d^2*R^2*σ^2/ε^3 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hL.le (sq_nonneg d)) (sq_nonneg R)) (sq_nonneg σ)]
  change 64*d*a+_+_+1 ≤ _ at hK
  have heleft : v*(32*R^2/ε^2)=32*v*R^2/ε^2 := by ring
  rw [heleft] at hv'
  exact ⟨hdet,by nlinarith [mul_nonneg hd ha]⟩

lemma coupled_tuning {D R ε v δ : ℝ} {K : ℕ}
    (hD : 0 < D) (hε : 0 < ε) (hv : 0 ≤ v) (hK : 0 < K)
    (hdet : 8*D*R^2/ε ≤ (K:ℝ)^2) (hnoise : 32*v*R^2/ε^2 ≤ K) (hδ : δ ≤ ε/8) :
    let M := D+8*(K:ℝ)*v/ε
    M*R^2/((K:ℝ)*((K:ℝ)+1))+δ+2*K*v/M ≤ ε := by
  let M := D+8*(K:ℝ)*v/ε
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have hM : 0 < M := by dsimp [M]; positivity
  have hd := (div_le_iff₀ hε).mp hdet
  have hn := (div_le_iff₀ (sq_pos_of_pos hε)).mp hnoise
  have hi : M*R^2/((K:ℝ)*((K:ℝ)+1)) ≤ 3*ε/8 := by
    apply (div_le_iff₀ (by positivity : 0 < (K:ℝ)*((K:ℝ)+1))).mpr
    have he : M*R^2=D*R^2+8*K*v*R^2/ε := by dsimp [M]; ring
    rw [he]
    have hv' : 8*K*v*R^2/ε ≤ ε*(K:ℝ)^2/4 := by
      apply (div_le_iff₀ hε).mpr
      have := mul_le_mul_of_nonneg_left hn hKr.le
      nlinarith
    nlinarith
  have hv' : 2*K*v/M ≤ ε/4 := by
    apply (div_le_iff₀ hM).mpr
    have he : ε/4*M=ε*D/4+2*K*v := by dsimp [M]; field_simp; ring
    rw [he]
    nlinarith [mul_pos hε hD]
  change M*R^2/((K:ℝ)*((K:ℝ)+1))+δ+2*K*v/M ≤ ε
  linarith

end OracleTemplate.ZerothOrder

end


section

open MeasureTheory Set Metric

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open StochasticGradient
open LongTails.Setups.StochasticSmoothAndConvex

attribute [local irreducible] twoPointEstimate coupledRun

lemma twoPoint_rate {d K : ℕ} [NeZero d] {Ω : Type} [MeasurableSpace Ω]
    {f : Point d → ℝ} {g : Point d → Ω → ℝ} {p : Measure Ω} [IsProbabilityMeasure p]
    {L R σ h M : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hh : 0 < h) (hM : 0 < M)
    (hLM : 128*L*(d:ℝ)^2 ≤ M) (hK : 0 < K)
    (hc : ConvexOn ℝ univ f) (hd : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p)=f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω-f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω-f x)^2 ∂p) ≤ σ^2)
    (x0 u : Point d) (hmin : IsMinOn f univ u) (hu : ‖x0-u‖ ≤ R) :
    let oracle := fun (x : Point d) (w : sphere (0 : Point d) 1 × (Ω × Ω)) => twoPointEstimate g h x w.1 w.2
    let q := (sphereLaw (Point d) : Measure (sphere (0 : Point d) 1)).prod (p.prod p)
    let v := 10*(d:ℝ)^2*L^2*h^2+(d:ℝ)^2*σ^2/h^2
    let output := fun ξ : Fin K → (sphere (0 : Point d) 1 × (Ω × Ω)) => (coupledRun oracle M (8*d) K 0 x0 x0 ξ).1
    Integrable (fun ξ => f (output ξ)-f u) (Measure.pi fun _ : Fin K => q) ∧
      (∫ ξ, f (output ξ)-f u ∂Measure.pi (fun _ : Fin K => q)) ≤
        M*R^2/((K:ℝ)*((K:ℝ)+1))+L*h^2/2+2*K*v/M := by
  intro oracle q v output
  let F := ballSmooth f h
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hgc : Continuous (gradient f) := (show LipschitzWith ⟨L,hL.le⟩ (gradient f) from
    LipschitzWith.of_dist_le_mul (fun x y => by
      change dist (gradient f x) (gradient f y) ≤ L * dist x y
      simpa only [dist_eq_norm] using hlip x y)).continuous
  have hFd (x : Point d) : HasGradientAt F (gradient F x) x := by
    have ht := ballSmooth_gradient hgc hd h x
    change HasGradientAt (ballSmooth f h) (gradient (ballSmooth f h) x) x
    rw [ht.gradient]
    exact ht
  have hFlo (x : Point d) : f u ≤ F x := (hmin (mem_univ x)).trans (ball_smoothing_lower hc hd x h)
  have hFu : F u-f u ≤ L*h^2/2 := by have ht := ballSmooth_upper hL.le hd hlip h u; linarith
  have harg : Measurable (fun w : Point d × (sphere (0 : Point d) 1 × (Ω × Ω)) => (w.1,((w.2.1:Point d),w.2.2))) := by fun_prop
  have hG0 := (measurable_twoPointEstimate hgm h).comp harg
  have hG : Measurable (Function.uncurry oracle) := hG0
  have hOracle (x : Point d) := twoPoint_sphere_oracle p hgm hgi hmean hvi hv hL.le hh hc hd hlip x
  have hmoment (x : Point d) : (∫ w, ‖oracle x w‖^2 ∂q) ≤ (8*(d:ℝ))*‖gradient F x‖^2+v := by
    simpa only [add_assoc] using twoPoint_sphere_relative_moment p hgm hgi hmean hvi hv hL.le hh hc hd hlip x
  have hr := coupled_expected_rate (g := oracle) (p := q) (f := F) hL.le hM (show 0 ≤ 8*(d:ℝ) by positivity)
    (show 0 ≤ v by dsimp [v]; positivity)
    (show 2*L*(8*(d:ℝ))^2 ≤ M by nlinarith only [hLM])
    hR (ballSmooth_convex hf hc h) hFd (ballSmooth_gradient_lipschitz hgc hd hlip h) hFlo
    hG (fun x => (hOracle x).1) (fun x => (hOracle x).2.1) (fun x => (hOracle x).2.2.1)
    hmoment x0 u hFu hu hK
  have ho : Measurable output := ((measurable_coupledRun (g := oracle) hG M (8*d) K 0).comp
    (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin K → (sphere (0 : Point d) 1 × (Ω × Ω)) => ((x0,x0),ξ)))).fst
  have hbound (ξ : Fin K → (sphere (0 : Point d) 1 × (Ω × Ω))) : f (output ξ)-f u ≤ F (output ξ)-f u :=
    sub_le_sub_right (ball_smoothing_lower hc hd (output ξ) h) (f u)
  have hi : Integrable (fun ξ => f (output ξ)-f u) (Measure.pi fun _ : Fin K => q) :=
    hr.1.mono_nonneg ((hf.measurable.comp ho).sub_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => sub_nonneg.mpr (hmin (mem_univ (output ξ)))))
      (Filter.Eventually.of_forall hbound)
  exact ⟨hi,(integral_mono hi hr.1 hbound).trans hr.2⟩

end OracleTemplate.ZerothOrder

end


section

open MeasureTheory Set Metric

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open StochasticGradient
open LongTails.Setups.StochasticSmoothAndConvex

attribute [local irreducible] twoPointEstimate coupledRun

lemma twoPoint_accuracy {d : ℕ} [NeZero d] {Ω : Type} [MeasurableSpace Ω]
    {f : Point d → ℝ} {g : Point d → Ω → ℝ} {p : Measure Ω} [IsProbabilityMeasure p]
    {L R σ ε : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hσ : 0 ≤ σ) (hε : 0 < ε)
    (hc : ConvexOn ℝ univ f) (hd : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p)=f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω-f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω-f x)^2 ∂p) ≤ σ^2)
    (x0 u : Point d) (hmin : IsMinOn f univ u) (hu : ‖x0-u‖ ≤ R) :
    let h := Real.sqrt (min (ε/(4*L)) (σ/L+ε/(128*L*d*(Real.sqrt (L*R^2/ε)+1))))
    let v := 10*(d:ℝ)^2*L^2*h^2+(d:ℝ)^2*σ^2/h^2
    let K := max 1 ⌈64*d*Real.sqrt (L*R^2/ε)+512*L*d^2*R^2*σ/ε^2+256*L*d^2*R^2*σ^2/ε^3+1⌉₊
    let M := 128*L*d^2+8*(K:ℝ)*v/ε
    let q := (sphereLaw (Point d) : Measure (sphere (0 : Point d) 1)).prod (p.prod p)
    let oracle := fun (x : Point d) (w : sphere (0 : Point d) 1 × (Ω × Ω)) => twoPointEstimate g h x w.1 w.2
    Integrable (fun ξ => f (coupledRun oracle M (8*d) K 0 x0 x0 ξ).1-f u) (Measure.pi fun _ : Fin K => q) ∧
      (∫ ξ, f (coupledRun oracle M (8*d) K 0 x0 x0 ξ).1-f u ∂Measure.pi (fun _ : Fin K => q)) ≤ ε := by
  intro h v K M q oracle
  have hdr : (0:ℝ) < d := by exact_mod_cast NeZero.pos d
  have ht := twoPoint_variance_bound (R := R) hL hσ hε hdr
  change 0 < h ∧ L*h^2/2 ≤ ε/8 ∧ v ≤ _ at ht
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hceil : 64*d*Real.sqrt (L*R^2/ε)+512*L*d^2*R^2*σ/ε^2+256*L*d^2*R^2*σ^2/ε^3+1 ≤ (K:ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hb := twoPoint_variance_budget hL hσ hε hdr.le ht.2.2 hceil
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hLM : 128*L*(d:ℝ)^2 ≤ M := le_add_of_nonneg_right (by positivity)
  have hr := twoPoint_rate hL hR ht.1 hM hLM hK hc hd hlip hgm hgi hmean hvi hv x0 u hmin hu
  have hb' : 8*(128*L*(d:ℝ)^2)*R^2/ε ≤ (K:ℝ)^2 := by convert hb.1 using 1; ring
  have hacc := coupled_tuning (D := 128*L*(d:ℝ)^2) (δ := L*h^2/2) (by positivity) hε hv0 hK hb' hb.2 ht.2.1
  exact ⟨hr.1,hr.2.trans hacc⟩

end OracleTemplate.ZerothOrder

end
