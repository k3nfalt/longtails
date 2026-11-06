import LongTails.Proofs.SpikedSoftCutSelection
import LongTails.Proofs.SoftCutCertificate
import LongTails.Proofs.SoftCutCertificateDensity

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.SpikedSoftCutCertificate

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCut
open LongTails.Proofs.SpikedSoftCutSelection

lemma selected_true_certificate (q : Params) (α M margin V W : ℝ) (T n : ℕ)
    (points gradients errors : Fin T → InnerSpace q)
    (hα : 0 ≤ α) (hR : 0 ≤ q.R) (hM : 0 ≤ M) (hn : 0 < n)
    (hmargin : 0 < margin) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hp : ∀ i, ‖points i‖ ≤ q.R) (hg : ∀ i, ‖gradients i + errors i‖ ≤ M)
    (hhinge : ∀ y, ‖y‖ ≤ q.R → 2 * margin ≤
      ∑ i, max 0 (⟪gradients i + errors i, y - points i⟫ + α / 2))
    (hgrid : (α / 2 + 2 * q.R * M) * T / n ≤ margin)
    (hoperator : ∀ a : Fin T → ℝ, ‖∑ i, a i • errors i‖ ^ 2 ≤ V * ∑ i, a i ^ 2)
    (hintercept : ∑ i, ⟪errors i, points i⟫ ^ 2 ≤ W)
    (hnoise : 2 * (q.R ^ 2 * V + W) * T ≤ margin ^ 2) :
    ∀ y, ‖y‖ ≤ q.R →
      ∑ i, certificateWeights q α T n points (fun j => gradients j + errors j) i *
        ⟪gradients i, points i - y⟫ ≤ α / 2 := by
  let estimates := fun i => gradients i + errors i
  let θ := selectedCoefficients q α T n points estimates
  have hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1 :=
    selectedCoefficients_bounds q α T n hn points estimates
  have hscore0 := selected_margin_of_hinge q α M (2 * margin) T n points estimates
    hα hR hM hn hp hg hhinge
  have hscore : margin ≤ certificateScore q α points estimates θ := by
    dsimp [θ]
    linarith
  have hS : 0 < ∑ i, θ i := selected_sum_pos_of_score_pos q α T n hn points estimates
    (hmargin.trans_le hscore)
  intro y hy
  have hcut := hscore.trans (certificateScore_le_affine q α points estimates θ y hy)
  have herr := SoftCutCertificate.weighted_error_le_margin θ errors points y q.R V W margin
    hθ hR hV hW hy (hoperator θ) hintercept hmargin.le (by simpa using hnoise)
  have hcert := SoftCutCertificate.normalized_certificate θ gradients errors points y α margin
    hS hcut herr
  have hweights (i : Fin T) : certificateWeights q α T n points estimates i =
      θ i / ∑ j, θ j := by
    simp only [certificateWeights, ← show θ = selectedCoefficients q α T n points estimates from rfl,
      ite_eq_left hS]
  change (∑ i, certificateWeights q α T n points estimates i *
    ⟪gradients i, points i - y⟫) ≤ α / 2
  simp_rw [hweights]
  exact hcert

lemma generator_true_certificate (q : Params) (α M V W r : ℝ) (T b n : ℕ)
    (replies : ℕ → InnerSpace q) (gradients : Fin T → InnerSpace q)
    (hα : 0 < α) (hR : 0 < q.R) (hG : 0 ≤ q.G) (hT : 0 < T) (hn : 0 < n)
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hM : q.G+Real.sqrt V ≤ M)
    (hr : 0 < r) (hrR : r ≤ q.R)
    (hlog : (q.m : ℝ)*Real.log (q.R/r) ≤ (T : ℝ)/48) (hrM : 2*r*M ≤ α/96)
    (hgrad : ∀ i, ‖gradients i‖ ≤ q.G)
    (hgrid : (α/2+2*q.R*M)*T/n ≤ α*T/32)
    (hoperator : ∀ a : Fin T → ℝ,
      ‖∑ i, a i • (innerEstimates q α T b replies i-gradients i)‖^2 ≤ V*∑ i, a i^2)
    (hintercept : ∑ i, ⟪innerEstimates q α T b replies i-gradients i,
      innerPoints q α T b replies i⟫^2 ≤ W)
    (hnoise : 2*(q.R^2*V+W)*T ≤ (α*T/32)^2) :
    ∀ y, ‖y‖ ≤ q.R → ∑ i, innerWeights q α T b n replies i *
      ⟪gradients i, innerPoints q α T b replies i-y⟫ ≤ α/2 := by
  classical
  let errors := fun i => innerEstimates q α T b replies i-gradients i
  have he (i : Fin T) : gradients i+errors i = innerEstimates q α T b replies i := by
    dsimp [errors]; abel
  have herr (i : Fin T) : ‖errors i‖ ≤ Real.sqrt V := by
    have hh := hoperator (fun j => if j=i then 1 else 0)
    have hs : ‖errors i‖^2 ≤ V := by simpa [errors] using hh
    have hsq := Real.sq_sqrt hV
    nlinarith [norm_nonneg (errors i), Real.sqrt_nonneg V]
  have hcap (i : Fin T) : ‖gradients i+errors i‖ ≤ M :=
    (norm_add_le _ _).trans ((add_le_add (hgrad i) (herr i)).trans hM)
  have hR2 : 2*(innerParams q α).R = q.R := by dsimp [innerParams]; ring
  have hRp : 0 < (innerParams q α).R := by dsimp [innerParams]; positivity
  have hp (i : Fin T) : ‖innerPoints q α T b replies i‖ ≤ q.R := by
    have hh := CovarianceSoftCutDensity.norm_centroid_le (innerParams q α) hRp α (2/α)
      (List.ofFn (LongTails.Algorithms.CovarianceSoftCut.generatorCuts (innerParams q α) α (2/α) b i replies))
    change ‖innerPoints q α T b replies i‖ ≤ 2*(innerParams q α).R at hh
    exact hh.trans_eq hR2
  have hhinge (y : InnerSpace q) (hy : ‖y‖ ≤ q.R) :
      2*(α*T/32) ≤ ∑ i, max 0 (⟪gradients i+errors i, y-innerPoints q α T b replies i⟫+α/2) := by
    simp_rw [he]
    have hh := SoftCutCertificateDensity.uniform_generator_penalty (innerParams q α) hRp α hα b T replies M r
      hr (by rwa [hR2]) (fun i => by
        change ‖innerEstimates q α T b replies i‖ ≤ M
        rw [← he]
        exact hcap i)
      (by rw [hR2]; exact hlog) hrM y (by rwa [hR2])
    change α*T/16 ≤ ∑ i : Fin T, max 0
      (⟪innerEstimates q α T b replies i, y-innerPoints q α T b replies i⟫+α/2) at hh
    linarith
  have hh := selected_true_certificate q α M (α*T/32) V W T n
    (innerPoints q α T b replies) gradients errors hα.le hR.le
    (le_trans (add_nonneg hG (Real.sqrt_nonneg V)) hM) hn (by positivity) hV hW hp hcap hhinge
    hgrid hoperator hintercept hnoise
  simpa only [he, innerWeights] using hh

end LongTails.Proofs.SpikedSoftCutCertificate
