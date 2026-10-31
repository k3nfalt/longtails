import LongTails.Proofs.AdamGeneralizedPath
import LongTails.Proofs.AdamAuxiliaryDescent

open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdamGeneralizedLogPath

open OracleTemplate.Adam AdamGeneralizedPath

lemma centered_path {d : ℕ} {f : Point d → ℝ} {u : Point d → Point d}
    {A K β η τ ρ B C : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hρq : 1 / 4 ≤ 1 - ρ) (hbρ : (1 + β) / 2 ≤ 1 - ρ)
    (hf : ∀ x, HasGradientAt f (u x) x)
    (hlip : ∀ x y, ‖u x - u y‖ ≤ A * ‖x - y‖)
    (hvalue : ∀ x y, |f x - f y| ≤ K * ‖x - y‖)
    (s : ℕ → Point d × Point d × Point d) (g Q signal : ℕ → Point d)
    (hv : ∀ t i, 0 < (s t).2.2 i) (hm0 : (s 0).2.1 = 0)
    (hm : ∀ t, (s (t + 1)).2.1 = β • (s t).2.1 + (1 - β) • g t)
    (hrec : ∀ t i, (s (t + 1)).2.2 i = (1 - ρ) * (s t).2.2 i + ρ * (g t i) ^ 2)
    (hx : ∀ t, (s (t + 1)).1 = (s t).1 - η • direction τ (s (t + 1)).2.1 (s (t + 1)).2.2)
    (hmnorm : ∀ t i, ρ * ((s t).2.1 i) ^ 2 ≤ (s t).2.2 i)
    (n : ℕ) (hB : 1 ≤ B) (hvn : ∀ i, (s n).2.2 i ≤ (s 0).2.2 i * B)
    (hlog : -(n : ℝ) * Real.log (1 - ρ) ≤ 2)
    (hu : ∀ t < n, ‖u (s t).1‖ ≤ K)
    (hsignal : ∀ t < n, 0 ≤ ⟪u (s t).1, signal t⟫)
    (hbias : ∀ t < n, ‖Q t - signal t‖ ≤ C) :
    f (s n).1 ≤ f (s 0).1 +
      (∑ t ∈ Finset.range n, -η * ⟪u (s t).1, direction τ (g t) (s (t + 1)).2.2 - Q t⟫) +
      n * η * K * C +
      (A * (1 + (β / (1 - β)) ^ 2) * η ^ 2 * d / ρ +
        3 * K * (β / (1 - β)) * (η / Real.sqrt ρ) * d) * (2 + Real.log B) +
      K * (η * β / (1 - β)) * (Real.sqrt d / Real.sqrt ρ) := by
  let z := fun t => auxiliaryPoint β η τ (s t)
  let q := fun t => direction τ (g t) (s (t + 1)).2.2
  let r := fun t => residual β η τ (s t) (s (t + 1)).2.2
  have hz0 : z 0 = (s 0).1 := by
    have he : direction τ (s 0).2.1 (s 0).2.2 = 0 := by
      apply PiLp.ext
      intro i
      simp [direction, hm0]
    simp only [z, auxiliaryPoint, he, smul_zero, sub_zero]
  have hz (t) : z (t + 1) = z t - η • q t + r t := by
    have hh := auxiliary_update (η := η) (ne_of_lt hβ1) hτ (s t) (g t) (s (t + 1)).2.2 (hv t) (hv (t + 1))
    have he : s (t + 1) = ((s t).1 - η • direction τ (β • (s t).2.1 + (1 - β) • g t)
        (s (t + 1)).2.2, β • (s t).2.1 + (1 - β) • g t, (s (t + 1)).2.2) := by
      apply Prod.ext
      · rw [hx t, hm t]
      · exact Prod.ext (hm t) rfl
    dsimp [z, q, r]
    rw [he]
    exact hh
  have hs := AdamAuxiliaryDescent.centered_log_path hA hη hf hlip hvalue
    (fun t => (s t).1) z q Q signal r n hz0 (fun t _ => hz t) hu hsignal hbias
  have hp := normalized_path_sums (g := g) (m := fun t => (s t).2.1) (v := fun t => (s t).2.2) hβ hβ1 hρ hρ1 hbρ hτ (hv 0) hm0 hm hrec n
    (by linarith : 0 < B) hvn hlog
  have ha := auxiliary_path_sum s β η τ n hm0 hp.2
  have hr := residual_path_sum s hβ hβ1 hη hτ hρ hρq hv hmnorm
    (fun t i => by rw [hrec t i]; exact le_add_of_nonneg_right (mul_nonneg hρ.le (sq_nonneg _))) n hB hvn hlog
  have hd := auxiliary_distance hβ hβ1 hη hτ hρ (s n) (hv n) (hmnorm n)
  have hd' : ‖(s n).1 - z n‖ ≤ η * β / (1 - β) * (Real.sqrt d / Real.sqrt ρ) := by
    rw [norm_sub_rev]
    exact hd
  calc
    _ ≤ f (s 0).1 + (∑ t ∈ Finset.range n, -η * ⟪u (s t).1, q t - Q t⟫) +
        n * η * K * C + A / 2 * (η * β / (1 - β)) ^ 2 * (2 * d * ((2 + Real.log B) / ρ)) +
        A * η ^ 2 * (d * ((2 + Real.log B) / ρ)) +
        K * (3 * (β / (1 - β)) * (η / Real.sqrt ρ) * d * (2 + Real.log B)) +
        K * (η * β / (1 - β) * (Real.sqrt d / Real.sqrt ρ)) := by
      apply hs.trans
      have h1 := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ A / 2)
      have h2 := mul_le_mul_of_nonneg_left hp.1 (by positivity : 0 ≤ A * η ^ 2)
      have h3 := mul_le_mul_of_nonneg_left hr hK
      have h4 := mul_le_mul_of_nonneg_left hd' hK
      dsimp [z, q, r] at h1 h2 h3 h4 ⊢
      nlinarith
    _ = _ := by dsimp [q]; ring

end LongTails.Proofs.AdamGeneralizedLogPath
