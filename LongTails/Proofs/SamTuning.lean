import LongTails.Proofs.SamStrongConvex
import LongTails.Proofs.ReshufflingTuning

namespace LongTails.Proofs.SamStrongConvex

lemma tuning {L μ ρ ε : ℝ} (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hρ : 0 < ρ) (hε : 0 < ε) :
    let η := 1/(2*L+2*L^2*ρ/Real.sqrt (μ*ε))
    let C := 2*L/μ+2*L^2*ρ/(μ*Real.sqrt (μ*ε))
    0 < η ∧ 2*L*η ≤ 1 ∧ 4*η^2*L^4*ρ^2/μ ≤ ε ∧ μ*η=1/C ∧ 1 ≤ C := by
  dsimp only
  let s := Real.sqrt (μ*ε)
  let D := 2*L+2*L^2*ρ/s
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos hμ hε)
  have hs2 : s^2=μ*ε := Real.sq_sqrt (mul_pos hμ hε).le
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 2*L ≤ D := by
    dsimp [D]
    have : 0 ≤ 2*L^2*ρ/s := by positivity
    linarith
  have hD2 : 2*L^2*ρ ≤ D*s := by
    dsimp [D]
    have he : (2*L+2*L^2*ρ/s)*s=2*L*s+2*L^2*ρ := by field_simp
    rw [he]
    nlinarith [mul_pos hL hs]
  have hc : 2*L/μ+2*L^2*ρ/(μ*s)=D/μ := by dsimp [D]; field_simp
  have he1 : 2*L*(1/D) ≤ 1 := by rw [mul_one_div, div_le_one hD]; exact hD1
  have he2 : 2*(1/D)*L^2*ρ ≤ s := by
    rw [show 2*(1/D)*L^2*ρ = (2*L^2*ρ)/D by ring]
    exact (div_le_iff₀ hD).mpr (by nlinarith [hD2])
  have he3 : 4*(1/D)^2*L^4*ρ^2/μ ≤ ε := by
    apply (div_le_iff₀ hμ).mpr
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 2*(1/D)*L^2*ρ) hs.le).mpr he2
    nlinarith
  have he4 : μ*(1/D)=1/(2*L/μ+2*L^2*ρ/(μ*s)) := by rw [hc]; field_simp
  have he5 : 1 ≤ 2*L/μ+2*L^2*ρ/(μ*s) := by
    rw [hc, le_div_iff₀ hμ]
    linarith
  exact ⟨by positivity, he1, he3, he4, he5⟩

lemma tuned_accuracy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E} {L ρ μ Δ ε : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (hμ : 0 < μ) (hμL : μ ≤ L) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hs : ∀ x y, f x + @inner ℝ E _ (g x) (y-x) + μ/2*‖y-x‖^2 ≤ f y)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hl : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x xs : E) (hx : f x-f xs ≤ Δ) :
    let η := 1/(2*L+2*L^2*ρ/Real.sqrt (μ*ε))
    let K := ⌈(2*L/μ+2*L^2*ρ/(μ*Real.sqrt (μ*ε)))*Real.log (1+Δ/ε)⌉₊
    f (LongTails.Algorithms.NormalizedSam.output g η ρ x K)-f xs ≤ ε := by
  let η := 1/(2*L+2*L^2*ρ/Real.sqrt (μ*ε))
  let C := 2*L/μ+2*L^2*ρ/(μ*Real.sqrt (μ*ε))
  let K := ⌈C*Real.log (1+Δ/ε)⌉₊
  change f (LongTails.Algorithms.NormalizedSam.output g η ρ x K)-f xs ≤ ε
  obtain ⟨hη, hstep, hfloor, he, hC⟩ := tuning hL hμ hμL hρ hε
  change 0 < η at hη
  change 2*L*η ≤ 1 at hstep
  change 4*η^2*L^4*ρ^2/μ ≤ ε at hfloor
  change μ*η=1/C at he
  change 1 ≤ C at hC
  have hC0 : 0 < C := by linarith
  have hb := OracleTemplate.QuadraticReshuffling.geometric_log_budget
    (q := C/2) (D := Δ) (ε := ε) (by positivity) (by linarith) hΔ hε
  rw [show 2*(C/2)=C by ring] at hb
  have hrate : (1-μ*η)^K*Δ ≤ ε := by
    rw [he]
    change Δ/2*(1-1/C)^K ≤ ε/2 at hb
    nlinarith
  have hq : 0 ≤ 1-μ*η := by
    rw [he]
    have := (div_le_one hC0).mpr hC
    linarith
  have hinit := mul_le_mul_of_nonneg_left hx (pow_nonneg hq K)
  exact (output_gap hL hρ hη hμ hμL hstep hs hg hl x xs K).trans
    (max_le (hinit.trans hrate) hfloor)

end LongTails.Proofs.SamStrongConvex
