import LongTails.Proofs.ComparisonTrustTaylor
import LongTails.Proofs.RelativeCurvatureSpectrum

namespace LongTails.Proofs.GatedEscapePancake

open scoped RealInnerProductSpace
open LongTails.Proofs.ComparisonTrustTaylor

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

lemma grad_remainder {f : E → ℝ} {L ρ : ℝ} (h : Smooth f L ρ) (hρ : 0 ≤ ρ) (x y y' : E) {R : ℝ}
    (hy : ‖y - x‖ ≤ R) (hy' : ‖y' - x‖ ≤ R) :
    ‖gradient f y' - gradient f y - fderiv ℝ (gradient f) x (y' - y)‖ ≤ ρ * R * ‖y' - y‖ := by
  set H := fderiv ℝ (gradient f) x
  have hs : Convex ℝ (Metric.closedBall x R) := convex_closedBall x R
  have hd : ∀ z ∈ Metric.closedBall x R,
      HasFDerivWithinAt (fun z => gradient f z - H z) (fderiv ℝ (gradient f) z - H)
        (Metric.closedBall x R) z := by
    intro z _
    exact ((h.hg z).sub H.hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ z ∈ Metric.closedBall x R, ‖fderiv ℝ (gradient f) z - H‖ ≤ ρ * R := by
    intro z hz
    have h1 := h.hess z x
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact h1.trans (mul_le_mul_of_nonneg_left hz hρ)
  have hmem : y ∈ Metric.closedBall x R := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy
  have hmem' : y' ∈ Metric.closedBall x R := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy'
  have key := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb hmem hmem'
  have heq : gradient f y' - H y' - (gradient f y - H y) =
      gradient f y' - gradient f y - H (y' - y) := by
    rw [map_sub]; abel
  rw [heq] at key
  exact key

omit [FiniteDimensional ℝ E] in
lemma linear_step_norm (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, H v⟫ = eig i * ⟪b i, v⟫) {η a : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ i, |1 - η * eig i| ≤ a) (v : E) : ‖v - η • H v‖ ≤ a * ‖v‖ := by
  have hs : ‖v - η • H v‖ ^ 2 ≤ (a * ‖v‖) ^ 2 := by
    rw [← b.sum_sq_inner_right (v - η • H v), mul_pow, ← b.sum_sq_inner_right v, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hco : ⟪b i, v - η • H v⟫ = (1 - η * eig i) * ⟪b i, v⟫ := by
      rw [inner_sub_right, inner_smul_right, hc]; ring
    rw [hco, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have h := ha i
    have h2 : (1 - η * eig i) ^ 2 = |1 - η * eig i| ^ 2 := (sq_abs _).symm
    rw [h2]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha0 (norm_nonneg _))).mp hs

omit [FiniteDimensional ℝ E] in
theorem eig_vector (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, H v⟫ = eig i * ⟪b i, v⟫) (j0 : ι) : H (b j0) = eig j0 • b j0 := by
  classical
  have h1 := b.sum_repr' (H (b j0))
  rw [← h1]
  simp_rw [hc, (orthonormal_iff_ite.mp b.orthonormal)]
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp

lemma seq_growth (ψ φ : ℕ → ℝ) {a β θ : ℝ} {Tn : ℕ}
    (h1 : ∀ t < Tn, a * ψ t - β * (|ψ t| + φ t) ≤ ψ (t + 1))
    (h2 : ∀ t < Tn, φ (t + 1) ≤ a * φ t + β * (|ψ t| + φ t))
    (hφ0 : φ 0 = 0) (hψ0 : ψ 0 = θ) (hθ : 0 ≤ θ) (hβ : 0 ≤ β) (hgap : 1 + 2 * β ≤ a)
    (hsmall : 8 * β * Tn ≤ 1) :
    θ * (a - 2 * β) ^ Tn ≤ ψ Tn := by
  have hinv : ∀ t ≤ Tn, 0 ≤ ψ t ∧ θ * (a - 2 * β) ^ t ≤ ψ t ∧ φ t ≤ 4 * β * t * ψ t := by
    intro t
    induction t with
    | zero => intro _; rw [hψ0, hφ0]; simp [hθ]
    | succ t ih =>
      intro ht
      obtain ⟨hp0, hpg, hph⟩ := ih (by omega)
      have htR : (t : ℝ) + 1 ≤ Tn := by exact_mod_cast ht
      have htn : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      have hct : 4 * β * t ≤ 1 / 2 := by nlinarith
      have hA := h1 t (by omega)
      have hB := h2 t (by omega)
      rw [abs_of_nonneg hp0] at hA hB
      have hδt : ψ t + φ t ≤ (1 + 4 * β * t) * ψ t := by nlinarith
      have hψnext : (a - β * (1 + 4 * β * t)) * ψ t ≤ ψ (t + 1) := by nlinarith
      have hφnext : φ (t + 1) ≤ (a * (4 * β * t) + β * (1 + 4 * β * t)) * ψ t := by nlinarith
      have hb2 : β * (1 + 4 * β * t) ≤ 2 * β := by nlinarith
      have k1 : β * (1 + 4 * β * t) * ψ t ≤ 2 * β * ψ t := mul_le_mul_of_nonneg_right hb2 hp0
      have hψ1 : (a - 2 * β) * ψ t ≤ ψ (t + 1) := by linarith
      have hpos : 0 ≤ ψ (t + 1) := le_trans (by nlinarith) hψ1
      refine ⟨hpos, ?_, ?_⟩
      · rw [pow_succ]; nlinarith
      · have hst : 8 * β * ((t : ℝ) + 1) ≤ 1 := by nlinarith
        have hu : 4 * β * ((t : ℝ) + 1) ≤ 1 / 2 := by linarith
        have hv : 1 + 4 * β * t ≤ 3 / 2 := by linarith
        have hw : 4 * β * ((t : ℝ) + 1) * (1 + 4 * β * t) ≤ 3 / 4 := by
          have := mul_le_mul hu hv (by positivity) (by norm_num)
          linarith
        have hz : 1 + 4 * β * t + 4 * β * ((t : ℝ) + 1) * (1 + 4 * β * t) ≤ 4 * a := by linarith
        have key : a * (4 * β * t) + β * (1 + 4 * β * t) ≤
            4 * β * ((t : ℝ) + 1) * (a - β * (1 + 4 * β * t)) := by
          nlinarith [mul_le_mul_of_nonneg_left hz hβ]
        push_cast
        have hk2 := mul_le_mul_of_nonneg_right key hp0
        have hm := mul_le_mul_of_nonneg_left hψnext (by positivity : (0 : ℝ) ≤ 4 * β * ((t : ℝ) + 1))
        nlinarith
  exact (hinv Tn le_rfl).2.1

omit [FiniteDimensional ℝ E] [Fintype ι] in
lemma perp_norm (e v : E) (he : ‖e‖ = 1) : ‖v - ⟪e, v⟫ • e‖ ≤ ‖v‖ := by
  have h1 : ‖v - ⟪e, v⟫ • e‖ ^ 2 = ‖v‖ ^ 2 - ⟪e, v⟫ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs,
      real_inner_comm v e]
    ring
  have h2 : ‖v - ⟪e, v⟫ • e‖ ^ 2 ≤ ‖v‖ ^ 2 := by rw [h1]; nlinarith [sq_nonneg ⟪e, v⟫]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

theorem pancake {f : E → ℝ} {L ρ : ℝ} (h : Smooth f L ρ) (hρ : 0 ≤ ρ) (x g0 : E)
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, fderiv ℝ (gradient f) x v⟫ = eig i * ⟪b i, v⟫)
    (j0 : ι) {η R ζ γ' θ : ℝ} {Tn : ℕ} (hj0 : eig j0 = -γ')
    (ha : ∀ i, |1 - η * eig i| ≤ 1 + η * γ') (hη : 0 < η) (hRζ : ρ * R ≤ ζ) (hζ : 0 ≤ ζ)
    (hgap : 2 * (η * ζ) ≤ η * γ') (hsmall : 8 * (η * ζ) * Tn ≤ 1)
    (u u' : ℕ → E) (hu : ∀ t, u (t + 1) = u t - η • (gradient f (x + u t) - g0))
    (hu' : ∀ t, u' (t + 1) = u' t - η • (gradient f (x + u' t) - g0))
    (hθ : u' 0 - u 0 = θ • b j0) (hθ0 : 0 ≤ θ)
    (hball : ∀ t ≤ Tn, ‖u t‖ ≤ R ∧ ‖u' t‖ ≤ R) :
    θ * (1 + η * γ' - 2 * (η * ζ)) ^ Tn ≤ 2 * R := by
  obtain ⟨H, hH⟩ : ∃ H : E →L[ℝ] E, H = fderiv ℝ (gradient f) x := ⟨_, rfl⟩
  rw [← hH] at hc
  have hb1 : ‖b j0‖ = 1 := b.orthonormal.1 j0
  have hHb : H (b j0) = (-γ') • b j0 := by rw [eig_vector H b eig hc j0, hj0]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → E, ∀ t, δ t = u' t - u t := ⟨_, fun _ => rfl⟩
  obtain ⟨Rr, hRr⟩ : ∃ Rr : ℕ → E, ∀ t,
      Rr t = gradient f (x + u' t) - gradient f (x + u t) - H (δ t) := ⟨_, fun _ => rfl⟩
  have hRbound : ∀ t ≤ Tn, ‖Rr t‖ ≤ ζ * ‖δ t‖ := by
    intro t ht
    obtain ⟨h1, h2⟩ := hball t ht
    have key := grad_remainder h hρ x (x + u t) (x + u' t) (R := R)
      (by simpa using h1) (by simpa using h2)
    have hd : x + u' t - (x + u t) = δ t := by rw [hδ]; abel
    rw [hd, ← hH] at key
    rw [hRr]
    exact key.trans (mul_le_mul_of_nonneg_right hRζ (norm_nonneg _))
  have hδsucc : ∀ t, δ (t + 1) = (δ t - η • H (δ t)) - η • Rr t := by
    intro t
    rw [hRr, hδ, hδ, hu, hu']
    module
  set ψ : ℕ → ℝ := fun t => ⟪b j0, δ t⟫ with hψ
  set φ : ℕ → ℝ := fun t => ‖δ t - ψ t • b j0‖ with hφ
  have hδle : ∀ t, ‖δ t‖ ≤ |ψ t| + φ t := by
    intro t
    have hsplit : δ t = (δ t - ψ t • b j0) + ψ t • b j0 := by abel
    calc ‖δ t‖ = ‖(δ t - ψ t • b j0) + ψ t • b j0‖ := by rw [← hsplit]
      _ ≤ φ t + ‖ψ t • b j0‖ := norm_add_le _ _
      _ = |ψ t| + φ t := by rw [norm_smul, hb1, Real.norm_eq_abs]; ring
  have hlin : ∀ v : E, ‖v - η • H v‖ ≤ (1 + η * γ') * ‖v‖ :=
    linear_step_norm H b eig hc (by nlinarith [mul_nonneg hη.le hζ]) ha
  have h1 : ∀ t < Tn, (1 + η * γ') * ψ t - η * ζ * (|ψ t| + φ t) ≤ ψ (t + 1) := by
    intro t ht
    have hψs : ψ (t + 1) = (1 + η * γ') * ψ t - η * ⟪b j0, Rr t⟫ := by
      simp only [hψ]
      rw [hδsucc, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right, hc, hj0]
      ring
    have hinR : ⟪b j0, Rr t⟫ ≤ ζ * (|ψ t| + φ t) := by
      have k1 := real_inner_le_norm (b j0) (Rr t)
      rw [hb1, one_mul] at k1
      exact k1.trans ((hRbound t ht.le).trans (mul_le_mul_of_nonneg_left (hδle t) hζ))
    rw [hψs]
    nlinarith
  have h2 : ∀ t < Tn, φ (t + 1) ≤ (1 + η * γ') * φ t + η * ζ * (|ψ t| + φ t) := by
    intro t ht
    have hφe : δ (t + 1) - ψ (t + 1) • b j0 =
        ((δ t - ψ t • b j0) - η • H (δ t - ψ t • b j0)) - η • (Rr t - ⟪b j0, Rr t⟫ • b j0) := by
      have hψs : ψ (t + 1) = (1 + η * γ') * ψ t - η * ⟪b j0, Rr t⟫ := by
        simp only [hψ]
        rw [hδsucc, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right, hc, hj0]
        ring
      rw [hψs, hδsucc, map_sub, map_smul, hHb]
      module
    simp only [hφ]
    rw [hφe]
    have s1 := norm_sub_le ((δ t - ψ t • b j0) - η • H (δ t - ψ t • b j0))
      (η • (Rr t - ⟪b j0, Rr t⟫ • b j0))
    have s2 : ‖η • (Rr t - ⟪b j0, Rr t⟫ • b j0)‖ ≤ η * (ζ * (|ψ t| + φ t)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
      exact mul_le_mul_of_nonneg_left ((perp_norm (b j0) (Rr t) hb1).trans
        ((hRbound t ht.le).trans (mul_le_mul_of_nonneg_left (hδle t) hζ))) hη.le
    have s3 := hlin (δ t - ψ t • b j0)
    simp only [hφ] at s2
    nlinarith
  have hψ0 : ψ 0 = θ := by
    simp only [hψ]; rw [hδ, hθ, inner_smul_right, real_inner_self_eq_norm_sq, hb1]; ring
  have hφ0 : φ 0 = 0 := by
    simp only [hφ]; rw [hψ0, hδ, hθ, sub_self, norm_zero]
  have hg := seq_growth ψ φ h1 h2 hφ0 hψ0 hθ0 (mul_nonneg hη.le hζ) (by linarith) hsmall
  have hfin : ψ Tn ≤ 2 * R := by
    have k1 : ψ Tn ≤ ‖δ Tn‖ := by
      have k2 := real_inner_le_norm (b j0) (δ Tn); rw [hb1, one_mul] at k2; exact k2
    obtain ⟨hr1, hr2⟩ := hball Tn le_rfl
    have k3 : ‖δ Tn‖ ≤ ‖u' Tn‖ + ‖u Tn‖ := by rw [hδ]; exact norm_sub_le _ _
    linarith
  have hfinal : θ * (1 + η * γ' - 2 * (η * ζ)) ^ Tn ≤ ψ Tn := by
    have := hg; ring_nf at this ⊢; linarith
  linarith

end LongTails.Proofs.GatedEscapePancake
