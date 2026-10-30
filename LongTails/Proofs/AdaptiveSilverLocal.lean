import LongTails.Proofs.AdaptiveSilverCycle

namespace LongTails.Proofs.AdaptiveSilverLocal

open scoped RealInnerProductSpace
open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.SilverTrace
open LongTails.Proofs.AdaptiveSilverScalar
open LongTails.Proofs.AdaptiveSilverSplit
open LongTails.Proofs.AdaptiveSilverDynamics
open LongTails.Proofs.AdaptiveSilverModel
open LongTails.Proofs.AdaptiveSilverCycle

lemma cycle_prefix {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (K : ℕ) {l : List ℝ}
    (hl : l <+: steps K ++ steps K) : |pr μ l| ≤ 1 := by
  obtain ⟨r, hr⟩ := hl
  rcases List.append_eq_append_iff.mp hr with ⟨a, ha, -⟩ | ⟨c, hc, -⟩
  · exact prefix_bound h0 h1 K ⟨a, ha.symm⟩
  · rw [hc, pr_append, abs_mul]
    have h2 := prefix_bound h0 h1 K (List.prefix_refl (steps K))
    have h3 : c <+: steps K := by
      have : steps K ++ c <+: steps K ++ steps K := ⟨r, by rw [← hr, hc]⟩
      exact (List.prefix_append_right_inj (steps K)).mp this
    have h4 := prefix_bound h0 h1 K h3
    nlinarith [abs_nonneg (pr μ (steps K)), abs_nonneg (pr μ c)]

lemma cycle_suffix {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (K : ℕ) {l : List ℝ}
    (hl : l <:+ steps K ++ steps K) : |pr μ l| ≤ 1 := by
  obtain ⟨t, ht⟩ := hl
  rcases List.append_eq_append_iff.mp ht with ⟨a, ha, hla⟩ | ⟨c, hc, hlc⟩
  · rw [hla, pr_append, abs_mul]
    have h2 := suffix_bound h0 h1 K (show a <:+ steps K from ⟨t, ha.symm⟩)
    have h3 := suffix_bound h0 h1 K (List.suffix_refl (steps K))
    nlinarith [abs_nonneg (pr μ a), abs_nonneg (pr μ (steps K))]
  · exact suffix_bound h0 h1 K ⟨c, hlc.symm⟩

lemma cycle_infix {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (K : ℕ) {l : List ℝ}
    (hl : l <:+: steps K ++ steps K) : |pr μ l| ≤ window K := by
  rcases List.infix_append_iff.mp hl with h | h | ⟨a, c, rfl, ha, hc⟩
  · exact infix_bound h0 h1 K h
  · exact infix_bound h0 h1 K h
  · rw [pr_append, abs_mul]
    have h2 := suffix_bound h0 h1 K ha
    have h3 := prefix_bound h0 h1 K hc
    have h4 := one_le_window K
    nlinarith [abs_nonneg (pr μ a), abs_nonneg (pr μ c)]

lemma sigma_ge (K : ℕ) (hK : 2 ≤ K) : 1 ≤ (steps K).sum ∧ window K ≤ (steps K).sum := by
  have hr := ratio_gt_two
  have hsq := ratio_square
  have hp : ratio ^ 2 ≤ ratio ^ K := pow_le_pow_right₀ (by linarith) hK
  rw [steps_sum]
  refine ⟨by nlinarith, ?_⟩
  unfold window
  apply max_le (by nlinarith)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma steps_nonneg (K : ℕ) : ∀ h ∈ steps K ++ steps K, 0 ≤ h := by
  intro h hh
  rcases List.mem_append.mp hh with hh | hh <;> exact (steps_positive K h hh).le

lemma cycle_sum (K : ℕ) : (steps K ++ steps K).sum = 2 * (steps K).sum := by
  rw [List.sum_append]; ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure Hyp (f : E → ℝ) (L ρ : ℝ) (x0 : E) : Prop where
  hL : 0 < L
  hρ : 0 ≤ ρ
  hf : ∀ x, HasFDerivAt f (innerSL ℝ (gradient f x)) x
  hg : ∀ x, HasFDerivAt (gradient f) (fderiv ℝ (gradient f) x) x
  hA : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖
  hsym : ∀ u v, ⟪fderiv ℝ (gradient f) x0 u, v⟫ = ⟪u, fderiv ℝ (gradient f) x0 v⟫
  hH : ‖fderiv ℝ (gradient f) x0‖ ≤ L

section Algebra

lemma abort_algebra {L σ e G Mg a δ S fm f0 Φ Ψ Φh c3 : ℝ} (hL : 0 < L) (hσ1 : 1 ≤ σ)
    (he0 : 0 ≤ e) (hG : 0 ≤ G) (hS : S ≤ 2 * σ) (hδ0 : 0 ≤ δ)
    (hmodel : fm ≤ f0 + (Φ + Ψ) + c3) (hphi : Φ ≤ Φh + a * δ + L / 2 * δ ^ 2) (hphi0 : Φh ≤ 0)
    (ha : a ≤ G) (hpsi : Ψ ≤ 0 + S / (2 * L) * e ^ 2) (hdev : δ ≤ σ * (S * (e / L)))
    (b1 : 16 * σ ^ 2 * e ≤ Mg) (b2 : 2 * G ≤ Mg) (b3 : c3 ≤ Mg ^ 2 / (32 * L)) :
    fm ≤ f0 + Mg ^ 2 / (8 * L) := by
  have hσ0 : 0 ≤ σ := by linarith
  have hMg : 0 ≤ Mg := by linarith
  have hS0 : 0 ≤ S ∨ S < 0 := le_or_gt 0 S
  have hLδ : L * δ ≤ 2 * σ ^ 2 * e := by
    have h1 : L * δ ≤ L * (σ * (S * (e / L))) := mul_le_mul_of_nonneg_left hdev hL.le
    have h2 : L * (σ * (S * (e / L))) = σ * S * e := by field_simp
    have h3 : σ * S * e ≤ σ * (2 * σ) * e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hσ0) he0
    nlinarith
  have hτ : L * δ ≤ Mg / 8 := by nlinarith
  have hA : L * (a * δ) ≤ Mg ^ 2 / 16 := by
    have h1 : a * (L * δ) ≤ G * (Mg / 8) := mul_le_mul ha hτ (by positivity) hG
    have h2 : G * (Mg / 8) ≤ Mg / 2 * (Mg / 8) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have hB : L * (L / 2 * δ ^ 2) ≤ Mg ^ 2 / 128 := by
    have h1 : (L * δ) ^ 2 ≤ (Mg / 8) ^ 2 := pow_le_pow_left₀ (by positivity) hτ 2
    have e1 : L * (L / 2 * δ ^ 2) = (L * δ) ^ 2 / 2 := by ring
    rw [e1]; nlinarith
  have hσe : σ * e ≤ Mg / 16 := by
    have h1 : σ * e ≤ σ ^ 2 * e := by nlinarith [mul_nonneg hσ0 he0]
    nlinarith
  have hee : e ≤ Mg / 16 := by nlinarith
  have hC : L * (S / (2 * L) * e ^ 2) ≤ Mg ^ 2 / 256 := by
    have e1 : L * (S / (2 * L) * e ^ 2) = S * e ^ 2 / 2 := by field_simp
    rw [e1]
    have h1 : S * e ^ 2 / 2 ≤ σ * e ^ 2 := by nlinarith [sq_nonneg e]
    have h2 : σ * e ^ 2 = (σ * e) * e := by ring
    have h3 : (σ * e) * e ≤ (Mg / 16) * (Mg / 16) :=
      mul_le_mul hσe hee he0 (by positivity)
    nlinarith
  have hD : L * c3 ≤ Mg ^ 2 / 32 := by
    have h1 := mul_le_mul_of_nonneg_left b3 hL.le
    have e1 : L * (Mg ^ 2 / (32 * L)) = Mg ^ 2 / 32 := by field_simp
    linarith
  have htot : L * (fm - f0) ≤ Mg ^ 2 / 8 := by
    have h1 : fm - f0 ≤ a * δ + L / 2 * δ ^ 2 + S / (2 * L) * e ^ 2 + c3 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hL.le
    have e1 : L * (a * δ + L / 2 * δ ^ 2 + S / (2 * L) * e ^ 2 + c3) =
        L * (a * δ) + L * (L / 2 * δ ^ 2) + L * (S / (2 * L) * e ^ 2) + L * c3 := by ring
    rw [e1] at h2
    nlinarith
  have h1 : fm - f0 ≤ Mg ^ 2 / (8 * L) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  linarith

lemma complete_algebra {L σ e G ε a a2 r δn δ2 f2 f0 Φ Ψ Ψn Φh c3 : ℝ} (hL : 0 < L)
    (hσ1 : 1 ≤ σ) (he0 : 0 ≤ e) (hG : 0 ≤ G) (hε : 0 ≤ ε) (hδ20 : 0 ≤ δ2)
    (hmodel : f2 ≤ f0 + (Φ + Ψ) + c3) (hphi : Φ ≤ Φh + a2 * δ2 + L / 2 * δ2 ^ 2)
    (hphi0 : Φh ≤ -((σ + 1) / (4 * L)) * a ^ 2) (ha2 : a2 ≤ G)
    (hpsi1 : Ψn ≤ 0 + σ / (2 * L) * e ^ 2)
    (hpsi2 : Ψ ≤ Ψn - σ / (2 * L) * max 0 (r - σ * e) ^ 2 + σ / (2 * L) * e ^ 2)
    (hjn : ε ≤ a + L * δn + r + e) (hdevn : δn ≤ σ * (e / L)) (hdev2 : δ2 ≤ 2 * σ * (e / L))
    (c1 : σ * e ≤ ε / 16) (c2 : G ≤ 2 * σ * ε / 25) (c3h : c3 ≤ σ * ε ^ 2 / (100 * L)) :
    σ * ε ^ 2 / (25 * L) ≤ f0 - f2 := by
  have hσ0 : 0 ≤ σ := by linarith
  have hLδn : L * δn ≤ σ * e := by
    have h1 := mul_le_mul_of_nonneg_left hdevn hL.le
    have e1 : L * (σ * (e / L)) = σ * e := by field_simp
    linarith
  have hLδ2 : L * δ2 ≤ 2 * σ * e := by
    have h1 := mul_le_mul_of_nonneg_left hdev2 hL.le
    have e1 : L * (2 * σ * (e / L)) = 2 * σ * e := by field_simp
    linarith
  obtain ⟨c, hcdef⟩ : ∃ c, c = max 0 (r - σ * e) := ⟨_, rfl⟩
  rw [← hcdef] at hpsi2
  have hc0 : 0 ≤ c := by rw [hcdef]; exact le_max_left _ _
  have hrc : r - σ * e ≤ c := by rw [hcdef]; exact le_max_right _ _
  have hes : e ≤ σ * e := le_mul_of_one_le_left he0 hσ1
  have hac : 13 * ε / 16 ≤ a + c := by linarith
  have hquad : σ * (13 * ε / 16) ^ 2 / 8 ≤ (σ + 1) / 4 * a ^ 2 + σ / 2 * c ^ 2 := by
    have h1 : (13 * ε / 16) ^ 2 ≤ (a + c) ^ 2 := pow_le_pow_left₀ (by positivity) hac 2
    have h2 : (a + c) ^ 2 ≤ 2 * (a ^ 2 + c ^ 2) := by linarith [sq_nonneg (a - c)]
    have h3 : σ * (13 * ε / 16) ^ 2 / 8 ≤ σ * (a ^ 2 + c ^ 2) / 4 := by
      have := mul_le_mul_of_nonneg_left (h1.trans h2) hσ0
      linarith
    linarith [sq_nonneg a, mul_nonneg hσ0 (sq_nonneg c)]
  have hE1 : a2 * (L * δ2) ≤ σ * ε ^ 2 / 100 := by
    have h1 : a2 * (L * δ2) ≤ G * (2 * σ * e) := mul_le_mul ha2 hLδ2 (by positivity) hG
    have h2 : G * (2 * σ * e) ≤ (2 * σ * ε / 25) * (ε / 8) :=
      mul_le_mul c2 (by linarith) (by positivity) (by positivity)
    have h3 : (2 * σ * ε / 25) * (ε / 8) = σ * ε ^ 2 / 100 := by ring
    linarith
  have hE2 : (L * δ2) ^ 2 / 2 ≤ σ * ε ^ 2 / 128 := by
    have h1 : (L * δ2) ^ 2 ≤ (2 * σ * e) ^ 2 := pow_le_pow_left₀ (by positivity) hLδ2 2
    have h2 : (2 * σ * e) ^ 2 ≤ (ε / 8) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h3 : (ε / 8) ^ 2 = ε ^ 2 / 64 := by ring
    have h4 : ε ^ 2 ≤ σ * ε ^ 2 := by
      have := mul_le_mul_of_nonneg_right hσ1 (sq_nonneg ε); linarith
    linarith
  have hE3 : σ * e ^ 2 ≤ σ * ε ^ 2 / 256 := by
    have h2 : (σ * e) ^ 2 ≤ (ε / 16) ^ 2 := pow_le_pow_left₀ (by positivity) c1 2
    have h3 : σ * e ^ 2 ≤ (σ * e) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hσ1 (mul_nonneg hσ0 (sq_nonneg e))
      have e1 : (σ * e) ^ 2 = σ * (σ * e ^ 2) := by ring
      linarith
    have h4 : (ε / 16) ^ 2 = ε ^ 2 / 256 := by ring
    have h5 : ε ^ 2 ≤ σ * ε ^ 2 := by
      have := mul_le_mul_of_nonneg_right hσ1 (sq_nonneg ε); linarith
    linarith
  have hE4 : L * c3 ≤ σ * ε ^ 2 / 100 := by
    have h1 := mul_le_mul_of_nonneg_left c3h hL.le
    have e1 : L * (σ * ε ^ 2 / (100 * L)) = σ * ε ^ 2 / 100 := by field_simp
    linarith
  have p1 : L * (-((σ + 1) / (4 * L)) * a ^ 2) = -((σ + 1) / 4 * a ^ 2) := by field_simp
  have p2 : L * (σ / (2 * L) * c ^ 2) = σ / 2 * c ^ 2 := by field_simp
  have p3 : L * (a2 * δ2) = a2 * (L * δ2) := by ring
  have p4 : L * (L / 2 * δ2 ^ 2) = (L * δ2) ^ 2 / 2 := by ring
  have p5 : L * (σ / (2 * L) * e ^ 2) = σ * e ^ 2 / 2 := by field_simp
  have h1 : f2 - f0 ≤ -((σ + 1) / (4 * L)) * a ^ 2 - σ / (2 * L) * c ^ 2 + a2 * δ2 +
      L / 2 * δ2 ^ 2 + σ / (2 * L) * e ^ 2 + σ / (2 * L) * e ^ 2 + c3 := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hL.le
  have e1 : L * (-((σ + 1) / (4 * L)) * a ^ 2 - σ / (2 * L) * c ^ 2 + a2 * δ2 +
      L / 2 * δ2 ^ 2 + σ / (2 * L) * e ^ 2 + σ / (2 * L) * e ^ 2 + c3) =
      L * (-((σ + 1) / (4 * L)) * a ^ 2) - L * (σ / (2 * L) * c ^ 2) + L * (a2 * δ2) +
        L * (L / 2 * δ2 ^ 2) + L * (σ / (2 * L) * e ^ 2) + L * (σ / (2 * L) * e ^ 2) + L * c3 := by
    ring
  rw [e1, p1, p2, p3, p4, p5] at h2
  have hfin : σ * ε ^ 2 / 25 ≤ L * (f0 - f2) := by
    have e2 : L * (f0 - f2) = -(L * (f2 - f0)) := by ring
    have h0 : 0 ≤ σ * ε ^ 2 := by positivity
    rw [e2]
    linarith
  rw [div_le_iff₀ (by positivity)]
  linarith

end Algebra

section Local

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {f : E → ℝ} {L ρ : ℝ} {x0 : E} (hyp : Hyp f L ρ x0)
variable (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
  (hc : ∀ j v, ⟪b j, fderiv ℝ (gradient f) x0 v⟫ = eig j * ⟪b j, v⟫)

include hyp hc

omit [DecidableEq ι] in
lemma eig_range (j : ι) (hj : 0 ≤ eig j) : 0 ≤ eig j / L ∧ eig j / L ≤ 1 := by
  have h := eig_le_norm b eig _ hc j
  have hL := hyp.hL
  refine ⟨div_nonneg hj hL.le, (div_le_one hL).mpr ?_⟩
  have := abs_le.mp (h.trans hyp.hH)
  linarith [this.2]

lemma lift_bound (hs : List ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : ∀ μ, 0 ≤ μ → μ ≤ 1 → |pr μ hs| ≤ W) (u : E) :
    ‖lin (fderiv ℝ (gradient f) x0) L hs (P b eig u)‖ ≤ W * ‖P b eig u‖ :=
  lin_bound b eig _ hc L hs hW
    (fun j hj => hb _ (eig_range hyp b eig hc j hj).1 (eig_range hyp b eig hc j hj).2) u

omit hc in
lemma err_bound (x : E) {D : ℝ} (hx : ‖x - x0‖ ≤ D) :
    ‖gradient f x - gradient f x0 - fderiv ℝ (gradient f) x0 (x - x0)‖ ≤ ρ * D ^ 2 / 2 := by
  have h := LongTails.Proofs.CubicRegularization.gradient_taylor hyp.hg hyp.hA x0 (x - x0)
  rw [add_sub_cancel] at h
  have hD : ‖x - x0‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have := mul_le_mul_of_nonneg_left hD hyp.hρ
  linarith

omit hc in
lemma model_bound (x : E) {D : ℝ} (hx : ‖x - x0‖ ≤ D) :
    f x ≤ f x0 + (⟪gradient f x0, x - x0⟫ + ⟪x - x0, fderiv ℝ (gradient f) x0 (x - x0)⟫ / 2) +
      ρ * D ^ 3 / 6 := by
  have h := LongTails.Proofs.CubicRegularization.objective_taylor hyp.hf hyp.hg hyp.hA x0 (x - x0)
  rw [add_sub_cancel] at h
  have hD : ‖x - x0‖ ^ 3 ≤ D ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hx 3
  have := mul_le_mul_of_nonneg_left hD hyp.hρ
  have := (abs_le.mp h).2
  linarith

lemma exact_grad_le (hs : List ℝ) (hb : ∀ μ, 0 ≤ μ → μ ≤ 1 → |pr μ hs| ≤ 1) :
    ‖P b eig (gradient f x0 + fderiv ℝ (gradient f) x0
      (run (fun y => (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0))) hs x0 - x0))‖ ≤
      ‖gradient f x0‖ := by
  set H := fderiv ℝ (gradient f) x0
  set g0 := gradient f x0
  have hsq : ‖P b eig (g0 + H (run (fun y => (1 / L) • (g0 + H (y - x0))) hs x0 - x0))‖ ^ 2 ≤
      ‖P b eig (g0 + H 0)‖ ^ 2 := by
    rw [grad_coords b eig H hc, grad_coords b eig H hc]
    apply Finset.sum_le_sum
    intro j _
    rw [coord_run b eig H hc L g0 x0 hs x0 j, sub_self, inner_zero_right,
      grad_run L _ _ hyp.hL, mul_zero, add_zero]
    by_cases hj : 0 ≤ eig j
    · have hr := eig_range hyp b eig hc j hj
      have hp := hb _ hr.1 hr.2
      have : pr (eig j / L) hs ^ 2 ≤ 1 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (pr (eig j / L) hs)]
      have hcj := cpos_nonneg eig j
      rw [mul_pow]
      nlinarith [sq_nonneg ⟪b j, g0⟫, mul_nonneg hcj (sq_nonneg ⟪b j, g0⟫)]
    · simp [cpos, hj]
  rw [map_zero, add_zero] at hsq
  have h1 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  exact h1.trans (P_norm_le b eig g0)

lemma exact_phi_prefix (hs : List ℝ) (hpos : ∀ h ∈ hs, 0 ≤ h)
    (hb : ∀ μ, 0 ≤ μ → μ ≤ 1 → |pr μ hs| ≤ 1) :
    phiPart b eig (fderiv ℝ (gradient f) x0) (gradient f x0)
      (run (fun y => (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0))) hs x0 - x0)
      ≤ 0 := by
  rw [phi_coords b eig _ hc]
  apply Finset.sum_nonpos
  intro j _
  rw [coord_run b eig _ hc L _ x0 hs x0 j, sub_self, inner_zero_right]
  by_cases hj : 0 ≤ eig j
  · have hr := eig_range hyp b eig hc j hj
    have := q1_prefix_nonpos (β := ⟪b j, gradient f x0⟫) hyp.hL hj hs hpos (hb _ hr.1 hr.2)
    exact mul_nonpos_of_nonneg_of_nonpos (cpos_nonneg eig j) this
  · simp [cpos, hj]

lemma exact_phi_cycle {K : ℕ} (hK : 2 ≤ K) :
    phiPart b eig (fderiv ℝ (gradient f) x0) (gradient f x0)
      (run (fun y => (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0)))
        (steps K ++ steps K) x0 - x0) ≤
      -(((steps K).sum + 1) / (4 * L)) *
        ‖P b eig (gradient f x0 + fderiv ℝ (gradient f) x0
          (run (fun y => (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0)))
            (steps K) x0 - x0))‖ ^ 2 := by
  rw [phi_coords b eig _ hc, grad_coords b eig _ hc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [coord_run b eig _ hc L _ x0 _ x0 j, coord_run b eig _ hc L _ x0 _ x0 j, sub_self,
    inner_zero_right, grad_run L _ _ hyp.hL]
  by_cases hj : 0 ≤ eig j
  · have hr := eig_range hyp b eig hc j hj
    have hle : eig j ≤ L := by
      have := hr.2; rwa [div_le_one hyp.hL] at this
    have := q1_cycle (β := ⟪b j, gradient f x0⟫) hyp.hL hj hle hK
    have hcj : cpos eig j = 1 := by simp [cpos, hj]
    rw [hcj, one_mul, one_mul]
    linarith
  · simp [cpos, hj]

omit hyp [DecidableEq ι] in
lemma lin_zero (hs : List ℝ) : lin (fderiv ℝ (gradient f) x0) L hs (0 : E) = 0 := by
  have := lin_smul b eig _ hc L hs 0 (0 : E)
  simpa using this

omit hyp hc in
lemma gn_gl (y : E) :
    (1 / L) • gradient f y - (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0)) =
      (1 / L) • (gradient f y - gradient f x0 - fderiv ℝ (gradient f) x0 (y - x0)) := by
  rw [← smul_sub]; congr 1; abel

lemma dev_bound (hs : List ℝ) (hpos : ∀ h ∈ hs, 0 ≤ h) {W e : ℝ} (hW : 0 ≤ W)
    (hsuf : ∀ s, s <:+ hs → ∀ μ, 0 ≤ μ → μ ≤ 1 → |pr μ s| ≤ W)
    (herr : ∀ t < hs.length, ‖gradient f (run (fun y => (1 / L) • gradient f y) (hs.take t) x0) -
      gradient f x0 - fderiv ℝ (gradient f) x0
        (run (fun y => (1 / L) • gradient f y) (hs.take t) x0 - x0)‖ ≤ e) :
    ‖P b eig (run (fun y => (1 / L) • gradient f y) hs x0 -
      run (fun y => (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0))) hs x0)‖ ≤
        W * (hs.sum * (e / L)) := by
  have hL := hyp.hL
  have hd := duhamel b eig (fderiv ℝ (gradient f) x0) hc L (fun y => (1 / L) • gradient f y)
    (fun y => (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0)))
    (fun y y' => by simp only [map_sub, smul_sub, smul_add]; abel) hW hs hpos
    (fun s hs' u => lift_bound hyp b eig hc s hW (hsuf s hs') u) x0 x0
  rw [sub_self, map_zero, lin_zero b eig hc, sub_zero] at hd
  refine hd.trans (mul_le_mul_of_nonneg_left ?_ hW)
  apply esum_le _ _ hs x0 hpos
  intro t ht
  rw [gn_gl]
  calc ‖P b eig ((1 / L) • (gradient f (run (fun y => (1 / L) • gradient f y) (hs.take t) x0) -
        gradient f x0 - fderiv ℝ (gradient f) x0
          (run (fun y => (1 / L) • gradient f y) (hs.take t) x0 - x0)))‖
      ≤ ‖(1 / L) • (gradient f (run (fun y => (1 / L) • gradient f y) (hs.take t) x0) -
        gradient f x0 - fderiv ℝ (gradient f) x0
          (run (fun y => (1 / L) • gradient f y) (hs.take t) x0 - x0))‖ := P_norm_le b eig _
    _ = (1 / L) * ‖gradient f (run (fun y => (1 / L) • gradient f y) (hs.take t) x0) -
        gradient f x0 - fderiv ℝ (gradient f) x0
          (run (fun y => (1 / L) • gradient f y) (hs.take t) x0 - x0)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (1 / L) * e := mul_le_mul_of_nonneg_left (herr t ht) (by positivity)
    _ = e / L := by ring

omit [DecidableEq ι] hc in
lemma node_grad (hs : List ℝ) {Mg : ℝ}
    (hmax : ∀ t < hs.length, ‖gradient f (run (fun y => (1 / L) • gradient f y) (hs.take t) x0)‖ ≤ Mg)
    (t : ℕ) (ht : t < hs.length) :
    ‖(fun y => (1 / L) • gradient f y) (run (fun y => (1 / L) • gradient f y) (hs.take t) x0)‖ ≤
      Mg / L := by
  have hL := hyp.hL
  calc ‖(fun y => (1 / L) • gradient f y) (run (fun y => (1 / L) • gradient f y) (hs.take t) x0)‖
      = (1 / L) * ‖gradient f (run (fun y => (1 / L) • gradient f y) (hs.take t) x0)‖ := by
        simp only; rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (1 / L) * Mg := mul_le_mul_of_nonneg_left (hmax t ht) (by positivity)
    _ = Mg / L := by ring

theorem aborted {K : ℕ} (hK : 2 ≤ K) {G Mg : ℝ} (hG0 : ‖gradient f x0‖ ≤ G)
    {m : ℕ} (hm : m ≤ (steps K ++ steps K).length)
    (hmax : ∀ t < m, ‖gradient f (run (fun y => (1 / L) • gradient f y)
      ((steps K ++ steps K).take t) x0)‖ ≤ Mg)
    (b1 : 16 * (steps K).sum ^ 2 * (ρ * (2 * (steps K).sum * Mg / L) ^ 2 / 2) ≤ Mg)
    (b2 : 2 * G ≤ Mg)
    (b3 : ρ * (2 * (steps K).sum * Mg / L) ^ 3 / 6 ≤ Mg ^ 2 / (32 * L)) :
    f (run (fun y => (1 / L) • gradient f y) ((steps K ++ steps K).take m) x0) ≤
      f x0 + Mg ^ 2 / (8 * L) := by
  have hL := hyp.hL
  obtain ⟨hσ1, hwin⟩ := sigma_ge K hK
  have hG : 0 ≤ G := (norm_nonneg _).trans hG0
  have hMg : 0 ≤ Mg := by linarith
  obtain ⟨hs, hhs⟩ : ∃ hs, hs = (steps K ++ steps K).take m := ⟨_, rfl⟩
  rw [← hhs]
  have hpre : hs <+: steps K ++ steps K := by rw [hhs]; exact List.take_prefix _ _
  have hpos : ∀ h ∈ hs, 0 ≤ h := fun h hh => steps_nonneg K h (hpre.subset hh)
  have hlen : hs.length = m := by rw [hhs, List.length_take]; omega
  have hsum : hs.sum ≤ 2 * (steps K).sum := by
    have h1 := List.sum_take_add_sum_drop (steps K ++ steps K) m
    have h2 : 0 ≤ ((steps K ++ steps K).drop m).sum :=
      List.sum_nonneg (fun h hh => steps_nonneg K h (List.mem_of_mem_drop hh))
    rw [cycle_sum] at h1
    rw [hhs]; linarith
  have hmax' : ∀ t < hs.length,
      ‖gradient f (run (fun y => (1 / L) • gradient f y) (hs.take t) x0)‖ ≤ Mg := by
    intro t ht
    have e : hs.take t = (steps K ++ steps K).take t := by
      rw [hhs, List.take_take, min_eq_left (by omega)]
    rw [e]; exact hmax t (by omega)
  have htravel : ∀ t ≤ hs.length,
      ‖run (fun y => (1 / L) • gradient f y) (hs.take t) x0 - x0‖ ≤ 2 * (steps K).sum * Mg / L := by
    intro t ht
    have h1 := travel_prefix (fun y => (1 / L) • gradient f y) hs x0 hpos
      (node_grad hyp hs hmax') t ht
    have h2 : hs.sum * (Mg / L) ≤ 2 * (steps K).sum * (Mg / L) :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    have e : 2 * (steps K).sum * (Mg / L) = 2 * (steps K).sum * Mg / L := by ring
    linarith
  have herr : ∀ t < hs.length, ‖gradient f (run (fun y => (1 / L) • gradient f y) (hs.take t) x0) -
      gradient f x0 - fderiv ℝ (gradient f) x0
        (run (fun y => (1 / L) • gradient f y) (hs.take t) x0 - x0)‖ ≤
        ρ * (2 * (steps K).sum * Mg / L) ^ 2 / 2 :=
    fun t ht => err_bound hyp _ (htravel t ht.le)
  have hdev := dev_bound hyp b eig hc hs hpos (W := (steps K).sum) (by linarith)
    (fun s hs' μ h0 h1 => (cycle_infix h0 h1 K ((hs'.isInfix).trans hpre.isInfix)).trans hwin) herr
  have hdm : ‖run (fun y => (1 / L) • gradient f y) hs x0 - x0‖ ≤ 2 * (steps K).sum * Mg / L := by
    have := htravel hs.length le_rfl
    rwa [List.take_length] at this
  have hmodel := model_bound hyp _ hdm
  rw [model_split b eig _ hc] at hmodel
  have hphi := phi_dev b eig _ hc hyp.hsym hyp.hH (gradient f x0)
    (run (fun y => (1 / L) • gradient f y) hs x0 - x0)
    (run (fun y => (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0))) hs x0 - x0)
  have hdd : run (fun y => (1 / L) • gradient f y) hs x0 - x0 -
      (run (fun y => (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0))) hs x0 - x0) =
      run (fun y => (1 / L) • gradient f y) hs x0 -
        run (fun y => (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0))) hs x0 := by
    abel
  rw [hdd] at hphi
  have hphi0 := exact_phi_prefix hyp b eig hc hs hpos (fun μ h0 h1 => cycle_prefix h0 h1 K hpre)
  have hgrad := exact_grad_le hyp b eig hc hs (fun μ h0 h1 => cycle_prefix h0 h1 K hpre)
  have hpsi := psi_run_upper b eig _ hc hyp.hsym L hL (gradient f) (gradient f x0) x0 hs x0 hpos herr
  have hpsi0 : psiPart b eig (fderiv ℝ (gradient f) x0) (gradient f x0) (x0 - x0) = 0 := by
    simp [psiPart]
  rw [hpsi0] at hpsi
  exact abort_algebra hL hσ1 (by have := hyp.hρ; positivity) hG hsum (norm_nonneg _) hmodel hphi
    hphi0 (hgrad.trans hG0) hpsi hdev b1 b2 b3

theorem completed {K : ℕ} (hK : 2 ≤ K) {G Mg ε : ℝ} (hε : 0 ≤ ε) (hG0 : ‖gradient f x0‖ ≤ G)
    (hmax : ∀ t < (steps K ++ steps K).length, ‖gradient f (run (fun y => (1 / L) • gradient f y)
      ((steps K ++ steps K).take t) x0)‖ ≤ Mg)
    (hjunc : ε ≤ ‖gradient f (run (fun y => (1 / L) • gradient f y) (steps K) x0)‖)
    (c1 : (steps K).sum * (ρ * (2 * (steps K).sum * Mg / L) ^ 2 / 2) ≤ ε / 16)
    (c2 : G ≤ 2 * (steps K).sum * ε / 25)
    (c3 : ρ * (2 * (steps K).sum * Mg / L) ^ 3 / 6 ≤ (steps K).sum * ε ^ 2 / (100 * L)) :
    (steps K).sum * ε ^ 2 / (25 * L) ≤
      f x0 - f (run (fun y => (1 / L) • gradient f y) (steps K ++ steps K) x0) := by
  have hL := hyp.hL
  obtain ⟨hσ1, -⟩ := sigma_ge K hK
  have hG : 0 ≤ G := (norm_nonneg _).trans hG0
  have hpos := steps_nonneg K
  have hpos1 : ∀ h ∈ steps K, 0 ≤ h := fun h hh => (steps_positive K h hh).le
  have htravel : ∀ t ≤ (steps K ++ steps K).length,
      ‖run (fun y => (1 / L) • gradient f y) ((steps K ++ steps K).take t) x0 - x0‖ ≤
        2 * (steps K).sum * Mg / L := by
    intro t ht
    have h1 := travel_prefix (fun y => (1 / L) • gradient f y) (steps K ++ steps K) x0 hpos
      (node_grad hyp _ hmax) t ht
    rw [cycle_sum] at h1
    have e : 2 * (steps K).sum * (Mg / L) = 2 * (steps K).sum * Mg / L := by ring
    linarith
  have herr : ∀ t < (steps K ++ steps K).length,
      ‖gradient f (run (fun y => (1 / L) • gradient f y) ((steps K ++ steps K).take t) x0) -
        gradient f x0 - fderiv ℝ (gradient f) x0
          (run (fun y => (1 / L) • gradient f y) ((steps K ++ steps K).take t) x0 - x0)‖ ≤
        ρ * (2 * (steps K).sum * Mg / L) ^ 2 / 2 :=
    fun t ht => err_bound hyp _ (htravel t ht.le)
  have hn : (steps K ++ steps K).length = (steps K).length + (steps K).length := List.length_append
  have htake : ∀ t ≤ (steps K).length, (steps K ++ steps K).take t = (steps K).take t := by
    intro t ht
    rw [List.take_append_of_le_length ht]
  have herr1 : ∀ t < (steps K).length,
      ‖gradient f (run (fun y => (1 / L) • gradient f y) ((steps K).take t) x0) -
        gradient f x0 - fderiv ℝ (gradient f) x0
          (run (fun y => (1 / L) • gradient f y) ((steps K).take t) x0 - x0)‖ ≤
        ρ * (2 * (steps K).sum * Mg / L) ^ 2 / 2 := by
    intro t ht
    rw [← htake t ht.le]; exact herr t (by omega)
  have hsplit2 : ∀ t ≤ (steps K).length,
      run (fun y => (1 / L) • gradient f y) ((steps K).take t)
        (run (fun y => (1 / L) • gradient f y) (steps K) x0) =
      run (fun y => (1 / L) • gradient f y) ((steps K ++ steps K).take ((steps K).length + t)) x0 := by
    intro t ht
    have e : (steps K ++ steps K).take ((steps K).length + t) = steps K ++ (steps K).take t := by
      rw [List.take_append, List.take_of_length_le
        (show (steps K).length ≤ (steps K).length + t by omega),
        show (steps K).length + t - (steps K).length = t by omega]
    rw [e, run_append]
  have herr2 : ∀ t < (steps K).length,
      ‖gradient f (run (fun y => (1 / L) • gradient f y) ((steps K).take t)
          (run (fun y => (1 / L) • gradient f y) (steps K) x0)) -
        gradient f x0 - fderiv ℝ (gradient f) x0
          (run (fun y => (1 / L) • gradient f y) ((steps K).take t)
            (run (fun y => (1 / L) • gradient f y) (steps K) x0) - x0)‖ ≤
        ρ * (2 * (steps K).sum * Mg / L) ^ 2 / 2 := by
    intro t ht
    rw [hsplit2 t ht.le]; exact herr _ (by omega)
  have hx2 : run (fun y => (1 / L) • gradient f y) (steps K ++ steps K) x0 =
      run (fun y => (1 / L) • gradient f y) (steps K)
        (run (fun y => (1 / L) • gradient f y) (steps K) x0) := run_append _ _ _ _
  have hd2 : ‖run (fun y => (1 / L) • gradient f y) (steps K ++ steps K) x0 - x0‖ ≤
      2 * (steps K).sum * Mg / L := by
    have := htravel _ le_rfl
    rwa [List.take_length] at this
  have hdn : ‖run (fun y => (1 / L) • gradient f y) (steps K) x0 - x0‖ ≤
      2 * (steps K).sum * Mg / L := by
    have := htravel (steps K).length (by omega)
    rwa [htake _ le_rfl, List.take_length] at this
  have hen : ‖gradient f (run (fun y => (1 / L) • gradient f y) (steps K) x0) - gradient f x0 -
      fderiv ℝ (gradient f) x0 (run (fun y => (1 / L) • gradient f y) (steps K) x0 - x0)‖ ≤
      ρ * (2 * (steps K).sum * Mg / L) ^ 2 / 2 := err_bound hyp _ hdn
  have hdev1 := dev_bound hyp b eig hc (steps K) hpos1 (W := 1) zero_le_one
    (fun s hs' μ h0 h1 => suffix_bound h0 h1 K hs') herr1
  have hdev2 := dev_bound hyp b eig hc (steps K ++ steps K) hpos (W := 1) zero_le_one
    (fun s hs' μ h0 h1 => cycle_suffix h0 h1 K hs') herr
  rw [one_mul] at hdev1 hdev2
  rw [cycle_sum] at hdev2
  have hmodel := model_bound hyp _ hd2
  rw [model_split b eig _ hc] at hmodel
  have hphi := phi_dev b eig _ hc hyp.hsym hyp.hH (gradient f x0)
    (run (fun y => (1 / L) • gradient f y) (steps K ++ steps K) x0 - x0)
    (run (fun y => (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0)))
      (steps K ++ steps K) x0 - x0)
  have hdd : ∀ u v : E, u - x0 - (v - x0) = u - v := fun u v => by abel
  rw [hdd] at hphi
  have hphi0 := exact_phi_cycle hyp b eig hc hK
  have hgrad2 := exact_grad_le hyp b eig hc (steps K ++ steps K)
    (fun μ h0 h1 => cycle_prefix h0 h1 K (List.prefix_refl _))
  have hpsi1 := psi_run_upper b eig _ hc hyp.hsym L hL (gradient f) (gradient f x0) x0 (steps K)
    x0 hpos1 herr1
  have hpsi0 : psiPart b eig (fderiv ℝ (gradient f) x0) (gradient f x0) (x0 - x0) = 0 := by
    simp [psiPart]
  rw [hpsi0] at hpsi1
  have hpsi2 := psi_run_lower b eig _ hc hyp.hsym L hL hyp.hH (gradient f) (gradient f x0) x0
    (by have := hyp.hρ; positivity) (steps K) (run (fun y => (1 / L) • gradient f y) (steps K) x0) _
    hpos1 herr2
    le_rfl
  rw [← hx2] at hpsi2
  have hjn : ε ≤ ‖P b eig (gradient f x0 + fderiv ℝ (gradient f) x0
        (run (fun y => (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0))) (steps K) x0
          - x0))‖ +
      L * ‖P b eig (run (fun y => (1 / L) • gradient f y) (steps K) x0 -
        run (fun y => (1 / L) • (gradient f x0 + fderiv ℝ (gradient f) x0 (y - x0))) (steps K) x0)‖ +
      ‖uq b eig (fderiv ℝ (gradient f) x0) (gradient f x0)
        (run (fun y => (1 / L) • gradient f y) (steps K) x0 - x0)‖ +
      ρ * (2 * (steps K).sum * Mg / L) ^ 2 / 2 := by
    obtain ⟨H, hH⟩ : ∃ H, H = fderiv ℝ (gradient f) x0 := ⟨_, rfl⟩
    obtain ⟨g0, hg0⟩ : ∃ g0, g0 = gradient f x0 := ⟨_, rfl⟩
    obtain ⟨xn, hxn⟩ : ∃ xn, xn = run (fun y => (1 / L) • gradient f y) (steps K) x0 := ⟨_, rfl⟩
    obtain ⟨yn, hyn⟩ : ∃ yn, yn = run (fun y => (1 / L) • (gradient f x0 +
      fderiv ℝ (gradient f) x0 (y - x0))) (steps K) x0 := ⟨_, rfl⟩
    rw [← hxn] at hen
    rw [← hH, ← hg0] at hen
    rw [← hxn] at hjunc
    rw [← hyn, ← hxn, ← hH, ← hg0]
    have hcH : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫ := by rw [hH]; exact hc
    have hsplit : gradient f xn = P b eig (g0 + H (yn - x0)) + H (P b eig (xn - yn)) +
        uq b eig H g0 (xn - x0) + (gradient f xn - g0 - H (xn - x0)) := by
      unfold uq
      have hc' : P b eig (g0 + H (xn - x0)) = P b eig (g0 + H (yn - x0)) + H (P b eig (xn - yn)) := by
        rw [P_comm b eig H hcH, ← map_add]
        congr 1
        simp only [map_sub]
        abel
      rw [hc']
      abel
    have hH' : ‖H‖ ≤ L := by rw [hH]; exact hyp.hH
    have h2 : ‖H (P b eig (xn - yn))‖ ≤ L * ‖P b eig (xn - yn)‖ :=
      (H.le_opNorm _).trans (mul_le_mul_of_nonneg_right hH' (norm_nonneg _))
    have h3 : ‖P b eig (g0 + H (yn - x0)) + H (P b eig (xn - yn)) + uq b eig H g0 (xn - x0) +
        (gradient f xn - g0 - H (xn - x0))‖ ≤ ‖P b eig (g0 + H (yn - x0))‖ +
        ‖H (P b eig (xn - yn))‖ + ‖uq b eig H g0 (xn - x0)‖ + ‖gradient f xn - g0 - H (xn - x0)‖ :=
      norm_add₄_le
    rw [← hsplit] at h3
    linarith
  exact complete_algebra hL hσ1 (by have := hyp.hρ; positivity) hG hε
    (norm_nonneg _) hmodel hphi hphi0 (hgrad2.trans hG0) hpsi1 hpsi2 hjn hdev1 hdev2 c1 c2 c3

end Local

end LongTails.Proofs.AdaptiveSilverLocal
