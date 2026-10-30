import LongTails.Proofs.AdaptiveSilverDynamics

namespace LongTails.Proofs.AdaptiveSilverModel

open scoped RealInnerProductSpace
open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.AdaptiveSilverScalar
open LongTails.Proofs.AdaptiveSilverSplit

noncomputable def run1 (L β lam : ℝ) : List ℝ → ℝ → ℝ
  | [], y => y
  | h :: hs, y => run1 L β lam hs (y - h / L * (β + lam * y))

noncomputable def acc (μ : ℝ) : List ℝ → ℝ
  | [] => 0
  | h :: hs => h + (1 - h * μ) * acc μ hs

lemma run1_formula (L β lam : ℝ) (hL : 0 < L) (hs : List ℝ) (y : ℝ) :
    run1 L β lam hs y = y - (β + lam * y) * acc (lam / L) hs / L := by
  induction hs generalizing y with
  | nil => simp [run1, acc]
  | cons h t ih =>
    simp only [run1, ih, acc]
    field_simp
    ring

lemma acc_identity (μ : ℝ) (hs : List ℝ) : μ * acc μ hs = 1 - pr μ hs := by
  induction hs with
  | nil => simp [acc, pr_nil]
  | cons h t ih =>
    simp only [acc, pr_cons]
    linear_combination (1 - h * μ) * ih

lemma acc_zero (hs : List ℝ) : acc 0 hs = hs.sum := by
  induction hs with
  | nil => simp [acc]
  | cons h t ih => simp [acc, ih]

lemma acc_nonneg {μ : ℝ} (h0 : 0 ≤ μ) (hs : List ℝ) (hpos : ∀ h ∈ hs, 0 ≤ h)
    (hp : |pr μ hs| ≤ 1) : 0 ≤ acc μ hs := by
  rcases h0.lt_or_eq with hμ | hμ
  · have := acc_identity μ hs
    have hle : pr μ hs ≤ 1 := (abs_le.mp hp).2
    nlinarith
  · subst hμ
    rw [acc_zero]
    exact List.sum_nonneg hpos

noncomputable def q1 (β lam y : ℝ) : ℝ := β * y + lam * y ^ 2 / 2

lemma q1_run (L β lam : ℝ) (hL : 0 < L) (hs : List ℝ) :
    q1 β lam (run1 L β lam hs 0) =
      -(β ^ 2 * acc (lam / L) hs / L) * (1 + pr (lam / L) hs) / 2 := by
  rw [run1_formula L β lam hL]
  have hi := acc_identity (lam / L) hs
  obtain ⟨A, hA⟩ : ∃ A, A = acc (lam / L) hs := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = pr (lam / L) hs := ⟨_, rfl⟩
  rw [← hA, ← hP] at hi ⊢
  have key : lam * A = L * (1 - P) := by
    rw [← hi]; field_simp
  unfold q1
  simp only [mul_zero, add_zero, zero_sub]
  have e : lam * (-(β * A / L)) ^ 2 / 2 = β ^ 2 * A * (lam * A) / (2 * L ^ 2) := by ring
  rw [e, key]
  field_simp
  ring

lemma grad_run (L β lam : ℝ) (hL : 0 < L) (hs : List ℝ) :
    β + lam * run1 L β lam hs 0 = pr (lam / L) hs * β := by
  rw [run1_formula L β lam hL]
  have hi := acc_identity (lam / L) hs
  have : lam * acc (lam / L) hs / L = 1 - pr (lam / L) hs := by
    rw [← hi]; field_simp
  simp only [mul_zero, add_zero, zero_sub]
  linear_combination (-β) * this

lemma q1_prefix_nonpos {L β lam : ℝ} (hL : 0 < L) (h0 : 0 ≤ lam)
    (hs : List ℝ) (hpos : ∀ h ∈ hs, 0 ≤ h) (hp : |pr (lam / L) hs| ≤ 1) :
    q1 β lam (run1 L β lam hs 0) ≤ 0 := by
  rw [q1_run L β lam hL]
  have ha := acc_nonneg (div_nonneg h0 hL.le) hs hpos hp
  have hp' : 0 ≤ 1 + pr (lam / L) hs := by linarith [(abs_le.mp hp).1]
  have h1 : 0 ≤ β ^ 2 * acc (lam / L) hs / L * (1 + pr (lam / L) hs) := by positivity
  have e : -(β ^ 2 * acc (lam / L) hs / L) * (1 + pr (lam / L) hs) / 2 =
      -(β ^ 2 * acc (lam / L) hs / L * (1 + pr (lam / L) hs)) / 2 := by ring
  rw [e]
  linarith

lemma pr_zero (hs : List ℝ) : pr 0 hs = 1 := by
  induction hs with
  | nil => rfl
  | cons h t ih => rw [pr_cons, ih]; ring

lemma q1_cycle {L β lam : ℝ} (hL : 0 < L) (h0 : 0 ≤ lam) (h1 : lam ≤ L) {K : ℕ} (hK : 2 ≤ K) :
    q1 β lam (run1 L β lam (steps K ++ steps K) 0) ≤
      -(((steps K).sum + 1) / (4 * L)) * (pr (lam / L) (steps K) * β) ^ 2 := by
  have hμ0 : 0 ≤ lam / L := div_nonneg h0 hL.le
  have hμ1 : lam / L ≤ 1 := (div_le_one hL).mpr h1
  have hps := prefix_bound hμ0 hμ1 K (List.prefix_refl (steps K))
  have hcert := block_certificate hμ0 hμ1 hK
  have hsum := steps_sum K
  rw [q1_run L β lam hL]
  obtain ⟨p, hp⟩ : ∃ p, p = pr (lam / L) (steps K) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = acc (lam / L) (steps K ++ steps K) := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = (steps K).sum := ⟨_, rfl⟩
  have hpp : pr (lam / L) (steps K ++ steps K) = p ^ 2 := by rw [pr_append, ← hp]; ring
  have hi : lam / L * A = 1 - p ^ 2 := by rw [hA, acc_identity, hpp]
  rw [← hp, ← hσ] at hcert
  rw [← hp] at hps
  rw [← hσ] at hsum
  rw [← hA, hpp, ← hp, ← hσ]
  have hp2 : p ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hps
  have hσ1 : 1 ≤ σ := by
    have hr := ratio_gt_two
    have : ratio ^ 2 ≤ ratio ^ K := pow_le_pow_right₀ (by linarith) hK
    nlinarith
  have hkey : 0 ≤ A ∧ (σ + 1) * p ^ 2 ≤ 2 * A := by
    rcases hμ0.lt_or_eq with hμ | hμ
    · have hA0 : 0 ≤ A := by
        have : 0 ≤ lam / L * A := by rw [hi]; linarith
        exact (mul_nonneg_iff_of_pos_left hμ).mp this
      refine ⟨hA0, ?_⟩
      have : (σ + 1) * p ^ 2 * (lam / L) ≤ 2 * A * (lam / L) := by nlinarith
      exact le_of_mul_le_mul_right this hμ
    · have hp1 : p = 1 := by rw [hp, ← hμ, pr_zero]
      have hA2 : A = 2 * σ := by rw [hA, ← hμ, acc_zero, List.sum_append, hσ]; ring
      rw [hp1, hA2]
      constructor <;> nlinarith
  obtain ⟨hA0, hk⟩ := hkey
  have hk2 : (σ + 1) * p ^ 2 * β ^ 2 ≤ 2 * A * (1 + p ^ 2) * β ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg β)
    nlinarith [sq_nonneg p]
  have e1 : -(β ^ 2 * A / L) * (1 + p ^ 2) / 2 = -(2 * A * (1 + p ^ 2) * β ^ 2) / (4 * L) := by
    field_simp; ring
  have e2 : -((σ + 1) / (4 * L)) * (p * β) ^ 2 = -((σ + 1) * p ^ 2 * β ^ 2) / (4 * L) := by
    field_simp
  rw [e1, e2, neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right hk2 (by positivity)

section Vector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (H : E →L[ℝ] E)
  (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)

include hc

omit [DecidableEq ι] in
lemma coord_run (L : ℝ) (g0 x0 : E) (hs : List ℝ) (x : E) (j : ι) :
    ⟪b j, run (fun y => (1 / L) • (g0 + H (y - x0))) hs x - x0⟫ =
      run1 L ⟪b j, g0⟫ (eig j) hs ⟪b j, x - x0⟫ := by
  induction hs generalizing x with
  | nil => simp [run, run1]
  | cons h t ih =>
    simp only [run, run1]
    rw [ih]
    congr 1
    have e : x - h • (1 / L) • (g0 + H (x - x0)) - x0 = (x - x0) - (h / L) • (g0 + H (x - x0)) := by
      module
    rw [e, inner_sub_right, inner_smul_right, inner_add_right, hc]

lemma phi_coords (g0 d : E) :
    LongTails.Proofs.AdaptiveSilverDynamics.phiPart b eig H g0 d =
      ∑ j, cpos eig j * q1 ⟪b j, g0⟫ (eig j) ⟪b j, d⟫ := by
  unfold LongTails.Proofs.AdaptiveSilverDynamics.phiPart
  rw [inner_coords b g0, inner_coords b (P b eig d), Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [P_coord', hc, P_coord']
  have h2 := cpos_sq eig j
  unfold q1
  have : cpos eig j * ⟪b j, d⟫ * (eig j * (cpos eig j * ⟪b j, d⟫)) =
      eig j * (cpos eig j * cpos eig j) * ⟪b j, d⟫ ^ 2 := by ring
  rw [this, h2]
  ring

lemma grad_coords (g0 d : E) :
    ‖P b eig (g0 + H d)‖ ^ 2 = ∑ j, cpos eig j * (⟪b j, g0⟫ + eig j * ⟪b j, d⟫) ^ 2 := by
  rw [norm_sq_coords b]
  apply Finset.sum_congr rfl
  intro j _
  rw [P_coord', inner_add_right, hc, mul_pow]
  have h2 := cpos_sq eig j
  rw [sq (cpos eig j), h2]

end Vector

end LongTails.Proofs.AdaptiveSilverModel
