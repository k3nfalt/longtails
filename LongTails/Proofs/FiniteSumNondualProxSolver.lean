import LongTails.Proofs.FiniteSumNondualProxEpoch
import LongTails.Proofs.FiniteSumNondualProxExecution

open Set
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.FiniteSumNondualProxSolver

open FiniteSumNondualProxGeometry FiniteSumNondualProxStep FiniteSumNondualProxEpoch
open FiniteSumNondualProxExecution
open RecursiveEnvelopeGeometry (Model)
open LongTails.Algorithms.FiniteSumNondualProx
open OracleTemplate.ComponentEnvelope (Program)
open OracleTemplate.FiniteSum (fullGradient)
open LongTails.Setups.FiniteSumSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [NeZero n]

lemma initial_gap {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    {L μ R : ℝ} {f : E → ℝ} {g : E → E} (hf : Model L f g) (hμ : 0 ≤ μ)
    (hR : 0 ≤ R) (c u : E) (hu : u ∈ C) (hdist : ‖c - u‖ ≤ 2 * R) :
    regularized f μ c (step C μ (1 / L) c c (g c)) - regularized f μ c u ≤ 2 * L * R ^ 2 := by
  have hL := hf.pos
  have he : (1 / L) * L = 1 := by field_simp
  have ht := exact_step_gap hne hco hcv hf hμ (one_div_pos.mpr hL) he.le c c u hu
  have hs := sq_le_sq₀ (norm_nonneg _) (show 0 ≤ 2 * R by positivity) |>.mpr hdist
  have hh := mul_le_mul_of_nonneg_left ht hL.le
  field_simp at hh
  nlinarith [mul_le_mul_of_nonneg_left hs hL.le]

omit [NeZero n] in
lemma solver_certificate {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    {L μ : ℝ} (hL : 0 < L) (hμ : 0 ≤ μ) (g : Fin n × E → E) (c : E)
    (s : ℕ) (seed : Fin s → Fin (144 * n) → Fin n) :
    let out := Program.eval g (solvePlan C L μ c s seed)
    out.point ∈ C ∧ out.gradient = fullGradient g out.point ∧
      ∃ v, Normal C out.point v ∧
        regularizedGradient (fullGradient g) μ c out.point + v = out.error := by
  rw [solvePlan_eval]
  dsimp only
  let initial := step C μ (1 / L) c c (fullGradient g c)
  let x := epochRun g C μ (1 / (12 * L)) c s initial seed
  let w := step C μ (1 / L) c x (fullGradient g x)
  refine ⟨step_mem hne hco hcv _ _ _ _ _, rfl,
    normalVector μ (1 / L) c x w (fullGradient g x), ?_, ?_⟩
  · exact step_normal hne hco hcv hμ (one_div_pos.mpr hL) c x (fullGradient g x)
  · exact residual_identity μ (1 / L) c x w (fullGradient g x) (fullGradient g w)

lemma expected_residual_squared {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L R : ℝ} {f : Fin n → E → ℝ} {g : Fin n × E → E}
    (hm : ∀ i, Model L (f i) (fun x => g (i, x))) (hR : 0 ≤ R)
    (c u : E) (hu : u ∈ C) (hdist : ‖c - u‖ ≤ 2 * R)
    (hmin : IsMinOn (regularized (objective f) (L / n) c) C u) (s : ℕ) :
    (𝔼 seed : Fin s → Fin (144 * n) → Fin n,
      ‖(Program.eval g (solvePlan C L (L / n) c s seed)).error‖ ^ 2) ≤
        16 * L ^ 2 * R ^ 2 * (3 / 4 : ℝ) ^ s := by
  have hf := OracleTemplate.ComponentEnvelope.finiteSum_model hm
  have hL := hf.pos
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hμ : 0 ≤ L / n := (div_pos hL hn).le
  let initial := step C (L / n) (1 / L) c c (fullGradient g c)
  have hi : initial ∈ C := step_mem hne hco hcv _ _ _ _ _
  have hinit := initial_gap hne hco hcv hf hμ hR c u hu hdist
  have ht := tuned_run_contraction hne hco hcv hm c u hu hmin s initial hi
  have hb := Finset.expect_le_expect (s := Finset.univ)
    (fun (seed : Fin s → Fin (144 * n) → Fin n) _ =>
      certificate_squared hne hco hcv hf hμ c
        (epochRun g C (L / n) (1 / (12 * L)) c s initial seed) u
        (epochRun_mem hne hco hcv g _ _ c (Nat.mul_pos (by decide : 0 < 144) (NeZero.pos n))
          s initial hi seed) hmin)
  simp only [← Finset.mul_expect] at hb
  simp only [solvePlan_eval]
  change (𝔼 seed : Fin s → Fin (144 * n) → Fin n,
    ‖LongTails.Algorithms.FiniteSumNondualProx.residual (1 / L)
      (epochRun g C (L / n) (1 / (12 * L)) c s initial seed)
      (step C (L / n) (1 / L) c (epochRun g C (L / n) (1 / (12 * L)) c s initial seed)
        (fullGradient g (epochRun g C (L / n) (1 / (12 * L)) c s initial seed)))
      (fullGradient g (epochRun g C (L / n) (1 / (12 * L)) c s initial seed))
      (fullGradient g (step C (L / n) (1 / L) c
        (epochRun g C (L / n) (1 / (12 * L)) c s initial seed)
        (fullGradient g (epochRun g C (L / n) (1 / (12 * L)) c s initial seed))))‖ ^ 2) ≤ _
  have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 8 * L by positivity)
  have hi' := mul_le_mul_of_nonneg_left hinit
    (show 0 ≤ 8 * L * (3 / 4 : ℝ) ^ s by positivity)
  dsimp only [initial] at ht hh hb
  simp only [Finset.expect_sub_distrib, Fintype.expect_const] at hb hh
  dsimp only [initial]
  nlinarith

omit [NeZero n] [InnerProductSpace ℝ E] in
lemma finite_markov {α : Type*} [Fintype α] (r : α → E)
    {B q ρ : ℝ} (hρ : 0 < ρ) (hmean : (𝔼 a, ‖r a‖ ^ 2) ≤ B)
    (hB : B ≤ q * ρ ^ 2) : (𝔼 a, if ρ < ‖r a‖ then (1 : ℝ) else 0) ≤ q := by
  have hp (a : α) : (if ρ < ‖r a‖ then (1 : ℝ) else 0) * ρ ^ 2 ≤ ‖r a‖ ^ 2 := by
    split_ifs with h
    · simp only [one_mul]
      exact (sq_le_sq₀ hρ.le (norm_nonneg _)).mpr h.le
    · simp only [zero_mul]; positivity
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun a _ => hp a)
  rw [← Finset.expect_mul] at hh
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hρ)).mp (hh.trans (hmean.trans hB))

lemma solver_failure_fraction {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L R q ρ : ℝ} {f : Fin n → E → ℝ} {g : Fin n × E → E}
    (hm : ∀ i, Model L (f i) (fun x => g (i, x))) (hR : 0 ≤ R)
    (c u : E) (hu : u ∈ C) (hdist : ‖c - u‖ ≤ 2 * R)
    (hmin : IsMinOn (regularized (objective f) (L / n) c) C u) (s : ℕ) (hρ : 0 < ρ)
    (hsmall : 16 * L ^ 2 * R ^ 2 * (3 / 4 : ℝ) ^ s ≤ q * ρ ^ 2) :
    (𝔼 seed : Fin s → Fin (144 * n) → Fin n,
      if ρ < ‖(Program.eval g (solvePlan C L (L / n) c s seed)).error‖ then (1 : ℝ) else 0) ≤ q :=
  finite_markov _ hρ (expected_residual_squared hne hco hcv hm hR c u hu hdist hmin s) hsmall

end LongTails.Proofs.FiniteSumNondualProxSolver
