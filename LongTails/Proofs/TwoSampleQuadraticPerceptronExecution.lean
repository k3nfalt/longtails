import LongTails.Proofs.TwoSampleQuadraticPerceptronMoves
import LongTails.Proofs.QuadraticPerceptronStopping

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSampleQuadraticPerceptronExecution

open LongTails.Setups.TwoSampleQuadraticPerceptron
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
open LongTails.Proofs.QuadraticPerceptronCone

def embedState (σ : ℝ) (c : Coordinates) (n : ℕ) : State :=
  ⟨σ * (c.p + c.q), σ * (c.p - c.q), -σ * c.z, c.r - c.y, c.r + c.y, n⟩

noncomputable def gains (m : Model) (d : ℕ) (D : Data d) (γ : ℝ) : Gains :=
  ⟨γ * (eigenvalues m d D).first, γ * (eigenvalues m d D).second, γ * (eigenvalues m d D).coupling,
    γ * (eigenvalues m d D).slow⟩

open Classical in
noncomputable def modelStep (m : Model) (d : ℕ) (D : Data d) (γ : ℝ) (θ : Space m d) : Space m d :=
  if margin m d D.positive θ ≤ 0 then move m d θ γ (direction m d D.positive θ)
  else if -margin m d D.negative θ ≤ 0 then move m d θ γ (negate m d (direction m d D.negative θ))
  else θ

section Correspondence

variable {m : Model} {d : ℕ} (D : Data d) (hD : InClass m d D) {σ : ℝ} (hσ : σ ^ 2 = 1)
  {γ : ℝ} (hγ : 0 < γ) (hs1 : 0 < (eigenvalues m d D).first)

include hD hσ hs1 in
lemma first_iff (θ : Space m d) (n : ℕ) :
    margin m d D.positive θ ≤ 0 ↔
      (embedState σ (coordinates m d D θ) n).a ^ 2 ≤
        (embedState σ (coordinates m d D θ) n).b ^ 2 := by
  rw [margin_positive D hD]
  simp only [embedState]
  set c := coordinates m d D θ
  have e : (σ * (c.p + c.q)) ^ 2 - (σ * (c.p - c.q)) ^ 2 = 4 * (c.p * c.q) := by
    linear_combination (4 * (c.p * c.q)) * hσ
  constructor
  · intro h
    have : c.p * c.q ≤ 0 := by
      by_contra hc; push Not at hc
      have := mul_pos hs1 hc; nlinarith
    nlinarith
  · intro h
    have : c.p * c.q ≤ 0 := by nlinarith
    have := mul_nonpos_of_nonneg_of_nonpos hs1.le this
    nlinarith

include hD hσ in
lemma test_eq (θ : Space m d) (n : ℕ) :
    (gains m d D γ).test (embedState σ (coordinates m d D θ) n) =
      4 * γ * margin m d D.negative θ := by
  rw [margin_negative D hD]
  simp only [Gains.test, gains, embedState]
  set c := coordinates m d D θ
  set s := eigenvalues m d D
  linear_combination (4 * γ * (s.second * c.p * c.q + s.coupling * c.p * c.z)) * hσ

include hD hσ hγ hs1 in
lemma step_embed (θ : Space m d) (n : ℕ) : ∃ n',
    (gains m d D γ).step (embedState σ (coordinates m d D θ) n) =
      embedState σ (coordinates m d D (modelStep m d D γ θ)) n' := by
  have hf := first_iff D hD hσ hs1 θ n
  have ht := test_eq D hD hσ (γ := γ) θ n
  by_cases h1 : margin m d D.positive θ ≤ 0
  · refine ⟨n, ?_⟩
    rw [Gains.step_opt1 (hf.mp h1)]
    simp only [modelStep, h1, ↓reduceIte]
    rw [coordinates_first D hD]
    simp only [Gains.opt1, gains, embedState]
    congr 1 <;> ring
  · by_cases h2 : -margin m d D.negative θ ≤ 0
    · refine ⟨n + 1, ?_⟩
      have h2' : 0 ≤ (gains m d D γ).test (embedState σ (coordinates m d D θ) n) := by
        rw [ht]; nlinarith
      rw [Gains.step_opt2 (fun h => h1 (hf.mpr h)) h2']
      simp only [modelStep, h1, h2, ↓reduceIte]
      rw [coordinates_second D hD]
      simp only [Gains.opt2, gains, embedState]
      congr 1 <;> ring
    · refine ⟨n, ?_⟩
      have hs : (gains m d D γ).Stopped (embedState σ (coordinates m d D θ) n) := by
        refine ⟨fun h => h1 (hf.mpr h), ?_⟩
        rw [ht]; push Not at h2; nlinarith
      rw [Gains.step_stopped hs]
      simp only [modelStep, h1, h2, ↓reduceIte]

include hD hσ hγ hs1 in
lemma separates_iff (θ : Space m d) (n : ℕ) :
    Separates m d D θ ↔ (gains m d D γ).Stopped (embedState σ (coordinates m d D θ) n) := by
  have hf := first_iff D hD hσ hs1 θ n
  have ht := test_eq D hD hσ (γ := γ) θ n
  unfold Separates Gains.Stopped
  rw [ht, ← hf, not_le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hc; push Not at hc; nlinarith

include hD hσ hγ hs1 in
lemma traj_embed (θ0 : Space m d) (t : ℕ) : ∃ n,
    (gains m d D γ).traj (embedState σ (coordinates m d D θ0) 0) t =
      embedState σ (coordinates m d D ((modelStep m d D γ)^[t] θ0)) n := by
  induction t with
  | zero => exact ⟨0, rfl⟩
  | succ t ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨n', hn'⟩ := step_embed D hD hσ hγ hs1 ((modelStep m d D γ)^[t] θ0) n
      refine ⟨n', ?_⟩
      rw [Gains.traj_succ, hn, hn', Function.iterate_succ_apply']

end Correspondence

end LongTails.Proofs.TwoSampleQuadraticPerceptronExecution
