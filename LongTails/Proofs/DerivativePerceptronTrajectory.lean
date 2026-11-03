import LongTails.Proofs.DerivativePerceptronControl
import LongTails.Proofs.ClusteredConvolutionalPerceptronDynamics

open scoped RealInnerProductSpace

namespace LongTails.Proofs.DerivativePerceptronTrajectory

open ManySampleConvolutionalPerceptronDynamics (State)
open ClusteredConvolutionalPerceptronDynamics (step)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma step_energy (b δ : ℝ) (p r : E) (x : State E)
    (hg : b * x.a * x.q + δ * (x.a * ⟪p, x.z⟫ + x.t * ⟪r, x.z⟫) ≤ 0) :
    δ * ‖(step b δ p r x).z‖ ^ 2 + (step b δ p r x).a ^ 2 ≤
      δ * ‖x.z‖ ^ 2 + x.a ^ 2 + δ * ‖x.a • p + x.t • r‖ ^ 2 +
        b ^ 2 * x.q ^ 2 + 2 * δ * (x.a + b * x.q) * ⟪p, x.z⟫ +
        δ ^ 2 * ⟪p, x.z⟫ ^ 2 := by
  have hn := norm_add_sq_real x.z (x.a • p + x.t • r)
  simp only [inner_add_right, real_inner_smul_right] at hn
  rw [← real_inner_comm x.z p, ← real_inner_comm x.z r] at hn
  have he := congrArg (fun v : ℝ => δ * v) hn
  simp only [step, add_assoc] at ⊢
  nlinarith

lemma step_residual_norm (b δ : ℝ) (p r : E) (x : State E)
    (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1) :
    ‖(step b δ p r x).z‖ ≤ ‖x.z‖ + |x.a| + |x.t| := by
  have hs := ManySampleConvolutionalPerceptronDynamics.residual_step_norm
    (a := x.a) (t := x.t) hp hr
  have hn := norm_add_le x.z (x.a • p + x.t • r)
  change ‖x.z + x.a • p + x.t • r‖ ≤ _
  rw [add_assoc]
  linarith

lemma step_signal_drift (b δ : ℝ) (p r : E) (x : State E)
    (hδ : 0 ≤ δ) (hr : ‖r‖ ≤ 1) :
    |(step b δ p r x).t - x.t| ≤ δ * ‖x.z‖ := by
  have hi := abs_real_inner_le_norm r x.z
  have hb : |⟪r, x.z⟫| ≤ ‖x.z‖ := by nlinarith [norm_nonneg x.z]
  change |x.t + δ * ⟪r, x.z⟫ - x.t| ≤ _
  rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hδ]
  exact mul_le_mul_of_nonneg_left hb hδ

lemma step_projection (b δ κ : ℝ) (p r w : E) (x : State E)
    (hp : ‖p‖ ≤ 1) (hw : ‖w‖ = 1) (hr : κ ≤ ⟪r, w⟫) (ht : 0 ≤ x.t) :
    ⟪x.z, w⟫ + x.t * κ - |x.a| ≤ ⟪(step b δ p r x).z, w⟫ := by
  have hi := abs_real_inner_le_norm p w
  rw [hw, mul_one] at hi
  have hip : |⟪p, w⟫| ≤ 1 := hi.trans hp
  have hm := mul_le_mul_of_nonneg_left hip (abs_nonneg x.a)
  have hn := neg_le_abs (x.a * ⟪p, w⟫)
  rw [abs_mul] at hn
  have htκ := mul_le_mul_of_nonneg_left hr ht
  change _ ≤ ⟪x.z + x.a • p + x.t • r, w⟫
  simp only [inner_add_left, real_inner_smul_left]
  linarith

lemma prefix_norm_signal (x : ℕ → State E) (b : ℕ → ℝ) (p r : ℕ → E)
    (δ : ℝ) (N : ℕ) (hδ : 0 ≤ δ) (hz₀ : (x 0).z = 0) (ht₀ : (x 0).t = 1)
    (hu : ∀ k < N, x (k + 1) = step (b k) δ (p k) (r k) (x k))
    (hp : ∀ k < N, ‖p k‖ ≤ 1) (hr : ∀ k < N, ‖r k‖ ≤ 1)
    (ha : ∀ k < N, |(x k).a| ≤ 2) (ht : ∀ k < N, |(x k).t| ≤ 2) :
    ∀ k ≤ N, ‖(x k).z‖ ≤ 4 * (k : ℝ) ∧ |(x k).t - 1| ≤ 4 * δ * (k : ℝ) ^ 2 := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [hz₀, ht₀]
  | succ k ih =>
    intro hk
    have hkN : k < N := by omega
    obtain ⟨hz, hts⟩ := ih (by omega)
    have hn := step_residual_norm (b k) δ (p k) (r k) (x k) (hp k hkN) (hr k hkN)
    have hd := step_signal_drift (b k) δ (p k) (r k) (x k) hδ (hr k hkN)
    rw [← hu k hkN] at hn hd
    have htri := abs_add_le ((x (k + 1)).t - (x k).t) ((x k).t - 1)
    have he : (x (k + 1)).t - (x k).t + ((x k).t - 1) = (x (k + 1)).t - 1 := by ring
    rw [he] at htri
    have hmul := mul_le_mul_of_nonneg_left hz hδ
    have hk₀ : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    constructor
    · push_cast
      linarith [ha k hkN, ht k hkN]
    · push_cast
      nlinarith

lemma scalar_inputs (b δ A T Z : ℝ) (p r : E) (x : State E)
    (hδ : 0 ≤ δ) (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    (ha : |x.a| ≤ A) (ht : |x.t| ≤ T) (hz : ‖x.z‖ ≤ Z)
    (hg : b * x.a * x.q + δ * (x.a * ⟪p, x.z⟫ + x.t * ⟪r, x.z⟫) ≤ 0) :
    |δ * ⟪p, x.z⟫| ≤ δ * Z ∧ b * x.a * x.q ≤ δ * (A + T) * Z := by
  have hA : 0 ≤ A := (abs_nonneg x.a).trans ha
  have hT : 0 ≤ T := (abs_nonneg x.t).trans ht
  have hip : |⟪p, x.z⟫| ≤ Z := by
    have hh := abs_real_inner_le_norm p x.z
    nlinarith [norm_nonneg x.z]
  have hir : |⟪r, x.z⟫| ≤ Z := by
    have hh := abs_real_inner_le_norm r x.z
    nlinarith [norm_nonneg x.z]
  constructor
  · rw [abs_mul, abs_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_left hip hδ
  · have hap := mul_le_mul ha hip (abs_nonneg _) hA
    have htr := mul_le_mul ht hir (abs_nonneg _) hT
    have hpa := neg_le_abs (x.a * ⟪p, x.z⟫)
    have hrt := neg_le_abs (x.t * ⟪r, x.z⟫)
    rw [abs_mul] at hpa hrt
    have hb : -(x.a * ⟪p, x.z⟫ + x.t * ⟪r, x.z⟫) ≤ (A + T) * Z := by
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hb hδ
    nlinarith

lemma two_mistake_scalar (b b₁ δ ρ A T Z : ℝ) (p r p₁ r₁ : E)
    (x y z : State E) (hxy : y = step b δ p r x) (hyz : z = step b₁ δ p₁ r₁ y)
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hb : ρ ≤ |b|) (hb₁ : ρ ≤ |b₁|)
    (hbu : |b| ≤ 1 / 4) (hb₁u : |b₁| ≤ 1 / 4)
    (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1) (hp₁ : ‖p₁‖ ≤ 1) (hr₁ : ‖r₁‖ ≤ 1)
    (hx : max |x.a| |x.q| ≤ A) (hy : max |y.a| |y.q| ≤ A)
    (hxt : |x.t| ≤ T) (hyt : |y.t| ≤ T) (hxz : ‖x.z‖ ≤ Z) (hyz' : ‖y.z‖ ≤ Z)
    (hg : b * x.a * x.q + δ * (x.a * ⟪p, x.z⟫ + x.t * ⟪r, x.z⟫) ≤ 0)
    (hg₁ : b₁ * y.a * y.q + δ * (y.a * ⟪p₁, y.z⟫ + y.t * ⟪r₁, y.z⟫) ≤ 0) :
    (max |z.a| |z.q|) ^ 2 ≤ (1 - ρ ^ 2 / 8) * (max |x.a| |x.q|) ^ 2 +
      8 * (δ * (A + T) * Z) + 6 * A * (δ * Z) + 10 * (δ * Z) ^ 2 := by
  have hxa : |x.a| ≤ A := (le_max_left _ _).trans hx
  have hya : |y.a| ≤ A := (le_max_left _ _).trans hy
  obtain ⟨he, hs⟩ := scalar_inputs b δ A T Z p r x hδ hp hr hxa hxt hxz hg
  obtain ⟨he₁, hs₁⟩ := scalar_inputs b₁ δ A T Z p₁ r₁ y hδ hp₁ hr₁ hya hyt hyz' hg₁
  have hA : 0 ≤ A := (abs_nonneg x.a).trans hxa
  have hT : 0 ≤ T := (abs_nonneg x.t).trans hxt
  have hZ : 0 ≤ Z := (norm_nonneg x.z).trans hxz
  have hya' : y.a = x.a + b * x.q + δ * ⟪p, x.z⟫ := by rw [hxy]; rfl
  have hyq' : y.q = x.q + b * x.a := by rw [hxy]; rfl
  have hh := DerivativePerceptronControl.scalar_two_step x.a x.q y.a y.q b b₁
    (δ * ⟪p, x.z⟫) (δ * ⟪p₁, y.z⟫) ρ A (δ * Z) (δ * (A + T) * Z)
    hya' hyq' hρ hb hb₁ hbu hb₁u hx hy he he₁ (by positivity) hs hs₁
  rw [hyz]
  exact hh

lemma one_mistake_scalar (b δ A T Z : ℝ) (p r : E) (x : State E)
    (hδ : 0 ≤ δ) (hbu : |b| ≤ 1 / 4) (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    (hx : max |x.a| |x.q| ≤ A) (ht : |x.t| ≤ T) (hz : ‖x.z‖ ≤ Z)
    (hg : b * x.a * x.q + δ * (x.a * ⟪p, x.z⟫ + x.t * ⟪r, x.z⟫) ≤ 0) :
    (max |(step b δ p r x).a| |(step b δ p r x).q|) ^ 2 ≤
      (max |x.a| |x.q|) ^ 2 + 4 * (δ * (A + T) * Z) +
        3 * A * (δ * Z) + (δ * Z) ^ 2 := by
  have hxa : |x.a| ≤ A := (le_max_left _ _).trans hx
  obtain ⟨he, hs⟩ := scalar_inputs b δ A T Z p r x hδ hp hr hxa ht hz hg
  have hA : 0 ≤ A := (abs_nonneg x.a).trans hxa
  have hT : 0 ≤ T := (abs_nonneg x.t).trans ht
  have hZ : 0 ≤ Z := (norm_nonneg x.z).trans hz
  exact (DerivativePerceptronControl.perturbed_gated_square_control x.a x.q b
    (δ * ⟪p, x.z⟫) 0 A (δ * Z) (δ * (A + T) * Z)
    le_rfl (abs_nonneg b) hbu hx he (by positivity) hs).1

lemma prefix_scalar_bound (x : ℕ → State E) (b : ℕ → ℝ) (p r : ℕ → E)
    (δ ρ Z : ℝ) (N : ℕ) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hρu : ρ ≤ 1 / 4)
    (hZ : 0 ≤ Z) (he : δ * Z ≤ 1) (hsmall : 216 * δ * Z ≤ ρ ^ 2)
    (hx₀ : max |(x 0).a| |(x 0).q| ≤ 1)
    (hu : ∀ k < N, x (k + 1) = step (b k) δ (p k) (r k) (x k))
    (hp : ∀ k < N, ‖p k‖ ≤ 1) (hr : ∀ k < N, ‖r k‖ ≤ 1)
    (hb : ∀ k < N, ρ ≤ |b k|) (hbu : ∀ k < N, |b k| ≤ 1 / 4)
    (hx : ∀ k < N, max |(x k).a| |(x k).q| ≤ 2)
    (ht : ∀ k < N, |(x k).t| ≤ 2) (hz : ∀ k < N, ‖(x k).z‖ ≤ Z)
    (hg : ∀ k < N, b k * (x k).a * (x k).q +
      δ * ((x k).a * ⟪p k, (x k).z⟫ + (x k).t * ⟪r k, (x k).z⟫) ≤ 0) :
    max |(x N).a| |(x N).q| ≤ 2 := by
  let f : ℕ → ℝ := fun k => (max |(x k).a| |(x k).q|) ^ 2
  have he₀ : 0 ≤ δ * Z := mul_nonneg hδ hZ
  have hesq : (δ * Z) ^ 2 ≤ δ * Z := by nlinarith
  have hcoef : 0 ≤ 1 - ρ ^ 2 / 8 := by nlinarith
  have hB : 0 ≤ 54 * δ * Z := by positivity
  have hBH : 2 + 54 * δ * Z ≤ 4 := by nlinarith
  have hc : (1 - ρ ^ 2 / 8) * 2 + 54 * δ * Z ≤ 2 := by nlinarith
  have hf₀ : f 0 ≤ 2 := by
    have hm : 0 ≤ max |(x 0).a| |(x 0).q| :=
      (abs_nonneg _).trans (le_max_left _ _)
    dsimp [f]
    nlinarith
  have hone : ∀ k < N, f k ≤ 4 → f (k + 1) ≤ f k + 54 * δ * Z := by
    intro k hk _
    have hh := one_mistake_scalar (b k) δ 2 2 Z (p k) (r k) (x k)
      hδ (hbu k hk) (hp k hk) (hr k hk) (hx k hk) (ht k hk) (hz k hk) (hg k hk)
    rw [← hu k hk] at hh
    dsimp [f]
    nlinarith
  have htwo : ∀ k, k + 2 ≤ N → f k ≤ 4 → f (k + 1) ≤ 4 →
      f (k + 2) ≤ (1 - ρ ^ 2 / 8) * f k + 54 * δ * Z := by
    intro k hk _ _
    have hk₀ : k < N := by omega
    have hk₁ : k + 1 < N := by omega
    have hnext : x (k + 2) = step (b (k + 1)) δ (p (k + 1)) (r (k + 1)) (x (k + 1)) :=
      hu (k + 1) hk₁
    have hh := two_mistake_scalar (b k) (b (k + 1)) δ ρ 2 2 Z
      (p k) (r k) (p (k + 1)) (r (k + 1)) (x k) (x (k + 1)) (x (k + 2))
      (hu k hk₀) hnext hδ hρ (hb k hk₀) (hb (k + 1) hk₁)
      (hbu k hk₀) (hbu (k + 1) hk₁) (hp k hk₀) (hr k hk₀)
      (hp (k + 1) hk₁) (hr (k + 1) hk₁) (hx k hk₀) (hx (k + 1) hk₁)
      (ht k hk₀) (ht (k + 1) hk₁) (hz k hk₀) (hz (k + 1) hk₁)
      (hg k hk₀) (hg (k + 1) hk₁)
    dsimp [f]
    nlinarith
  have hh := DerivativePerceptronControl.two_step_envelope_all f N
    (1 - ρ ^ 2 / 8) (54 * δ * Z) 2 4 hcoef hB hBH hc hf₀ hone htwo N le_rfl
  dsimp [f] at hh
  have hm : 0 ≤ max |(x N).a| |(x N).q| := (abs_nonneg _).trans (le_max_left _ _)
  nlinarith

lemma warmup_bounds (x : ℕ → State E) (b : ℕ → ℝ) (p r : ℕ → E)
    (δ ρ : ℝ) (K : ℕ) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hρu : ρ ≤ 1 / 4)
    (hsmall : 864 * δ * (K : ℝ) ≤ ρ ^ 2) (hquadratic : δ * (K : ℝ) ^ 2 ≤ 1 / 16)
    (hx₀ : max |(x 0).a| |(x 0).q| ≤ 1) (hz₀ : (x 0).z = 0) (ht₀ : (x 0).t = 1)
    (hu : ∀ k < K, x (k + 1) = step (b k) δ (p k) (r k) (x k))
    (hp : ∀ k < K, ‖p k‖ ≤ 1) (hr : ∀ k < K, ‖r k‖ ≤ 1)
    (hb : ∀ k < K, ρ ≤ |b k|) (hbu : ∀ k < K, |b k| ≤ 1 / 4)
    (hg : ∀ k < K, b k * (x k).a * (x k).q +
      δ * ((x k).a * ⟪p k, (x k).z⟫ + (x k).t * ⟪r k, (x k).z⟫) ≤ 0) :
    ∀ n ≤ K, max |(x n).a| |(x n).q| ≤ 2 ∧
      |(x n).t - 1| ≤ 1 / 4 ∧ ‖(x n).z‖ ≤ 4 * (n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hprex : ∀ j < n, max |(x j).a| |(x j).q| ≤ 2 := by
      intro j hj
      exact (ih j hj (by omega)).1
    have hpret : ∀ j < n, |(x j).t| ≤ 2 := by
      intro j hj
      have ht := (ih j hj (by omega)).2.1
      have hh := abs_add_le ((x j).t - 1) (1 : ℝ)
      simp only [sub_add_cancel, abs_one] at hh
      linarith
    have hpn := prefix_norm_signal x b p r δ n hδ hz₀ ht₀
      (fun j hj => hu j (by omega)) (fun j hj => hp j (by omega))
      (fun j hj => hr j (by omega))
      (fun j hj => (le_max_left _ _).trans (hprex j hj)) hpret
    have hN₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hK₀ : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hnK : (n : ℝ) ≤ K := Nat.cast_le.mpr hn
    have hsq : (n : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 := by nlinarith
    have hδsq := mul_le_mul_of_nonneg_left hsq hδ
    have hsignal : |(x n).t - 1| ≤ 1 / 4 := by
      have hh := (hpn n le_rfl).2
      nlinarith
    have hscalar := prefix_scalar_bound x b p r δ ρ (4 * (K : ℝ)) n hδ hρ hρu
      (by positivity) (by nlinarith) (by nlinarith) hx₀
      (fun j hj => hu j (by omega)) (fun j hj => hp j (by omega))
      (fun j hj => hr j (by omega)) (fun j hj => hb j (by omega))
      (fun j hj => hbu j (by omega)) hprex hpret
      (fun j hj => by
        have hh := (hpn j (by omega)).1
        have hjK : (j : ℝ) ≤ K := Nat.cast_le.mpr (by omega)
        linarith)
      (fun j hj => hg j (by omega))
    exact ⟨hscalar, hsignal, (hpn n le_rfl).1⟩

lemma warmup_geometric (x : ℕ → State E) (b : ℕ → ℝ) (p r : ℕ → E)
    (δ ρ : ℝ) (K n : ℕ) (hδ : 0 ≤ δ) (hρ : 0 < ρ) (hρu : ρ ≤ 1 / 4)
    (he : δ * (4 * (K : ℝ)) ≤ 1) (hn : 2 * n ≤ K)
    (hx₀ : max |(x 0).a| |(x 0).q| ≤ 1)
    (hu : ∀ k < K, x (k + 1) = step (b k) δ (p k) (r k) (x k))
    (hp : ∀ k < K, ‖p k‖ ≤ 1) (hr : ∀ k < K, ‖r k‖ ≤ 1)
    (hb : ∀ k < K, ρ ≤ |b k|) (hbu : ∀ k < K, |b k| ≤ 1 / 4)
    (hx : ∀ k < K, max |(x k).a| |(x k).q| ≤ 2)
    (ht : ∀ k < K, |(x k).t| ≤ 2) (hz : ∀ k < K, ‖(x k).z‖ ≤ 4 * (K : ℝ))
    (hg : ∀ k < K, b k * (x k).a * (x k).q +
      δ * ((x k).a * ⟪p k, (x k).z⟫ + (x k).t * ⟪r k, (x k).z⟫) ≤ 0) :
    (max |(x (2 * n)).a| |(x (2 * n)).q|) ^ 2 ≤
      (1 - ρ ^ 2 / 8) ^ n + 1728 * δ * (K : ℝ) / ρ ^ 2 := by
  let f : ℕ → ℝ := fun k => (max |(x k).a| |(x k).q|) ^ 2
  have hcoef : 0 ≤ 1 - ρ ^ 2 / 8 := by nlinarith [hρ.le]
  have he₀ : 0 ≤ δ * (4 * (K : ℝ)) := by positivity
  have hesq : (δ * (4 * (K : ℝ))) ^ 2 ≤ δ * (4 * (K : ℝ)) := by nlinarith
  have hstep : ∀ k, k + 2 ≤ K → f (k + 2) ≤
      (1 - ρ ^ 2 / 8) * f k + 216 * δ * (K : ℝ) := by
    intro k hk
    have hk₀ : k < K := by omega
    have hk₁ : k + 1 < K := by omega
    have hh := two_mistake_scalar (b k) (b (k + 1)) δ ρ 2 2 (4 * (K : ℝ))
      (p k) (r k) (p (k + 1)) (r (k + 1)) (x k) (x (k + 1)) (x (k + 2))
      (hu k hk₀) (hu (k + 1) hk₁) hδ hρ.le (hb k hk₀) (hb (k + 1) hk₁)
      (hbu k hk₀) (hbu (k + 1) hk₁) (hp k hk₀) (hr k hk₀)
      (hp (k + 1) hk₁) (hr (k + 1) hk₁) (hx k hk₀) (hx (k + 1) hk₁)
      (ht k hk₀) (ht (k + 1) hk₁) (hz k hk₀) (hz (k + 1) hk₁)
      (hg k hk₀) (hg (k + 1) hk₁)
    dsimp [f]
    nlinarith
  have hQid : (1 - (1 - ρ ^ 2 / 8)) * (1728 * δ * (K : ℝ) / ρ ^ 2) =
      216 * δ * (K : ℝ) := by
    field_simp
    ring
  have hh := DerivativePerceptronControl.even_geometric_bound f K n
    (1 - ρ ^ 2 / 8) (216 * δ * (K : ℝ)) (1728 * δ * (K : ℝ) / ρ ^ 2)
    hn hcoef (by positivity) (le_of_eq hQid.symm) hstep
  have hf₀ : f 0 ≤ 1 := by
    have hm : 0 ≤ max |(x 0).a| |(x 0).q| := (abs_nonneg _).trans (le_max_left _ _)
    dsimp [f]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hf₀ (pow_nonneg hcoef n)
  dsimp [f] at hh ⊢
  nlinarith

lemma prefix_small_scalar_bound (x : ℕ → State E) (b : ℕ → ℝ) (p r : ℕ → E)
    (δ ρ A Z : ℝ) (N : ℕ) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hρu : ρ ≤ 1 / 4)
    (hA : 0 ≤ A) (hAu : A ≤ 1) (hZ : 0 ≤ Z) (he : δ * Z ≤ 1) (hsmall : 640 * δ * Z ≤ ρ ^ 2 * A ^ 2)
    (hx₀ : (max |(x 0).a| |(x 0).q|) ^ 2 ≤ A ^ 2 / 4)
    (hu : ∀ k < N, x (k + 1) = step (b k) δ (p k) (r k) (x k))
    (hp : ∀ k < N, ‖p k‖ ≤ 1) (hr : ∀ k < N, ‖r k‖ ≤ 1)
    (hb : ∀ k < N, ρ ≤ |b k|) (hbu : ∀ k < N, |b k| ≤ 1 / 4)
    (hx : ∀ k < N, max |(x k).a| |(x k).q| ≤ A)
    (ht : ∀ k < N, |(x k).t| ≤ 2) (hz : ∀ k < N, ‖(x k).z‖ ≤ Z)
    (hg : ∀ k < N, b k * (x k).a * (x k).q +
      δ * ((x k).a * ⟪p k, (x k).z⟫ + (x k).t * ⟪r k, (x k).z⟫) ≤ 0) :
    max |(x N).a| |(x N).q| ≤ A := by
  let f : ℕ → ℝ := fun k => (max |(x k).a| |(x k).q|) ^ 2
  have he₀ : 0 ≤ δ * Z := mul_nonneg hδ hZ
  have hesq : (δ * Z) ^ 2 ≤ δ * Z := by nlinarith
  have hcoef : 0 ≤ 1 - ρ ^ 2 / 8 := by nlinarith
  have hB : 0 ≤ 40 * δ * Z := by positivity
  have hρsq : ρ ^ 2 ≤ 1 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hρsq (sq_nonneg A)
  have hAe := mul_le_mul_of_nonneg_right hAu he₀
  have hBH : A ^ 2 / 2 + 40 * δ * Z ≤ A ^ 2 := by nlinarith
  have hc : (1 - ρ ^ 2 / 8) * (A ^ 2 / 2) + 40 * δ * Z ≤ A ^ 2 / 2 := by nlinarith
  have hf₀ : f 0 ≤ A ^ 2 / 2 := by
    dsimp [f]
    nlinarith [sq_nonneg A]
  have hone : ∀ k < N, f k ≤ A ^ 2 → f (k + 1) ≤ f k + 40 * δ * Z := by
    intro k hk _
    have hh := one_mistake_scalar (b k) δ A 2 Z (p k) (r k) (x k)
      hδ (hbu k hk) (hp k hk) (hr k hk) (hx k hk) (ht k hk) (hz k hk) (hg k hk)
    rw [← hu k hk] at hh
    dsimp [f]
    nlinarith
  have htwo : ∀ k, k + 2 ≤ N → f k ≤ A ^ 2 → f (k + 1) ≤ A ^ 2 →
      f (k + 2) ≤ (1 - ρ ^ 2 / 8) * f k + 40 * δ * Z := by
    intro k hk _ _
    have hk₀ : k < N := by omega
    have hk₁ : k + 1 < N := by omega
    have hnext : x (k + 2) = step (b (k + 1)) δ (p (k + 1)) (r (k + 1)) (x (k + 1)) :=
      hu (k + 1) hk₁
    have hh := two_mistake_scalar (b k) (b (k + 1)) δ ρ A 2 Z
      (p k) (r k) (p (k + 1)) (r (k + 1)) (x k) (x (k + 1)) (x (k + 2))
      (hu k hk₀) hnext hδ hρ (hb k hk₀) (hb (k + 1) hk₁)
      (hbu k hk₀) (hbu (k + 1) hk₁) (hp k hk₀) (hr k hk₀)
      (hp (k + 1) hk₁) (hr (k + 1) hk₁) (hx k hk₀) (hx (k + 1) hk₁)
      (ht k hk₀) (ht (k + 1) hk₁) (hz k hk₀) (hz (k + 1) hk₁)
      (hg k hk₀) (hg (k + 1) hk₁)
    dsimp [f]
    nlinarith
  have hh := DerivativePerceptronControl.two_step_envelope_all f N
    (1 - ρ ^ 2 / 8) (40 * δ * Z) (A ^ 2 / 2) (A ^ 2) hcoef hB hBH hc hf₀ hone htwo N le_rfl
  dsimp [f] at hh
  have hm : 0 ≤ max |(x N).a| |(x N).q| := (abs_nonneg _).trans (le_max_left _ _)
  nlinarith

lemma small_scalar_envelope (x : ℕ → State E) (b : ℕ → ℝ) (p r : ℕ → E)
    (δ ρ A Z : ℝ) (N : ℕ) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hρu : ρ ≤ 1 / 4)
    (hA : 0 ≤ A) (hAu : A ≤ 1) (hZ : 0 ≤ Z) (he : δ * Z ≤ 1)
    (hsmall : 640 * δ * Z ≤ ρ ^ 2 * A ^ 2)
    (hx₀ : (max |(x 0).a| |(x 0).q|) ^ 2 ≤ A ^ 2 / 4)
    (hu : ∀ k < N, x (k + 1) = step (b k) δ (p k) (r k) (x k))
    (hp : ∀ k < N, ‖p k‖ ≤ 1) (hr : ∀ k < N, ‖r k‖ ≤ 1)
    (hb : ∀ k < N, ρ ≤ |b k|) (hbu : ∀ k < N, |b k| ≤ 1 / 4)
    (ht : ∀ k < N, |(x k).t| ≤ 2) (hz : ∀ k < N, ‖(x k).z‖ ≤ Z)
    (hg : ∀ k < N, b k * (x k).a * (x k).q +
      δ * ((x k).a * ⟪p k, (x k).z⟫ + (x k).t * ⟪r k, (x k).z⟫) ≤ 0) :
    ∀ n ≤ N, max |(x n).a| |(x n).q| ≤ A := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    exact prefix_small_scalar_bound x b p r δ ρ A Z n hδ hρ hρu hA hAu hZ he hsmall hx₀
      (fun j hj => hu j (by omega)) (fun j hj => hp j (by omega))
      (fun j hj => hr j (by omega)) (fun j hj => hb j (by omega))
      (fun j hj => hbu j (by omega)) (fun j hj => ih j hj (by omega))
      (fun j hj => ht j (by omega)) (fun j hj => hz j (by omega))
      (fun j hj => hg j (by omega))

lemma postwarm_plateau (x : ℕ → State E) (b : ℕ → ℝ) (p r : ℕ → E)
    (δ ρ : ℝ) (K n₀ : ℕ) (hδ : 0 < δ) (hρ : 0 < ρ) (hρu : ρ ≤ 1 / 4)
    (hK : 1 ≤ K) (he : δ * (4 * (K : ℝ)) ≤ 1)
    (hlog : Real.log (1 / δ) ≤ (ρ ^ 2 / 8) * (n₀ : ℝ))
    (hx₀ : max |(x 0).a| |(x 0).q| ≤ 1)
    (hu : ∀ k < K, x (k + 1) = step (b k) δ (p k) (r k) (x k))
    (hp : ∀ k < K, ‖p k‖ ≤ 1) (hr : ∀ k < K, ‖r k‖ ≤ 1)
    (hb : ∀ k < K, ρ ≤ |b k|) (hbu : ∀ k < K, |b k| ≤ 1 / 4)
    (hx : ∀ k < K, max |(x k).a| |(x k).q| ≤ 2)
    (ht : ∀ k < K, |(x k).t| ≤ 2) (hz : ∀ k < K, ‖(x k).z‖ ≤ 4 * (K : ℝ))
    (hg : ∀ k < K, b k * (x k).a * (x k).q +
      δ * ((x k).a * ⟪p k, (x k).z⟫ + (x k).t * ⟪r k, (x k).z⟫) ≤ 0) :
    ∀ k, 2 * n₀ ≤ k → k ≤ K → (max |(x k).a| |(x k).q|) ^ 2 ≤
      4096 * δ * (K : ℝ) / ρ ^ 2 := by
  have heven : ∀ j, n₀ ≤ j → 2 * j ≤ K →
      (max |(x (2 * j)).a| |(x (2 * j)).q|) ^ 2 ≤ 2048 * δ * (K : ℝ) / ρ ^ 2 := by
    intro j hj hjK
    have hgeom := warmup_geometric x b p r δ ρ K j hδ.le hρ hρu he hjK hx₀
      hu hp hr hb hbu hx ht hz hg
    have hcast : (n₀ : ℝ) ≤ j := Nat.cast_le.mpr hj
    have hm := mul_le_mul_of_nonneg_left hcast (show 0 ≤ ρ ^ 2 / 8 by positivity)
    exact DerivativePerceptronControl.plateau_after_log _ δ ρ K j hδ hρ
      (by linarith) hK (hlog.trans hm) hgeom
  have hratio : 0 ≤ δ * (K : ℝ) / ρ ^ 2 := by positivity
  have hδK : δ * (K : ℝ) ≤ δ * (K : ℝ) / ρ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    have hs : ρ ^ 2 ≤ 1 := by nlinarith [hρ.le]
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ δ * (K : ℝ) by positivity)
    nlinarith
  have hesq : (δ * (4 * (K : ℝ))) ^ 2 ≤ δ * (4 * (K : ℝ)) := by
    have hn : 0 ≤ δ * (4 * (K : ℝ)) := by positivity
    nlinarith
  intro k hk₀ hk
  have hbase := heven (k / 2) (by omega) (by omega)
  by_cases hmod : k % 2 = 0
  · have hEq : k = 2 * (k / 2) := by omega
    rw [← hEq] at hbase
    simp only [div_eq_mul_inv] at hbase hratio ⊢
    nlinarith
  · have hEq : k = 2 * (k / 2) + 1 := by omega
    have hj : 2 * (k / 2) < K := by omega
    have hh := one_mistake_scalar (b (2 * (k / 2))) δ 2 2 (4 * (K : ℝ))
      (p (2 * (k / 2))) (r (2 * (k / 2))) (x (2 * (k / 2))) hδ.le
      (hbu _ hj) (hp _ hj) (hr _ hj) (hx _ hj) (ht _ hj) (hz _ hj) (hg _ hj)
    rw [← hu _ hj, ← hEq] at hh
    simp only [div_eq_mul_inv] at hbase hratio hδK ⊢
    nlinarith

lemma trajectory_barriers (x : ℕ → State E) (b : ℕ → ℝ) (p r : ℕ → E)
    (δ ρ c A Z J D : ℝ) (N : ℕ) (hδ : 0 ≤ δ) (hρ : 0 < ρ)
    (hc : 0 ≤ c) (hc₁ : c ≤ 1) (hAu : A ≤ 1) (hZ : 0 ≤ Z)
    (hJ : 0 ≤ J) (hDJ : J ≤ D) (hforce : 4 * (δ * Z) * A ≤ ρ ^ 2 * J)
    (hD : (3 * δ * Z) / ρ + J + 2 * (3 * δ * Z) + 4 * c ^ 2 * (δ * Z) * A ≤ D)
    (hI₀ : (x 0).q ^ 2 - (x 0).a ^ 2 ≤ J)
    (hF₀ : (x 0).q ^ 2 - c ^ 2 * (x 0).a ^ 2 ≤ D)
    (hu : ∀ k < N, x (k + 1) = step (b k) δ (p k) (r k) (x k))
    (hp : ∀ k < N, ‖p k‖ ≤ 1) (hr : ∀ k < N, ‖r k‖ ≤ 1)
    (hb : ∀ k < N, ρ ≤ |b k|) (hbu : ∀ k < N, |b k| ≤ c)
    (hx : ∀ k < N, max |(x k).a| |(x k).q| ≤ A)
    (ht : ∀ k < N, |(x k).t| ≤ 2) (hz : ∀ k < N, ‖(x k).z‖ ≤ Z)
    (hg : ∀ k < N, b k * (x k).a * (x k).q +
      δ * ((x k).a * ⟪p k, (x k).z⟫ + (x k).t * ⟪r k, (x k).z⟫) ≤ 0) :
    ∀ n ≤ N, (x n).q ^ 2 - (x n).a ^ 2 ≤ J ∧
      (x n).q ^ 2 - c ^ 2 * (x n).a ^ 2 ≤ D := by
  intro n
  induction n with
  | zero => intro _; exact ⟨hI₀, hF₀⟩
  | succ n ih =>
    intro hn
    have hk : n < N := by omega
    obtain ⟨hI, hF⟩ := ih (by omega)
    have ha : |(x n).a| ≤ A := (le_max_left _ _).trans (hx n hk)
    have hq : |(x n).q| ≤ A := (le_max_right _ _).trans (hx n hk)
    obtain ⟨he, hs⟩ := scalar_inputs (b n) δ A 2 Z (p n) (r n) (x n)
      hδ (hp n hk) (hr n hk) ha (ht n hk) (hz n hk) (hg n hk)
    have hmul := mul_le_mul_of_nonneg_right hAu (mul_nonneg hδ hZ)
    have hg' : b n * (x n).a * (x n).q ≤ 3 * δ * Z := by nlinarith
    have hh := DerivativePerceptronControl.joint_barrier_step
      (x n).a (x n).q (b n) (δ * ⟪p n, (x n).z⟫) c A (δ * Z) ρ J (3 * δ * Z) D
      ha hq he hc (hbu n hk) hc₁ hρ (hb n hk) hJ hDJ hI hF hforce hg' hD
    rw [hu n hk]
    exact hh

lemma step_energy_bound (b δ c A Z P D : ℝ) (p r : E) (x : State E)
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hc₁ : c ≤ 1) (hb : |b| ≤ c)
    (hAu : A ≤ 1) (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    (hx : max |x.a| |x.q| ≤ A) (ht : |x.t| ≤ 2) (hz : ‖x.z‖ ≤ Z)
    (hP : x.a ^ 2 ≤ P) (hF : x.q ^ 2 - c ^ 2 * x.a ^ 2 ≤ D)
    (hg : b * x.a * x.q + δ * (x.a * ⟪p, x.z⟫ + x.t * ⟪r, x.z⟫) ≤ 0) :
    δ * ‖(step b δ p r x).z‖ ^ 2 + (step b δ p r x).a ^ 2 ≤
      δ * ‖x.z‖ ^ 2 + x.a ^ 2 + 9 * δ + 4 * δ * A * Z + δ ^ 2 * Z ^ 2 +
        c ^ 4 * P + c ^ 2 * D := by
  have ha : |x.a| ≤ A := (le_max_left _ _).trans hx
  have hq : |x.q| ≤ A := (le_max_right _ _).trans hx
  have hA : 0 ≤ A := (abs_nonneg x.a).trans ha
  have hZ : 0 ≤ Z := (norm_nonneg x.z).trans hz
  have hinc := ManySampleConvolutionalPerceptronDynamics.residual_step_norm
    (a := x.a) (t := x.t) hp hr
  have hincsq : ‖x.a • p + x.t • r‖ ^ 2 ≤ 9 := by
    nlinarith [norm_nonneg (x.a • p + x.t • r)]
  have hnorm := mul_le_mul_of_nonneg_left hincsq hδ
  have hinner : |⟪p, x.z⟫| ≤ Z := by
    have hi := abs_real_inner_le_norm p x.z
    nlinarith [norm_nonneg x.z]
  have hinner_sq : ⟪p, x.z⟫ ^ 2 ≤ Z ^ 2 := by
    nlinarith [sq_abs ⟪p, x.z⟫, abs_nonneg ⟪p, x.z⟫]
  have herr := mul_le_mul_of_nonneg_left hinner_sq (sq_nonneg δ)
  have hb₁ : |b| ≤ 1 := hb.trans hc₁
  have hsum : |x.a + b * x.q| ≤ 2 * A := by
    have hm := mul_le_mul_of_nonneg_right hb₁ (abs_nonneg x.q)
    have ht := abs_add_le x.a (b * x.q)
    rw [abs_mul] at ht
    linarith
  have hcross := mul_le_mul hsum hinner (abs_nonneg _) (show 0 ≤ 2 * A by positivity)
  have hcross' := le_abs_self ((x.a + b * x.q) * ⟪p, x.z⟫)
  rw [abs_mul] at hcross'
  have hcross'' : (x.a + b * x.q) * ⟪p, x.z⟫ ≤ 2 * A * Z := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hcross'' (show 0 ≤ 2 * δ by positivity)
  have hb₂ : b ^ 2 ≤ c ^ 2 := by nlinarith [sq_abs b, abs_nonneg b]
  have hqP := mul_le_mul_of_nonneg_left hP (sq_nonneg c)
  have hqbound : x.q ^ 2 ≤ c ^ 2 * P + D := by linarith
  have hq₁ := mul_le_mul_of_nonneg_right hb₂ (sq_nonneg x.q)
  have hq₂ := mul_le_mul_of_nonneg_left hqbound (sq_nonneg c)
  have he := step_energy b δ p r x hg
  nlinarith

lemma energy_sum (x : ℕ → State E) (b : ℕ → ℝ) (p r : ℕ → E)
    (δ c A Z P D : ℝ) (N : ℕ) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hc₁ : c ≤ 1)
    (hAu : A ≤ 1)
    (hu : ∀ k < N, x (k + 1) = step (b k) δ (p k) (r k) (x k))
    (hp : ∀ k < N, ‖p k‖ ≤ 1) (hr : ∀ k < N, ‖r k‖ ≤ 1)
    (hbu : ∀ k < N, |b k| ≤ c)
    (hx : ∀ k < N, max |(x k).a| |(x k).q| ≤ A)
    (ht : ∀ k < N, |(x k).t| ≤ 2) (hz : ∀ k < N, ‖(x k).z‖ ≤ Z)
    (hP : ∀ k < N, (x k).a ^ 2 ≤ P)
    (hF : ∀ k < N, (x k).q ^ 2 - c ^ 2 * (x k).a ^ 2 ≤ D)
    (hg : ∀ k < N, b k * (x k).a * (x k).q +
      δ * ((x k).a * ⟪p k, (x k).z⟫ + (x k).t * ⟪r k, (x k).z⟫) ≤ 0) :
    δ * ‖(x N).z‖ ^ 2 + (x N).a ^ 2 ≤ δ * ‖(x 0).z‖ ^ 2 + (x 0).a ^ 2 +
      (N : ℝ) * (9 * δ + 4 * δ * A * Z + δ ^ 2 * Z ^ 2 + c ^ 4 * P + c ^ 2 * D) := by
  apply DerivativePerceptronControl.additive_bound
    (fun k => δ * ‖(x k).z‖ ^ 2 + (x k).a ^ 2) N
  intro k hk
  have hh := step_energy_bound (b k) δ c A Z P D (p k) (r k) (x k)
    hδ hc hc₁ (hbu k hk) hAu (hp k hk) (hr k hk) (hx k hk) (ht k hk) (hz k hk)
    (hP k hk) (hF k hk) (hg k hk)
  rw [← hu k hk] at hh
  linarith

lemma projection_sum (x : ℕ → State E) (b : ℕ → ℝ) (p r : ℕ → E)
    (δ κ : ℝ) (w : E) (N : ℕ) (hκ : 0 ≤ κ) (hw : ‖w‖ = 1)
    (hu : ∀ k < N, x (k + 1) = step (b k) δ (p k) (r k) (x k))
    (hp : ∀ k < N, ‖p k‖ ≤ 1) (hr : ∀ k < N, κ ≤ ⟪r k, w⟫)
    (ha : ∀ k < N, |(x k).a| ≤ κ / 4) (ht : ∀ k < N, 1 / 2 ≤ (x k).t) :
    ⟪(x 0).z, w⟫ + (N : ℝ) * κ / 4 ≤ ⟪(x N).z, w⟫ := by
  have hh := DerivativePerceptronControl.additive_bound (fun k => -⟪(x k).z, w⟫) N (-κ / 4)
    (fun k hk => by
      have hs := step_projection (b k) δ κ (p k) (r k) w (x k) (hp k hk) hw (hr k hk)
        (by linarith [ht k hk])
      rw [← hu k hk] at hs
      have hm := mul_le_mul_of_nonneg_right (ht k hk) hκ
      linarith [ha k hk])
  nlinarith

lemma projection_norm_lower (z₀ z w : E) (κ K K₀ N : ℝ)
    (hw : ‖w‖ = 1) (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1)
    (hK : 0 ≤ K) (hK₀ : 0 ≤ K₀) (htotal : K = N + K₀)
    (hz₀ : ‖z₀‖ ≤ 4 * K₀) (hsize : 64 * K₀ ≤ κ * K)
    (hprogress : ⟪z₀, w⟫ + N * κ / 4 ≤ ⟪z, w⟫) :
    κ ^ 2 * K ^ 2 / 64 ≤ ‖z‖ ^ 2 := by
  have hi₀ := abs_real_inner_le_norm z₀ w
  have hi := abs_real_inner_le_norm z w
  rw [hw, mul_one] at hi₀ hi
  have hlo := neg_le_abs ⟪z₀, w⟫
  have hup := le_abs_self ⟪z, w⟫
  have hm := mul_le_mul_of_nonneg_right hκ₁ hK₀
  have hnorm : κ * K / 8 ≤ ‖z‖ := by nlinarith
  have hκK : 0 ≤ κ * K := mul_nonneg hκ hK
  nlinarith [norm_nonneg z]

end LongTails.Proofs.DerivativePerceptronTrajectory
