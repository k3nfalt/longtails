import LongTails.Setups.SharpLipschitzConvex
import LongTails.Algorithms.RestartedSubgradient
import LongTails.Proofs.Execution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.RestartedSubgradient

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma subgradient_norm_le (f : E → ℝ) (L : ℝ) (hL0 : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) (x g : E)
    (hg : ∀ y, f x + ⟪g, y - x⟫ ≤ f y) : ‖g‖ ≤ L := by
  have h1 := hg (x + g)
  rw [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h1
  have h2 := hLip (x + g) x
  rw [add_sub_cancel_left] at h2
  have h3 : ‖g‖ ^ 2 ≤ L * ‖g‖ := by
    have := le_abs_self (f (x + g) - f x)
    linarith
  nlinarith [norm_nonneg g]

lemma convex_average_step (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (t : ℕ) (sum x : E)
    (h0 : t = 0 → sum = 0) :
    ((t : ℝ) + 1) * f (((t : ℝ) + 1)⁻¹ • (sum + x)) ≤ (t : ℝ) * f ((t : ℝ)⁻¹ • sum) + f x := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    rw [h0 rfl]
    simp
  · have htr : (0 : ℝ) < t := by exact_mod_cast ht
    have hdec : ((t : ℝ) + 1)⁻¹ • (sum + x) =
        ((t : ℝ) / ((t : ℝ) + 1)) • ((t : ℝ)⁻¹ • sum) + (1 / ((t : ℝ) + 1)) • x := by
      rw [smul_smul, div_mul_eq_mul_div, mul_inv_cancel₀ htr.ne', smul_add, one_div]
    have hc := hf.2 (Set.mem_univ ((t : ℝ)⁻¹ • sum)) (Set.mem_univ x)
      (show (0 : ℝ) ≤ (t : ℝ) / ((t : ℝ) + 1) by positivity)
      (show (0 : ℝ) ≤ 1 / ((t : ℝ) + 1) by positivity)
      (by field_simp)
    rw [hdec]
    simp only [smul_eq_mul] at hc
    have hpos : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    calc ((t : ℝ) + 1) * f (((t : ℝ) / ((t : ℝ) + 1)) • ((t : ℝ)⁻¹ • sum) +
          (1 / ((t : ℝ) + 1)) • x)
        ≤ ((t : ℝ) + 1) * ((t : ℝ) / ((t : ℝ) + 1) * f ((t : ℝ)⁻¹ • sum) +
          1 / ((t : ℝ) + 1) * f x) := mul_le_mul_of_nonneg_left hc hpos.le
      _ = (t : ℝ) * f ((t : ℝ)⁻¹ • sum) + f x := by field_simp

section Trajectory

variable (f : E → ℝ) (g : E → E) (L D : ℝ) (T : ℕ) (x0 : E)

noncomputable def trajectory (n : ℕ) : RestartedSubgradientState E :=
  (fun s => (restartedSubgradient L D T x0).update s (f s.x, g s.x))^[n] ⟨0, 0, x0, 0⟩

lemma trajectory_succ (n : ℕ) :
    trajectory f g L D T x0 (n + 1) =
      (restartedSubgradient L D T x0).update (trajectory f g L D T x0 n)
        (f (trajectory f g L D T x0 n).x, g (trajectory f g L D T x0 n).x) := by
  unfold trajectory
  exact Function.iterate_succ_apply' _ n _

lemma descent_step (hL0 : 0 ≤ L) (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    (hg : ∀ x y, f x + ⟪g x, y - x⟫ ≤ f y) (γ : ℝ) (hγ : 0 ≤ γ) (x z : E) :
    ‖x - γ • g x - z‖ ^ 2 + 2 * γ * (f x - f z) ≤ ‖x - z‖ ^ 2 + γ ^ 2 * L ^ 2 := by
  have hn := subgradient_norm_le f L hL0 hLip x (g x) (hg x)
  have hsub := hg x z
  have e : x - γ • g x - z = (x - z) - γ • g x := by abel
  rw [e, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
  have hi : ⟪x - z, g x⟫ = -⟪g x, z - x⟫ := by
    rw [real_inner_comm, ← inner_neg_right, neg_sub]
  rw [hi]
  have hgn : ‖g x‖ ^ 2 ≤ L ^ 2 := by
    have := norm_nonneg (g x)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hgn (sq_nonneg γ)]

lemma last_step (hL0 : 0 ≤ L) (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    (hg : ∀ x y, f x + ⟪g x, y - x⟫ ≤ f y) (γ : ℝ) (hγ : 0 ≤ γ) (x z : E) :
    2 * γ * (f x - f z) ≤ ‖x - z‖ ^ 2 + γ ^ 2 * L ^ 2 := by
  have h := descent_step f g L hL0 hLip hg γ hγ x z
  nlinarith [sq_nonneg ‖x - γ • g x - z‖]

lemma phase_invariant (hf : ConvexOn ℝ Set.univ f) (hL0 : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) (hg : ∀ x y, f x + ⟪g x, y - x⟫ ≤ f y)
    (hD : 0 ≤ D) (hT : 0 < T) (hL : 0 < L) (m k : ℕ) (y z : E)
    (hm : trajectory f g L D T x0 m = ⟨k, 0, y, 0⟩) (hyz : ‖y - z‖ ≤ D / 2 ^ k) :
    ∀ t, t < T → ∃ x sum a, trajectory f g L D T x0 (m + t) = ⟨k, t, x, sum⟩ ∧
      (t = 0 → sum = 0) ∧
      ‖x - z‖ ^ 2 + 2 * restartedSubgradientStep L D T k * (a - t * f z) ≤
        (D / 2 ^ k) ^ 2 + t * restartedSubgradientStep L D T k ^ 2 * L ^ 2 ∧
      (t : ℝ) * f ((t : ℝ)⁻¹ • sum) ≤ a := by
  have hγ : 0 ≤ restartedSubgradientStep L D T k := by
    unfold restartedSubgradientStep
    positivity
  intro t ht
  induction t with
  | zero =>
    refine ⟨y, 0, 0, by simpa using hm, fun _ => rfl, ?_, by simp⟩
    have h := pow_le_pow_left₀ (norm_nonneg _) hyz 2
    simp only [Nat.cast_zero, zero_mul, sub_zero, mul_zero, add_zero]
    exact h
  | succ t ih =>
    obtain ⟨x, sum, a, hs, h0, hinv, hjen⟩ := ih (by omega)
    refine ⟨x - restartedSubgradientStep L D T k • g x, sum + x, a + f x, ?_, ?_, ?_, ?_⟩
    · rw [← add_assoc, trajectory_succ, hs]
      have hne : ¬ (t + 1 = T) := by omega
      simp only [restartedSubgradient, hne, ↓reduceIte]
    · intro h
      omega
    · have hd := descent_step f g L hL0 hLip hg _ hγ x z
      push_cast
      nlinarith
    · have hc := convex_average_step f hf t sum x h0
      push_cast
      linarith

lemma phase_end (hf : ConvexOn ℝ Set.univ f) (hL0 : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) (hg : ∀ x y, f x + ⟪g x, y - x⟫ ≤ f y)
    (hD : 0 ≤ D) (hT : 0 < T) (hL : 0 < L) (m k : ℕ) (y z : E)
    (hm : trajectory f g L D T x0 m = ⟨k, 0, y, 0⟩) (hyz : ‖y - z‖ ≤ D / 2 ^ k) :
    ∃ y', trajectory f g L D T x0 (m + T) = ⟨k + 1, 0, y', 0⟩ ∧
      2 * restartedSubgradientStep L D T k * ((T : ℝ) * (f y' - f z)) ≤
        (D / 2 ^ k) ^ 2 + T * restartedSubgradientStep L D T k ^ 2 * L ^ 2 := by
  have hγ : 0 ≤ restartedSubgradientStep L D T k := by
    unfold restartedSubgradientStep
    positivity
  obtain ⟨x, sum, a, hs, h0, hinv, hjen⟩ :=
    phase_invariant f g L D T x0 hf hL0 hLip hg hD hT hL m k y z hm hyz (T - 1) (by omega)
  refine ⟨((T : ℝ)⁻¹) • (sum + x), ?_, ?_⟩
  · have e : m + T = m + (T - 1) + 1 := by omega
    rw [e, trajectory_succ, hs]
    have hy : T - 1 + 1 = T := by omega
    simp only [restartedSubgradient, hy, ↓reduceIte]
  · have hc := convex_average_step f hf (T - 1) sum x h0
    have hTc : ((T - 1 : ℕ) : ℝ) + 1 = T := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hTc] at hc
    have hl := last_step f g L hL0 hLip hg _ hγ x z
    have hTm : ((T - 1 : ℕ) : ℝ) = T - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hTm] at hinv hjen hc
    nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 2 * restartedSubgradientStep L D T k),
      mul_le_mul_of_nonneg_left hjen (by positivity : (0 : ℝ) ≤ 2 * restartedSubgradientStep L D T k)]

lemma step_bound (hT : 0 < T) (hL : 0 < L) (k : ℕ) :
    (D / 2 ^ k) ^ 2 + T * restartedSubgradientStep L D T k ^ 2 * L ^ 2 =
      2 * restartedSubgradientStep L D T k * T * (L * (D / 2 ^ k) / Real.sqrt T) := by
  unfold restartedSubgradientStep
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have hss : Real.sqrt T ^ 2 = T := Real.sq_sqrt (by positivity)
  field_simp
  rw [hss]
  ring


lemma phases (hf : ConvexOn ℝ Set.univ f) (hLip : ∀ x y, |f x - f y| ≤ L * ‖x - y‖)
    (hg : ∀ x y, f x + ⟪g x, y - x⟫ ≤ f y) (μ : ℝ) (hμ : 0 < μ) (hL : 0 < L) (hD : 0 < D)
    (hT : 0 < T) (hTμ : 4 * L ^ 2 / μ ^ 2 ≤ T)
    (hsharp : ∀ x, ∃ z, IsMinOn f Set.univ z ∧ μ * ‖x - z‖ ≤ f x - f z)
    (hx0 : ∃ z, IsMinOn f Set.univ z ∧ ‖x0 - z‖ ≤ D) :
    ∀ k, ∃ y z, trajectory f g L D T x0 (k * T) = ⟨k, 0, y, 0⟩ ∧ IsMinOn f Set.univ z ∧
      ‖y - z‖ ≤ D / 2 ^ k ∧ (1 ≤ k → f y - f z ≤ μ * D / 2 ^ k) := by
  intro k
  induction k with
  | zero =>
    obtain ⟨z, hz, hdz⟩ := hx0
    exact ⟨x0, z, by simp only [trajectory, zero_mul, Function.iterate_zero, id_eq], hz, by simpa using hdz, fun h => absurd h (by omega)⟩
  | succ k ih =>
    obtain ⟨y, z, hs, hz, hyz, -⟩ := ih
    obtain ⟨y', hs', hb⟩ := phase_end f g L D T x0 hf hL.le hLip hg hD.le hT hL (k * T) k y z
      hs hyz
    have hγ : 0 < restartedSubgradientStep L D T k := by
      unfold restartedSubgradientStep
      have : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
      positivity
    have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    rw [step_bound L D T hT hL k] at hb
    have hgap : f y' - f z ≤ L * (D / 2 ^ k) / Real.sqrt T := by
      have hpos : 0 < 2 * restartedSubgradientStep L D T k * T := by positivity
      have h2 : 2 * restartedSubgradientStep L D T k * T * (f y' - f z) ≤
          2 * restartedSubgradientStep L D T k * T * (L * (D / 2 ^ k) / Real.sqrt T) := by
        linarith
      exact le_of_mul_le_mul_left h2 hpos
    have hsq : 2 * L / μ ≤ Real.sqrt T := by
      apply Real.le_sqrt_of_sq_le
      have e : (2 * L / μ) ^ 2 = 4 * L ^ 2 / μ ^ 2 := by ring
      rw [e]
      exact hTμ
    have hsqpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTr
    have hbound : L * (D / 2 ^ k) / Real.sqrt T ≤ μ * D / 2 ^ (k + 1) := by
      rw [div_le_iff₀ hsqpos, pow_succ]
      have h2k : (0 : ℝ) < 2 ^ k := by positivity
      have hmul : μ * (2 * L / μ) = 2 * L := by field_simp
      have : L * (D / 2 ^ k) = μ * D / (2 ^ k * 2) * (2 * L / μ) := by
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    obtain ⟨z', hz', hsh⟩ := hsharp y'
    have hfz : f z' = f z := le_antisymm (hz' (Set.mem_univ z)) (hz (Set.mem_univ z'))
    refine ⟨y', z', ?_, hz', ?_, fun _ => ?_⟩
    · rw [Nat.succ_mul]
      exact hs'
    · rw [hfz] at hsh
      have h1 : μ * ‖y' - z'‖ ≤ μ * D / 2 ^ (k + 1) := hsh.trans (hgap.trans hbound)
      have h2 : μ * D / 2 ^ (k + 1) = μ * (D / 2 ^ (k + 1)) := by ring
      rw [h2] at h1
      exact le_of_mul_le_mul_left h1 hμ
    · rw [hfz.symm] at hgap
      exact hgap.trans hbound

end Trajectory


open LongTails.Setups.SharpLipschitzConvex

noncomputable def phaseLength (p : Params) : ℕ := ⌈4 * p.L ^ 2 / p.μ ^ 2⌉₊

noncomputable def phaseCount (p : Params) : ℕ := Nat.clog 2 ⌈p.μ * p.D / p.ε⌉₊ + 1

lemma phaseLength_pos (p : Params) (hp : spec.valid p) : 0 < phaseLength p := by
  obtain ⟨hμ, hμL, -, -⟩ := hp
  unfold phaseLength
  apply Nat.ceil_pos.mpr
  have hL : 0 < p.L := hμ.trans_le hμL
  positivity

lemma final_gap (p : Params) (hp : spec.valid p) :
    p.μ * p.D / 2 ^ phaseCount p ≤ p.ε := by
  obtain ⟨hμ, -, hD, hε⟩ := hp
  unfold phaseCount
  have hc := Nat.le_pow_clog (by norm_num : 1 < 2) ⌈p.μ * p.D / p.ε⌉₊
  have h1 : p.μ * p.D / p.ε ≤ (2 : ℝ) ^ Nat.clog 2 ⌈p.μ * p.D / p.ε⌉₊ := by
    have := Nat.le_ceil (p.μ * p.D / p.ε)
    have hc' : ((⌈p.μ * p.D / p.ε⌉₊ : ℕ) : ℝ) ≤ ((2 ^ Nat.clog 2 ⌈p.μ * p.D / p.ε⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast hc
    push_cast at hc'
    linarith
  rw [div_le_iff₀ (by positivity), pow_succ]
  rw [div_le_iff₀ hε] at h1
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (Nat.clog 2 ⌈p.μ * p.D / p.ε⌉₊)]

lemma execute_eq_trajectory (p : Params) (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
    (g : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d))
    (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (ℝ × EuclideanSpace ℝ (Fin p.d)))
    (hO : ∀ h x s, O.answer h (0, x) s = (f x, g x)) (N : ℕ)
    (seed : (restartedSubgradient p.L p.D (phaseLength p) p.x0).Seed)
    (ξ : (k : ℕ) → O.Seed k) :
    execute O (restartedSubgradient p.L p.D (phaseLength p) p.x0) (fun _ => N) seed ξ =
      (trajectory f g p.L p.D (phaseLength p) p.x0 N).x := by
  rw [OracleTemplate.execute_eq_of_answer_eq O (fun x => (f x, g x)) (fun k q s => hO k q s)]
  exact OracleTemplate.execute_iterate (fun x => (f x, g x)) _ N seed

theorem convergence (p : Params) (hp : spec.valid p) (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
    (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (ℝ × EuclideanSpace ℝ (Fin p.d)))
    (hadm : spec.admissible p f O) :
    let A := restartedSubgradient p.L p.D (phaseLength p) p.x0
    spec.successful p f
      (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
        execute O A (fun _ => phaseLength p * phaseCount p) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  intro A
  obtain ⟨hconv, hLip, hx0, hsharp, g, hg, hO⟩ := hadm
  have hv := hp
  obtain ⟨hμ, hμL, hD, hε⟩ := hp
  have hL : 0 < p.L := hμ.trans_le hμL
  have hT := phaseLength_pos p hv
  have hTμ : 4 * p.L ^ 2 / p.μ ^ 2 ≤ (phaseLength p : ℝ) := Nat.le_ceil _
  obtain ⟨y, z, hs, hz, -, hgap⟩ := phases f g p.L p.D (phaseLength p) p.x0 hconv hLip hg p.μ hμ
    hL hD hT hTμ hsharp hx0 (phaseCount p)
  have hK : 1 ≤ phaseCount p := by unfold phaseCount; omega
  have hfin := (hgap hK).trans (final_gap p hv)
  have hout : ∀ w : A.Seed × ((k : ℕ) → O.Seed k),
      execute O A (fun _ => phaseLength p * phaseCount p) w.1 w.2 = y := by
    intro w
    rw [execute_eq_trajectory p f g O hO, Nat.mul_comm, hs]
  refine ⟨z, hz, ?_, ?_⟩
  · change Integrable _ ((A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k)))
    simp only [hout]
    exact integrable_const _
  · change (∫ w, _ ∂((A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k)))) ≤ _
    simp only [hout, integral_const, probReal_univ, one_smul]
    exact hfin

end LongTails.Proofs.RestartedSubgradient
