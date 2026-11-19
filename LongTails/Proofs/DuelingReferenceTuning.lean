import LongTails.Proofs.DuelingReferenceField

open LongTails.Setups.StronglyConvexDueling
open LongTails.Algorithms.DuelingReferenceDescent
open LongTails.Proofs.DuelingReferenceSmoothing

namespace LongTails.Proofs.DuelingReferenceTuning

lemma sufficient_calls {p : Params} (hp : spec.valid p) {K : ℕ}
    (hK : 72 * (p.d:ℝ)^2 * (4/p.μ)^(2*p.k) * (max 1 (8*p.G/p.r))^(4*p.k+2) / (p.c^2*p.μ*p.ε) +
      10368 * ((p.d:ℝ)*p.M*p.L)^2 * (4/p.μ)^(4*p.k) * (max 1 (8*p.G/p.r))^(8*p.k) /
        (p.c^2*p.μ*p.ε)^2 ≤ K) :
    8*((p.d:ℝ)/radius p)^2 ≤ K * slope p^2 * p.μ * p.ε := by
  obtain ⟨hμ,hL,hG,hr,hc,hM,hε⟩ := hp
  let C := max 1 (8*p.G/p.r)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let A := (4/p.μ)^p.k * (C^p.k)^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hs : spacing p = 1/C := rfl
  have hm : slope p = p.c/(3*A) := by
    unfold LongTails.Algorithms.DuelingReferenceDescent.slope
    rw [hs]
    dsimp [A]
    rw [div_pow, mul_pow, div_pow, one_pow, div_pow, one_pow]
    simp only [← pow_mul, Nat.mul_comm 2 p.k]
    field_simp
    rw [div_pow]; field_simp
  change 72*(p.d:ℝ)^2*(4/p.μ)^(2*p.k)*C^(4*p.k+2)/(p.c^2*p.μ*p.ε)+
    10368*((p.d:ℝ)*p.M*p.L)^2*(4/p.μ)^(4*p.k)*C^(8*p.k)/(p.c^2*p.μ*p.ε)^2 ≤ K at hK
  have he₁ : (4/p.μ)^(2*p.k)*C^(4*p.k+2) = A^2*C^2 := by
    dsimp [A]
    rw [pow_add, Nat.mul_comm 2 p.k, Nat.mul_comm 4 p.k, pow_mul,pow_mul]
    ring
  have he₂ : (4/p.μ)^(4*p.k)*C^(8*p.k) = A^4 := by
    dsimp [A]
    rw [Nat.mul_comm 4 p.k, Nat.mul_comm 8 p.k, pow_mul,pow_mul]
    ring
  have hKr : 72*(p.d:ℝ)^2*(A^2*C^2)/(p.c^2*p.μ*p.ε) +
    10368*((p.d:ℝ)*p.M*p.L)^2*A^4/(p.c^2*p.μ*p.ε)^2 ≤ K := by
    convert hK using 1
    rw [← he₁, ← he₂]
    ring
  have hsqrt := Real.sq_sqrt (mul_nonneg hμ.le hε.le)
  have hspos := Real.sqrt_pos.mpr (mul_pos hμ hε)
  unfold radius
  rcases le_total (spacing p) (slope p*Real.sqrt (p.μ*p.ε)/(4*p.M*p.L)) with h | h
  · rw [min_eq_left h,hs,hm]
    have ha : 72*(p.d:ℝ)^2*(A^2*C^2)/(p.c^2*p.μ*p.ε) ≤ K :=
      (le_add_of_nonneg_right (by positivity)).trans hKr
    field_simp at ha ⊢
    nlinarith
  · rw [min_eq_right h,hm]
    have ha : 10368*((p.d:ℝ)*p.M*p.L)^2*A^4/(p.c^2*p.μ*p.ε)^2 ≤ K :=
      (le_add_of_nonneg_left (by positivity)).trans hKr
    field_simp at ha ⊢
    rw [hsqrt]
    nlinarith

end LongTails.Proofs.DuelingReferenceTuning
