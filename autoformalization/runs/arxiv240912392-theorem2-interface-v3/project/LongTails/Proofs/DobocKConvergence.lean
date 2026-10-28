import LongTails.Algorithms.DobocK
import LongTails.Setups.DobocK
import LongTails.Proofs.DobocKAnalysis
import Mathlib.Algebra.QuadraticDiscriminant

open scoped RealInnerProductSpace

namespace OracleTemplate.DobocK

open LongTails.Setups.DobocK

section Operator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem psd_norm_le (T : V →ₗ[ℝ] V) (hsym : ∀ u v, ⟪T u, v⟫ = ⟪u, T v⟫)
    (hpos : ∀ v, 0 ≤ ⟪T v, v⟫) (hle : ∀ v, ⟪T v, v⟫ ≤ ‖v‖ ^ 2) (v : V) : ‖T v‖ ≤ ‖v‖ := by
  have cs : ∀ w, (inner ℝ (T v) (w)) ^ 2 ≤ (inner ℝ (T v) (v)) * (inner ℝ (T w) (w)) := by
    intro w
    have h : ∀ t : ℝ, 0 ≤ (inner ℝ (T w) (w)) * (t * t) + 2 * (inner ℝ (T v) (w)) * t + (inner ℝ (T v) (v)) := by
      intro t
      have := hpos (v + t • w)
      simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, RCLike.conj_to_real] at this
      have e : (inner ℝ (T w) (v)) = (inner ℝ (T v) (w)) := by rw [hsym, real_inner_comm]
      rw [e] at this
      nlinarith
    have := discrim_le_zero h
    unfold discrim at this
    nlinarith
  have h1 := cs (T v)
  rw [real_inner_self_eq_norm_sq] at h1
  have h2 : (inner ℝ (T v) (v)) * (inner ℝ (T (T v)) (T v)) ≤ ‖v‖ ^ 2 * ‖T v‖ ^ 2 :=
    mul_le_mul (hle v) (hle (T v)) (hpos _) (sq_nonneg _)
  have h3 : (‖T v‖ ^ 2) ^ 2 ≤ ‖v‖ ^ 2 * ‖T v‖ ^ 2 := le_trans h1 h2
  by_cases h0 : ‖T v‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hp : 0 < ‖T v‖ ^ 2 := by positivity
    have : ‖T v‖ ^ 2 ≤ ‖v‖ ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

theorem pow_comm_apply (T : V →ₗ[ℝ] V) (l : ℕ) (v : V) : (T ^ l) (T v) = T ((T ^ l) v) := by
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]

theorem pow_symm (T : V →ₗ[ℝ] V) (hsym : ∀ u v, ⟪T u, v⟫ = ⟪u, T v⟫) (l : ℕ) (u v : V) :
    ⟪(T ^ l) u, v⟫ = ⟪u, (T ^ l) v⟫ := by
  induction l generalizing u v with
  | zero => simp
  | succ l ih =>
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hsym, pow_comm_apply]

theorem pow_norm_le (T : V →ₗ[ℝ] V) (hsym : ∀ u v, ⟪T u, v⟫ = ⟪u, T v⟫)
    (hpos : ∀ v, 0 ≤ ⟪T v, v⟫) (hle : ∀ v, ⟪T v, v⟫ ≤ ‖v‖ ^ 2) (l : ℕ) (v : V) :
    ‖(T ^ l) v‖ ≤ ‖v‖ := by
  induction l with
  | zero => simp
  | succ l ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact (psd_norm_le T hsym hpos hle _).trans ih

theorem pow_inner_nonneg (T : V →ₗ[ℝ] V) (hsym : ∀ u v, ⟪T u, v⟫ = ⟪u, T v⟫)
    (hpos : ∀ v, 0 ≤ ⟪T v, v⟫) (l : ℕ) (v : V) : 0 ≤ ⟪(T ^ l) v, v⟫ := by
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' l
  · rw [two_mul, pow_add, Module.End.mul_apply, pow_symm T hsym]
    exact real_inner_self_nonneg
  · rw [two_mul, pow_succ, pow_add, Module.End.mul_apply, Module.End.mul_apply, pow_symm T hsym,
      pow_comm_apply]
    exact hpos _

end Operator

theorem penaltyHessian_add (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (x u v : Stacked p.n p.dim) :
    penaltyHessian p.toPublic f x (u + v) =
      penaltyHessian p.toPublic f x u + penaltyHessian p.toPublic f x v := by
  ext i : 1
  simp only [penaltyHessian, mix_add, PiLp.add_apply, map_add]
  module

theorem penaltyHessian_smul (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (x : Stacked p.n p.dim) (c : ℝ) (u : Stacked p.n p.dim) :
    penaltyHessian p.toPublic f x (c • u) = c • penaltyHessian p.toPublic f x u := by
  ext i : 1
  simp only [penaltyHessian, mix_smul, PiLp.smul_apply, map_smul, smul_add, ← smul_sub]
  rw [smul_comm c (1 / p.lam)]

theorem localBase_eq (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (x : Stacked p.n p.dim) :
    localBase p.toPublic x (localOracle p.toPublic f x) = p.η • penaltyGradient p.toPublic f x := by
  ext i : 1
  rfl

theorem innerStep_eq (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (x g : Stacked p.n p.dim) :
    innerStep p.toPublic x (localOracle p.toPublic f x) g =
      p.η • penaltyGradient p.toPublic f x + (g - p.η • penaltyHessian p.toPublic f x g) := by
  have hb := localBase_eq p f x
  ext i : 1
  have hbi : localBase p.toPublic x (localOracle p.toPublic f x) i = (p.η • penaltyGradient p.toPublic f x) i := by
    rw [hb]
  simp only [innerStep, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] at hbi ⊢
  rw [hbi]
  simp only [penaltyHessian, localOracle, smul_add, smul_sub, smul_smul, sub_smul, one_smul]
  have : p.η * (1 / p.lam) = p.η / p.lam := by ring
  rw [this]
  module

theorem a_ge_m (p : Constants) (hnet : Network p.toPublic) (hlam : 0 < p.lam) (hmM : p.m ≤ p.M) :
    p.m ≤ a p := by
  have h0 : wmin p.toPublic ≤ 1 := by
    have hi := wmin_le p.toPublic ⟨0, hnet.1⟩
    have hrow := hnet.2.2.2.1 ⟨0, hnet.1⟩
    have : p.W ⟨0, hnet.1⟩ ⟨0, hnet.1⟩ ≤ ∑ j, p.W ⟨0, hnet.1⟩ j :=
      Finset.single_le_sum (fun j _ => hnet.2.2.1 _ j) (Finset.mem_univ _)
    linarith
  unfold a
  have : 0 ≤ 2 * (1 - wmin p.toPublic) / p.lam := by
    apply div_nonneg _ hlam.le; linarith
  linarith

theorem direction_bounds (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (hnet : Network p.toPublic) (hlam : 0 < p.lam) (hη : 0 < p.η) (hK : 1 ≤ p.K)
    (hm : 0 < p.m) (hmM : p.m ≤ p.M) (hA1 : Assumption1 p.toPublic p.m p.M f)
    (hηa : p.η < 1 / a p) (x : Stacked p.n p.dim) :
    p.η * ‖penaltyGradient p.toPublic f x‖ ^ 2 ≤
        ⟪penaltyGradient p.toPublic f x, direction p.toPublic x (localOracle p.toPublic f x)⟫ ∧
      ‖direction p.toPublic x (localOracle p.toPublic f x)‖ ≤
        p.η * p.K * ‖penaltyGradient p.toPublic f x‖ := by
  set G := penaltyGradient p.toPublic f x with hG
  have hma : p.m ≤ a p := a_ge_m p hnet hlam hmM
  have ha : 0 < a p := lt_of_lt_of_le hm hma
  have h2 : p.η * a p ≤ 1 := by
    have := hηa; rw [lt_div_iff₀ ha] at this; linarith
  let Hl : Stacked p.n p.dim →ₗ[ℝ] Stacked p.n p.dim :=
    { toFun := penaltyHessian p.toPublic f x
      map_add' := penaltyHessian_add p f x
      map_smul' := fun c u => penaltyHessian_smul p f x c u }
  let A : Stacked p.n p.dim →ₗ[ℝ] Stacked p.n p.dim := LinearMap.id - p.η • Hl
  have hA : ∀ v, A v = v - p.η • penaltyHessian p.toPublic f x v := fun v => rfl
  have hHb := penaltyHessian_bounds p f hnet hlam hA1 x
  have hAsym : ∀ u v, (inner ℝ (A u) (v)) = (inner ℝ (u) (A v)) := by
    intro u v
    rw [hA, hA, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      penaltyHessian_symm p f hnet hA1, RCLike.conj_to_real]
  have hApos : ∀ v, 0 ≤ (inner ℝ (A v) (v)) := by
    intro v
    rw [hA, inner_sub_left, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
    have h1 := (hHb v).2
    nlinarith [sq_nonneg ‖v‖, mul_le_mul_of_nonneg_left h1 hη.le]
  have hAle : ∀ v, (inner ℝ (A v) (v)) ≤ ‖v‖ ^ 2 := by
    intro v
    rw [hA, inner_sub_left, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
    have h1 := (hHb v).1
    nlinarith [sq_nonneg ‖v‖, mul_nonneg hη.le (mul_nonneg hm.le (sq_nonneg ‖v‖))]
  have hiter : ∀ k : ℕ, (innerStep p.toPublic x (localOracle p.toPublic f x))^[k]
      (localBase p.toPublic x (localOracle p.toPublic f x)) =
        p.η • ∑ l ∈ Finset.range (k + 1), (A ^ l) G := by
    intro k
    induction k with
    | zero => simp [localBase_eq, hG]
    | succ k ih =>
        have e : ∀ v, v - p.η • penaltyHessian p.toPublic f x v = A v := fun v => rfl
        rw [Function.iterate_succ_apply', ih, innerStep_eq, e, map_smul, map_sum,
          Finset.sum_range_succ' (fun l => (A ^ l) G) (k + 1), pow_zero, Module.End.one_apply]
        simp only [← Module.End.mul_apply, ← pow_succ']
        rw [smul_add, add_comm]
  have hdsum : direction p.toPublic x (localOracle p.toPublic f x) =
      p.η • ∑ l ∈ Finset.range p.K, (A ^ l) G := by
    rw [direction, hiter, Nat.sub_add_cancel hK]
  rw [hdsum]
  constructor
  · rw [inner_smul_right, inner_sum]
    have hnn : ∀ l ∈ Finset.range p.K, 0 ≤ (inner ℝ (G) ((A ^ l) G)) := fun l _ => by
      rw [real_inner_comm]; exact pow_inner_nonneg A hAsym hApos l G
    have := Finset.single_le_sum hnn (Finset.mem_range.2 (by omega : 0 < p.K))
    rw [pow_zero, Module.End.one_apply, real_inner_self_eq_norm_sq] at this
    exact mul_le_mul_of_nonneg_left this hη.le
  · rw [norm_smul, Real.norm_of_nonneg hη.le, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hη.le
    calc ‖∑ l ∈ Finset.range p.K, (A ^ l) G‖ ≤ ∑ l ∈ Finset.range p.K, ‖(A ^ l) G‖ := norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.range p.K, ‖G‖ :=
          Finset.sum_le_sum fun l _ => pow_norm_le A hAsym hApos hAle l G
      _ = p.K * ‖G‖ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem gradient_gap_bounds (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (hnet : Network p.toPublic) (hlam : 0 < p.lam) (hm : 0 < p.m) (hmM : p.m ≤ p.M)
    (hA1 : Assumption1 p.toPublic p.m p.M f) (xstar : Stacked p.n p.dim)
    (hmin : IsMinOn (penalty p.toPublic f) Set.univ xstar) (x : Stacked p.n p.dim) :
    2 * p.m * (penalty p.toPublic f x - penalty p.toPublic f xstar) ≤
        ‖penaltyGradient p.toPublic f x‖ ^ 2 ∧
      ‖penaltyGradient p.toPublic f x‖ ^ 2 ≤
        2 * a p * (penalty p.toPublic f x - penalty p.toPublic f xstar) := by
  set G := penaltyGradient p.toPublic f x
  have ha : 0 < a p := lt_of_lt_of_le hm (a_ge_m p hnet hlam hmM)
  have hFx := penalty_quadratic_bounds p f hnet hlam hA1
  constructor
  · have h := (hFx x xstar).1
    have hsq : 0 ≤ ‖G + p.m • (xstar - x)‖ ^ 2 := sq_nonneg _
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg hm.le] at hsq
    nlinarith
  · have h := (hFx x (x - (1 / a p) • G)).2
    have hm' : penalty p.toPublic f xstar ≤ penalty p.toPublic f (x - (1 / a p) • G) :=
      hmin (Set.mem_univ _)
    rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
      Real.norm_of_nonneg (by positivity), real_inner_self_eq_norm_sq] at h
    have e : 1 / a p * ‖G‖ ^ 2 - a p / 2 * (1 / a p * ‖G‖) ^ 2 = ‖G‖ ^ 2 / (2 * a p) := by
      field_simp; ring
    have h3 : ‖G‖ ^ 2 / (2 * a p) ≤ penalty p.toPublic f x - penalty p.toPublic f xstar := by
      linarith
    rwa [div_le_iff₀ (by positivity), mul_comm] at h3

theorem lemma5_scalar (m aa η K L Δ s g c q : ℝ) (hm : 0 < m) (hma : m ≤ aa) (hη : 0 < η)
    (hK : 0 < K) (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (hηK : η < 2 * m / (aa ^ 2 * K ^ 2))
    (hs : s = g ^ 2) (hg : 0 ≤ g) (hlo : 2 * m * Δ ≤ s) (hhi : s ≤ 2 * aa * Δ)
    (hc : η * s ≤ c) (hq : q ≤ aa * (η * K * g) ^ 2) :
    -c + 1 / 2 * q + L / 6 * (η * K * g) ^ 3 ≤
      -((2 * m ^ 2 * η - m * aa ^ 2 * η ^ 2 * K ^ 2) / aa) * Δ +
        aa ^ 3 * (2 * aa) ^ (3 / 2 : ℝ) * η ^ 3 * K ^ 3 * L / (6 * m ^ 3) * Δ ^ (3 / 2 : ℝ) := by
  have ha : 0 < aa := lt_of_lt_of_le hm hma
  have hc1 : 0 ≤ 2 * m * η - aa ^ 2 * η ^ 2 * K ^ 2 := by
    have := (lt_div_iff₀ (by positivity : 0 < aa ^ 2 * K ^ 2)).1 hηK
    nlinarith
  have hquad : -c + 1 / 2 * q ≤ -((2 * m ^ 2 * η - m * aa ^ 2 * η ^ 2 * K ^ 2) / aa) * Δ := by
    have e : (η * K * g) ^ 2 = η ^ 2 * K ^ 2 * s := by rw [hs]; ring
    rw [e] at hq
    have hms : m / aa * η * s ≤ η * s := by
      have : m / aa ≤ 1 := (div_le_one ha).2 hma
      have h0 : 0 ≤ η * s := by rw [hs]; positivity
      nlinarith
    have step1 : -c + 1 / 2 * q ≤ -((2 * m * η - aa ^ 2 * η ^ 2 * K ^ 2) / (2 * aa)) * s := by
      have e2 : -((2 * m * η - aa ^ 2 * η ^ 2 * K ^ 2) / (2 * aa)) * s =
          -(m / aa * η * s) + aa * (η ^ 2 * K ^ 2 * s) / 2 := by
        field_simp; ring
      rw [e2]; nlinarith
    have hcoef : 0 ≤ (2 * m * η - aa ^ 2 * η ^ 2 * K ^ 2) / (2 * aa) := by positivity
    have step2 : -((2 * m * η - aa ^ 2 * η ^ 2 * K ^ 2) / (2 * aa)) * s ≤
        -((2 * m * η - aa ^ 2 * η ^ 2 * K ^ 2) / (2 * aa)) * (2 * m * Δ) := by
      nlinarith
    have e3 : -((2 * m * η - aa ^ 2 * η ^ 2 * K ^ 2) / (2 * aa)) * (2 * m * Δ) =
        -((2 * m ^ 2 * η - m * aa ^ 2 * η ^ 2 * K ^ 2) / aa) * Δ := by
      field_simp
    linarith
  have hcub : L / 6 * (η * K * g) ^ 3 ≤
      aa ^ 3 * (2 * aa) ^ (3 / 2 : ℝ) * η ^ 3 * K ^ 3 * L / (6 * m ^ 3) * Δ ^ (3 / 2 : ℝ) := by
    have hG3 : g ^ 3 = s ^ (3 / 2 : ℝ) := by
      rw [hs, ← Real.rpow_natCast g 2, ← Real.rpow_mul hg]
      norm_num
    have hs32 : s ^ (3 / 2 : ℝ) ≤ (2 * aa) ^ (3 / 2 : ℝ) * Δ ^ (3 / 2 : ℝ) := by
      rw [← Real.mul_rpow (by positivity) hΔ]
      exact Real.rpow_le_rpow (by rw [hs]; positivity) hhi (by norm_num)
    have hratio : 1 ≤ aa ^ 3 / m ^ 3 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hm.le hma 3
    set c0 := L / 6 * η ^ 3 * K ^ 3 with hc0d
    have hc0 : 0 ≤ c0 := by positivity
    have e : L / 6 * (η * K * g) ^ 3 = c0 * s ^ (3 / 2 : ℝ) := by
      rw [← hG3, hc0d]; ring
    have e2 : aa ^ 3 * (2 * aa) ^ (3 / 2 : ℝ) * η ^ 3 * K ^ 3 * L / (6 * m ^ 3) * Δ ^ (3 / 2 : ℝ) =
        (aa ^ 3 / m ^ 3) * (c0 * ((2 * aa) ^ (3 / 2 : ℝ) * Δ ^ (3 / 2 : ℝ))) := by
      rw [hc0d]; field_simp
    rw [e, e2]
    set Y := (2 * aa) ^ (3 / 2 : ℝ) * Δ ^ (3 / 2 : ℝ)
    have h1 : c0 * s ^ (3 / 2 : ℝ) ≤ c0 * Y := mul_le_mul_of_nonneg_left hs32 hc0
    have h2 : 0 ≤ c0 * Y := by positivity
    calc c0 * s ^ (3 / 2 : ℝ) ≤ c0 * Y := h1
      _ = 1 * (c0 * Y) := (one_mul _).symm
      _ ≤ aa ^ 3 / m ^ 3 * (c0 * Y) := mul_le_mul_of_nonneg_right hratio h2
  linarith

theorem lemma5 (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (hnet : Network p.toPublic) (hlam : 0 < p.lam) (hη : 0 < p.η) (hK : 1 ≤ p.K)
    (hm : 0 < p.m) (hmM : p.m ≤ p.M) (hL : 0 ≤ p.L)
    (hA1 : Assumption1 p.toPublic p.m p.M f) (hA2 : Assumption2 p.toPublic p.L f)
    (hstep : StepSizeLemma5 p) (xstar : Stacked p.n p.dim)
    (hmin : IsMinOn (penalty p.toPublic f) Set.univ xstar) (j : ℕ) :
    penalty p.toPublic f (iterate p.toPublic f (j + 1)) - penalty p.toPublic f xstar ≤
      (1 - (2 * p.m ^ 2 * p.η - p.m * a p ^ 2 * p.η ^ 2 * (p.K : ℝ) ^ 2) / a p) *
          (penalty p.toPublic f (iterate p.toPublic f j) - penalty p.toPublic f xstar) +
        a p ^ 3 * (2 * a p) ^ (3 / 2 : ℝ) * p.η ^ 3 * (p.K : ℝ) ^ 3 * p.L / (6 * p.m ^ 3) *
          (penalty p.toPublic f (iterate p.toPublic f j) - penalty p.toPublic f xstar) ^ (3 / 2 : ℝ) := by
  obtain ⟨_, hηa, hηK⟩ := hstep
  set x := iterate p.toPublic f j
  set d := direction p.toPublic x (localOracle p.toPublic f x)
  have hnext : iterate p.toPublic f (j + 1) = x - d := by
    rw [iterate, Function.iterate_succ_apply']; rfl
  obtain ⟨hGd, hdn⟩ := direction_bounds p f hnet hlam hη hK hm hmM hA1 hηa x
  obtain ⟨hlo, hhi⟩ := gradient_gap_bounds p f hnet hlam hm hmM hA1 xstar hmin x
  have hcub := penalty_cubic_bound p f hnet hA1 hA2 hL x (x - d)
  have e1 : x - d - x = -d := sub_sub_cancel_left x d
  have hHneg : penaltyHessian p.toPublic f x (-d) = -penaltyHessian p.toPublic f x d := by
    have := penaltyHessian_smul p f x (-1) d
    simpa using this
  rw [e1, inner_neg_right, hHneg, inner_neg_left, inner_neg_right, neg_neg, norm_neg] at hcub
  have hHd : (inner ℝ (penaltyHessian p.toPublic f x d) (d)) ≤
      a p * (p.η * p.K * ‖penaltyGradient p.toPublic f x‖) ^ 2 :=
    ((penaltyHessian_bounds p f hnet hlam hA1 x d).2).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdn 2)
        (lt_of_lt_of_le hm (a_ge_m p hnet hlam hmM)).le)
  have hd3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdn 3)
    (by positivity : 0 ≤ p.L / 6)
  have hΔ : 0 ≤ penalty p.toPublic f x - penalty p.toPublic f xstar := by
    have := hmin (Set.mem_univ x); simp only [Set.mem_ofPred_eq] at this; linarith
  have hsc := lemma5_scalar p.m (a p) p.η p.K p.L _ _ _ _ _ hm (a_ge_m p hnet hlam hmM) hη
    (by exact_mod_cast (show 0 < p.K by omega)) hL hΔ hηK rfl (norm_nonneg _) hlo hhi hGd hHd
  rw [hnext]
  linarith

theorem rate_bounds (p : Constants) (hη : 0 < p.η) (hK : 1 ≤ p.K) (hm : 0 < p.m) (hma : p.m ≤ a p)
    (hL : 0 ≤ p.L) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hT : StepSizeTheorem2 p Δ) :
    0 < rate p Δ ∧ rate p Δ < 1 := by
  obtain ⟨hη1, hη2⟩ := hT
  have ha : 0 < a p := lt_of_lt_of_le hm hma
  have hK0 : (1 : ℝ) ≤ p.K := by exact_mod_cast hK
  set A := a p
  set k : ℝ := (p.K : ℝ)
  have hden : 0 < A ^ 2 * k ^ 2 := by positivity
  have hηm : p.η * (A ^ 2 * k ^ 2) < p.m := (lt_div_iff₀ hden).1 hη1
  have hB0 : 0 ≤ A ^ 3 * (2 * A) ^ (3 / 2 : ℝ) * p.η ^ 3 * k ^ 3 * p.L / (6 * p.m ^ 3) * Δ ^ (1 / 2 : ℝ) := by
    positivity
  have hAlo : p.m ^ 2 * p.η / A < (2 * p.m ^ 2 * p.η - p.m * A ^ 2 * p.η ^ 2 * k ^ 2) / A := by
    apply div_lt_div_of_pos_right _ ha
    nlinarith [mul_pos hm hη]
  have hBlt : A ^ 3 * (2 * A) ^ (3 / 2 : ℝ) * p.η ^ 3 * k ^ 3 * p.L / (6 * p.m ^ 3) * Δ ^ (1 / 2 : ℝ) <
      p.m ^ 2 * p.η / A := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) ha]
    have : A ^ 3 * (2 * A) ^ (3 / 2 : ℝ) * p.η ^ 3 * k ^ 3 * p.L * Δ ^ (1 / 2 : ℝ) * A =
        p.η * p.m ^ 0 * (p.η ^ 2 * (A ^ 4 * (2 * A) ^ (3 / 2 : ℝ) * k ^ 3 * p.L * Δ ^ (1 / 2 : ℝ))) := by
      ring
    rw [this]
    have h6 : p.η * p.m ^ 0 * (p.η ^ 2 * (A ^ 4 * (2 * A) ^ (3 / 2 : ℝ) * k ^ 3 * p.L * Δ ^ (1 / 2 : ℝ))) <
        p.η * p.m ^ 0 * (6 * p.m ^ 5) := by
      apply mul_lt_mul_of_pos_left hη2; positivity
    nlinarith
  have hAhi : (2 * p.m ^ 2 * p.η - p.m * A ^ 2 * p.η ^ 2 * k ^ 2) / A < 1 := by
    rw [div_lt_one ha]
    have hsq : 0 < (p.m - p.η * (A ^ 2 * k ^ 2)) ^ 2 := by
      have : 0 < p.m - p.η * (A ^ 2 * k ^ 2) := by linarith
      positivity
    have hm3 : p.m ^ 3 ≤ A ^ 3 * k ^ 2 := by
      have h1 : p.m ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ hm.le hma 3
      have h2 : A ^ 3 ≤ A ^ 3 * k ^ 2 := by
        have : (1 : ℝ) ≤ k ^ 2 := by nlinarith
        nlinarith [pow_pos ha 3]
      linarith
    have key : p.m * (2 * p.m * p.η * (A ^ 2 * k ^ 2) - p.η ^ 2 * (A ^ 2 * k ^ 2) ^ 2) < p.m * p.m ^ 2 := by
      apply mul_lt_mul_of_pos_left _ hm; nlinarith
    have e : (2 * p.m ^ 2 * p.η - p.m * A ^ 2 * p.η ^ 2 * k ^ 2) * (A * k ^ 2) =
        p.m * (2 * p.m * p.η * (A ^ 2 * k ^ 2) - p.η ^ 2 * (A ^ 2 * k ^ 2) ^ 2) / A := by
      field_simp
    have hk2 : 0 < A * k ^ 2 := by positivity
    by_contra hcon
    push Not at hcon
    have := mul_le_mul_of_nonneg_right hcon hk2.le
    rw [e, le_div_iff₀ ha] at this
    nlinarith
  unfold rate
  constructor <;> linarith

theorem theorem2 (p : Constants) (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (hnet : Network p.toPublic) (hlam : 0 < p.lam) (hη : 0 < p.η) (hK : 1 ≤ p.K)
    (hm : 0 < p.m) (hmM : p.m ≤ p.M) (hL : 0 ≤ p.L)
    (hA1 : Assumption1 p.toPublic p.m p.M f) (hA2 : Assumption2 p.toPublic p.L f)
    (hstep : StepSizeLemma5 p) (xstar : Stacked p.n p.dim)
    (hmin : IsMinOn (penalty p.toPublic f) Set.univ xstar)
    (hT : StepSizeTheorem2 p (penalty p.toPublic f p.x0 - penalty p.toPublic f xstar)) :
    0 < rate p (penalty p.toPublic f p.x0 - penalty p.toPublic f xstar) ∧
      rate p (penalty p.toPublic f p.x0 - penalty p.toPublic f xstar) < 1 ∧
      ∀ k, penalty p.toPublic f (iterate p.toPublic f k) - penalty p.toPublic f xstar ≤
        (1 - rate p (penalty p.toPublic f p.x0 - penalty p.toPublic f xstar)) ^ k *
          (penalty p.toPublic f p.x0 - penalty p.toPublic f xstar) := by
  set F := penalty p.toPublic f
  set Δ0 := F p.x0 - F xstar
  have hma := a_ge_m p hnet hlam hmM
  have hΔ : ∀ x, 0 ≤ F x - F xstar := fun x => by
    have := hmin (Set.mem_univ x); simp only [Set.mem_ofPred_eq] at this; linarith
  obtain ⟨hε0, hε1⟩ := rate_bounds p hη hK hm hma hL Δ0 (hΔ _) hT
  refine ⟨hε0, hε1, ?_⟩
  set ε := rate p Δ0
  set B := a p ^ 3 * (2 * a p) ^ (3 / 2 : ℝ) * p.η ^ 3 * (p.K : ℝ) ^ 3 * p.L / (6 * p.m ^ 3)
  have hB : 0 ≤ B := by
    have := lt_of_lt_of_le hm hma; positivity
  have hstepk : ∀ j, F (iterate p.toPublic f j) - F xstar ≤ Δ0 →
      F (iterate p.toPublic f (j + 1)) - F xstar ≤ (1 - ε) * (F (iterate p.toPublic f j) - F xstar) := by
    intro j hj
    have h5 := lemma5 p f hnet hlam hη hK hm hmM hL hA1 hA2 hstep xstar hmin j
    set D := F (iterate p.toPublic f j) - F xstar
    have hD := hΔ (iterate p.toPublic f j)
    have h32 : D ^ (3 / 2 : ℝ) = D ^ (1 / 2 : ℝ) * D := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add' hD (by norm_num), Real.rpow_one]
    have hsq : D ^ (1 / 2 : ℝ) ≤ Δ0 ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hD hj (by norm_num)
    have hε : ε = (2 * p.m ^ 2 * p.η - p.m * a p ^ 2 * p.η ^ 2 * (p.K : ℝ) ^ 2) / a p - B * Δ0 ^ (1 / 2 : ℝ) := rfl
    rw [h32] at h5
    have : B * (D ^ (1 / 2 : ℝ) * D) ≤ B * (Δ0 ^ (1 / 2 : ℝ) * D) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hD) hB
    rw [hε]
    nlinarith
  intro k
  have main : ∀ k, F (iterate p.toPublic f k) - F xstar ≤ Δ0 ∧
      F (iterate p.toPublic f k) - F xstar ≤ (1 - ε) ^ k * Δ0 := by
    intro k
    induction k with
    | zero => simp [iterate, Δ0]
    | succ k ih =>
        have h := hstepk k ih.1
        have hD := hΔ (iterate p.toPublic f k)
        constructor
        · nlinarith [ih.1]
        · rw [pow_succ, mul_comm ((1 - ε) ^ k), mul_assoc]
          exact h.trans (mul_le_mul_of_nonneg_left ih.2 (by linarith))
  exact (main k).2

theorem execute_dobocK (q : Public) (f : Fin q.n → EuclideanSpace ℝ (Fin q.dim) → ℝ)
    (O : Oracle (Stacked q.n q.dim) (LocalReply q.n q.dim) 1)
    (hO : ∀ k x seed, O.answer k (0, x) seed = localOracle q f x) (k : ℕ)
    (seed : (dobocK q).Seed) (ξ : (j : ℕ) → O.Seed j) :
    execute O (dobocK q) (fun _ => k) seed ξ = iterate q f k := by
  unfold execute iterate
  simp only [Fin.sum_univ_one]
  change _ = (fun x => step q x (localOracle q f x))^[k] ((dobocK q).initial seed)
  generalize (dobocK q).initial seed = state
  generalize (0 : ℕ) = call
  induction k generalizing state call with
  | zero => rfl
  | succ k ih =>
      change (if k + 1 = 0 then _ else _) = _
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      have hr : Function.update (fun _ : Fin 1 => k + 1) ((dobocK q).query state).1 k = fun _ => k := by
        funext i
        have hi : i = ((dobocK q).query state).1 := Subsingleton.elim _ _
        subst i
        simp
      simp only [Nat.add_sub_cancel]
      rw [hr]
      have ha : O.answer call ((dobocK q).query state) (ξ call) = localOracle q f state := hO _ _ _
      rw [ha]
      exact (ih _ _).trans (Function.iterate_succ_apply _ k state).symm

end OracleTemplate.DobocK

namespace OracleTemplate.DobocKTuning

open OracleTemplate OracleTemplate.DobocK LongTails.Setups.DobocK

theorem curvature_bounds (p : LongTails.Setups.DobocK.Params)
    (hp : LongTails.Setups.DobocK.spec.valid p) :
    0 < p.m ∧ p.m ≤ a (constants p.toPublic) ∧
      a (constants p.toPublic) ≤ curvatureBound p.toPublic := by
  rcases hp with ⟨hnet, hlam, hK, hm, hmM, hL, hΔ, hε⟩
  refine ⟨hm, a_ge_m (constants p.toPublic) hnet hlam hmM, ?_⟩
  let : Nonempty (Fin (sourceInput p.toPublic).n) := ⟨⟨0, hnet.1⟩⟩
  have hw : 0 ≤ wmin (sourceInput p.toPublic) :=
    le_ciInf (fun i => hnet.2.2.1 i i)
  change p.M + 2 * (1 - wmin (sourceInput p.toPublic)) / p.lam ≤ p.M + 2 / p.lam
  apply add_le_add_right
  apply (div_le_div_iff_of_pos_right hlam).mpr
  linarith

theorem scalar_tuning (m a A k L Δ d C : ℝ)
    (hm : 0 < m) (hma : m ≤ a) (haA : a ≤ A) (hk : 1 ≤ k)
    (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (hd : 0 ≤ d) (hdΔ : d ≤ Δ)
    (hC : C = 1 + A + A ^ 2 * k ^ 2 / m +
      Real.sqrt (A ^ 4 * (2 * A) ^ (3 / 2 : ℝ) * k ^ 3 * L *
        Real.sqrt Δ / (6 * m ^ 5))) :
    let η := 1 / (2 * C)
    0 < η ∧ 0 < m ^ 2 / (2 * A * C) ∧
      (η < 1 ∧ η < 1 / a ∧ η < 2 * m / (a ^ 2 * k ^ 2)) ∧
      (η < m / (a ^ 2 * k ^ 2) ∧
        η ^ 2 * (a ^ 4 * (2 * a) ^ (3 / 2 : ℝ) * k ^ 3 * L *
          d ^ (1 / 2 : ℝ)) < 6 * m ^ 5) ∧
      m ^ 2 / (2 * A * C) ≤
        (2 * m ^ 2 * η - m * a ^ 2 * η ^ 2 * k ^ 2) / a -
          a ^ 3 * (2 * a) ^ (3 / 2 : ℝ) * η ^ 3 * k ^ 3 * L /
            (6 * m ^ 3) * d ^ (1 / 2 : ℝ) := by
  dsimp only
  have ha : 0 < a := lt_of_lt_of_le hm hma
  have hA : 0 < A := lt_of_lt_of_le ha haA
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  let B := A ^ 4 * (2 * A) ^ (3 / 2 : ℝ) * k ^ 3 * L * Real.sqrt Δ / (6 * m ^ 5)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hq : 0 ≤ A ^ 2 * k ^ 2 / m := by positivity
  have hs : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hC' : C = 1 + A + A ^ 2 * k ^ 2 / m + Real.sqrt B := hC
  have h1C : 1 ≤ C := by linarith
  have hAC : A ≤ C := by linarith
  have hqC : A ^ 2 * k ^ 2 / m ≤ C := by linarith
  have hsC : Real.sqrt B ≤ C := by linarith
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one h1C
  let η := 1 / (2 * C)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηC : η * C = 1 / 2 := by dsimp [η]; field_simp
  have hηhalf : η ≤ 1 / 2 := by
    calc η = η * 1 := by ring
         _ ≤ η * C := mul_le_mul_of_nonneg_left h1C hη.le
         _ = 1 / 2 := hηC
  have hηa : η * a ≤ 1 / 2 := by
    calc η * a ≤ η * C := mul_le_mul_of_nonneg_left (haA.trans hAC) hη.le
         _ = 1 / 2 := hηC
  have hqa : a ^ 2 * k ^ 2 / m ≤ C := by
    calc a ^ 2 * k ^ 2 / m ≤ A ^ 2 * k ^ 2 / m := by gcongr
         _ ≤ C := hqC
  let u := η * (a ^ 2 * k ^ 2 / m)
  have hu : u ≤ 1 / 2 := by
    calc u ≤ η * C := mul_le_mul_of_nonneg_left hqa hη.le
         _ = 1 / 2 := hηC
  have hηak : η * (a ^ 2 * k ^ 2) ≤ (1 / 2) * m := by
    apply (div_le_iff₀ hm).mp
    simpa only [u, mul_div_assoc] using hu
  have hdenak : 0 < a ^ 2 * k ^ 2 := by positivity
  have hstep : η < m / (a ^ 2 * k ^ 2) :=
    (lt_div_iff₀ hdenak).mpr (by linarith)
  let b := a ^ 4 * (2 * a) ^ (3 / 2 : ℝ) * k ^ 3 * L * d ^ (1 / 2 : ℝ)
  have hroot : Real.sqrt d ≤ Real.sqrt Δ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg d) (Real.sqrt_nonneg Δ)).mp
    simpa only [Real.sq_sqrt hd, Real.sq_sqrt hΔ] using hdΔ
  have hbB : b / (6 * m ^ 5) ≤ B := by
    dsimp [b, B]
    rw [← Real.sqrt_eq_rpow]
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 6 * m ^ 5)).mpr
    exact mul_le_mul (by gcongr) hroot (Real.sqrt_nonneg d) (by positivity)
  have hBC : B ≤ C ^ 2 := by
    calc B = (Real.sqrt B) ^ 2 := (Real.sq_sqrt hB).symm
         _ ≤ C ^ 2 := pow_le_pow_left₀ hs hsC 2
  have hden : 0 < 6 * m ^ 5 := by positivity
  have hb : b ≤ 6 * m ^ 5 * C ^ 2 := by
    have hh := (div_le_iff₀ hden).mp (hbB.trans hBC)
    nlinarith only [hh]
  have hηb : η ^ 2 * b ≤ (6 * m ^ 5) / 4 := by
    calc η ^ 2 * b ≤ η ^ 2 * (6 * m ^ 5 * C ^ 2) :=
           mul_le_mul_of_nonneg_left hb (sq_nonneg η)
         _ = (6 * m ^ 5) * (η * C) ^ 2 := by ring
         _ = (6 * m ^ 5) / 4 := by rw [hηC]; ring
  let v := η ^ 2 * b / (6 * m ^ 5)
  have hv : v ≤ 1 / 4 := by
    apply (div_le_iff₀ hden).mpr
    linarith only [hηb]
  have hfactor : 1 ≤ 2 - u - v := by linarith
  have hmain : 0 ≤ m ^ 2 * η / a := by positivity
  have hrate :
      (2 * m ^ 2 * η - m * a ^ 2 * η ^ 2 * k ^ 2) / a -
        a ^ 3 * (2 * a) ^ (3 / 2 : ℝ) * η ^ 3 * k ^ 3 * L /
          (6 * m ^ 3) * d ^ (1 / 2 : ℝ) =
      (m ^ 2 * η / a) * (2 - u - v) := by
    dsimp only [u, v, b]
    field_simp
  refine ⟨hη, by positivity, ⟨by linarith, ?_, ?_⟩, ⟨hstep, ?_⟩, ?_⟩
  · exact (lt_div_iff₀ ha).mpr (by linarith)
  · exact (lt_div_iff₀ hdenak).mpr (by linarith)
  · change η ^ 2 * b < 6 * m ^ 5
    linarith only [hηb, hden]
  · rw [hrate]
    calc m ^ 2 / (2 * A * C) = m ^ 2 * η / A := by dsimp [η]; field_simp
         _ ≤ m ^ 2 * η / a := by gcongr
         _ = (m ^ 2 * η / a) * 1 := by ring
         _ ≤ (m ^ 2 * η / a) * (2 - u - v) := mul_le_mul_of_nonneg_left hfactor hmain

theorem tuning_bounds (p : LongTails.Setups.DobocK.Params)
    (hp : LongTails.Setups.DobocK.spec.valid p) :
    0 < stepSize p.toPublic ∧ 0 < contraction p.toPublic ∧
      StepSizeLemma5 (constants p.toPublic) ∧
      ∀ d : ℝ, 0 ≤ d → d ≤ p.Δ →
        StepSizeTheorem2 (constants p.toPublic) d ∧
          contraction p.toPublic ≤ rate (constants p.toPublic) d := by
  rcases curvature_bounds p hp with ⟨hm, hma, haA⟩
  rcases hp with ⟨hnet, hlam, hK, _, hmM, hL, hΔ, hε⟩
  have hk : (1 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hK
  have ht (d : ℝ) (hd : 0 ≤ d) (hdΔ : d ≤ p.Δ) :=
    scalar_tuning p.m (a (constants p.toPublic)) (curvatureBound p.toPublic)
      (p.K : ℝ) p.L p.Δ d (tuningScale p.toPublic) hm hma haA hk hL hΔ hd hdΔ rfl
  have h0 := ht 0 le_rfl hΔ
  refine ⟨h0.1, h0.2.1, h0.2.2.1, ?_⟩
  intro d hd hdΔ
  exact (ht d hd hdΔ).2.2.2

theorem geometric_accuracy (ρ r d Δ ε : ℝ)
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hr : r < 1)
    (hd : 0 ≤ d) (hdΔ : d ≤ Δ) (hε : 0 < ε) :
    (1 - r) ^ ⌈1 / ρ * Real.log (max 1 (Δ / ε))⌉₊ * d ≤ ε := by
  by_cases hΔε : Δ ≤ ε
  · have hmax : max 1 (Δ / ε) = 1 := max_eq_left ((div_le_one hε).mpr hΔε)
    simpa [hmax] using hdΔ.trans hΔε
  have hεΔ : ε < Δ := lt_of_not_ge hΔε
  have hΔ : 0 < Δ := hε.trans hεΔ
  have hratio : 0 < Δ / ε := div_pos hΔ hε
  have hmax : max 1 (Δ / ε) = Δ / ε := max_eq_right ((one_le_div hε).mpr hεΔ.le)
  rw [hmax]
  let K : ℕ := ⌈1 / ρ * Real.log (Δ / ε)⌉₊
  have hceil : Real.log (Δ / ε) ≤ (K : ℝ) * ρ := by
    apply (div_le_iff₀ hρ).mp
    simpa only [K, div_eq_mul_inv, mul_comm, mul_one, one_mul] using
      (Nat.le_ceil (1 / ρ * Real.log (Δ / ε)))
  have hbase : 1 - r ≤ Real.exp (-ρ) := by
    have hh := Real.add_one_le_exp (-ρ)
    linarith
  have hpow : (1 - r) ^ K ≤ Real.exp (-ρ) ^ K :=
    pow_le_pow_left₀ (by linarith) hbase K
  calc (1 - r) ^ K * d ≤ Real.exp (-ρ) ^ K * Δ :=
         mul_le_mul hpow hdΔ hd (by positivity)
       _ = Real.exp ((K : ℝ) * (-ρ)) * Δ := by rw [Real.exp_nat_mul]
       _ ≤ Real.exp (-Real.log (Δ / ε)) * Δ := by
         apply mul_le_mul_of_nonneg_right _ hΔ.le
         apply Real.exp_le_exp.mpr
         linarith only [hceil]
       _ = ε := by rw [Real.exp_neg, Real.exp_log hratio]; field_simp

theorem iterations_accuracy (p : LongTails.Setups.DobocK.Params)
    (hp : LongTails.Setups.DobocK.spec.valid p)
    (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (hA1 : Assumption1 (sourceInput p.toPublic) p.m p.M f)
    (hA2 : Assumption2 (sourceInput p.toPublic) p.L f)
    (hmin : IsMinOn (penalty (sourceInput p.toPublic) f) Set.univ p.xstar)
    (hgap : penalty (sourceInput p.toPublic) f p.x0 -
      penalty (sourceInput p.toPublic) f p.xstar ≤ p.Δ) :
    penalty (sourceInput p.toPublic) f
      (iterate (sourceInput p.toPublic) f (horizon p.toPublic)) -
      penalty (sourceInput p.toPublic) f p.xstar ≤ p.ε := by
  have ht := tuning_bounds p hp
  rcases hp with ⟨hnet, hlam, hK, hm, hmM, hL, hΔ, hε⟩
  have hd : 0 ≤ penalty (sourceInput p.toPublic) f p.x0 -
      penalty (sourceInput p.toPublic) f p.xstar := sub_nonneg.mpr (hmin (Set.mem_univ p.x0))
  have htd := ht.2.2.2 _ hd hgap
  have hr := theorem2 (constants p.toPublic) f hnet hlam ht.1 hK hm hmM hL
    hA1 hA2 ht.2.2.1 p.xstar hmin htd.1
  have hg := geometric_accuracy (contraction p.toPublic)
    (rate (constants p.toPublic) (penalty (sourceInput p.toPublic) f p.x0 -
      penalty (sourceInput p.toPublic) f p.xstar)) _ p.Δ p.ε ht.2.1 htd.2 hr.2.1 hd hgap hε
  have hh : (⌈1 / contraction p.toPublic * Real.log (max 1 (p.Δ / p.ε))⌉₊ : ℕ) =
      horizon p.toPublic := by
    change ⌈1 / (p.m ^ 2 / (2 * curvatureBound p.toPublic * tuningScale p.toPublic)) *
      Real.log (max 1 (p.Δ / p.ε))⌉₊ =
      ⌈2 * curvatureBound p.toPublic * tuningScale p.toPublic / p.m ^ 2 *
        Real.log (max 1 (p.Δ / p.ε))⌉₊
    rw [one_div_div]
  rw [hh] at hg
  exact (hr.2.2 (horizon p.toPublic)).trans hg

theorem execution_accuracy (p : LongTails.Setups.DobocK.Params)
    (hp : LongTails.Setups.DobocK.spec.valid p)
    (f : Fin p.n → EuclideanSpace ℝ (Fin p.dim) → ℝ)
    (O : Oracle (Stacked p.n p.dim) (LocalReply p.n p.dim) 1)
    (hadm : LongTails.Setups.DobocK.spec.admissible p f O)
    (seed : (algorithm p.toPublic).Seed) (ξ : (j : ℕ) → O.Seed j) :
    penalty (sourceInput p.toPublic) f
      (execute O (algorithm p.toPublic) (fun _ => horizon p.toPublic) seed ξ) -
      penalty (sourceInput p.toPublic) f p.xstar ≤ p.ε := by
  rcases hadm with ⟨hA1, hA2, hmin, hgap, hO⟩
  change penalty (sourceInput p.toPublic) f
    (execute O (dobocK (sourceInput p.toPublic)) (fun _ => horizon p.toPublic) seed ξ) -
      penalty (sourceInput p.toPublic) f p.xstar ≤ p.ε
  have he := execute_dobocK (sourceInput p.toPublic) f O hO (horizon p.toPublic) seed ξ
  exact (congrArg (fun x => penalty (sourceInput p.toPublic) f x -
    penalty (sourceInput p.toPublic) f p.xstar) he).trans_le
      (iterations_accuracy p hp f hA1 hA2 hmin hgap)

end OracleTemplate.DobocKTuning
