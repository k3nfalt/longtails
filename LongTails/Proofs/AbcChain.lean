import LongTails.Proofs.AbcChainProfiles
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

open scoped BigOperators RealInnerProductSpace Topology

namespace LongTails.Proofs.AbcChain

open LongTails.Proofs.AbcChainProfiles

noncomputable def link (a b : ℝ) : ℝ := psi (-a) * phi (-b) - psi a * phi b

noncomputable def linkA (a b : ℝ) : ℝ := -(dpsi (-a) * phi (-b)) - dpsi a * phi b

noncomputable def linkB (a b : ℝ) : ℝ := -(psi (-a) * dphi (-b)) - psi a * dphi b

lemma product_model (a b a' b' : ℝ) :
    |psi a' * phi b' - psi a * phi b - dpsi a * phi b * (a' - a) - psi a * dphi b * (b' - b)|
      ≤ 98 * (a' - a) ^ 2 + 4 * (b' - b) ^ 2 := by
  have e : psi a' * phi b' - psi a * phi b - dpsi a * phi b * (a' - a) -
      psi a * dphi b * (b' - b) =
      (psi a' - psi a - dpsi a * (a' - a)) * phi b' + dpsi a * (a' - a) * (phi b' - phi b) +
        psi a * (phi b' - phi b - dphi b * (b' - b)) := by ring
  rw [e]
  have h1 := psi_model a a'
  have h2 := phi_model b b'
  have h3 := phi_lipschitz b' b
  have p0 := phi_nonneg b'
  have p3 := phi_le b'
  have q0 := dpsi_nonneg a
  have q4 := dpsi_le a
  have s0 := psi_nonneg a
  have s1 := psi_le_one a
  have t1 : |(psi a' - psi a - dpsi a * (a' - a)) * phi b'| ≤ 96 * (a' - a) ^ 2 := by
    rw [abs_mul, abs_of_nonneg p0]
    nlinarith [abs_nonneg (psi a' - psi a - dpsi a * (a' - a)), sq_nonneg (a' - a)]
  have t2 : |dpsi a * (a' - a) * (phi b' - phi b)| ≤ 2 * (a' - a) ^ 2 + 2 * (b' - b) ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg q0]
    have hb : |phi b' - phi b| ≤ |b' - b| := h3
    have hx : |a' - a| * |b' - b| ≤ ((a' - a) ^ 2 + (b' - b) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|a' - a| - |b' - b|), sq_abs (a' - a), sq_abs (b' - b)]
    calc dpsi a * |a' - a| * |phi b' - phi b| ≤ 4 * |a' - a| * |b' - b| := by
          gcongr
      _ ≤ 2 * (a' - a) ^ 2 + 2 * (b' - b) ^ 2 := by nlinarith
  have t3 : |psi a * (phi b' - phi b - dphi b * (b' - b))| ≤ 2 * (b' - b) ^ 2 := by
    rw [abs_mul, abs_of_nonneg s0]
    nlinarith [abs_nonneg (phi b' - phi b - dphi b * (b' - b)), sq_nonneg (b' - b)]
  calc _ ≤ |(psi a' - psi a - dpsi a * (a' - a)) * phi b'| +
        |dpsi a * (a' - a) * (phi b' - phi b)| +
        |psi a * (phi b' - phi b - dphi b * (b' - b))| := abs_add_three _ _ _
    _ ≤ _ := by nlinarith

lemma link_model (a b a' b' : ℝ) :
    |link a' b' - link a b - linkA a b * (a' - a) - linkB a b * (b' - b)| ≤
      200 * ((a' - a) ^ 2 + (b' - b) ^ 2) := by
  have hn := product_model (-a) (-b) (-a') (-b')
  have hp := product_model a b a' b'
  have e : link a' b' - link a b - linkA a b * (a' - a) - linkB a b * (b' - b) =
      (psi (-a') * phi (-b') - psi (-a) * phi (-b) - dpsi (-a) * phi (-b) * (-a' - -a) -
        psi (-a) * dphi (-b) * (-b' - -b)) -
      (psi a' * phi b' - psi a * phi b - dpsi a * phi b * (a' - a) -
        psi a * dphi b * (b' - b)) := by
    simp only [link, linkA, linkB]; ring
  rw [e]
  have e1 : (-a' - -a) ^ 2 = (a' - a) ^ 2 := by ring
  have e2 : (-b' - -b) ^ 2 = (b' - b) ^ 2 := by ring
  rw [e1, e2] at hn
  calc _ ≤ _ := abs_sub_le_sum _ _
    _ ≤ _ := by nlinarith

lemma link_ge (a b : ℝ) : -3 ≤ link a b := by
  unfold link
  nlinarith [mul_nonneg (psi_nonneg (-a)) (phi_nonneg (-b)), psi_le_one a, psi_nonneg a,
    phi_le b, phi_nonneg b, mul_le_mul (psi_le_one a) (phi_le b) (phi_nonneg b) zero_le_one]

lemma link_le (a b : ℝ) : link a b ≤ 3 := by
  unfold link
  nlinarith [mul_nonneg (psi_nonneg a) (phi_nonneg b), psi_le_one (-a), psi_nonneg (-a),
    phi_le (-b), phi_nonneg (-b),
    mul_le_mul (psi_le_one (-a)) (phi_le (-b)) (phi_nonneg (-b)) zero_le_one]

lemma link_of_small {a : ℝ} (b : ℝ) (ha : |a| ≤ 1 / 4) : link a b = 0 := by
  have h1 := neg_abs_le a
  have h2 := le_abs_self a
  unfold link
  rw [psi_of_le (by linarith : -a ≤ 1 / 2), psi_of_le (by linarith : a ≤ 1 / 2)]
  ring

lemma linkA_of_small {a : ℝ} (b : ℝ) (ha : |a| ≤ 1 / 4) : linkA a b = 0 := by
  have h1 := neg_abs_le a
  have h2 := le_abs_self a
  unfold linkA
  rw [dpsi_of_le (by linarith : -a ≤ 1 / 2), dpsi_of_le (by linarith : a ≤ 1 / 2)]
  ring

lemma linkB_of_small {a : ℝ} (b : ℝ) (ha : |a| ≤ 1 / 4) : linkB a b = 0 := by
  have h1 := neg_abs_le a
  have h2 := le_abs_self a
  unfold linkB
  rw [psi_of_le (by linarith : -a ≤ 1 / 2), psi_of_le (by linarith : a ≤ 1 / 2)]
  ring

lemma linkA_nonpos (a b : ℝ) : linkA a b ≤ 0 := by
  unfold linkA
  nlinarith [mul_nonneg (dpsi_nonneg (-a)) (phi_nonneg (-b)),
    mul_nonneg (dpsi_nonneg a) (phi_nonneg b)]

lemma linkB_nonpos (a b : ℝ) : linkB a b ≤ 0 := by
  unfold linkB
  nlinarith [mul_nonneg (psi_nonneg (-a)) (dphi_nonneg (-b)),
    mul_nonneg (psi_nonneg a) (dphi_nonneg b)]

lemma linkA_abs (a b : ℝ) : |linkA a b| ≤ 24 := by
  rw [abs_of_nonpos (linkA_nonpos a b)]
  unfold linkA
  nlinarith [mul_le_mul (dpsi_le (-a)) (phi_le (-b)) (phi_nonneg (-b)) (by norm_num),
    mul_le_mul (dpsi_le a) (phi_le b) (phi_nonneg b) (by norm_num)]

lemma linkB_abs (a b : ℝ) : |linkB a b| ≤ 2 := by
  rw [abs_of_nonpos (linkB_nonpos a b)]
  unfold linkB
  nlinarith [mul_le_mul (psi_le_one (-a)) (dphi_le_one (-b)) (dphi_nonneg (-b)) zero_le_one,
    mul_le_mul (psi_le_one a) (dphi_le_one b) (dphi_nonneg b) zero_le_one]

lemma linkA_lipschitz (a b a' b' : ℝ) :
    |linkA a b - linkA a' b'| ≤ 384 * |a - a'| + 8 * |b - b'| := by
  have e : linkA a b - linkA a' b' =
      -((dpsi (-a) - dpsi (-a')) * phi (-b) + dpsi (-a') * (phi (-b) - phi (-b'))) -
      ((dpsi a - dpsi a') * phi b + dpsi a' * (phi b - phi b')) := by
    simp only [linkA]; ring
  rw [e]
  have l1 := dpsi_lipschitz (-a) (-a')
  have l2 := dpsi_lipschitz a a'
  have l3 := phi_lipschitz (-b) (-b')
  have l4 := phi_lipschitz b b'
  have e1 : |-a - -a'| = |a - a'| := by rw [← abs_neg]; ring_nf
  have e2 : |-b - -b'| = |b - b'| := by rw [← abs_neg]; ring_nf
  rw [e1] at l1
  rw [e2] at l3
  have k1 : |(dpsi (-a) - dpsi (-a')) * phi (-b)| ≤ 192 * |a - a'| := by
    rw [abs_mul, abs_of_nonneg (phi_nonneg _)]
    nlinarith [phi_le (-b), abs_nonneg (dpsi (-a) - dpsi (-a'))]
  have k2 : |dpsi (-a') * (phi (-b) - phi (-b'))| ≤ 4 * |b - b'| := by
    rw [abs_mul, abs_of_nonneg (dpsi_nonneg _)]
    nlinarith [dpsi_le (-a'), abs_nonneg (phi (-b) - phi (-b')), dpsi_nonneg (-a')]
  have k3 : |(dpsi a - dpsi a') * phi b| ≤ 192 * |a - a'| := by
    rw [abs_mul, abs_of_nonneg (phi_nonneg _)]
    nlinarith [phi_le b, abs_nonneg (dpsi a - dpsi a')]
  have k4 : |dpsi a' * (phi b - phi b')| ≤ 4 * |b - b'| := by
    rw [abs_mul, abs_of_nonneg (dpsi_nonneg _)]
    nlinarith [dpsi_le a', abs_nonneg (phi b - phi b'), dpsi_nonneg a']
  calc _ ≤ |(dpsi (-a) - dpsi (-a')) * phi (-b) + dpsi (-a') * (phi (-b) - phi (-b'))| +
        |(dpsi a - dpsi a') * phi b + dpsi a' * (phi b - phi b')| := by
          have h := abs_sub_le_sum
            (-((dpsi (-a) - dpsi (-a')) * phi (-b) + dpsi (-a') * (phi (-b) - phi (-b'))))
            ((dpsi a - dpsi a') * phi b + dpsi a' * (phi b - phi b'))
          rwa [abs_neg] at h
    _ ≤ _ := by
      linarith [abs_add_le ((dpsi (-a) - dpsi (-a')) * phi (-b))
        (dpsi (-a') * (phi (-b) - phi (-b'))),
        abs_add_le ((dpsi a - dpsi a') * phi b) (dpsi a' * (phi b - phi b'))]

lemma linkB_lipschitz (a b a' b' : ℝ) :
    |linkB a b - linkB a' b'| ≤ 8 * |a - a'| + 8 * |b - b'| := by
  have e : linkB a b - linkB a' b' =
      -((psi (-a) - psi (-a')) * dphi (-b) + psi (-a') * (dphi (-b) - dphi (-b'))) -
      ((psi a - psi a') * dphi b + psi a' * (dphi b - dphi b')) := by
    simp only [linkB]; ring
  rw [e]
  have l1 := psi_lipschitz (-a) (-a')
  have l2 := psi_lipschitz a a'
  have l3 := dphi_lipschitz (-b) (-b')
  have l4 := dphi_lipschitz b b'
  have e1 : |-a - -a'| = |a - a'| := by rw [← abs_neg]; ring_nf
  have e2 : |-b - -b'| = |b - b'| := by rw [← abs_neg]; ring_nf
  rw [e1] at l1
  rw [e2] at l3
  have k1 : |(psi (-a) - psi (-a')) * dphi (-b)| ≤ 4 * |a - a'| := by
    rw [abs_mul, abs_of_nonneg (dphi_nonneg _)]
    nlinarith [dphi_le_one (-b), abs_nonneg (psi (-a) - psi (-a')), dphi_nonneg (-b)]
  have k2 : |psi (-a') * (dphi (-b) - dphi (-b'))| ≤ 4 * |b - b'| := by
    rw [abs_mul, abs_of_nonneg (psi_nonneg _)]
    nlinarith [psi_le_one (-a'), abs_nonneg (dphi (-b) - dphi (-b')), psi_nonneg (-a')]
  have k3 : |(psi a - psi a') * dphi b| ≤ 4 * |a - a'| := by
    rw [abs_mul, abs_of_nonneg (dphi_nonneg _)]
    nlinarith [dphi_le_one b, abs_nonneg (psi a - psi a'), dphi_nonneg b]
  have k4 : |psi a' * (dphi b - dphi b')| ≤ 4 * |b - b'| := by
    rw [abs_mul, abs_of_nonneg (psi_nonneg _)]
    nlinarith [psi_le_one a', abs_nonneg (dphi b - dphi b'), psi_nonneg a']
  calc _ ≤ |(psi (-a) - psi (-a')) * dphi (-b) + psi (-a') * (dphi (-b) - dphi (-b'))| +
        |(psi a - psi a') * dphi b + psi a' * (dphi b - dphi b')| := by
          have h := abs_sub_le_sum
            (-((psi (-a) - psi (-a')) * dphi (-b) + psi (-a') * (dphi (-b) - dphi (-b'))))
            ((psi a - psi a') * dphi b + psi a' * (dphi b - dphi b'))
          rwa [abs_neg] at h
    _ ≤ _ := by
      linarith [abs_add_le ((psi (-a) - psi (-a')) * dphi (-b))
        (psi (-a') * (dphi (-b) - dphi (-b'))),
        abs_add_le ((psi a - psi a') * dphi b) (psi a' * (dphi b - dphi b'))]


section Vector

variable {n : ℕ}

abbrev Chain (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

noncomputable def chain (u : Chain n) : ℝ :=
  -phi (u 0) + ∑ i : Fin n, link (u i.castSucc) (u i.succ)

noncomputable def fieldFirst (u : Chain n) : Fin (n + 1) → ℝ :=
  Fin.cases (-dphi (u 0)) (fun _ => 0)

noncomputable def fieldA (u : Chain n) : Fin (n + 1) → ℝ :=
  Fin.lastCases 0 (fun i : Fin n => linkA (u i.castSucc) (u i.succ))

noncomputable def fieldB (u : Chain n) : Fin (n + 1) → ℝ :=
  Fin.cases 0 (fun i : Fin n => linkB (u i.castSucc) (u i.succ))

noncomputable def field (u : Chain n) : Chain n :=
  WithLp.toLp 2 (fun k => fieldFirst u k + fieldA u k + fieldB u k)

lemma field_apply (u : Chain n) (k : Fin (n + 1)) :
    field u k = fieldFirst u k + fieldA u k + fieldB u k := rfl

lemma sum_fieldFirst (u : Chain n) (h : Fin (n + 1) → ℝ) :
    ∑ k, fieldFirst u k * h k = -dphi (u 0) * h 0 := by
  rw [Fin.sum_univ_succ]; simp [fieldFirst]

lemma sum_fieldA (u : Chain n) (h : Fin (n + 1) → ℝ) :
    ∑ k, fieldA u k * h k = ∑ i : Fin n, linkA (u i.castSucc) (u i.succ) * h i.castSucc := by
  rw [Fin.sum_univ_castSucc]; simp [fieldA]

lemma sum_fieldB (u : Chain n) (h : Fin (n + 1) → ℝ) :
    ∑ k, fieldB u k * h k = ∑ i : Fin n, linkB (u i.castSucc) (u i.succ) * h i.succ := by
  rw [Fin.sum_univ_succ]; simp [fieldB]

lemma inner_field (u v : Chain n) :
    ⟪field u, v⟫ = -dphi (u 0) * v 0 +
      ∑ i : Fin n, (linkA (u i.castSucc) (u i.succ) * v i.castSucc +
        linkB (u i.castSucc) (u i.succ) * v i.succ) := by
  have h : ⟪field u, v⟫ = ∑ k, (fieldFirst u k + fieldA u k + fieldB u k) * v k := by
    simp [PiLp.inner_apply, RCLike.inner_apply, field, mul_comm]
  rw [h]
  simp only [add_mul, Finset.sum_add_distrib, sum_fieldFirst, sum_fieldA, sum_fieldB]
  ring

lemma sum_castSucc_sq_le (h : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, h i.castSucc ^ 2 ≤ ∑ k, h k ^ 2 := by
  rw [Fin.sum_univ_castSucc]; nlinarith [sq_nonneg (h (Fin.last n))]

lemma sum_succ_sq_le (h : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, h i.succ ^ 2 ≤ ∑ k, h k ^ 2 := by
  rw [Fin.sum_univ_succ]; nlinarith [sq_nonneg (h 0)]

lemma zero_sq_le (h : Fin (n + 1) → ℝ) : h 0 ^ 2 ≤ ∑ k, h k ^ 2 :=
  Finset.single_le_sum (f := fun k => h k ^ 2) (fun k _ => sq_nonneg (h k)) (Finset.mem_univ _)

lemma chain_model (u v : Chain n) :
    |chain v - chain u - ⟪field u, v - u⟫| ≤ 402 * ‖v - u‖ ^ 2 := by
  rw [inner_field, EuclideanSpace.real_norm_sq_eq]
  have e : chain v - chain u - (-dphi (u 0) * (v - u) 0 + ∑ i : Fin n,
      (linkA (u i.castSucc) (u i.succ) * (v - u) i.castSucc +
        linkB (u i.castSucc) (u i.succ) * (v - u) i.succ)) =
      -(phi (v 0) - phi (u 0) - dphi (u 0) * (v 0 - u 0)) +
        ∑ i : Fin n, (link (v i.castSucc) (v i.succ) - link (u i.castSucc) (u i.succ) -
          linkA (u i.castSucc) (u i.succ) * (v i.castSucc - u i.castSucc) -
          linkB (u i.castSucc) (u i.succ) * (v i.succ - u i.succ)) := by
    simp only [chain, PiLp.sub_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  rw [e]
  have h0 := phi_model (u 0) (v 0)
  have hs : |∑ i : Fin n, (link (v i.castSucc) (v i.succ) - link (u i.castSucc) (u i.succ) -
          linkA (u i.castSucc) (u i.succ) * (v i.castSucc - u i.castSucc) -
          linkB (u i.castSucc) (u i.succ) * (v i.succ - u i.succ))| ≤
      ∑ i : Fin n, 200 * ((v i.castSucc - u i.castSucc) ^ 2 + (v i.succ - u i.succ) ^ 2) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => link_model _ _ _ _))
  have hc := sum_castSucc_sq_le (fun k => (v - u) k)
  have hu := sum_succ_sq_le (fun k => (v - u) k)
  have hz := zero_sq_le (fun k => (v - u) k)
  simp only [PiLp.sub_apply] at hc hu hz
  rw [Finset.sum_congr rfl (fun i _ => mul_add 200 _ _), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum] at hs
  calc _ ≤ |-(phi (v 0) - phi (u 0) - dphi (u 0) * (v 0 - u 0))| + _ := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_neg]
      simp only [PiLp.sub_apply]
      nlinarith

lemma chain_hasGradientAt (u : Chain n) : HasGradientAt chain (field u) u := by
  rw [hasGradientAt_iff_isLittleO]
  have hb : (fun v => chain v - chain u - ⟪field u, v - u⟫) =O[𝓝 u]
      (fun v => ‖v - u‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound 402
    filter_upwards [] with v
    have hm := chain_model u v
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖v - u‖)] using hm
  exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub u (by norm_num : 1 < 2))

end Vector

end LongTails.Proofs.AbcChain
