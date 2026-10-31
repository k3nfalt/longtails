import LongTails.Proofs.ComparisonOrthStep

open scoped RealInnerProductSpace

namespace OracleTemplate.ComparisonOrth

open QueryPlan

lemma recip_sq_tangent {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    3 / a ^ 2 - 2 * x / a ^ 3 ≤ 1 / x ^ 2 := by
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  have h1 : 0 ≤ (x - a) ^ 2 * (2 * x + a) := by positivity
  have h2 : 0 ≤ a ^ 2 * ((x - a) ^ 2 * (2 * x + a)) := by positivity
  nlinarith [h2]

lemma sum_inv_sq_ge (K : ℕ) (hK : 0 < K) (ρ : ℕ → ℝ) (hρ : ∀ k < K, 0 < ρ k) :
    (K : ℝ) ^ 3 / (∑ k ∈ Finset.range K, ρ k) ^ 2 ≤ ∑ k ∈ Finset.range K, 1 / ρ k ^ 2 := by
  set S := ∑ k ∈ Finset.range K, ρ k with hS
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hSpos : 0 < S := by
    apply Finset.sum_pos (fun k hk => hρ k (Finset.mem_range.mp hk))
    exact ⟨0, Finset.mem_range.mpr hK⟩
  set a := S / K with ha
  have hapos : 0 < a := by positivity
  have h1 : ∑ k ∈ Finset.range K, (3 / a ^ 2 - 2 * ρ k / a ^ 3) ≤
      ∑ k ∈ Finset.range K, 1 / ρ k ^ 2 :=
    Finset.sum_le_sum fun k hk => recip_sq_tangent (hρ k (Finset.mem_range.mp hk)) hapos
  have h2 : ∑ k ∈ Finset.range K, (3 / a ^ 2 - 2 * ρ k / a ^ 3) =
      (K : ℝ) ^ 3 / S ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_div, ← Finset.mul_sum, ← hS, ha]
    field_simp
    ring
  rw [← h2]; exact h1

noncomputable def stepFn {n : ℕ} (f : Pt n → ℝ) (x0 : Pt n) (R h : ℝ) (m : ℕ)
    (s : OrthState n) : OrthState n :=
  eval (cmp f) (orthStepPlan x0 R h m s)

lemma eval_orthPlan {n : ℕ} (f : Pt n → ℝ) (x0 : Pt n) (R h : ℝ) (m K : ℕ) :
    eval (cmp f) (orthPlan x0 R h m K) = ((stepFn f x0 R h m)^[K] (initState x0)).x := by
  simp only [orthPlan, eval_map, eval_iteratePlan]
  rfl

lemma tune_basic {n : ℕ} {T : ℝ} (hn : 1 ≤ n) (hT : 0 < T) :
    (1 : ℝ) ≤ ((n * ⌈T⌉₊ : ℕ) : ℝ) ∧ T ≤ ((n * ⌈T⌉₊ : ℕ) : ℝ) ∧
      (128 : ℝ) * ((n * ⌈T⌉₊ : ℕ) : ℝ) < 2 ^ (Nat.log2 (n * ⌈T⌉₊) + 8) := by
  have hc1 : 1 ≤ ⌈T⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hT).ne'
  have hN1 : 1 ≤ n * ⌈T⌉₊ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨by exact_mod_cast hN1, ?_, ?_⟩
  · calc T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
      _ ≤ ((n * ⌈T⌉₊ : ℕ) : ℝ) := by
          push_cast
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith [Nat.cast_nonneg (α := ℝ) ⌈T⌉₊]
  · have h := Nat.lt_log2_self (n := n * ⌈T⌉₊)
    have h' : ((n * ⌈T⌉₊ : ℕ) : ℝ) < 2 ^ (Nat.log2 (n * ⌈T⌉₊) + 1) := by exact_mod_cast h
    rw [show Nat.log2 (n * ⌈T⌉₊) + 8 = (Nat.log2 (n * ⌈T⌉₊) + 1) + 7 by ring, pow_add]
    have h7 : (2 : ℝ) ^ 7 = 128 := by norm_num
    rw [h7]
    linarith

lemma ternary_decay (j : ℕ) :
    ((12 * j : ℕ) + 1 : ℝ) ^ 2 * (2 / 3) ^ (12 * j) ≤ 169 / ((2 : ℝ) ^ j) ^ 5 := by
  have hj : (j : ℝ) ≤ 2 ^ j := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h1 : ((12 * j : ℕ) + 1 : ℝ) ^ 2 ≤ 169 * (2 ^ j) ^ 2 := by
    push_cast
    have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have h3 : ((2 : ℝ) / 3) ^ (12 * j) ≤ (1 / 128) ^ j := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) j
  have h4 : (0 : ℝ) < 2 ^ j := by positivity
  calc ((12 * j : ℕ) + 1 : ℝ) ^ 2 * (2 / 3) ^ (12 * j) ≤ 169 * (2 ^ j) ^ 2 * (1 / 128) ^ j :=
        mul_le_mul h1 h3 (by positivity) (by positivity)
    _ = 169 / ((2 : ℝ) ^ j) ^ 5 := by
        have h128 : (128 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 7 := by
          rw [show (128 : ℝ) = 2 ^ 7 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
        rw [div_pow, one_pow, h128]
        field_simp

lemma boxErr_le {m : ℕ} {M w R q : ℝ} (hq : q = (2 / 3) ^ m) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hRw : R ≤ w) :
    boxErr m M w R ≤ 3 * ((m : ℝ) + 1) ^ 2 * q * M * (2 * w) := by
  unfold boxErr
  rw [← hq]
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hm : (1 : ℝ) ≤ m + 1 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have h1 : M * (q * (R - -R)) ≤ M * (q * (w - -w)) := by
    apply mul_le_mul_of_nonneg_left _ hM; apply mul_le_mul_of_nonneg_left _ hq0; linarith
  have hA : 0 ≤ M * (q * (w - -w)) := by
    apply mul_nonneg hM; apply mul_nonneg hq0; linarith
  rw [show 3 * ((m : ℝ) + 1) ^ 2 * q * M * (2 * w) =
    3 * ((m : ℝ) + 1) ^ 2 * (M * (q * (w - -w))) by ring]
  set A := M * (q * (w - -w))
  set B := M * (q * (R - -R))
  have hm0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hsq : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have s1 : ((m : ℝ) + 1) * ((m + 1) * B + B) ≤ ((m : ℝ) + 1) * ((m + 1) * A + A) := by
    apply mul_le_mul_of_nonneg_left _ hm0
    have := mul_le_mul_of_nonneg_left h1 hm0
    linarith
  have s2 : ((m : ℝ) + 1) * ((m + 1) * A + A) + A ≤ 3 * ((m : ℝ) + 1) ^ 2 * A := by
    have t1 : ((m : ℝ) + 1) * A ≤ ((m : ℝ) + 1) ^ 2 * A := by
      apply mul_le_mul_of_nonneg_right _ hA; nlinarith
    have t2 : A ≤ ((m : ℝ) + 1) ^ 2 * A := le_mul_of_one_le_left hA hsq
    nlinarith
  linarith

section Main

variable {n : ℕ} {f : Pt n → ℝ} {L : ℝ}
  (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
  (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
include hc hg hlip

theorem orth_converges_core {x0 xs : Pt n} (hmin : IsMinOn f Set.univ xs) {R ε T h : ℝ}
    {m j K Nb : ℕ} (hn : 1 ≤ n) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hx0 : ‖x0 - xs‖ ≤ R)
    (hT : T = L * R ^ 2 / ε) (hm : m = 12 * j) (hN1 : (1 : ℝ) ≤ Nb) (hTN : T ≤ Nb)
    (hnN : (n : ℝ) ≤ Nb) (hjN : (128 : ℝ) * Nb < 2 ^ j) (hKpos : 1 ≤ K)
    (hK_le : (K : ℝ) ≤ 8 * Nb) (hK_ge : 36 * T ≤ (K : ℝ) ^ 2)
    (hh : h = R / (160 * n ^ 2 * K * T ^ 2)) :
    f (eval (cmp f) (orthPlan x0 R h m K)) - f xs ≤ ε := by
  have hTpos : 0 < T := by rw [hT]; positivity
  have hεT : ε * T = L * R ^ 2 := by rw [hT]; field_simp
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
  have hK0 : (0 : ℝ) < K := by linarith
  have hNb0 : (0 : ℝ) < Nb := by linarith
  set η := ε / (1152 * K * T) with hη
  have hηpos : 0 < η := by positivity
  set q := ((2 : ℝ) / 3) ^ m with hq
  have hdecay : ((m : ℝ) + 1) ^ 2 * q ≤ 169 / ((2 : ℝ) ^ j) ^ 5 := by
    have := ternary_decay j
    simpa [hm, hq] using this
  have hbox_ok : ∀ w, R ≤ w → w ≤ 2 * K * R →
      boxErr m (L * (w + 3 * R)) w R ≤ η := by
    intro w hRw hw
    have hw0 : 0 ≤ w := hR.le.trans hRw
    have hM0 : 0 ≤ L * (w + 3 * R) := mul_nonneg hL.le (by linarith)
    refine (boxErr_le hq hM0 hR.le hRw).trans ?_
    have hM : L * (w + 3 * R) ≤ 5 * K * L * R := by
      have h3 : 3 * R ≤ 3 * K * R := by nlinarith
      have := mul_le_mul_of_nonneg_left (show w + 3 * R ≤ 5 * K * R by linarith) hL.le
      linarith
    have hpow : (128 * (Nb : ℝ)) ^ 5 ≤ ((2 : ℝ) ^ j) ^ 5 :=
      pow_le_pow_left₀ (by positivity) hjN.le 5
    have hq' : ((m : ℝ) + 1) ^ 2 * q ≤ 169 / (128 * (Nb : ℝ)) ^ 5 :=
      hdecay.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow)
    have hq0 : 0 ≤ ((m : ℝ) + 1) ^ 2 * q := by positivity
    have hbig : 3 * ((m : ℝ) + 1) ^ 2 * q * (L * (w + 3 * R)) * (2 * w) ≤
        60 * K ^ 2 * L * R ^ 2 * (((m : ℝ) + 1) ^ 2 * q) := by
      have := mul_le_mul hM hw hw0 (le_trans hM0 hM)
      have h6 := mul_le_mul_of_nonneg_left this
        (show (0 : ℝ) ≤ 6 * (((m : ℝ) + 1) ^ 2 * q) by positivity)
      linarith only [h6]
    refine hbig.trans ?_
    rw [hη, le_div_iff₀ (by positivity)]
    have hK3 : (K : ℝ) ^ 3 ≤ 512 * Nb ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) hK_le 3; nlinarith only [this]
    have hT2 : T ^ 2 ≤ (Nb : ℝ) ^ 2 := pow_le_pow_left₀ hTpos.le hTN 2
    have e1 : 60 * K ^ 2 * L * R ^ 2 * (((m : ℝ) + 1) ^ 2 * q) * (1152 * K * T) =
        69120 * (K : ℝ) ^ 3 * T * (L * R ^ 2) * (((m : ℝ) + 1) ^ 2 * q) := by ring
    rw [e1, ← hεT]
    have hN5 : (0 : ℝ) < (128 * (Nb : ℝ)) ^ 5 := pow_pos (by linarith) 5
    have key : 69120 * (K : ℝ) ^ 3 * T ^ 2 * (((m : ℝ) + 1) ^ 2 * q) ≤ 1 := by
      calc 69120 * (K : ℝ) ^ 3 * T ^ 2 * (((m : ℝ) + 1) ^ 2 * q)
          ≤ 69120 * (512 * Nb ^ 3) * Nb ^ 2 * (169 / (128 * (Nb : ℝ)) ^ 5) := by
            gcongr
        _ ≤ 1 := by
            rw [mul_div_assoc', div_le_one hN5]
            nlinarith only [pow_nonneg (show (0 : ℝ) ≤ Nb by linarith) 5]
    have := mul_le_mul_of_nonneg_left key hε.le
    linarith only [this]
  have hsqK1 : 1 ≤ Real.sqrt K := Real.one_le_sqrt.mpr hK1
  have hsqK_le : Real.sqrt K ≤ K := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsqKsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt (by linarith)
  set θ := 1 / (2 * Real.sqrt K) with hθ
  set θg := 3 / (16 * Real.sqrt K * T) with hθg
  have hθhalf : θ ≤ 1 / 2 := by
    rw [hθ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → OrthState n,
      ∀ k, S k = (stepFn f x0 R h m)^[k] (initState x0) := ⟨_, fun _ => rfl⟩
  have hS0 : S 0 = initState x0 := by rw [hSdef]; rfl
  have hSsucc : ∀ k, S (k + 1) = eval (cmp f) (orthStepPlan x0 R h m (S k)) := by
    intro k; rw [hSdef, hSdef, Function.iterate_succ_apply']; rfl
  have hbox_k : ∀ k, k + 1 ≤ K → Inv f x0 R η k (S k) →
      boxErr m (L * (max R ‖(S k).x - x0‖ + 3 * R)) (max R ‖(S k).x - x0‖) R ≤ η := by
    intro k hk hI
    apply hbox_ok _ (le_max_left _ _)
    apply max_le
    · have := mul_le_mul_of_nonneg_right hK1 hR.le
      linarith only [this, mul_nonneg hK0.le hR.le]
    · have h1 := hI.xnorm
      have hk' : (2 * (k : ℝ) + 1) ≤ 2 * K := by
        have : ((k : ℝ) + 1) ≤ K := by exact_mod_cast hk
        linarith only [this]
      have h2 : ‖(S k).x - x0‖ ^ 2 ≤ (2 * K * R) ^ 2 := by
        have a := mul_le_mul_of_nonneg_right hk' (sq_nonneg R)
        have b := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 * K - 1 by linarith only [hK1])
          (show (0 : ℝ) ≤ 2 * K by linarith only [hK1])) (sq_nonneg R)
        nlinarith only [h1, a, b]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h2
  have hinv : ∀ k, k ≤ K → Inv f x0 R η k (S k) ∧
      (S k).d = ∑ i ∈ Finset.range k, (S (i + 1)).u3 ∧
      (∀ i, i ≤ k → f (S k).x ≤ f (S i).x) := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨by rw [hS0]; exact inv_init f x0 hR.le hηpos.le, by rw [hS0]; simp [initState], ?_⟩
        intro i hi; rw [Nat.le_zero.mp hi]
    | succ k ih =>
        intro hk
        obtain ⟨hI, hd, hmono⟩ := ih (Nat.le_of_succ_le hk)
        have hst := orth_step hc hg hlip hmin (θ := θ) (θg := θg) (h := h) (m := m) (K := K)
          hL hR hηpos hε hθhalf hx0 hk hI (hbox_k k hk hI)
        rw [hSsucc k]
        refine ⟨hst.1, ?_, ?_⟩
        · rw [hst.2.2.1, Finset.sum_range_succ, hd, hSsucc k]
        · intro i hi
          rcases Nat.lt_or_eq_of_le hi with hi | hi
          · exact hst.2.1.trans (hmono i (Nat.lt_succ_iff.mp hi))
          · rw [hi, hSsucc k]
  rw [eval_orthPlan, ← hSdef K]
  by_contra hcon
  push Not at hcon
  obtain ⟨hIK, hdK, hmonoK⟩ := hinv K le_rfl
  have hδ : ∀ k, k ≤ K → ε < f (S k).x - f xs := fun k hk => by
    have := hmonoK k hk; linarith
  have hg0 : gradient f xs = 0 := PLHessian.grad_zero_of_min hL hg hlip hmin
  have hδ0 : f x0 - f xs ≤ L * R ^ 2 / 2 := by
    have h2 := Gradient.smooth_upper_bound hg hlip xs x0
    rw [hg0, inner_zero_left, add_zero] at h2
    have h3 : ‖x0 - xs‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx0 2
    have h4 := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ L / 2 by linarith only [hL])
    linarith only [h2, h4]
  have hT2 : 2 < T := by
    have h0 := hδ 0 (Nat.zero_le _)
    rw [hS0] at h0
    simp only [initState] at h0
    have : ε * 2 < ε * T := by linarith only [h0, hδ0, hεT]
    exact lt_of_mul_lt_mul_left this hε.le
  have hKT : 2 ≤ (K : ℝ) * T := by
    have := mul_le_mul_of_nonneg_right hK1 hTpos.le
    linarith only [this, hT2]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqn : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith only [mul_nonneg (show (0 : ℝ) ≤ n - 1 by linarith only [hn1])
      (show (0 : ℝ) ≤ n by linarith only [hn1])]
  have hsqn_sq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
  have hpow_m : (128 * (Nb : ℝ)) ^ 3 ≤ 2 ^ m := by
    have h1 : (128 * (Nb : ℝ)) ^ 3 ≤ ((2 : ℝ) ^ j) ^ 3 := pow_le_pow_left₀ (by positivity) hjN.le 3
    have h2 : ((2 : ℝ) ^ j) ^ 3 ≤ 2 ^ m := by
      rw [← pow_mul, hm]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith only [h1, h2]
  have hnpos : (0 : ℝ) < n := by linarith only [hn1]
  have hhpos : 0 < h := by rw [hh]; positivity
  have hdir : ∀ x, 3 * ε / (4 * R) ≤ ‖gradient f x‖ →
      ‖eval (cmp f) (dirPlan x h m) - nrm (gradient f x)‖ ≤ θg := by
    intro x hgx
    have hgpos : 0 < ‖gradient f x‖ := lt_of_lt_of_le (by positivity) hgx
    have hεR : 3 * ε / (4 * R) = 3 * (L * R) / (4 * T) := by
      rw [show ε = L * R ^ 2 / T by rw [hT]; field_simp]; field_simp
    rw [hεR] at hgx
    have hgx' : 3 * (L * R) ≤ ‖gradient f x‖ * (4 * T) := (div_le_iff₀ (by positivity)).mp hgx
    have hLh : L * h = L * R / (160 * n ^ 2 * K * T ^ 2) := by rw [hh]; ring
    have hbig : 2 * (n + 1) * (L * h) * Real.sqrt n ≤ ‖gradient f x‖ := by
      have h1 : 2 * ((n : ℝ) + 1) * Real.sqrt n ≤ 4 * n ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_left hsqn
          (show (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) by linarith only [hn1]),
          mul_nonneg (show (0 : ℝ) ≤ n - 1 by linarith only [hn1])
            (show (0 : ℝ) ≤ n by linarith only [hn1])]
      have h2 : 2 * ((n : ℝ) + 1) * (L * h) * Real.sqrt n ≤ 4 * n ^ 2 * (L * h) := by
        have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ L * h)
        linarith only [this]
      have h3 : 4 * (n : ℝ) ^ 2 * (L * h) = L * R / (40 * K * T ^ 2) := by
        rw [hLh]; field_simp; ring
      have h4 : L * R / (40 * K * T ^ 2) ≤ 3 * (L * R) / (4 * T) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left (show (4 : ℝ) ≤ 120 * K * T by linarith only [hKT])
          (show (0 : ℝ) ≤ L * R * T by positivity)
        linarith only [this]
      linarith only [h2, h3, h4, hgx]
    have hacc := dir_accuracy hc hg hlip x hhpos hL.le hn m hgpos hbig
    refine hacc.trans ?_
    have t1 : 2 * Real.sqrt n * (2 / 2 ^ m) ≤ 9 / (80 * Real.sqrt K * T) := by
      rw [show 2 * Real.sqrt n * (2 / 2 ^ m) = 4 * Real.sqrt n / 2 ^ m by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have hNb1 : (1 : ℝ) ≤ Nb := hN1
      have e1 : 4 * Real.sqrt n * (80 * Real.sqrt K * T) ≤ 2560 * (Nb : ℝ) ^ 3 := by
        have a1 : Real.sqrt n ≤ Nb := hsqn.trans hnN
        have a2 : Real.sqrt K ≤ 8 * Nb := hsqK_le.trans hK_le
        have := mul_le_mul (mul_le_mul a1 a2 (Real.sqrt_nonneg _) (by positivity)) hTN
          hTpos.le (by positivity)
        linarith only [this]
      linarith only [e1, hpow_m, pow_nonneg hNb0.le 3]
    have t2 : 2 * Real.sqrt n * (9 * (L * h) * Real.sqrt n / (2 * ‖gradient f x‖)) ≤
        6 / (80 * Real.sqrt K * T) := by
      have e1 : 2 * Real.sqrt n * (9 * (L * h) * Real.sqrt n / (2 * ‖gradient f x‖)) =
          9 * n * (L * h) / ‖gradient f x‖ := by
        rw [show (9 : ℝ) * n = 9 * Real.sqrt n ^ 2 by rw [hsqn_sq]]
        field_simp
      rw [e1, div_le_div_iff₀ hgpos (by positivity)]
      have e2 : 9 * (n : ℝ) * (L * h) * (80 * Real.sqrt K * T) =
          9 * (L * R) * Real.sqrt K / (2 * n * K * T) := by
        rw [hLh]; field_simp; ring
      rw [e2, div_le_iff₀ (by positivity)]
      have hnK : Real.sqrt K ≤ (n : ℝ) * K := by
        have := mul_le_mul_of_nonneg_right hn1 hK0.le
        linarith only [hsqK_le, this]
      have a := mul_le_mul_of_nonneg_left hgx' (show (0 : ℝ) ≤ 3 * n * K by positivity)
      have b := mul_le_mul_of_nonneg_left hnK (show (0 : ℝ) ≤ 9 * (L * R) by positivity)
      linarith only [a, b]
    calc 2 * Real.sqrt n * (2 / 2 ^ m + 9 * (L * h) * Real.sqrt n / (2 * ‖gradient f x‖))
        = 2 * Real.sqrt n * (2 / 2 ^ m) +
            2 * Real.sqrt n * (9 * (L * h) * Real.sqrt n / (2 * ‖gradient f x‖)) := by ring
      _ ≤ 9 / (80 * Real.sqrt K * T) + 6 / (80 * Real.sqrt K * T) := add_le_add t1 t2
      _ = θg := by rw [hθg]; field_simp; ring
  have hηe : η * (1152 * K * T) = ε := by rw [hη]; field_simp
  have h2η : 2 * η ≤ ε / 4 := by
    have := mul_le_mul_of_nonneg_left (show (16 : ℝ) ≤ 1152 * K * T by linarith only [hKT])
      hηpos.le
    linarith only [this, hηe, hε]
  have hDη : 8 * L * η * K * R ^ 2 ≤ ε ^ 2 / 16 := by
    have e : 8 * L * η * K * R ^ 2 = ε ^ 2 / 144 := by
      linear_combination (-(8 * η * K)) * hεT + (ε / 144) * hηe
    rw [e]; linarith only [sq_nonneg ε]
  have h25 : 25 * L * R ^ 2 * η ≤ ε ^ 2 := by
    have e1 : 25 * L * R ^ 2 * η = 25 * (T * η) * ε := by
      linear_combination (-(25 * η)) * hεT
    have e2 : 1152 * K * (T * η) = ε := by linear_combination hηe
    have hTη : 0 ≤ T * η := by positivity
    have h1 : 25 * (T * η) ≤ ε := by
      have := mul_le_mul_of_nonneg_right hK1 hTη
      linarith only [e2, this, hTη]
    rw [e1]
    have := mul_le_mul_of_nonneg_right h1 hε.le
    linarith only [this]
  have hθgT : θg * T = 3 / (16 * Real.sqrt K) := by rw [hθg]; field_simp
  have hθg8 : 8 * θg * L * R ^ 2 ≤ 3 * ε * θ := by
    apply le_of_eq
    linear_combination (-(8 * θg)) * hεT + (8 * ε) * hθgT - (3 * ε) * hθ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℝ, ∀ k, ρ k = ⟪(S (k + 1)).u3, x0 - xs⟫ + θ * R :=
    ⟨_, fun _ => rfl⟩
  have hprog : ∀ k, k < K → 0 < ρ k ∧
      1 / (f (S k).x - f xs) + 1 / (8 * L * ρ k ^ 2) ≤ 1 / (f (S (k + 1)).x - f xs) := by
    intro k hk
    obtain ⟨hI, -, -⟩ := hinv k hk.le
    have hst := orth_step hc hg hlip hmin (θ := θ) (θg := θg) (h := h) (m := m) (K := K)
      hL hR hηpos hε hθhalf hx0 hk hI (hbox_k k hk hI)
    have hp := hst.2.2.2 (hδ k hk.le).le h2η hDη h25 hθg8 hdir
    rw [← hSsucc k, ← hρ k] at hp
    obtain ⟨hρpos, -, hdec⟩ := hp
    refine ⟨hρpos, ?_⟩
    set δ := f (S k).x - f xs
    set δ' := f (S (k + 1)).x - f xs
    have hδpos : 0 < δ := by linarith only [hδ k hk.le, hε]
    have hδ'pos : 0 < δ' := by linarith only [hδ (k + 1) hk, hε]
    set u := δ / (8 * L * ρ k ^ 2) with hu
    have hu0 : 0 ≤ u := by positivity
    have hdec' : δ' ≤ δ * (1 - u) := by
      have : δ ^ 2 / (8 * L * ρ k ^ 2) = δ * u := by rw [hu]; ring
      linarith only [hdec, this]
    have hu1 : u < 1 := by
      by_contra h1; push Not at h1
      have : δ * (1 - u) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδpos.le (by linarith only [h1])
      linarith only [hdec', this, hδ'pos]
    rw [div_add_div _ _ hδpos.ne' (by positivity), div_le_div_iff₀ (by positivity) hδ'pos]
    have e : (1 * (8 * L * ρ k ^ 2) + δ * 1) = 8 * L * ρ k ^ 2 * (1 + u) := by
      rw [hu]; field_simp
    rw [e]
    have : δ' * (1 + u) ≤ δ := by
      nlinarith only [mul_le_mul_of_nonneg_right hdec' (show (0 : ℝ) ≤ 1 + u by linarith only [hu0]),
        mul_nonneg hδpos.le (sq_nonneg u)]
    have h8 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 8 * L * ρ k ^ 2)
    linarith only [h8]
  have htel : ∀ k, k ≤ K → ∑ i ∈ Finset.range k, 1 / (8 * L * ρ i ^ 2) ≤
      1 / (f (S k).x - f xs) := by
    intro k
    induction k with
    | zero =>
        intro _
        simp only [Finset.range_zero, Finset.sum_empty]
        exact (one_div_pos.mpr (by linarith only [hδ 0 (Nat.zero_le _), hε])).le
    | succ k ih =>
        intro hk
        rw [Finset.sum_range_succ]
        have h1 := ih (Nat.le_of_succ_le hk)
        have h2 := (hprog k hk).2
        linarith only [h1, h2]
  have hsumρ : ∑ k ∈ Finset.range K, ρ k ≤ 3 / 2 * Real.sqrt K * R := by
    have e : ∑ k ∈ Finset.range K, ρ k = ⟪(S K).d, x0 - xs⟫ + K * (θ * R) := by
      simp only [hρ]
      rw [hdK, sum_inner, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    rw [e]
    have hd : ‖(S K).d‖ ≤ Real.sqrt K := by
      rw [← Real.sqrt_sq (norm_nonneg _)]; exact Real.sqrt_le_sqrt hIK.dnorm
    have h1 : ⟪(S K).d, x0 - xs⟫ ≤ Real.sqrt K * R :=
      (real_inner_le_norm _ _).trans (mul_le_mul hd hx0 (norm_nonneg _) (Real.sqrt_nonneg _))
    have hKθ : (K : ℝ) * θ = Real.sqrt K / 2 := by
      have hsK : 0 < Real.sqrt K := by positivity
      rw [hθ]; field_simp; linarith only [hsqKsq]
    have h2 : (K : ℝ) * (θ * R) = Real.sqrt K * R / 2 := by
      rw [← mul_assoc, hKθ]; ring
    linarith only [h1, h2]
  have hρpos : ∀ k < K, 0 < ρ k := fun k hk => (hprog k hk).1
  have hpm := sum_inv_sq_ge K hKpos ρ hρpos
  have hsum_pos : 0 < ∑ k ∈ Finset.range K, ρ k :=
    Finset.sum_pos (fun k hk => hρpos k (Finset.mem_range.mp hk)) ⟨0, Finset.mem_range.mpr hKpos⟩
  have hfin := htel K le_rfl
  have hsplit : ∑ k ∈ Finset.range K, 1 / (8 * L * ρ k ^ 2) =
      (1 / (8 * L)) * ∑ k ∈ Finset.range K, 1 / ρ k ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; field_simp
  rw [hsplit] at hfin
  have hS2 : (∑ k ∈ Finset.range K, ρ k) ^ 2 ≤ 9 / 4 * K * R ^ 2 := by
    have := pow_le_pow_left₀ hsum_pos.le hsumρ 2
    rw [mul_pow, mul_pow, hsqKsq] at this; linarith only [this]
  have hlow : (K : ℝ) ^ 3 / (9 / 4 * K * R ^ 2) ≤ ∑ k ∈ Finset.range K, 1 / ρ k ^ 2 :=
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hS2).trans hpm
  have hδK := hδ K le_rfl
  set δK := f (S K).x - f xs
  have hδKpos : 0 < δK := by linarith only [hδK, hε]
  have key : (1 / (8 * L)) * ((K : ℝ) ^ 3 / (9 / 4 * K * R ^ 2)) ≤ 1 / δK :=
    (mul_le_mul_of_nonneg_left hlow (by positivity)).trans hfin
  have e2 : (1 / (8 * L)) * ((K : ℝ) ^ 3 / (9 / 4 * K * R ^ 2)) = K ^ 2 / (18 * L * R ^ 2) := by
    field_simp; ring
  rw [e2, div_le_div_iff₀ (by positivity) hδKpos] at key
  have : (K : ℝ) ^ 2 * δK ≤ 18 * (L * R ^ 2) := by linarith only [key]
  rw [← hεT] at this
  have a := mul_le_mul_of_nonneg_right hK_ge hδKpos.le
  have b := mul_pos hTpos (show (0 : ℝ) < 2 * δK - ε by linarith only [hδK, hε])
  linarith only [this, a, b]

theorem orth_converges {x0 xs : Pt n} (hmin : IsMinOn f Set.univ xs) {R ε : ℝ}
    (hn : 1 ≤ n) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hx0 : ‖x0 - xs‖ ≤ R) :
    f (eval (cmp f) (orthPlan x0 R
      (R / (160 * n ^ 2 * (⌈6 * Real.sqrt (L * R ^ 2 / ε)⌉₊ + 1 : ℕ) * (L * R ^ 2 / ε) ^ 2))
      (12 * (Nat.log2 (n * ⌈L * R ^ 2 / ε⌉₊) + 8))
      (⌈6 * Real.sqrt (L * R ^ 2 / ε)⌉₊ + 1))) - f xs ≤ ε := by
  set T := L * R ^ 2 / ε with hT
  have hTpos : 0 < T := by positivity
  obtain ⟨hN1, hTN, hjN⟩ := tune_basic (T := T) hn hTpos
  have hnN : (n : ℝ) ≤ ((n * ⌈T⌉₊ : ℕ) : ℝ) := by
    have hc1 : 1 ≤ ⌈T⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hTpos).ne'
    exact_mod_cast Nat.le_mul_of_pos_right n hc1
  have hsqT : Real.sqrt T ≤ ((n * ⌈T⌉₊ : ℕ) : ℝ) := by
    rcases le_total T 1 with h1 | h1
    · exact (Real.sqrt_le_one.mpr h1).trans hN1
    · refine le_trans ?_ hTN
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hK_le : ((⌈6 * Real.sqrt T⌉₊ + 1 : ℕ) : ℝ) ≤ 8 * ((n * ⌈T⌉₊ : ℕ) : ℝ) := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 6 * Real.sqrt T by positivity)
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hK_ge : 36 * T ≤ ((⌈6 * Real.sqrt T⌉₊ + 1 : ℕ) : ℝ) ^ 2 := by
    have h1 : 6 * Real.sqrt T ≤ ((⌈6 * Real.sqrt T⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (6 * Real.sqrt T)]
    have h2 : (6 * Real.sqrt T) ^ 2 = 36 * T := by
      rw [mul_pow, Real.sq_sqrt hTpos.le]; ring
    nlinarith [Real.sqrt_nonneg T]
  exact orth_converges_core hc hg hlip hmin hn hL hR hε hx0 hT rfl hN1 hTN hnN hjN
    (Nat.le_add_left 1 _) hK_le hK_ge rfl

end Main

def planIdx {Q R U : Type} {k : ℕ} (_ : QueryPlan Q R U k) : ℕ := k

lemma orth_len_le {n : ℕ} (x0 : Pt n) (R h : ℝ) (m K : ℕ) (hm : 3 ≤ m) :
    planIdx (orthPlan x0 R h m K) ≤ K * (m * (3 * n + 7 * m ^ 2)) := by
  unfold planIdx
  rw [mul_comm]
  apply Nat.mul_le_mul_left
  ring_nf
  nlinarith [Nat.zero_le n, Nat.zero_le (n * m)]

lemma execute_cmp {n : ℕ} {U : Type} (f : Pt n → ℝ) (O : Oracle (Pt n × Pt n) Bool)
    (hO : ∀ hist q s, O.answer hist q s = decide (f q.2.1 ≤ f q.2.2))
    (q0 : Pt n × Pt n) (u0 : U) {k K : ℕ} (plan : Unit → QueryPlan (Pt n × Pt n) Bool U k)
    (hk : k ≤ K) (ξ : (i : ℕ) → O.Seed i) :
    execute O (QueryPlan.algorithm ⟨MeasureTheory.Measure.dirac (), inferInstance⟩ q0 u0 k plan)
      (fun _ => K) () ξ = eval (cmp f) (plan ()) := by
  erw [StochasticGradient.execute_advance_of_answer _ _ _ _ _ (fun _ q => cmp f q.2)
    (fun hist q => by rw [hO]; rfl)]
  change QueryPlan.output u0 (StochasticGradient.advance
    (fun _ s => QueryPlan.update s (cmp f (QueryPlan.query q0 s))) K 0 ⟨k, plan ()⟩) = _
  rw [QueryPlan.advance_plan_of_le (cmp f) q0 _ hk]
  rfl

end OracleTemplate.ComparisonOrth
