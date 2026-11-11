import LongTails.Proofs.PhaseCertificate
import LongTails.Proofs.LogScaleCut
import LongTails.Proofs.BlackBoxValidity
import LongTails.Proofs.BlackBoxRun

open scoped BigOperators

namespace OracleTemplate.BlackBoxDiagonal

variable {d : ℕ}

@[simp] lemma ystep_apply (α : ℝ) (x v : Vec d) (i : Fin d) :
    ystep α x v i = (α * v i + x i) / (1 + α) := rfl

@[simp] lemma xstep_apply (m : Fin d → ℝ) (y g : Vec d) (i : Fin d) :
    xstep m y g i = y i - g i / m i := rfl

@[simp] lemma vstep_apply (m : Fin d → ℝ) (α μ : ℝ) (v y g : Vec d) (i : Fin d) :
    vstep m α μ v y g i = (1 - α) * v i + α * y i - α / μ * (g i / m i) := rfl

lemma ystep_self (α : ℝ) (hα : 0 < α) (b : Vec d) : ystep α b b = b := by
  ext i
  rw [ystep_apply]
  have : (1 + α) ≠ 0 := by linarith
  field_simp
  ring

lemma alph_sq (j : ℕ) : alph j ^ 2 = muh j := by
  unfold alph muh
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  norm_num

lemma alph_pos (j : ℕ) : 0 < alph j := by unfold alph; positivity

lemma alph_le (j : ℕ) : alph j ≤ 1 / 2 := by
  unfold alph
  have h : 1 ≤ Real.sqrt (2 ^ j) := by
    rw [Real.one_le_sqrt]; exact one_le_pow₀ (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

lemma muh_pos (j : ℕ) : 0 < muh j := by unfold muh; positivity

lemma len_pos (j : ℕ) : 1 ≤ len j := by
  unfold len
  have h1 : 1 ≤ Real.sqrt (2 ^ j) := by
    rw [Real.one_le_sqrt]; exact one_le_pow₀ (by norm_num)
  have h2 : 0 < Real.log (512 * (2 ^ j) ^ 3) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ (2 ^ j) ^ 3 := one_le_pow₀ (one_le_pow₀ (by norm_num))
    nlinarith
  apply Nat.one_le_iff_ne_zero.mpr
  intro h0
  rw [Nat.ceil_eq_zero] at h0
  nlinarith

lemma contraction (j : ℕ) : (1 - alph j) ^ len j ≤ 1 / (512 * 8 ^ j) := by
  have hα := alph_pos j
  have hα1 := alph_le j
  have h1 : (1 - alph j) ^ len j ≤ Real.exp (-(alph j * len j)) := by
    rw [show -(alph j * len j) = (len j : ℝ) * (-alph j) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-alph j)]) _
  have hlen : 2 * Real.sqrt (2 ^ j) * Real.log (512 * (2 ^ j) ^ 3) ≤ len j := Nat.le_ceil _
  have hs : 0 < Real.sqrt (2 ^ j) := by positivity
  have h2 : Real.log (512 * (2 ^ j) ^ 3) ≤ alph j * len j := by
    unfold alph
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : Real.exp (-(alph j * len j)) ≤ Real.exp (-Real.log (512 * (2 ^ j) ^ 3)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4 : Real.exp (-Real.log (512 * (2 ^ j) ^ 3)) = 1 / (512 * 8 ^ j) := by
    have e8 : ((2 : ℝ) ^ j) ^ 3 = 8 ^ j := by
      rw [← pow_mul, mul_comm j 3, pow_mul]; norm_num
    rw [Real.exp_neg, Real.exp_log (by positivity), e8, inv_eq_one_div]
  linarith

section Outcome

variable {f : Vec d → ℝ} {w : Fin d → ℝ} {μ : ℝ}

structure PhaseData (f : Vec d → ℝ) (θ : Fin d → ℝ) (j : ℕ) (base : Vec d)
    (H : ℕ → ℝ × Vec d) : Prop where
  cons : Cons f (metric θ) (alph j) (muh j) (len j) base H

variable {θ : Fin d → ℝ} {j : ℕ} {base : Vec d} {H : ℕ → ℝ × Vec d}

lemma PhaseData.atY (P : PhaseData f θ j base H) {k : ℕ} (hk : k < len j) :
    H (2 * k) = orc f (yAt (metric θ) (alph j) (muh j) base H k) := by
  rw [P.cons (2 * k) (by omega)]
  unfold phaseQuery
  have h1 : 2 * k ≠ 2 * len j := by omega
  simp only [h1, ↓reduceIte, Nat.mul_mod_right]
  rw [Nat.mul_div_cancel_left k (by norm_num)]

lemma PhaseData.atX (P : PhaseData f θ j base H) {k : ℕ} (hk : k < len j) :
    H (2 * k + 1) = orc f (xv (metric θ) (alph j) (muh j) base H (k + 1)).1 := by
  rw [P.cons (2 * k + 1) (by omega)]
  unfold phaseQuery
  have h1 : 2 * k + 1 ≠ 2 * len j := by omega
  have h2 : (2 * k + 1) % 2 = 1 := by omega
  have h3 : (2 * k + 1) / 2 = k := by omega
  simp only [h1, ↓reduceIte, h2, h3]
  rfl

lemma PhaseData.atZ (P : PhaseData f θ j base H) :
    H (2 * len j) = orc f (zAt (metric θ) (alph j) (muh j) base H (len j)) := by
  rw [P.cons (2 * len j) le_rfl]
  unfold phaseQuery
  simp

end Outcome

lemma find_none_val {θ : Fin d → ℝ} {cs : List (Cut d)} (h : firstViolated θ cs = none)
    {C : Cut d} (hC : C ∈ cs) : C.val θ ≤ 0 := by
  have := List.find?_eq_none.mp h C hC
  simpa using this

lemma find_some {θ : Fin d → ℝ} {cs : List (Cut d)} {C : Cut d}
    (h : firstViolated θ cs = some C) : C ∈ cs ∧ 0 < C.val θ := by
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  exact ⟨h1, by simpa using h2⟩

section Members

variable (m : Fin d → ℝ) (α μ : ℝ) (N : ℕ) (base : Vec d) (H : ℕ → ℝ × Vec d)

lemma mem_A {k : ℕ} (hk : k < N) :
    cutCoco (H (2 * k)).1 (H (2 * k + 1)).1 (yAt m α μ base H k) (xv m α μ base H (k + 1)).1
      (H (2 * k)).2 (H (2 * k + 1)).2 ∈ phaseCuts m α μ N base H := by
  dsimp only [phaseCuts]
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

lemma mem_AN :
    cutCoco (H (2 * N - 1)).1 (H (2 * N)).1 (xv m α μ base H N).1 (zAt m α μ base H N)
      (H (2 * N - 1)).2 (H (2 * N)).2 ∈ phaseCuts m α μ N base H := by
  dsimp only [phaseCuts]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))

lemma mem_B {k : ℕ} (hk : k < N) :
    cutSc μ (H (2 * N)).1 (H (2 * k)).1 (zAt m α μ base H N) (yAt m α μ base H k) (H (2 * k)).2 ∈
      phaseCuts m α μ N base H := by
  dsimp only [phaseCuts]
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

lemma mem_C :
    cutSc μ (H (2 * N - 1)).1 (H 0).1 (xv m α μ base H N).1 base (H 0).2 ∈
      phaseCuts m α μ N base H := by
  dsimp only [phaseCuts]
  exact List.mem_append_right _ (by simp)

lemma mem_D :
    cutMono μ (zAt m α μ base H N) base (H (2 * N)).2 (H 0).2 ∈ phaseCuts m α μ N base H := by
  dsimp only [phaseCuts]
  exact List.mem_append_right _ (by simp)

lemma mem_E :
    cutCocoMono (zAt m α μ base H N) (xv m α μ base H N).1 (H (2 * N)).2 (H (2 * N - 1)).2 ∈
      phaseCuts m α μ N base H := by
  dsimp only [phaseCuts]
  exact List.mem_append_right _ (by simp)

end Members

section Main

variable {f : Vec d → ℝ} {w : Fin d → ℝ} {μ : ℝ} {θ : Fin d → ℝ} {j : ℕ} {base : Vec d}
  {H : ℕ → ℝ × Vec d}

lemma yAt_zero_eq : yAt (metric θ) (alph j) (muh j) base H 0 = base := by
  simp only [yAt, xv]
  exact ystep_self _ (alph_pos j) base

lemma PhaseData.at0 (P : PhaseData f θ j base H) : H 0 = orc f base := by
  have := P.atY (k := 0) (len_pos j)
  rw [yAt_zero_eq] at this
  simpa using this

lemma PhaseData.atXN (P : PhaseData f θ j base H) :
    H (2 * len j - 1) = orc f (xv (metric θ) (alph j) (muh j) base H (len j)).1 := by
  have h := P.atX (k := len j - 1) (by have := len_pos j; omega)
  have e1 : 2 * (len j - 1) + 1 = 2 * len j - 1 := by have := len_pos j; omega
  have e2 : len j - 1 + 1 = len j := by have := len_pos j; omega
  rw [e1, e2] at h
  exact h

lemma PhaseData.agd (P : PhaseData f θ j base H) :
    PhaseRec (gradient f) (metric θ) (muh j) (alph j)
      (fun k => (xv (metric θ) (alph j) (muh j) base H k).1)
      (fun k => (xv (metric θ) (alph j) (muh j) base H k).2)
      (yAt (metric θ) (alph j) (muh j) base H) (len j) where
  m_pos := metric_pos θ
  α_pos := alph_pos j
  α_le := alph_le j
  μ_eq := (alph_sq j).symm
  v0 := rfl
  y_eq := by
    intro k _ i
    simp only [yAt, ystep_apply]
    have : (1 + alph j) ≠ 0 := by linarith [alph_pos j]
    field_simp
  x_eq := by
    intro k hk i
    have h := P.atY hk
    simp only [xv, xstep_apply]
    rw [h]
    rfl
  v_eq := by
    intro k hk i
    have h := P.atY hk
    simp only [xv, vstep_apply]
    rw [h]
    rfl

theorem phase_success (Hy : BHyp f w μ) (P : PhaseData f θ j base H) {J : Fin d → ℝ}
    (hlo : ∀ k, J k ≤ metric θ k) (hhi : ∀ k, metric θ k ≤ 4 * 2 ^ j * J k)
    (hnone : firstViolated θ (phaseCuts (metric θ) (alph j) (muh j) (len j) base H) = none) :
    isq J (gradient f (xv (metric θ) (alph j) (muh j) base H (len j)).1) ≤
      isq J (gradient f base) / (4 * 2 ^ j) := by
  have hN := len_pos j
  have hm := metric_pos θ
  have hJ : ∀ k, 0 < J k := fun k => by
    have := hhi k; have := hm k; nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) j]
  have hval := fun C hC => find_none_val (θ := θ) hnone (C := C) hC
  have hY : ∀ k, k < (len j) → H (2 * k) = orc f (yAt (metric θ) (alph j) (muh j) base H k) := fun k hk => P.atY hk
  have hX : ∀ k, k < (len j) → H (2 * k + 1) = orc f ((xv (metric θ) (alph j) (muh j) base H (k + 1)).1) := fun k hk => P.atX hk
  have hZ : H (2 * (len j)) = orc f (zAt (metric θ) (alph j) (muh j) base H (len j)) := P.atZ
  have hXN : H (2 * (len j) - 1) = orc f ((xv (metric θ) (alph j) (muh j) base H (len j)).1) := P.atXN
  have h0 : H 0 = orc f base := P.at0
  have hsubi : ∀ (a b : Vec d), isq (metric θ) (a - b) = ∑ i, (a i - b i) ^ 2 / (metric θ) i := fun a b => by
    unfold isq; exact Finset.sum_congr rfl fun i _ => by simp only [PiLp.sub_apply]
  have hsubw : ∀ (a b : Vec d), wsq (metric θ) (a - b) = ∑ i, (metric θ) i * (a i - b i) ^ 2 := fun a b => by
    unfold wsq; exact Finset.sum_congr rfl fun i _ => by simp only [PiLp.sub_apply]
  have cert := phase_certificate (F := f) (G := gradient f) (z := zAt (metric θ) (alph j) (muh j) base H (len j)) P.agd
    (fun k _ => Hy.conv _ _)
    (by
      intro k hk
      have := hval _ (mem_A (metric θ) (alph j) (muh j) (len j) base H hk)
      rw [cutCoco_val, hY k hk, hX k hk] at this
      simp only [orc] at this
      rw [hsubi]
      linarith)
    (by
      intro i
      show (xstep (metric θ) ((xv (metric θ) (alph j) (muh j) base H (len j)).1) (H (2 * (len j) - 1)).2) i = _
      rw [hXN]
      rfl)
    (by
      have := hval _ (mem_AN (metric θ) (alph j) (muh j) (len j) base H)
      rw [cutCoco_val, hXN, hZ] at this
      simp only [orc] at this
      rw [hsubi]
      linarith)
    (by
      intro k hk
      have := hval _ (mem_B (metric θ) (alph j) (muh j) (len j) base H hk)
      rw [cutSc_val, hY k hk, hZ] at this
      simp only [orc] at this
      rw [hsubw]
      linarith)
    (by
      have := hval _ (mem_C (metric θ) (alph j) (muh j) (len j) base H)
      rw [cutSc_val, hXN, h0] at this
      simp only [orc] at this
      show (muh j) / 2 * wsq (metric θ) ((xv (metric θ) (alph j) (muh j) base H (len j)).1 - base) ≤ f ((xv (metric θ) (alph j) (muh j) base H (len j)).1) - f base - dot (gradient f base) ((xv (metric θ) (alph j) (muh j) base H (len j)).1 - base)
      rw [hsubw]
      linarith)
    (by
      have := hval _ (mem_D (metric θ) (alph j) (muh j) (len j) base H)
      rw [cutMono_val, hZ, h0] at this
      simp only [orc] at this
      show (muh j) * wsq (metric θ) ((zAt (metric θ) (alph j) (muh j) base H (len j)) - base) ≤ dot (gradient f (zAt (metric θ) (alph j) (muh j) base H (len j)) - gradient f base) ((zAt (metric θ) (alph j) (muh j) base H (len j)) - base)
      rw [hsubw]
      linarith)
    (by
      have := hval _ (mem_E (metric θ) (alph j) (muh j) (len j) base H)
      rw [cutCocoMono_val, hZ, hXN] at this
      simp only [orc] at this
      rw [hsubi]
      linarith)
    (by
      have hc := contraction j
      have : (1 : ℝ) / (512 * 8 ^ j) ≤ (muh j) / 24 := by
        rw [show muh j / 24 = 1 / (96 * 2 ^ j) by unfold muh; field_simp; ring]
        apply one_div_le_one_div_of_le (by positivity)
        have : (2 : ℝ) ^ j ≤ 8 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
        have : (0 : ℝ) ≤ 2 ^ j := by positivity
        linarith
      linarith)
  have hb1 : 8 * (1 - (alph j)) ^ (len j) / (muh j) ≤ 1 / (16 * 4 ^ j) := by
    have hc := contraction j
    have e1 : 8 * (1 - alph j) ^ len j / muh j = 32 * 2 ^ j * (1 - alph j) ^ len j := by
      unfold muh; field_simp; ring
    have e8 : (8 : ℝ) ^ j = 2 ^ j * 4 ^ j := by
      rw [← mul_pow]; norm_num
    rw [e8] at hc
    rw [le_div_iff₀ (by positivity)] at hc
    rw [e1, le_div_iff₀ (by positivity)]
    have e2 : 32 * 2 ^ j * (1 - alph j) ^ len j * (16 * 4 ^ j) =
        (1 - alph j) ^ len j * (512 * (2 ^ j * 4 ^ j)) := by ring
    linarith
  have hmJ : ∀ g : Vec d, isq (metric θ) g ≤ isq J g := fun g =>
    Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_left (sq_nonneg _) (hJ i) (hlo i)
  have hJm : ∀ g : Vec d, isq J g ≤ 4 * 2 ^ j * isq (metric θ) g := fun g => by
    unfold isq
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hhi i
    have h2 := hm i
    rw [mul_div_assoc', div_le_div_iff₀ (hJ i) h2]
    nlinarith [sq_nonneg (g i)]
  have hq := isq_nonneg hm (gradient f base)
  calc isq J (gradient f ((xv (metric θ) (alph j) (muh j) base H (len j)).1)) ≤ 4 * 2 ^ j * isq (metric θ) (gradient f ((xv (metric θ) (alph j) (muh j) base H (len j)).1)) := hJm _
    _ ≤ 4 * 2 ^ j * (8 * (1 - (alph j)) ^ (len j) / (muh j) * isq (metric θ) (gradient f base)) :=
        mul_le_mul_of_nonneg_left cert (by positivity)
    _ ≤ 4 * 2 ^ j * (1 / (16 * 4 ^ j) * isq J (gradient f base)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hb1 (hmJ _) hq (by positivity)
    _ = isq J (gradient f base) / (4 * 2 ^ j) := by
        have e4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
        rw [e4]
        field_simp
        ring

theorem phase_cut_valid (Hy : BHyp f w μ) (P : PhaseData f θ j base H) (hμj : 4 * muh j ≤ μ)
    {C : Cut d} (hC : C ∈ phaseCuts (metric θ) (alph j) (muh j) (len j) base H) :
    (∀ k, 0 ≤ C.a k) ∧ (∀ k, 0 ≤ C.b k) ∧
      ∀ θ', (∀ i, w i ≤ metric θ' i ∧ metric θ' i ≤ 4 * w i) → C.val θ' ≤ 0 := by
  have hμh := (muh_pos j).le
  have hY : ∀ k, k < len j → H (2 * k) = orc f (yAt (metric θ) (alph j) (muh j) base H k) :=
    fun k hk => P.atY hk
  have hX : ∀ k, k < len j →
      H (2 * k + 1) = orc f (xv (metric θ) (alph j) (muh j) base H (k + 1)).1 :=
    fun k hk => P.atX hk
  have hZ := P.atZ (f := f)
  have hXN := P.atXN (f := f)
  have h0 := P.at0 (f := f)
  dsimp only [phaseCuts] at hC
  rcases List.mem_append.mp hC with h1 | h4
  · rcases List.mem_append.mp h1 with h2 | h3
    · rcases List.mem_append.mp h2 with hA | hAN
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hA
        have hk' := List.mem_range.mp hk
        rw [hY k hk', hX k hk']
        refine ⟨fun _ => by dsimp only [cutCoco, cutSc, cutMono, cutCocoMono]; positivity, fun _ => by dsimp only [cutCoco, cutSc, cutMono, cutCocoMono]; exact le_rfl, fun θ' hθ' => ?_⟩
        exact Hy.valid_coco (fun i => (hθ' i).1) _ _
      · rw [List.mem_singleton.mp hAN, hXN, hZ]
        refine ⟨fun _ => by dsimp only [cutCoco, cutSc, cutMono, cutCocoMono]; positivity, fun _ => by dsimp only [cutCoco, cutSc, cutMono, cutCocoMono]; exact le_rfl, fun θ' hθ' => ?_⟩
        exact Hy.valid_coco (fun i => (hθ' i).1) _ _
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h3
      have hk' := List.mem_range.mp hk
      rw [hY k hk', hZ]
      refine ⟨fun _ => by dsimp only [cutCoco, cutSc, cutMono, cutCocoMono]; exact le_rfl, fun _ => by dsimp only [cutCoco, cutSc, cutMono, cutCocoMono]; positivity, fun θ' hθ' => ?_⟩
      exact Hy.valid_sc hμh hμj (fun i => (hθ' i).2) _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
    rcases h4 with rfl | rfl | rfl
    · rw [hXN, h0]
      refine ⟨fun _ => by dsimp only [cutCoco, cutSc, cutMono, cutCocoMono]; exact le_rfl, fun _ => by dsimp only [cutCoco, cutSc, cutMono, cutCocoMono]; positivity, fun θ' hθ' => ?_⟩
      exact Hy.valid_sc hμh hμj (fun i => (hθ' i).2) _ _
    · rw [hZ, h0]
      refine ⟨fun _ => by dsimp only [cutCoco, cutSc, cutMono, cutCocoMono]; exact le_rfl, fun _ => by dsimp only [cutCoco, cutSc, cutMono, cutCocoMono]; positivity, fun θ' hθ' => ?_⟩
      exact Hy.valid_mono hμh hμj (fun i => (hθ' i).2) _ _
    · rw [hZ, hXN]
      refine ⟨fun _ => by dsimp only [cutCoco, cutSc, cutMono, cutCocoMono]; positivity, fun _ => by dsimp only [cutCoco, cutSc, cutMono, cutCocoMono]; exact le_rfl, fun θ' hθ' => ?_⟩
      exact Hy.valid_cocomono (fun i => (hθ' i).1) _ _

end Main

end OracleTemplate.BlackBoxDiagonal
