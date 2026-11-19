import LongTails.Proofs.WeakMintyHybridExecution
import LongTails.Setups.WeakMintySecondOrderExpected

open scoped RealInnerProductSpace

namespace OracleTemplate.WeakMintyHybrid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable {F : E → E} {J : E → E →L[ℝ] E} {L₁ L₂ ρ ε : ℝ} {z : E}

lemma fallback_progress_residual (h : Hyp F J L₁ L₂ ρ z)
    (hL₁ : 0 < L₁) (hρ : 0 ≤ ρ) (hρL : ρ * L₁ < 2)
    (x : E) (hε : 0 ≤ ε) (hg : ε ≤ ‖F x‖) :
    let δ := margin L₁ ρ
    let η := (1 - δ / 4) / L₁
    let y := picardPoint F x η (innerCount δ)
    ‖x - (δ / 4 * η) • F y - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 -
      δ ^ 2 * ε ^ 2 / (256 * L₁ ^ 2) := by
  dsimp only
  let δ := margin L₁ ρ
  let η := (1 - δ / 4) / L₁
  let T : E → E := fun y => x - η • F y
  let y := picardPoint F x η (innerCount δ)
  let s := y - x
  have hδ : 0 < δ := margin_pos hρL
  have hδ1 : δ ≤ 1 := margin_le_one hL₁.le hρ
  have hη := WeakMintyTaylor.fallback_margin hL₁ hδ hδ1 (margin_relation L₁ ρ)
  have hηL : η * L₁ = 1 - δ / 4 := by dsimp [η]; field_simp
  have hT : ∀ u v, ‖T u - T v‖ ≤ (1 - δ / 4) * ‖u - v‖ := by
    intro u v
    have hid : T u - T v = -(η • (F u - F v)) := by dsimp [T]; module
    rw [hid, norm_neg, norm_smul, Real.norm_of_nonneg hη.1.le]
    have hh := mul_le_mul_of_nonneg_left (h.lip u v) hη.1.le
    change η * ‖F u - F v‖ ≤ η * (L₁ * ‖u - v‖) at hh
    rw [← mul_assoc, hηL] at hh
    exact hh
  have hcert := WeakMintyPicard.iterate_residual T x hδ hδ1 hT
    (show (4 / δ) * Real.log (1024 / δ ^ 2) ≤ (innerCount δ : ℝ) from Nat.le_ceil _)
  have he : ‖s + η • F y‖ ≤ (δ / 16) * ‖s‖ := by
    have hid : s + η • F y = y - T y := by dsimp [s, T]; abel
    rw [hid]
    exact hcert
  have hlip : ‖F x - F y‖ ≤ L₁ * ‖s‖ := by
    simpa only [s, norm_sub_rev x y] using h.lip x y
  have hanchor := WeakMintyTaylor.fallback_anchor_bound s (F x) (F y) hL₁ hη.1
    (show δ / 16 ≤ 1 by linarith) (show η * L₁ ≤ 1 by rw [hηL]; linarith)
    (show 3 / 4 ≤ η * L₁ by rw [hηL]; linarith) he hlip
  have hm : -(ρ / 2) * ‖F y‖ ^ 2 ≤ ⟪F y, x + s - z⟫ := by
    simpa [s] using h.minty y
  have hp := WeakMintyTaylor.relaxed_progress x z s (F y) hη.1 hρ hδ hδ1 hη.2 hm he
  have hb : ε ≤ 4 * L₁ * ‖s‖ := hg.trans hanchor
  have hsq : ε ^ 2 ≤ 16 * L₁ ^ 2 * ‖s‖ ^ 2 := by
    have := pow_le_pow_left₀ hε hb 2
    nlinarith
  have hcharge : δ ^ 2 * ε ^ 2 / (256 * L₁ ^ 2) ≤ δ ^ 2 / 16 * ‖s‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hsq (sq_nonneg δ)
    nlinarith
  exact hp.trans (by dsimp [δ, η, y, s] at *; linarith)

noncomputable def blockDecrease (L₁ L₂ ρ ε : ℝ) : ℝ :=
  if 64 * L₂ * ε < (margin L₁ ρ) ^ 2 * L₁ ^ 2 then (margin L₁ ρ) ^ 4 * ε / (16384 * L₂)
  else (margin L₁ ρ) ^ 2 * ε ^ 2 / (256 * L₁ ^ 2)

lemma block_progress_min (h : Hyp F J L₁ L₂ ρ z)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hρ : 0 ≤ ρ) (hρL : ρ * L₁ < 2)
    (hε : 0 < ε) (x : E) :
    ∃ n ≤ innerCount (margin L₁ ρ) + 2,
      (∃ y, (step L₁ L₂ ρ ε F J)^[n] (.anchor x) = .done y ∧ ‖F y‖ ≤ ε) ∨
      (∃ x', (step L₁ L₂ ρ ε F J)^[n] (.anchor x) = .anchor x' ∧
        ‖x' - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 - blockDecrease L₁ L₂ ρ ε) := by
  let δ := margin L₁ ρ
  have hδ : 0 < δ := margin_pos hρL
  have hδ1 : δ ≤ 1 := margin_le_one hL₁.le hρ
  have hK := innerCount_pos hδ hδ1
  by_cases hg : ‖F x‖ ≤ ε
  · refine ⟨1, by omega, Or.inl ⟨x, ?_, hg⟩⟩
    simp [step, hybrid, exactReply, hg]
  by_cases hcap : ‖F x‖ ≤ δ ^ 2 * L₁ ^ 2 / (64 * L₂)
  · have hreg : 64 * L₂ * ε < δ ^ 2 * L₁ ^ 2 := by
      have h1 : ε < δ ^ 2 * L₁ ^ 2 / (64 * L₂) := lt_of_lt_of_le (lt_of_not_ge hg) hcap
      rw [lt_div_iff₀ (by positivity)] at h1
      linarith
    have hD : blockDecrease L₁ L₂ ρ ε = δ ^ 4 * ε / (16384 * L₂) := by
      simp only [blockDecrease, δ] at hreg ⊢
      rw [ite_eq_left hreg]
    obtain ⟨n, hn, hres⟩ := block_progress h hL₁ hL₂ hρ hρL hε x
    refine ⟨n, hn, ?_⟩
    rcases hres with hres | ⟨x', hx', hb⟩
    · exact Or.inl hres
    · exact Or.inr ⟨x', hx', by rw [hD]; exact hb⟩
  · by_cases hreg : 64 * L₂ * ε < δ ^ 2 * L₁ ^ 2
    · have hD : blockDecrease L₁ L₂ ρ ε = δ ^ 4 * ε / (16384 * L₂) := by
        simp only [blockDecrease, δ] at hreg ⊢
        rw [ite_eq_left hreg]
      obtain ⟨n, hn, hres⟩ := block_progress h hL₁ hL₂ hρ hρL hε x
      refine ⟨n, hn, ?_⟩
      rcases hres with hres | ⟨x', hx', hb⟩
      · exact Or.inl hres
      · exact Or.inr ⟨x', hx', by rw [hD]; exact hb⟩
    · have hD : blockDecrease L₁ L₂ ρ ε = δ ^ 2 * ε ^ 2 / (256 * L₁ ^ 2) := by
        simp only [blockDecrease, δ] at hreg ⊢
        rw [ite_eq_right hreg]
      let η := (1 - δ / 4) / L₁
      let T : E → E := fun y => x - η • F y
      let y := picardPoint F x η (innerCount δ)
      have hs : (step L₁ L₂ ρ ε F J)^[innerCount δ + 1] (.anchor x) =
          finish δ ε x y η (F y) := by
        rw [Function.iterate_succ_apply]
        have ha : step L₁ L₂ ρ ε F J (.anchor x) =
            .picard x (T x) (innerCount δ - 1) := by
          simp only [step, hybrid, exactReply, Sum.elim_inl, hg, ↓reduceIte]
          change (if ‖F x‖ ≤ δ ^ 2 * L₁ ^ 2 / (64 * L₂) then _ else _) = _
          rw [ite_eq_right hcap]
        rw [ha]
        have hKi : innerCount δ - 1 + 1 = innerCount δ := by omega
        nth_rw 1 [← hKi]
        rw [picard_steps]
        change finish δ ε x (T^[innerCount δ - 1] (T x)) η
          (F (T^[innerCount δ - 1] (T x))) = _
        rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, hKi]
        rfl
      refine ⟨innerCount δ + 1, by change innerCount δ + 1 ≤ innerCount δ + 2; omega, ?_⟩
      by_cases hv : ‖F y‖ ≤ ε
      · exact Or.inl ⟨y, hs.trans (by simp [finish, hv]), hv⟩
      · refine Or.inr ⟨x - (δ / 4 * η) • F y, hs.trans (by simp [finish, hv]), ?_⟩
        rw [hD]
        exact fallback_progress_residual h hL₁ hρ hρL x hε.le (le_of_not_ge hg)

lemma many_blocks_min (h : Hyp F J L₁ L₂ ρ z)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hρ : 0 ≤ ρ) (hρL : ρ * L₁ < 2)
    (hε : 0 < ε) (x0 : E) (N : ℕ) :
    ∃ n ≤ N * (innerCount (margin L₁ ρ) + 2),
      (∃ y, (step L₁ L₂ ρ ε F J)^[n] (.anchor x0) = .done y ∧ ‖F y‖ ≤ ε) ∨
      (∃ x, (step L₁ L₂ ρ ε F J)^[n] (.anchor x0) = .anchor x ∧
        ‖x - z‖ ^ 2 ≤ ‖x0 - z‖ ^ 2 - N * blockDecrease L₁ L₂ ρ ε) := by
  induction N with
  | zero => exact ⟨0, by simp, Or.inr ⟨x0, rfl, by simp⟩⟩
  | succ N ih =>
    obtain ⟨n, hn, hd | ⟨x, hx, hb⟩⟩ := ih
    · exact ⟨n, hn.trans (Nat.mul_le_mul_right _ (Nat.le_succ N)), Or.inl hd⟩
    · obtain ⟨m, hm, ⟨y, hy, hacc⟩ | ⟨x', hx', hb'⟩⟩ :=
        block_progress_min h hL₁ hL₂ hρ hρL hε x
      · refine ⟨m + n, ?_, Or.inl ⟨y, ?_, hacc⟩⟩
        · rw [Nat.succ_mul]
          omega
        · rw [Function.iterate_add_apply, hx, hy]
      · refine ⟨m + n, ?_, Or.inr ⟨x', ?_, ?_⟩⟩
        · rw [Nat.succ_mul]
          omega
        · rw [Function.iterate_add_apply, hx, hx']
        · push_cast
          linarith

lemma execute_accurate_min (h : Hyp F J L₁ L₂ ρ z)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hρ : 0 ≤ ρ) (hρL : ρ * L₁ < 2)
    (hε : 0 < ε) (x0 : E) {N K : ℕ}
    (hN : ‖x0 - z‖ ^ 2 < N * blockDecrease L₁ L₂ ρ ε)
    (hK : N * (innerCount (margin L₁ ρ) + 2) ≤ K)
    (oracle : Oracle (E ⊕ E) (E × (E →L[ℝ] E)))
    (hF : ∀ k seed x, oracle.answer k (0, Sum.inl x) seed = (F x, 0))
    (hJ : ∀ k seed x, oracle.answer k (0, Sum.inr x) seed = (0, J x))
    (seed : (hybrid L₁ L₂ ρ ε x0).Seed) (ξ : (k : ℕ) → oracle.Seed k) :
    ‖F (execute oracle (hybrid L₁ L₂ ρ ε x0) (fun _ => K) seed ξ)‖ ≤ ε := by
  have hw : ∃ n ≤ N * (innerCount (margin L₁ ρ) + 2), ∃ y,
      (step L₁ L₂ ρ ε F J)^[n] (.anchor x0) = .done y ∧ ‖F y‖ ≤ ε := by
    obtain ⟨n, hn, hd | ⟨x, _, hb⟩⟩ := many_blocks_min h hL₁ hL₂ hρ hρL hε x0 N
    · exact ⟨n, hn, hd⟩
    · nlinarith [sq_nonneg ‖x - z‖]
  obtain ⟨y, hy, hacc⟩ := done_after hK hw
  have horacle : ∀ k query seed, oracle.answer k (0, query) seed = exactReply F J query := by
    intro k query seed
    cases query with
    | inl x => exact hF k seed x
    | inr x => exact hJ k seed x
  rw [execute_eq_of_answer_eq oracle (exactReply F J) horacle
    (hybrid L₁ L₂ ρ ε x0) K seed ξ, execute_iterate]
  change ‖F ((hybrid L₁ L₂ ρ ε x0).output ((step L₁ L₂ ρ ε F J)^[K] (.anchor x0)))‖ ≤ ε
  rw [hy]
  exact hacc

end OracleTemplate.WeakMintyHybrid

open MeasureTheory

namespace OracleTemplate.WeakMintyHybrid

lemma margin_half {L₁ ρ : ℝ} (hρL : ρ * L₁ ≤ 1) : 1 / 2 ≤ margin L₁ ρ := by
  dsimp [margin]
  linarith

lemma blockDecrease_pos {L₁ L₂ ρ ε : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hε : 0 < ε)
    (hδ : 0 < margin L₁ ρ) : 0 < blockDecrease L₁ L₂ ρ ε := by
  unfold blockDecrease
  split_ifs <;> positivity

lemma radius_le_blocks {L₁ L₂ ρ ε R : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hε : 0 < ε)
    (hρ : 0 ≤ ρ) (hρL : ρ * L₁ ≤ 1) :
    R ^ 2 ≤ 2 ^ 18 * min (L₂ * R ^ 2 / ε) (L₁ ^ 2 * R ^ 2 / ε ^ 2) *
      blockDecrease L₁ L₂ ρ ε := by
  set δ := margin L₁ ρ with hδdef
  have hδ : 1 / 2 ≤ δ := margin_half hρL
  have hδ1 : δ ≤ 1 := margin_le_one hL₁.le hρ
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  unfold blockDecrease
  rw [← hδdef]
  split_ifs with hreg
  · have hle : L₂ * R ^ 2 / ε ≤ L₁ ^ 2 * R ^ 2 / ε ^ 2 := by
      rw [div_le_div_iff₀ hε (by positivity)]
      have : δ ^ 2 ≤ 1 := by nlinarith
      have h1 : L₂ * ε ≤ L₁ ^ 2 := by nlinarith [sq_nonneg L₁]
      have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hR2 hε.le)
      nlinarith
    rw [min_eq_left hle]
    have hδ4 : 1 / 16 ≤ δ ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hδ 4]
    have he : 2 ^ 18 * (L₂ * R ^ 2 / ε) * (δ ^ 4 * ε / (16384 * L₂)) = 16 * δ ^ 4 * R ^ 2 := by
      field_simp
      ring
    rw [he]
    nlinarith
  · push Not at hreg
    have hδ2 : 1 / 4 ≤ δ ^ 2 := by nlinarith
    have hL : L₁ ^ 2 ≤ 256 * L₂ * ε := by
      nlinarith [mul_le_mul_of_nonneg_right hδ2 (sq_nonneg L₁)]
    have hmin : L₁ ^ 2 * R ^ 2 / (256 * ε ^ 2) ≤ min (L₂ * R ^ 2 / ε) (L₁ ^ 2 * R ^ 2 / ε ^ 2) := by
      apply le_min
      · rw [div_le_div_iff₀ (by positivity) hε]
        have := mul_le_mul_of_nonneg_left hL (mul_nonneg hR2 hε.le)
        nlinarith
      · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [sq_nonneg ε, hε]
    have hD : 0 ≤ δ ^ 2 * ε ^ 2 / (256 * L₁ ^ 2) := by positivity
    have hstep := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin
      (by norm_num : (0 : ℝ) ≤ 2 ^ 18)) hD
    have he : 2 ^ 18 * (L₁ ^ 2 * R ^ 2 / (256 * ε ^ 2)) * (δ ^ 2 * ε ^ 2 / (256 * L₁ ^ 2)) =
        4 * δ ^ 2 * R ^ 2 := by
      field_simp
      ring
    rw [he] at hstep
    nlinarith [mul_le_mul_of_nonneg_right hδ2 hR2]

lemma innerCount_le {δ : ℝ} (hδ : 1 / 2 ≤ δ) (hδ1 : δ ≤ 1) :
    innerCount δ + 2 ≤ 276 := by
  have hδ0 : 0 < δ := by linarith
  have h := innerCount_bound hδ0 hδ1
  have hlog : Real.log (2 / δ) ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 / δ by positivity)
    have h4 : 2 / δ ≤ 4 := by rw [div_le_iff₀ hδ0]; linarith
    linarith
  have hlog0 : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hb : 46 * Real.log (2 / δ) / δ ≤ 276 := by
    rw [div_le_iff₀ hδ0]
    nlinarith
  have : ((innerCount δ + 2 : ℕ) : ℝ) ≤ 276 := by push_cast; linarith
  exact_mod_cast this

lemma upper_budget {L₁ L₂ ρ ε R : ℝ} (hρ : 0 ≤ ρ) (hρL : ρ * L₁ ≤ 1) (hL₁ : 0 ≤ L₁)
    (hM : 0 ≤ min (L₂ * R ^ 2 / ε) (L₁ ^ 2 * R ^ 2 / ε ^ 2)) :
    (⌈2 ^ 18 * min (L₂ * R ^ 2 / ε) (L₁ ^ 2 * R ^ 2 / ε ^ 2)⌉₊ + 1) *
        (innerCount (margin L₁ ρ) + 2) ≤
      ⌈2 ^ 27 * (1 + min (L₂ * R ^ 2 / ε) (L₁ ^ 2 * R ^ 2 / ε ^ 2))⌉₊ := by
  set M := min (L₂ * R ^ 2 / ε) (L₁ ^ 2 * R ^ 2 / ε ^ 2)
  have hK := innerCount_le (margin_half hρL) (margin_le_one hL₁ hρ)
  have hN : ((⌈2 ^ 18 * M⌉₊ + 1 : ℕ) : ℝ) ≤ 2 ^ 18 * M + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ 18 * M by positivity)
    push_cast
    linarith
  have hKr : ((innerCount (margin L₁ ρ) + 2 : ℕ) : ℝ) ≤ 276 := by exact_mod_cast hK
  have hp := mul_le_mul hN hKr (by positivity) (by positivity)
  have hfin : (2 ^ 18 * M + 2) * 276 ≤ 2 ^ 27 * (1 + M) := by nlinarith
  have hreal := (hp.trans hfin).trans (Nat.le_ceil _)
  exact_mod_cast hreal

lemma blocks_sufficient {L₁ L₂ ρ ε R r : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hε : 0 < ε)
    (hρ : 0 ≤ ρ) (hρL : ρ * L₁ ≤ 1) (hr : 0 ≤ r) (hrR : r ≤ R) :
    r ^ 2 < (⌈2 ^ 18 * min (L₂ * R ^ 2 / ε) (L₁ ^ 2 * R ^ 2 / ε ^ 2)⌉₊ + 1 : ℕ) *
      blockDecrease L₁ L₂ ρ ε := by
  have hD := blockDecrease_pos (ρ := ρ) hL₁ hL₂ hε
    (by have := margin_half hρL; linarith)
  have hb := radius_le_blocks (R := R) hL₁ hL₂ hε hρ hρL
  have hc : 2 ^ 18 * min (L₂ * R ^ 2 / ε) (L₁ ^ 2 * R ^ 2 / ε ^ 2) <
      ((⌈2 ^ 18 * min (L₂ * R ^ 2 / ε) (L₁ ^ 2 * R ^ 2 / ε ^ 2)⌉₊ + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil (2 ^ 18 * min (L₂ * R ^ 2 / ε) (L₁ ^ 2 * R ^ 2 / ε ^ 2))
    push_cast
    linarith
  have hr2 := pow_le_pow_left₀ hr hrR 2
  have := mul_lt_mul_of_pos_right hc hD
  linarith

open LongTails.Setups.WeakMintySecondOrderExpected in
lemma upper_success (q : Params) (hq : spec.valid q) (F : q.E → q.E)
    (oracle : Oracle (q.E ⊕ q.E) (q.E × (q.E →L[ℝ] q.E)))
    (hadm : spec.admissible q F oracle) :
    let A := hybrid q.L₁ q.L₂ q.ρ q.ε q.x0
    let K := ⌈2 ^ 27 * (1 + min (q.L₂ * q.R ^ 2 / q.ε) (q.L₁ ^ 2 * q.R ^ 2 / q.ε ^ 2))⌉₊
    spec.successful q F (fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
        execute oracle A (fun _ => K) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩ := by
  intro A K
  rcases hq with ⟨hL₁, hL₂, hρ, hρL, hR, hε⟩
  rcases hadm with ⟨J, hF, hJ, hder, hjlip, hlip, z, -, hdist, hm⟩
  have h : Hyp F J q.L₁ q.L₂ q.ρ z := ⟨hder, hjlip, hlip, hm⟩
  have hρL2 : q.ρ * q.L₁ < 2 := by linarith
  have hM0 : 0 ≤ min (q.L₂ * q.R ^ 2 / q.ε) (q.L₁ ^ 2 * q.R ^ 2 / q.ε ^ 2) :=
    le_min (by positivity) (by positivity)
  have horacle : ∀ k query seed, oracle.answer k (0, query) seed = exactReply F J query := by
    intro k query seed
    cases query with
    | inl x => exact hF k seed x
    | inr x => exact hJ k seed x
  set c := ‖F (A.output ((fun s => A.update s (exactReply F J (A.query s).2))^[K]
    (A.initial ())))‖ with hc
  have hconst : (fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
      ‖F (execute oracle A (fun _ => K) seed.1 seed.2)‖) = fun _ => c := by
    funext seed
    rw [execute_eq_of_answer_eq oracle (exactReply F J) horacle A K seed.1 seed.2,
      execute_iterate]
    rfl
  obtain ⟨ξ0⟩ := nonempty_of_isProbabilityMeasure (oracle.law : Measure ((k : ℕ) → oracle.Seed k))
  have hcε : c ≤ q.ε := by
    have hacc := execute_accurate_min h hL₁ hL₂ hρ hρL2 hε q.x0
      (blocks_sufficient hL₁ hL₂ hε hρ hρL (norm_nonneg _) hdist)
      (upper_budget hρ hρL hL₁.le hM0) oracle hF hJ () ξ0
    have hv := congrFun hconst ((), ξ0)
    simp only at hv
    rw [hv] at hacc
    exact hacc
  let P : ProbabilityMeasure (A.Seed × ((k : ℕ) → oracle.Seed k)) :=
    ⟨(A.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩
  change Integrable (fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
      ‖F (execute oracle A (fun _ => K) seed.1 seed.2)‖) (P : Measure _) ∧
    (∫ seed : A.Seed × ((k : ℕ) → oracle.Seed k),
      ‖F (execute oracle A (fun _ => K) seed.1 seed.2)‖ ∂(P : Measure _)) ≤ q.ε
  rw [hconst]
  refine ⟨integrable_const c, ?_⟩
  rw [integral_const]
  simp only [probReal_univ, one_smul]
  exact hcε

end OracleTemplate.WeakMintyHybrid
