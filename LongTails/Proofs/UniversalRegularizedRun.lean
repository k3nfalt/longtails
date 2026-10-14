import LongTails.Algorithms.UniversalRegularizedExtragradient
import LongTails.Proofs.UniversalRegularizedStep
import LongTails.Proofs.Execution

open scoped RealInnerProductSpace

namespace OracleTemplate.HolderMonotone

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def trans (F : E → E) (ε : ℝ) (x0 : E) (σ : UregState E) : UregState E :=
  uregStep ε x0 σ (F (if σ.phase = 1 then σ.x - σ.s • σ.g else σ.x))

def Done (F : E → E) (ε : ℝ) (σ : UregState E) : Prop := σ.phase = 2 ∧ ‖F σ.x‖ ≤ ε

lemma trans_done {F : E → E} {ε : ℝ} (x0 : E) {σ : UregState E} (h : Done F ε σ) :
    trans F ε x0 σ = σ := by
  simp [trans, uregStep, h.1]

lemma iterate_done {F : E → E} {ε : ℝ} (x0 : E) {σ : UregState E} (h : Done F ε σ) (n : ℕ) :
    (trans F ε x0)^[n] σ = σ :=
  Function.iterate_fixed (trans_done x0 h) n

structure StageInv (F : E → E) (ε : ℝ) (x0 z : E) (ρ sb q D M : ℝ) (n : ℕ)
    (σ : UregState E) : Prop where
  rho : σ.ρ = ρ
  ex : ∃ a f : ℕ, n = 2 * a + f + σ.phase ∧ σ.s * 2 ^ f = ρ / (2 * ε) ∧ sb ≤ 2 * σ.s ∧
    ‖σ.x - z‖ ^ 2 ≤ q ^ a * D ^ 2 ∧
    ((σ.phase = 0 ∧ q * (ε * sb) ^ 2 ≤ q ^ a * M ^ 2) ∨
      (σ.phase = 1 ∧ σ.g = reg F (ε / (4 * ρ)) x0 σ.x ∧ ε / 2 < ‖σ.g‖ ∧
        (ε * sb) ^ 2 ≤ q ^ a * M ^ 2))

structure StageCtx (F : E → E) (L r ε : ℝ) (x0 z : E) (ρ sb q D M : ℝ) : Prop where
  hyp : Hyp F L r ε
  hr : 0 < r
  hε : 0 < ε
  hL : 0 ≤ L
  hρ : 0 < ρ
  hz : reg F (ε / (4 * ρ)) x0 z = 0
  hD : ‖x0 - z‖ ≤ D
  hDM : D ≤ M
  hsb : 0 < sb
  hsbL : sb * (L + ε / (4 * ρ)) ≤ 1 / 4
  hsbr : sb ≤ 2 * r / ε
  hq : q = 1 - sb * (ε / (4 * ρ)) / 2
  hsbM : ε * sb ≤ M

namespace StageCtx

variable {F : E → E} {L r ε : ℝ} {x0 z : E} {ρ sb q D M : ℝ}

lemma hμ (c : StageCtx F L r ε x0 z ρ sb q D M) : 0 < ε / (4 * ρ) :=
  div_pos c.hε (mul_pos (by norm_num) c.hρ)

lemma hsbμ (c : StageCtx F L r ε x0 z ρ sb q D M) : sb * (ε / (4 * ρ)) ≤ 1 / 4 := by
  have h := c.hsbL
  have : 0 ≤ sb * L := mul_nonneg c.hsb.le c.hL
  nlinarith

lemma hq0 (c : StageCtx F L r ε x0 z ρ sb q D M) : 0 < q := by
  rw [c.hq]; linarith [c.hsbμ]

lemma hq1 (c : StageCtx F L r ε x0 z ρ sb q D M) : q ≤ 1 := by
  rw [c.hq]
  have := mul_pos c.hsb c.hμ
  linarith

lemma hD0 (c : StageCtx F L r ε x0 z ρ sb q D M) : 0 ≤ D := le_trans (norm_nonneg _) c.hD

lemma hinit (c : StageCtx F L r ε x0 z ρ sb q D M) : ρ / (2 * ε) * (ε / (4 * ρ)) = 1 / 8 := by
  have := c.hε.ne'
  have := c.hρ.ne'
  field_simp
  ring

lemma hsb_init (c : StageCtx F L r ε x0 z ρ sb q D M) : sb ≤ 2 * (ρ / (2 * ε)) := by
  have h1 := c.hsbμ
  have h2 := c.hinit
  have hμ := c.hμ
  by_contra hcon
  have hcon := not_le.mp hcon
  have := mul_lt_mul_of_pos_right hcon hμ
  linarith

end StageCtx

lemma stage_init {F : E → E} {L r ε : ℝ} {x0 z : E} {ρ sb q D M : ℝ}
    (c : StageCtx F L r ε x0 z ρ sb q D M) :
    StageInv F ε x0 z ρ sb q D M 0 (stageStart ε x0 ρ) := by
  refine ⟨rfl, 0, 0, by simp [stageStart], by simp [stageStart], c.hsb_init, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · simp only [stageStart, pow_zero, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) c.hD 2
  · simp only [pow_zero, one_mul]
    have h1 : (ε * sb) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (mul_pos c.hε c.hsb).le c.hsbM 2
    have h2 : q * (ε * sb) ^ 2 ≤ 1 * (ε * sb) ^ 2 :=
      mul_le_mul_of_nonneg_right c.hq1 (sq_nonneg _)
    linarith

lemma stage_step {F : E → E} {L r ε : ℝ} {x0 z : E} {ρ sb q D M : ℝ}
    (c : StageCtx F L r ε x0 z ρ sb q D M) {n : ℕ} {σ : UregState E}
    (h : StageInv F ε x0 z ρ sb q D M n σ) :
    Done F ε (trans F ε x0 σ) ∨ (ρ < D ∧ trans F ε x0 σ = stageStart ε x0 (2 * ρ)) ∨
      StageInv F ε x0 z ρ sb q D M (n + 1) (trans F ε x0 σ) := by
  obtain ⟨hρ, a, f, hn, hs, hsb, hd, hph⟩ := h
  have hμ := c.hμ
  have hq0 := c.hq0
  have hq1 := c.hq1
  have hqa : q ^ a ≤ 1 := pow_le_one₀ hq0.le hq1
  have hqa0 : 0 < q ^ a := pow_pos hq0 a
  have hspos : 0 < σ.s := by
    have h2 : (0 : ℝ) < 2 ^ f := by positivity
    have h3 : 0 < ρ / (2 * ε) := div_pos c.hρ (mul_pos (by norm_num) c.hε)
    rw [← hs] at h3
    exact (mul_pos_iff_of_pos_right h2).mp h3
  rcases hph with ⟨hp, hcount⟩ | ⟨hp, hg, hgbig, hcount⟩
  · have hT : trans F ε x0 σ = uregStep ε x0 σ (F σ.x) := by simp [trans, hp]
    by_cases h1 : ‖F σ.x‖ ≤ ε
    · left
      rw [hT]
      simp only [uregStep, hp, ↓reduceIte, h1]
      exact ⟨rfl, h1⟩
    · by_cases h2 : ‖F σ.x + (ε / (4 * σ.ρ)) • (σ.x - x0)‖ ≤ ε / 2
      · right; left
        refine ⟨?_, ?_⟩
        · have hdx : ‖σ.x - z‖ ≤ D := by
            have : ‖σ.x - z‖ ^ 2 ≤ D ^ 2 := by nlinarith [sq_nonneg D]
            exact (pow_le_pow_iff_left₀ (norm_nonneg _) c.hD0 (by norm_num)).mp this
          have h3 := norm_le_reg F hμ.le x0 σ.x
          rw [hρ] at h2
          unfold reg at h3
          have h4 : ‖σ.x - x0‖ ≤ 2 * D := by
            have e : σ.x - x0 = (σ.x - z) - (x0 - z) := by abel
            rw [e]
            have := norm_sub_le (σ.x - z) (x0 - z)
            linarith [c.hD]
          have h5 : ε / (4 * ρ) * ‖σ.x - x0‖ ≤ ε / (4 * ρ) * (2 * D) :=
            mul_le_mul_of_nonneg_left h4 hμ.le
          have h6 : ε / 2 < ε / (4 * ρ) * (2 * D) := by
            have := not_le.mp h1
            linarith
          have e : ε / (4 * ρ) * (2 * D) = ε / 2 * (D / ρ) := by
            have := c.hρ.ne'
            field_simp
            ring
          rw [e] at h6
          have h7 : 1 < D / ρ := by
            have hε2 : 0 < ε / 2 := by linarith [c.hε]
            by_contra hcon
            have hcon := not_lt.mp hcon
            have := mul_le_mul_of_nonneg_left hcon hε2.le
            linarith
          exact (one_lt_div c.hρ).mp h7
        · rw [hT]
          have h2' := h2
          rw [hρ] at h2'
          simp only [uregStep, hp, ↓reduceIte, h1, hρ]
          simp only [h2', ↓reduceIte]
      · right; right
        rw [hT]
        simp only [uregStep, hp, ↓reduceIte, h1, h2]
        refine ⟨hρ, a, f, by simp [hn, hp], hs, hsb, hd, Or.inr ⟨rfl, ?_, ?_, ?_⟩⟩
        · simp [reg, hρ]
        · exact not_le.mp h2
        · have hbig : ε * sb < ‖σ.x - z‖ := by
            by_contra hcon
            have hcon := not_lt.mp hcon
            have := small_of_close c.hyp c.hr c.hε hμ.le c.hL x0 c.hz c.hsbL c.hsbr σ.x hcon
            rw [hρ] at h2
            exact h2 (by simpa [reg] using this)
          have h3 : (ε * sb) ^ 2 ≤ ‖σ.x - z‖ ^ 2 :=
            pow_le_pow_left₀ (mul_pos c.hε c.hsb).le hbig.le 2
          have h4 : q ^ a * D ^ 2 ≤ q ^ a * M ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ c.hD0 c.hDM 2) hqa0.le
          linarith
  · have hT : trans F ε x0 σ = uregStep ε x0 σ (F (σ.x - σ.s • σ.g)) := by simp [trans, hp]
    have hregy : F (σ.x - σ.s • σ.g) + (ε / (4 * σ.ρ)) • (σ.x - σ.s • σ.g - x0) =
        reg F (ε / (4 * ρ)) x0 (σ.x - σ.s • reg F (ε / (4 * ρ)) x0 σ.x) := by
      simp [reg, hρ, hg]
    have hsinit : σ.s ≤ ρ / (2 * ε) := by
      have h2 : (1 : ℝ) ≤ 2 ^ f := one_le_pow₀ (by norm_num)
      have := mul_le_mul_of_nonneg_left h2 hspos.le
      linarith
    have hsμ : σ.s * (ε / (4 * ρ)) ≤ 1 / 8 := by
      have := mul_le_mul_of_nonneg_right hsinit hμ.le
      linarith [c.hinit]
    by_cases h1 : ‖F (σ.x - σ.s • σ.g) + (ε / (4 * σ.ρ)) • (σ.x - σ.s • σ.g - x0) - σ.g‖ ≤
        ‖σ.g‖ / 2
    · right; right
      rw [hT]
      simp only [uregStep, hp, ↓reduceIte, h1, one_ne_zero]
      rw [hregy] at h1 ⊢
      rw [hg] at h1
      have hfe := fejer_step hμ.le (reg_strong c.hyp.mono (ε / (4 * ρ)) x0) c.hz hspos.le hsμ σ.x h1
      have hq' : 1 - σ.s * (ε / (4 * ρ)) ≤ q := by
        rw [c.hq]
        have := mul_le_mul_of_nonneg_right hsb hμ.le
        linarith
      have hnn : 0 ≤ ‖σ.x - z‖ ^ 2 := sq_nonneg _
      refine ⟨hρ, a + 1, f, by simp [hn, hp]; ring, hs, hsb, ?_, Or.inl ⟨rfl, ?_⟩⟩
      · calc _ ≤ (1 - σ.s * (ε / (4 * ρ))) * ‖σ.x - z‖ ^ 2 := hfe
          _ ≤ q * ‖σ.x - z‖ ^ 2 := mul_le_mul_of_nonneg_right hq' hnn
          _ ≤ q * (q ^ a * D ^ 2) := mul_le_mul_of_nonneg_left hd hq0.le
          _ = q ^ (a + 1) * D ^ 2 := by ring
      · calc q * (ε * sb) ^ 2 ≤ q * (q ^ a * M ^ 2) := mul_le_mul_of_nonneg_left hcount hq0.le
          _ = q ^ (a + 1) * M ^ 2 := by ring
    · right; right
      rw [hT]
      simp only [uregStep, hp, ↓reduceIte, h1, one_ne_zero]
      have hslt : sb < σ.s := by
        by_contra hcon
        have hcon := not_lt.mp hcon
        apply h1
        rw [hregy, hg]
        have hLμ : 0 ≤ L + ε / (4 * ρ) := add_nonneg c.hL hμ.le
        refine pass_test c.hyp c.hr c.hε hμ.le x0 hspos.le ?_ (le_trans hcon c.hsbr) σ.x
          (by rw [← hg]; exact hgbig)
        exact le_trans (mul_le_mul_of_nonneg_right hcon hLμ) c.hsbL
      refine ⟨hρ, a, f + 1, by simp [hn, hp]; ring, ?_, by linarith, hd,
        Or.inr ⟨rfl, hg, hgbig, hcount⟩⟩
      rw [pow_succ]
      linarith

def Hit (F : E → E) (ε : ℝ) (x0 : E) (ρ D : ℝ) (σ : UregState E) : Prop :=
  Done F ε σ ∨ (ρ < D ∧ σ = stageStart ε x0 (2 * ρ))

lemma stage_progress {F : E → E} {L r ε : ℝ} {x0 z : E} {ρ sb q D M : ℝ}
    (c : StageCtx F L r ε x0 z ρ sb q D M) (n : ℕ) :
    (∃ m ≤ n, Hit F ε x0 ρ D ((trans F ε x0)^[m] (stageStart ε x0 ρ))) ∨
      StageInv F ε x0 z ρ sb q D M n ((trans F ε x0)^[n] (stageStart ε x0 ρ)) := by
  induction n with
  | zero => exact Or.inr (stage_init c)
  | succ n ih =>
    rcases ih with ⟨m, hm, hit⟩ | hinv
    · exact Or.inl ⟨m, Nat.le_succ_of_le hm, hit⟩
    · rw [Function.iterate_succ_apply']
      rcases stage_step c hinv with hd | hr | hi
      · exact Or.inl ⟨n + 1, le_rfl, by rw [Function.iterate_succ_apply']; exact Or.inl hd⟩
      · exact Or.inl ⟨n + 1, le_rfl, by rw [Function.iterate_succ_apply']; exact Or.inr hr⟩
      · exact Or.inr hi

lemma stage_count {F : E → E} {L r ε : ℝ} {x0 z : E} {ρ sb q D M : ℝ}
    (c : StageCtx F L r ε x0 z ρ sb q D M) {n : ℕ} {σ : UregState E}
    (h : StageInv F ε x0 z ρ sb q D M n σ) :
    (n : ℝ) ≤ 3 + ρ / (ε * sb) + 32 * (ρ / (ε * sb)) * Real.log (M / (ε * sb)) := by
  obtain ⟨-, a, f, hn, hs, hsb, -, hph⟩ := h
  have hμ := c.hμ
  have hq0 := c.hq0
  have hq1 := c.hq1
  have hεsb : 0 < ε * sb := mul_pos c.hε c.hsb
  have hκ : 0 < ρ / (ε * sb) := div_pos c.hρ hεsb
  have hlog : 0 ≤ Real.log (M / (ε * sb)) :=
    Real.log_nonneg ((one_le_div hεsb).mpr c.hsbM)
  have hspos : 0 < σ.s := by
    have h2 : (0 : ℝ) < 2 ^ f := by positivity
    have h3 : 0 < ρ / (2 * ε) := div_pos c.hρ (mul_pos (by norm_num) c.hε)
    rw [← hs] at h3
    exact (mul_pos_iff_of_pos_right h2).mp h3
  have hf : (f : ℝ) ≤ ρ / (ε * sb) := by
    have h1 : (f : ℝ) ≤ 2 ^ f := by exact_mod_cast (Nat.lt_two_pow_self (n := f)).le
    have h2 : (2 : ℝ) ^ f = ρ / (2 * ε) / σ.s := by
      rw [← hs]; field_simp
    have h3 : ρ / (2 * ε) / σ.s ≤ ρ / (ε * sb) := by
      rw [div_div, div_le_div_iff₀ (mul_pos (mul_pos two_pos c.hε) hspos) hεsb]
      have := mul_le_mul_of_nonneg_left hsb (mul_pos c.hρ c.hε).le
      nlinarith
    linarith
  have hcount : q * (ε * sb) ^ 2 ≤ q ^ a * M ^ 2 := by
    rcases hph with ⟨-, h⟩ | ⟨-, -, -, h⟩
    · exact h
    · have : q * (ε * sb) ^ 2 ≤ 1 * (ε * sb) ^ 2 := mul_le_mul_of_nonneg_right hq1 (sq_nonneg _)
      linarith
  have hphase : (σ.phase : ℝ) ≤ 1 := by
    rcases hph with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have ha : (a : ℝ) ≤ 1 + 16 * (ρ / (ε * sb)) * Real.log (M / (ε * sb)) := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0]; simp; positivity
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have h1 : (ε * sb) ^ 2 ≤ q ^ b * M ^ 2 := by
        have e : q ^ (b + 1) * M ^ 2 = q * (q ^ b * M ^ 2) := by ring
        rw [e] at hcount
        exact le_of_mul_le_mul_left hcount hq0
      have hMpos : 0 < M := lt_of_lt_of_le hεsb c.hsbM
      have hqe : q ≤ Real.exp (-(sb * (ε / (4 * ρ)) / 2)) := by
        have := Real.add_one_le_exp (-(sb * (ε / (4 * ρ)) / 2))
        rw [c.hq]; linarith
      have hqb : q ^ b ≤ Real.exp (-(sb * (ε / (4 * ρ)) / 2) * b) := by
        calc q ^ b ≤ Real.exp (-(sb * (ε / (4 * ρ)) / 2)) ^ b := pow_le_pow_left₀ hq0.le hqe b
          _ = Real.exp (-(sb * (ε / (4 * ρ)) / 2) * b) := by
            rw [← Real.exp_nat_mul]; ring_nf
      have h2 : (ε * sb) ^ 2 ≤ Real.exp (-(sb * (ε / (4 * ρ)) / 2) * b) * M ^ 2 :=
        le_trans h1 (mul_le_mul_of_nonneg_right hqb (sq_nonneg M))
      have h3 := Real.log_le_log (pow_pos hεsb 2) h2
      rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hMpos 2).ne', Real.log_exp, Real.log_pow,
        Real.log_pow] at h3
      have h4 : Real.log (M / (ε * sb)) = Real.log M - Real.log (ε * sb) :=
        Real.log_div hMpos.ne' hεsb.ne'
      have h5 : sb * (ε / (4 * ρ)) / 2 * b ≤ 2 * Real.log (M / (ε * sb)) := by
        rw [h4]; push_cast at h3; linarith
      have e : sb * (ε / (4 * ρ)) / 2 * b = (b : ℝ) / (8 * (ρ / (ε * sb))) := by
        have := c.hρ.ne'
        have := c.hε.ne'
        have := c.hsb.ne'
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)] at h5
      push_cast
      linarith
  have hn' : (n : ℝ) = 2 * a + f + σ.phase := by exact_mod_cast hn
  rw [hn']
  linarith

lemma stage_hit {F : E → E} {L r ε : ℝ} {x0 z : E} {ρ sb q D M : ℝ}
    (c : StageCtx F L r ε x0 z ρ sb q D M) (N : ℕ)
    (hN : 3 + ρ / (ε * sb) + 32 * (ρ / (ε * sb)) * Real.log (M / (ε * sb)) < N) :
    ∃ m ≤ N, Hit F ε x0 ρ D ((trans F ε x0)^[m] (stageStart ε x0 ρ)) := by
  rcases stage_progress c N with h | h
  · exact h
  · exact absurd (stage_count c h) (not_le.mpr hN)

end OracleTemplate.HolderMonotone
