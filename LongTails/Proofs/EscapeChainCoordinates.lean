import LongTails.Proofs.EscapeChainFunction

namespace LongTails.Proofs.EscapeChainCoordinates

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction RelativeHessianArctan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

structure Frame (K : ℕ) (u v : ℕ → E) : Prop where
  uu : ∀ i j, i < K → j < K → ⟪u i, u j⟫ = if i = j then 1 else 0
  vv : ∀ i j, i < K → j < K → ⟪v i, v j⟫ = if i = j then 1 else 0
  uv : ∀ i j, i < K → j < K → ⟪u i, v j⟫ = 0

variable {K : ℕ} {u v : ℕ → E}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma Frame.vu (fr : Frame K u v) {i j : ℕ} (hi : i < K) (hj : j < K) : ⟪v i, u j⟫ = 0 := by
  rw [real_inner_comm]; exact fr.uv j i hj hi

noncomputable def weight (u v : ℕ → E) (l : ℕ) (x : E) : ℝ :=
  prevGam u l x * sad ⟪v l, x⟫ * loc1 (quarter u v l x) / 2

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma sum_delta (f : ℕ → ℝ) (l m : ℕ) :
    ∑ m' ∈ Finset.range l, f m' * (if m' = m then 1 else 0) = if m < l then f m else 0 := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_range]

lemma resid_u (fr : Frame K u v) {l m : ℕ} (hl : l ≤ K) (hm : m < K) (x : E) :
    D (resid u v l) x (u m) = if l ≤ m then 2 * ⟪u m, x⟫ else 0 := by
  rw [D_resid]
  have h1 : ∀ m' ∈ Finset.range l, (2 * ⟪u m', x⟫ * ⟪u m', u m⟫ + 2 * ⟪v m', x⟫ * ⟪v m', u m⟫) =
      (2 * ⟪u m', x⟫) * (if m' = m then 1 else 0) := by
    intro m' hm'
    have hm'K : m' < K := lt_of_lt_of_le (Finset.mem_range.1 hm') hl
    rw [fr.uu m' m hm'K hm, fr.vu hm'K hm]
    ring
  rw [Finset.sum_congr rfl h1, sum_delta (fun m' => 2 * ⟪u m', x⟫), real_inner_comm x (u m)]
  by_cases h : l ≤ m
  · rw [ite_eq_right (by omega), ite_eq_left h]; ring
  · rw [ite_eq_left (by omega), ite_eq_right h]; ring

lemma resid_v (fr : Frame K u v) {l m : ℕ} (hl : l ≤ K) (hm : m < K) (x : E) :
    D (resid u v l) x (v m) = if l ≤ m then 2 * ⟪v m, x⟫ else 0 := by
  rw [D_resid]
  have h1 : ∀ m' ∈ Finset.range l, (2 * ⟪u m', x⟫ * ⟪u m', v m⟫ + 2 * ⟪v m', x⟫ * ⟪v m', v m⟫) =
      (2 * ⟪v m', x⟫) * (if m' = m then 1 else 0) := by
    intro m' hm'
    have hm'K : m' < K := lt_of_lt_of_le (Finset.mem_range.1 hm') hl
    rw [fr.uv m' m hm'K hm, fr.vv m' m hm'K hm]
    ring
  rw [Finset.sum_congr rfl h1, sum_delta (fun m' => 2 * ⟪v m', x⟫), real_inner_comm x (v m)]
  by_cases h : l ≤ m
  · rw [ite_eq_right (by omega), ite_eq_left h]; ring
  · rw [ite_eq_left (by omega), ite_eq_right h]; ring

lemma resid_qu (fr : Frame K u v) {l m : ℕ} (hl : l ≤ K) (hm : m < K) (x : E) :
    Q (resid u v l) x (u m) = if l ≤ m then 2 else 0 := by
  rw [Q_resid]
  have hn : ‖u m‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, fr.uu m m hm hm, ite_eq_left rfl]
  have h1 : ∀ m' ∈ Finset.range l, (2 * ⟪u m', u m⟫ ^ 2 + 2 * ⟪v m', u m⟫ ^ 2) =
      2 * (if m' = m then 1 else 0) := by
    intro m' hm'
    have hm'K : m' < K := lt_of_lt_of_le (Finset.mem_range.1 hm') hl
    rw [fr.uu m' m hm'K hm, fr.vu hm'K hm]
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl h1, hn]
  have h2 := sum_delta (fun _ => (2 : ℝ)) l m
  simp only [mul_ite, mul_one, mul_zero] at h2 ⊢
  rw [h2]
  by_cases h : l ≤ m
  · rw [ite_eq_right (by omega), ite_eq_left h]; ring
  · rw [ite_eq_left (by omega), ite_eq_right h]; ring

lemma resid_qv (fr : Frame K u v) {l m : ℕ} (hl : l ≤ K) (hm : m < K) (x : E) :
    Q (resid u v l) x (v m) = if l ≤ m then 2 else 0 := by
  rw [Q_resid]
  have hn : ‖v m‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, fr.vv m m hm hm, ite_eq_left rfl]
  have h1 : ∀ m' ∈ Finset.range l, (2 * ⟪u m', v m⟫ ^ 2 + 2 * ⟪v m', v m⟫ ^ 2) =
      2 * (if m' = m then 1 else 0) := by
    intro m' hm'
    have hm'K : m' < K := lt_of_lt_of_le (Finset.mem_range.1 hm') hl
    rw [fr.uv m' m hm'K hm, fr.vv m' m hm'K hm]
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl h1, hn]
  have h2 := sum_delta (fun _ => (2 : ℝ)) l m
  simp only [mul_ite, mul_one, mul_zero] at h2 ⊢
  rw [h2]
  by_cases h : l ≤ m
  · rw [ite_eq_right (by omega), ite_eq_left h]; ring
  · rw [ite_eq_left (by omega), ite_eq_right h]; ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma dPsi_u (fr : Frame K u v) {l m : ℕ} (hl : l < K) (hm : m < K) (x : E) :
    dPsi u l x (u m) = if l = m + 1 then psi1 ⟪u m, x⟫ else 0 := by
  cases l with
  | zero => simp [dPsi]
  | succ l =>
    simp only [dPsi, fr.uu l m (by omega) hm]
    by_cases h : l = m
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (by omega)]; ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma dGam_u (fr : Frame K u v) {l m : ℕ} (hl : l < K) (hm : m < K) (x : E) :
    dGam u l x (u m) = if l = m + 1 then gam1 ⟪u m, x⟫ else 0 := by
  cases l with
  | zero => simp [dGam]
  | succ l =>
    simp only [dGam, fr.uu l m (by omega) hm]
    by_cases h : l = m
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (by omega)]; ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma qPsi_u (fr : Frame K u v) {l m : ℕ} (hl : l < K) (hm : m < K) (x : E) :
    qPsi u l x (u m) = if l = m + 1 then psi2 ⟪u m, x⟫ else 0 := by
  cases l with
  | zero => simp [qPsi]
  | succ l =>
    simp only [qPsi, fr.uu l m (by omega) hm]
    by_cases h : l = m
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (by omega)]; ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma qGam_u (fr : Frame K u v) {l m : ℕ} (hl : l < K) (hm : m < K) (x : E) :
    qGam u l x (u m) = if l = m + 1 then gam2 ⟪u m, x⟫ else 0 := by
  cases l with
  | zero => simp [qGam]
  | succ l =>
    simp only [qGam, fr.uu l m (by omega) hm]
    by_cases h : l = m
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (by omega)]; ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma dPsi_v (fr : Frame K u v) {l m : ℕ} (hl : l < K) (hm : m < K) (x : E) :
    dPsi u l x (v m) = 0 := by
  cases l with
  | zero => simp [dPsi]
  | succ l => simp [dPsi, fr.uv l m (by omega) hm]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma dGam_v (fr : Frame K u v) {l m : ℕ} (hl : l < K) (hm : m < K) (x : E) :
    dGam u l x (v m) = 0 := by
  cases l with
  | zero => simp [dGam]
  | succ l => simp [dGam, fr.uv l m (by omega) hm]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma qPsi_v (fr : Frame K u v) {l m : ℕ} (hl : l < K) (hm : m < K) (x : E) :
    qPsi u l x (v m) = 0 := by
  cases l with
  | zero => simp [qPsi]
  | succ l => simp [qPsi, fr.uv l m (by omega) hm]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma qGam_v (fr : Frame K u v) {l m : ℕ} (hl : l < K) (hm : m < K) (x : E) :
    qGam u l x (v m) = 0 := by
  cases l with
  | zero => simp [qGam]
  | succ l => simp [qGam, fr.uv l m (by omega) hm]

lemma term_u (fr : Frame K u v) {l m : ℕ} (hl : l < K) (hm : m < K) (x : E) :
    D (link u v l) x (u m) + D (saddle u v l) x (u m) =
      (if l = m then -strength * (lam ⟪v m, x⟫ * prevPsi u m x * density ⟪u m, x⟫) else 0) +
      (if l = m + 1 then -strength * (lam ⟪v l, x⟫ * profile ⟪u l, x⟫ * psi1 ⟪u m, x⟫) +
        sad ⟪v l, x⟫ * window u v l x * gam1 ⟪u m, x⟫ else 0) +
      (if l ≤ m then weight u v l x * ⟪u m, x⟫ else 0) := by
  rw [D_link, D_saddle, D_window, resid_u fr hl.le hm, dPsi_u fr hl hm, dGam_u fr hl hm,
    fr.uu l m hl hm, fr.vu hl hm]
  unfold weight
  split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring

lemma term_v (fr : Frame K u v) {l m : ℕ} (hl : l < K) (hm : m < K) (x : E) :
    D (link u v l) x (v m) + D (saddle u v l) x (v m) =
      (if l = m then -strength * (prevPsi u m x * profile ⟪u m, x⟫ * lam1 ⟪v m, x⟫) +
        prevGam u m x * window u v m x * sad1 ⟪v m, x⟫ else 0) +
      (if l ≤ m then weight u v l x * ⟪v m, x⟫ else 0) := by
  rw [D_link, D_saddle, D_window, resid_v fr hl.le hm, dPsi_v fr hl hm, dGam_v fr hl hm,
    fr.uv l m hl hm, fr.vv l m hl hm]
  unfold weight
  split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring

lemma term_qv (fr : Frame K u v) {l m : ℕ} (hl : l < K) (hm : m < K) (x : E) :
    Q (link u v l) x (v m) + Q (saddle u v l) x (v m) =
      (if l = m then -strength * (prevPsi u m x * profile ⟪u m, x⟫ * lam2 ⟪v m, x⟫) +
        prevGam u m x * (sad1 ⟪v m, x⟫ * loc1 (quarter u v m x) * ⟪v m, x⟫ +
          window u v m x * sad2 ⟪v m, x⟫) else 0) +
      (if l ≤ m then prevGam u l x * sad ⟪v l, x⟫ *
        (loc1 (quarter u v l x) / 2 + loc2 (quarter u v l x) * ⟪v m, x⟫ ^ 2 / 4) else 0) := by
  rw [Q_link, Q_saddle, Q_window, D_window, resid_v fr hl.le hm, resid_qv fr hl.le hm,
    dPsi_v fr hl hm, dGam_v fr hl hm, qPsi_v fr hl hm, qGam_v fr hl hm,
    fr.uv l m hl hm, fr.vv l m hl hm]
  split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring

lemma term_qu (fr : Frame K u v) {l m : ℕ} (hl : l < K) (hm : m < K) (x : E) :
    Q (link u v l) x (u m) + Q (saddle u v l) x (u m) =
      (if l = m then -strength * (lam ⟪v m, x⟫ * prevPsi u m x * densitySlope ⟪u m, x⟫) else 0) +
      (if l = m + 1 then -strength * (lam ⟪v l, x⟫ * profile ⟪u l, x⟫ * psi2 ⟪u m, x⟫) +
        sad ⟪v l, x⟫ * window u v l x * gam2 ⟪u m, x⟫ else 0) +
      (if l ≤ m then prevGam u l x * sad ⟪v l, x⟫ *
        (loc1 (quarter u v l x) / 2 + loc2 (quarter u v l x) * ⟪u m, x⟫ ^ 2 / 4) else 0) := by
  rw [Q_link, Q_saddle, Q_window, D_window, resid_u fr hl.le hm, resid_qu fr hl.le hm,
    dPsi_u fr hl hm, dGam_u fr hl hm, qPsi_u fr hl hm, qGam_u fr hl hm,
    fr.uu l m hl hm, fr.vu hl hm]
  split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma sum_eq_at {f : ℕ → ℝ} {m : ℕ} (hm : m < K) :
    ∑ l ∈ Finset.range K, (if l = m then f l else 0) = f m := by
  rw [Finset.sum_ite_eq']; simp [Finset.mem_range, hm]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma sum_eq_succ {f : ℕ → ℝ} (m : ℕ) :
    ∑ l ∈ Finset.range K, (if l = m + 1 then f l else 0) = if m + 1 < K then f (m + 1) else 0 := by
  rw [Finset.sum_ite_eq']; simp [Finset.mem_range]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma sum_le_at {f : ℕ → ℝ} {m : ℕ} (hm : m < K) :
    ∑ l ∈ Finset.range K, (if l ≤ m then f l else 0) = ∑ l ∈ Finset.range (m + 1), f l := by
  rw [← Finset.sum_filter]
  congr 1
  ext l; simp only [Finset.mem_filter, Finset.mem_range]; omega

lemma hidden_u (fr : Frame K u v) {m : ℕ} (hm : m < K) (x : E) :
    D (hidden K u v) x (u m) = -strength * (lam ⟪v m, x⟫ * prevPsi u m x * density ⟪u m, x⟫) +
      (if m + 1 < K then -strength * (lam ⟪v (m + 1), x⟫ * profile ⟪u (m + 1), x⟫ * psi1 ⟪u m, x⟫) +
        sad ⟪v (m + 1), x⟫ * window u v (m + 1) x * gam1 ⟪u m, x⟫ else 0) +
      (∑ l ∈ Finset.range (m + 1), weight u v l x) * ⟪u m, x⟫ := by
  rw [D_hidden, Finset.sum_congr rfl (fun l hl => term_u fr (Finset.mem_range.1 hl) hm x),
    Finset.sum_add_distrib, Finset.sum_add_distrib, sum_eq_at hm, sum_eq_succ m, sum_le_at hm,
    Finset.sum_mul]

lemma hidden_v (fr : Frame K u v) {m : ℕ} (hm : m < K) (x : E) :
    D (hidden K u v) x (v m) = -strength * (prevPsi u m x * profile ⟪u m, x⟫ * lam1 ⟪v m, x⟫) +
      prevGam u m x * window u v m x * sad1 ⟪v m, x⟫ +
      (∑ l ∈ Finset.range (m + 1), weight u v l x) * ⟪v m, x⟫ := by
  rw [D_hidden, Finset.sum_congr rfl (fun l hl => term_v fr (Finset.mem_range.1 hl) hm x),
    Finset.sum_add_distrib, sum_eq_at hm, sum_le_at hm, Finset.sum_mul]

lemma hidden_qv (fr : Frame K u v) {m : ℕ} (hm : m < K) (x : E) :
    Q (hidden K u v) x (v m) = -strength * (prevPsi u m x * profile ⟪u m, x⟫ * lam2 ⟪v m, x⟫) +
      prevGam u m x * (sad1 ⟪v m, x⟫ * loc1 (quarter u v m x) * ⟪v m, x⟫ +
        window u v m x * sad2 ⟪v m, x⟫) +
      ∑ l ∈ Finset.range (m + 1), prevGam u l x * sad ⟪v l, x⟫ *
        (loc1 (quarter u v l x) / 2 + loc2 (quarter u v l x) * ⟪v m, x⟫ ^ 2 / 4) := by
  rw [Q_hidden, Finset.sum_congr rfl (fun l hl => term_qv fr (Finset.mem_range.1 hl) hm x),
    Finset.sum_add_distrib, sum_eq_at hm, sum_le_at hm]

lemma hidden_qu (fr : Frame K u v) {m : ℕ} (hm : m < K) (x : E) :
    Q (hidden K u v) x (u m) = -strength * (lam ⟪v m, x⟫ * prevPsi u m x * densitySlope ⟪u m, x⟫) +
      (if m + 1 < K then -strength * (lam ⟪v (m + 1), x⟫ * profile ⟪u (m + 1), x⟫ * psi2 ⟪u m, x⟫) +
        sad ⟪v (m + 1), x⟫ * window u v (m + 1) x * gam2 ⟪u m, x⟫ else 0) +
      ∑ l ∈ Finset.range (m + 1), prevGam u l x * sad ⟪v l, x⟫ *
        (loc1 (quarter u v l x) / 2 + loc2 (quarter u v l x) * ⟪u m, x⟫ ^ 2 / 4) := by
  rw [Q_hidden, Finset.sum_congr rfl (fun l hl => term_qu fr (Finset.mem_range.1 hl) hm x),
    Finset.sum_add_distrib, Finset.sum_add_distrib, sum_eq_at hm, sum_eq_succ m, sum_le_at hm]

noncomputable def tail (u v : ℕ → E) (i : ℕ) (x : E) : E :=
  x - ∑ m ∈ Finset.range i, (⟪u m, x⟫ • u m + ⟪v m, x⟫ • v m) - ⟪v i, x⟫ • v i

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma tail_u (fr : Frame K u v) {i l : ℕ} (hi : i < K) (hl : l < K) (x : E) :
    ⟪u l, tail u v i x⟫ = if i ≤ l then ⟪u l, x⟫ else 0 := by
  unfold tail
  rw [inner_sub_right, inner_sub_right, inner_sum, inner_smul_right, fr.uv l i hl hi]
  have h1 : ∀ m ∈ Finset.range i, ⟪u l, ⟪u m, x⟫ • u m + ⟪v m, x⟫ • v m⟫ =
      ⟪u m, x⟫ * (if m = l then 1 else 0) := by
    intro m hm
    have hmK : m < K := lt_trans (Finset.mem_range.1 hm) hi
    rw [inner_add_right, inner_smul_right, inner_smul_right, fr.uu l m hl hmK, fr.uv l m hl hmK]
    by_cases h : m = l
    · subst h; simp
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h]; ring
  rw [Finset.sum_congr rfl h1, sum_delta (fun m => ⟪u m, x⟫)]
  split_ifs <;> first | (exfalso; omega) | ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma tail_v (fr : Frame K u v) {i l : ℕ} (hi : i < K) (hl : l < K) (x : E) :
    ⟪v l, tail u v i x⟫ = if i < l then ⟪v l, x⟫ else 0 := by
  unfold tail
  rw [inner_sub_right, inner_sub_right, inner_sum, inner_smul_right, fr.vv l i hl hi]
  have h1 : ∀ m ∈ Finset.range i, ⟪v l, ⟪u m, x⟫ • u m + ⟪v m, x⟫ • v m⟫ =
      ⟪v m, x⟫ * (if m = l then 1 else 0) := by
    intro m hm
    have hmK : m < K := lt_trans (Finset.mem_range.1 hm) hi
    rw [inner_add_right, inner_smul_right, inner_smul_right, fr.vu hl hmK, fr.vv l m hl hmK]
    by_cases h : m = l
    · subst h; simp
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h]; ring
  rw [Finset.sum_congr rfl h1, sum_delta (fun m => ⟪v m, x⟫)]
  split_ifs <;> subst_vars <;> first | (exfalso; omega) | ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma tail_norm (fr : Frame K u v) {i : ℕ} (hi : i < K) (x : E) :
    ‖tail u v i x‖ ^ 2 = ⟪x, tail u v i x⟫ := by
  rw [← real_inner_self_eq_norm_sq]
  have hexp : ⟪tail u v i x, tail u v i x⟫ = ⟪x - ∑ m ∈ Finset.range i, (⟪u m, x⟫ • u m + ⟪v m, x⟫ • v m) -
      ⟪v i, x⟫ • v i, tail u v i x⟫ := rfl
  rw [hexp]
  rw [inner_sub_left, inner_sub_left, sum_inner, real_inner_smul_left, tail_v fr hi hi, ite_eq_right (lt_irrefl i)]
  have h1 : ∀ m ∈ Finset.range i, ⟪⟪u m, x⟫ • u m + ⟪v m, x⟫ • v m, tail u v i x⟫ = 0 := by
    intro m hm
    have hmi := Finset.mem_range.1 hm
    have hmK : m < K := lt_trans hmi hi
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, tail_u fr hi hmK,
      tail_v fr hi hmK, ite_eq_right (by omega), ite_eq_right (by omega)]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_const_zero]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma resid_tail (fr : Frame K u v) {i : ℕ} (hi : i < K) (x : E) :
    resid u v i x = ‖tail u v i x‖ ^ 2 + ⟪v i, x⟫ ^ 2 := by
  rw [tail_norm fr hi]
  unfold resid tail
  rw [normsq_eq, inner_sub_right, inner_sub_right, inner_sum, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm x (v i)]
  simp only [RidgeJets.value, sqf]
  have h1 : ∀ m ∈ Finset.range i, ⟪x, ⟪u m, x⟫ • u m + ⟪v m, x⟫ • v m⟫ = ⟪u m, x⟫ ^ 2 + ⟪v m, x⟫ ^ 2 := by
    intro m _
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_comm x (u m),
      real_inner_comm x (v m)]
    ring
  rw [Finset.sum_congr rfl h1]
  ring

lemma resid_tail_D (fr : Frame K u v) {i l : ℕ} (hi : i < K) (hl : l ≤ i) (x : E) :
    D (resid u v l) x (tail u v i x) = 2 * ‖tail u v i x‖ ^ 2 := by
  rw [D_resid, tail_norm fr hi]
  have h1 : ∀ m ∈ Finset.range l, (2 * ⟪u m, x⟫ * ⟪u m, tail u v i x⟫ +
      2 * ⟪v m, x⟫ * ⟪v m, tail u v i x⟫) = 0 := by
    intro m hm
    have hml := Finset.mem_range.1 hm
    rw [tail_u fr hi (by omega), tail_v fr hi (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_const_zero, sub_zero]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma dPsi_tail (fr : Frame K u v) {i l : ℕ} (hi : i < K) (hl : l < K) (x : E)
    (hdead : ∀ m, i ≤ m → m < K → ⟪u m, x⟫ ≤ 1 / 2) :
    dPsi u l x (tail u v i x) = 0 := by
  cases l with
  | zero => rfl
  | succ l =>
    simp only [dPsi]
    rw [tail_u fr hi (by omega)]
    split_ifs with h
    · rw [(psi_flat (hdead l h (by omega))).2.1]; ring
    · ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma dGam_tail (fr : Frame K u v) {i l : ℕ} (hi : i < K) (hl : l < K) (x : E)
    (hdead : ∀ m, i ≤ m → m < K → ⟪u m, x⟫ ≤ 1 / 2) :
    dGam u l x (tail u v i x) = 0 := by
  cases l with
  | zero => rfl
  | succ l =>
    simp only [dGam]
    rw [tail_u fr hi (by omega)]
    split_ifs with h
    · rw [(gam_flat (by linarith [hdead l h (by omega)])).2.1]; ring
    · ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma prevPsi_dead {i l : ℕ} (hil : i < l) (hl : l < K) (x : E)
    (hdead : ∀ m, i ≤ m → m < K → ⟪u m, x⟫ ≤ 1 / 2) : prevPsi u l x = 0 := by
  cases l with
  | zero => omega
  | succ l => exact (psi_flat (hdead l (by omega) (by omega))).1

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma prevGam_dead {i l : ℕ} (hil : i < l) (hl : l < K) (x : E)
    (hdead : ∀ m, i ≤ m → m < K → ⟪u m, x⟫ ≤ 1 / 2) : prevGam u l x = 0 := by
  cases l with
  | zero => omega
  | succ l => exact (gam_flat (by linarith [hdead l (by omega) (by omega)])).1

lemma term_tail (fr : Frame K u v) {i l : ℕ} (hi : i < K) (hl : l < K) (x : E)
    (hdead : ∀ m, i ≤ m → m < K → ⟪u m, x⟫ ≤ 1 / 2) :
    D (link u v l) x (tail u v i x) + D (saddle u v l) x (tail u v i x) =
      (if l = i then -strength * (lam ⟪v i, x⟫ * prevPsi u i x * density ⟪u i, x⟫) * ⟪u i, x⟫
        else 0) + (if l ≤ i then weight u v l x * ‖tail u v i x‖ ^ 2 else 0) := by
  rw [D_link, D_saddle, dPsi_tail fr hi hl x hdead, dGam_tail fr hi hl x hdead,
    tail_u fr hi hl, tail_v fr hi hl]
  rcases lt_trichotomy l i with h | h | h
  · rw [D_window, resid_tail_D fr hi h.le, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left h.le]
    unfold weight; ring
  · subst h
    rw [D_window, resid_tail_D fr hi le_rfl, ite_eq_left le_rfl, ite_eq_right (lt_irrefl _), ite_eq_left rfl,
      ite_eq_left le_rfl]
    unfold weight; ring
  · rw [prevPsi_dead h hl x hdead, prevGam_dead h hl x hdead, ite_eq_left h.le, ite_eq_left h,
      ite_eq_right (by omega), ite_eq_right (by omega)]
    ring

lemma hidden_tail (fr : Frame K u v) {i : ℕ} (hi : i < K) (x : E)
    (hdead : ∀ m, i ≤ m → m < K → ⟪u m, x⟫ ≤ 1 / 2) :
    D (hidden K u v) x (tail u v i x) =
      -strength * (lam ⟪v i, x⟫ * prevPsi u i x * density ⟪u i, x⟫) * ⟪u i, x⟫ +
        (∑ l ∈ Finset.range (i + 1), weight u v l x) * ‖tail u v i x‖ ^ 2 := by
  rw [D_hidden, Finset.sum_congr rfl (fun l hl => term_tail fr hi (Finset.mem_range.1 hl) x hdead),
    Finset.sum_add_distrib, sum_eq_at hi, sum_le_at hi, Finset.sum_mul]

end LongTails.Proofs.EscapeChainCoordinates
