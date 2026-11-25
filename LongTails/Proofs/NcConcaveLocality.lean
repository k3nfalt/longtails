import LongTails.Proofs.NcConcaveModel

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveLocality

open LongTails.Proofs.SmoothConvexFiniteGeometry LongTails.Proofs.NcConcaveScalars
open LongTails.Proofs.NcConcaveTransitions LongTails.Proofs.NcConcaveTransitionBounds
open LongTails.Proofs.NcConcavePsi LongTails.Proofs.NcConcaveGadgets
open LongTails.Proofs.NcConcaveHuber LongTails.Proofs.NcConcaveBlock
open LongTails.Proofs.NcConcaveInstance LongTails.Proofs.NcConcavePhi

variable {n m : ℕ}

def pU (m j : ℕ) : ℕ := j * (m + 4)
def pA (m i : ℕ) : ℕ := i * (m + 4) + 1
def pY (m i k : ℕ) : ℕ := i * (m + 4) + 2 + k
def pB (m i : ℕ) : ℕ := i * (m + 4) + m + 3

lemma pA_eq (m i : ℕ) : pA m i = pU m i + 1 := rfl
lemma pY_zero (m i : ℕ) : pY m i 0 = pA m i + 1 := by simp [pY, pA]
lemma pY_succ (m i k : ℕ) : pY m i (k + 1) = pY m i k + 1 := by simp [pY]; ring
lemma pB_eq (m i : ℕ) : pB m i = pY m i m + 1 := by simp [pB, pY]; ring
lemma pU_succ (m i : ℕ) : pU m (i + 1) = pB m i + 1 := by simp [pU, pB]; ring
lemma pU_zero (m : ℕ) : pU m 0 = 0 := by simp [pU]

structure Dead (θ : ℝ) (s : ℕ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ)
    (y : Fin n → Fin (m + 1) → ℝ) : Prop where
  hu : ∀ j : Fin (n + 1), s ≤ pU m j → |u j| < θ
  ha : ∀ i : Fin n, s ≤ pA m i → |a i| < θ
  hb : ∀ i : Fin n, s ≤ pB m i → |b i| < θ
  hy : ∀ (i : Fin n) (k : Fin (m + 1)), s ≤ pY m i k → |y i k| < θ

structure Agree (s : ℕ) (u u' : Fin (n + 1) → ℝ) (a a' b b' : Fin n → ℝ)
    (y y' : Fin n → Fin (m + 1) → ℝ) : Prop where
  hu : ∀ j : Fin (n + 1), pU m j ≤ s → u j = u' j
  ha : ∀ i : Fin n, pA m i ≤ s → a i = a' i
  hb : ∀ i : Fin n, pB m i ≤ s → b i = b' i
  hy : ∀ (i : Fin n) (k : Fin (m + 1)), pY m i k ≤ s → y i k = y' i k

lemma single_eq {θ : ℝ} {φ : ℝ → ℝ} (hφ : ∀ t, |t| < θ → φ t = φ 0) {s p : ℕ} {c c' : ℝ}
    (hag : p ≤ s → c = c') (hd : s ≤ p → |c| < θ) (hd' : s ≤ p → |c'| < θ) : φ c = φ c' := by
  rcases le_total p s with h | h
  · rw [hag h]
  · rw [hφ c (hd h), hφ c' (hd' h)]

lemma pair_eq {θ : ℝ} {G : ℝ → ℝ → ℝ} (hG : ∀ t1 t2, |t1| < θ → |t2| < θ → G t1 t2 = 0)
    {s p : ℕ} {c1 c1' c2 c2' : ℝ}
    (hag1 : p ≤ s → c1 = c1') (hag2 : p + 1 ≤ s → c2 = c2')
    (hd1 : s ≤ p → |c1| < θ) (hd1' : s ≤ p → |c1'| < θ)
    (hd2 : s ≤ p + 1 → |c2| < θ) (hd2' : s ≤ p + 1 → |c2'| < θ) :
    G c1 c2 = G c1' c2' := by
  by_cases h : p + 1 ≤ s
  · rw [hag1 (by omega), hag2 h]
  · push Not at h
    rw [hG _ _ (hd1 (by omega)) (hd2 (by omega)), hG _ _ (hd1' (by omega)) (hd2' (by omega))]

lemma zeta_dead {θ t : ℝ} (hθ : 0 < θ) (ht : |t| < θ) : zeta θ t = 0 := zeta_small hθ ht.le

lemma q_local {θ : ℝ} (hθ : 0 < θ) {s : ℕ} {u u' : Fin (n + 1) → ℝ} {a a' b b' : Fin n → ℝ}
    {y y' : Fin n → Fin (m + 1) → ℝ}
    (hd : Dead (m := m) θ s u a b y) (hd' : Dead (m := m) θ s u' a' b' y')
    (hag : Agree (m := m) s u u' a a' b b' y y') :
    q (zu θ u) = q (zu θ u') := by
  funext i
  simp only [q, zu]
  have hν : ∀ t, |t| < θ → nu (zeta θ t) = nu (zeta θ 0) := by
    intro t ht; rw [zeta_dead hθ ht, zeta_dead hθ (by rw [abs_zero]; exact hθ)]
  have hsucc : nu (zeta θ (u i.succ)) = nu (zeta θ (u' i.succ)) :=
    single_eq hν (hag.hu i.succ) (hd.hu i.succ) (hd'.hu i.succ)
  by_cases h : s ≤ pU m i.castSucc
  · have h1 : zeta θ (u i.castSucc) = 0 := zeta_dead hθ (hd.hu _ h)
    have h2 : zeta θ (u' i.castSucc) = 0 := zeta_dead hθ (hd'.hu _ h)
    rw [h1, h2, nu_of_nonpos (le_refl 0)]; ring
  · push Not at h
    rw [hag.hu _ h.le, hsucc]

lemma rho_local {θ : ℝ} (hθ : 0 < θ) {s : ℕ} {u u' : Fin (n + 1) → ℝ} {a a' b b' : Fin n → ℝ}
    {y y' : Fin n → Fin (m + 1) → ℝ}
    (hd : Dead (m := m) θ s u a b y) (hd' : Dead (m := m) θ s u' a' b' y')
    (hag : Agree (m := m) s u u' a a' b b' y y') :
    rho (zu θ u) = rho (zu θ u') := by
  rw [rho_eq_phiN, rho_eq_phiN, q_local hθ hd hd' hag]

lemma arho_local {θ : ℝ} (hθ : 0 < θ) {s : ℕ} {u u' : Fin (n + 1) → ℝ} {a a' b b' : Fin n → ℝ}
    {y y' : Fin n → Fin (m + 1) → ℝ}
    (hd : Dead (m := m) θ s u a b y) (hd' : Dead (m := m) θ s u' a' b' y')
    (hag : Agree (m := m) s u u' a a' b b' y y') (i : Fin n) :
    a i * rho (zu θ u) i = a' i * rho (zu θ u') i := by
  rw [← rho_local hθ hd hd' hag]
  by_cases hr : rho (zu θ u) i = 0
  · rw [hr, mul_zero, mul_zero]
  · have : pA m i ≤ s := by
      by_contra hc
      push Not at hc
      apply hr
      have h1 : s ≤ pU m i.castSucc := by
        simp only [Fin.val_castSucc]; rw [pA_eq] at hc; omega
      have hz : zeta θ (u i.castSucc) = 0 := zeta_dead hθ (hd.hu _ h1)
      simp only [rho, q, zu, hz, nu_of_nonpos (le_refl (0 : ℝ)), zero_mul, zero_div]
    rw [hag.ha i this]

theorem robP_local {θ : ℝ} (hθ : 0 < θ) {s : ℕ} {u u' : Fin (n + 1) → ℝ} {a a' b b' : Fin n → ℝ}
    {y y' : Fin n → Fin (m + 1) → ℝ}
    (hd : Dead (m := m) θ s u a b y) (hd' : Dead (m := m) θ s u' a' b' y')
    (hag : Agree (m := m) s u u' a a' b b' y y') :
    robP θ u a b = robP θ u' a' b' := by
  have h0 : ∀ t, |t| < θ → zeta θ t = zeta θ 0 := by
    intro t ht; rw [zeta_dead hθ ht, zeta_dead hθ (by rw [abs_zero]; exact hθ)]
  have hν : ∀ t, |t| < θ → nu (zeta θ t) = nu (zeta θ 0) := fun t ht => by rw [h0 t ht]
  have hr : ∀ t, |t| < θ → rr (zeta θ t) ^ 2 = rr (zeta θ 0) ^ 2 := fun t ht => by rw [h0 t ht]
  have hz : ∀ t, |t| < θ → zeta θ t ^ 2 = zeta θ 0 ^ 2 := fun t ht => by rw [h0 t ht]
  have e0 : u 0 = u' 0 := hag.hu 0 (by simp [pU_zero])
  have e1 : ∑ j : Fin n, nu (zeta θ (u j.succ)) = ∑ j : Fin n, nu (zeta θ (u' j.succ)) :=
    Finset.sum_congr rfl fun j _ => single_eq hν (hag.hu j.succ) (hd.hu j.succ) (hd'.hu j.succ)
  have e2 : ∑ j, rr (zeta θ (u j)) ^ 2 = ∑ j, rr (zeta θ (u' j)) ^ 2 :=
    Finset.sum_congr rfl fun j _ =>
      single_eq (φ := fun t => rr (zeta θ t) ^ 2) hr (hag.hu j) (hd.hu j) (hd'.hu j)
  have e3 : ∑ i, zeta θ (a i) ^ 2 = ∑ i, zeta θ (a' i) ^ 2 :=
    Finset.sum_congr rfl fun i _ =>
      single_eq (φ := fun t => zeta θ t ^ 2) hz (hag.ha i) (hd.ha i) (hd'.ha i)
  have e4 : ∑ i, a i * rho (zu θ u) i = ∑ i, a' i * rho (zu θ u') i :=
    Finset.sum_congr rfl fun i _ => arho_local hθ hd hd' hag i
  have e5 : ∑ i, rho (zu θ u) i ^ 2 = ∑ i, rho (zu θ u') i ^ 2 := by
    rw [rho_local hθ hd hd' hag]
  have e6 : ∑ i, zeta θ (b i) ^ 2 = ∑ i, zeta θ (b' i) ^ 2 :=
    Finset.sum_congr rfl fun i _ =>
      single_eq (φ := fun t => zeta θ t ^ 2) hz (hag.hb i) (hd.hb i) (hd'.hb i)
  have hβR : ∀ t1 t2, |t1| < θ → |t2| < θ → betaR θ t1 t2 = 0 := by
    intro t1 t2 h1 h2
    simp only [betaR, zeta_dead hθ h1, zeta_dead hθ h2, rr_zero, zero_mul, mul_zero, add_zero]
  have e7 : ∑ i, betaR θ (b i) (u i.succ) = ∑ i, betaR θ (b' i) (u' i.succ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : pU m (i.succ : Fin (n + 1)) = pB m i + 1 := by
      simp only [Fin.val_succ]; exact pU_succ m i
    exact pair_eq hβR (p := pB m i) (s := s) (hag.hb i) (fun h => hag.hu i.succ (by omega))
      (hd.hb i) (hd'.hb i) (fun h => hd.hu i.succ (by omega)) (fun h => hd'.hu i.succ (by omega))
  have e8 : ∑ i : Fin n, rr (zeta θ (u i.succ)) ^ 2 = ∑ i : Fin n, rr (zeta θ (u' i.succ)) ^ 2 :=
    Finset.sum_congr rfl fun j _ =>
      single_eq (φ := fun t => rr (zeta θ t) ^ 2) hr (hag.hu j.succ) (hd.hu j.succ) (hd'.hu j.succ)
  simp only [robP, e0, e1, e2, e3, e4, e5, e6, e7, e8]

theorem robB_local {θ τ : ℝ} (hθ : 0 < θ) {s : ℕ} {u u' : Fin (n + 1) → ℝ} {a a' b b' : Fin n → ℝ}
    {y y' : Fin n → Fin (m + 1) → ℝ}
    (hd : Dead (m := m) θ s u a b y) (hd' : Dead (m := m) θ s u' a' b' y')
    (hag : Agree (m := m) s u u' a a' b b' y y') (i : Fin n) :
    robB θ τ (a i) (b i) (y i) = robB θ τ (a' i) (b' i) (y' i) := by
  have h0 : ∀ t, |t| < θ → zeta θ t = zeta θ 0 := by
    intro t ht; rw [zeta_dead hθ ht, zeta_dead hθ (by rw [abs_zero]; exact hθ)]
  have hz : ∀ t, |t| < θ → zeta θ t ^ 2 = zeta θ 0 ^ 2 := fun t ht => by rw [h0 t ht]
  have hω : ∀ t, |t| < θ → omega θ t = omega θ 0 := by
    intro t ht; rw [omega_small hθ ht.le, omega_small hθ (by simp [hθ.le])]
  have hp0 : pY m i ((0 : Fin (m + 1)) : ℕ) = pA m i + 1 := by rw [Fin.val_zero]; exact pY_zero m i
  have hpl : pB m i = pY m i (Fin.last m) + 1 := by simp only [Fin.val_last]; exact pB_eq m i
  have e1 : zeta θ (y i 0) ^ 2 = zeta θ (y' i 0) ^ 2 :=
    single_eq (φ := fun t => zeta θ t ^ 2) hz (hag.hy i 0) (hd.hy i 0) (hd'.hy i 0)
  have hH : ∀ t1 t2, |t1| < θ → |t2| < θ → huber τ (zeta (2 * θ) (t1 - t2)) = 0 := by
    intro t1 t2 h1 h2
    have : |t1 - t2| ≤ 2 * θ := by
      calc |t1 - t2| ≤ |t1| + |t2| := abs_sub _ _
        _ ≤ 2 * θ := by linarith
    rw [zeta_small (by linarith) this]
    simp [huber, ramp]
  have e2 : ∑ k : Fin m, huber τ (zeta (2 * θ) (y i k.castSucc - y i k.succ)) =
      ∑ k : Fin m, huber τ (zeta (2 * θ) (y' i k.castSucc - y' i k.succ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hp : pY m i (k.succ : Fin (m + 1)) = pY m i (k.castSucc : Fin (m + 1)) + 1 := by
      simp only [Fin.val_succ, Fin.val_castSucc]; exact pY_succ m i k
    exact pair_eq (G := fun t1 t2 => huber τ (zeta (2 * θ) (t1 - t2))) hH
      (p := pY m i k.castSucc) (s := s) (hag.hy i _) (fun h => hag.hy i _ (by omega))
      (hd.hy i _) (hd'.hy i _) (fun h => hd.hy i _ (by omega)) (fun h => hd'.hy i _ (by omega))
  have hβ : ∀ t1 t2, |t1| < θ → |t2| < θ → beta θ t1 t2 = 0 := by
    intro t1 t2 h1 h2
    simp only [beta, zeta_dead hθ h1, zeta_dead hθ h2, zero_mul, mul_zero, add_zero]
  have e3 : beta θ (a i) (y i 0) = beta θ (a' i) (y' i 0) :=
    pair_eq hβ (p := pA m i) (s := s) (hag.ha i) (fun h => hag.hy i 0 (by omega))
      (hd.ha i) (hd'.ha i) (fun h => hd.hy i 0 (by omega)) (fun h => hd'.hy i 0 (by omega))
  have hβ' : ∀ t1 t2, |t1| < θ → |t2| < θ → beta θ t2 t1 = 0 := fun t1 t2 h1 h2 => hβ t2 t1 h2 h1
  have e4 : beta θ (b i) (y i (Fin.last m)) = beta θ (b' i) (y' i (Fin.last m)) :=
    pair_eq (G := fun t1 t2 => beta θ t2 t1) hβ' (p := pY m i (Fin.last m)) (s := s)
      (hag.hy i _) (fun h => hag.hb i (by omega))
      (hd.hy i _) (hd'.hy i _) (fun h => hd.hb i (by omega)) (fun h => hd'.hb i (by omega))
  have e5 : zeta θ (b i) ^ 2 = zeta θ (b' i) ^ 2 :=
    single_eq (φ := fun t => zeta θ t ^ 2) hz (hag.hb i) (hd.hb i) (hd'.hb i)
  have e6 : omega θ (y i 0) = omega θ (y' i 0) := single_eq hω (hag.hy i 0) (hd.hy i 0) (hd'.hy i 0)
  have e7 : omega θ (y i (Fin.last m)) = omega θ (y' i (Fin.last m)) :=
    single_eq hω (hag.hy i _) (hd.hy i _) (hd'.hy i _)
  simp only [robB, e1, e2, e3, e4, e5, e6, e7]

theorem robF_local {θ τ : ℝ} (hθ : 0 < θ) {s : ℕ} {u u' : Fin (n + 1) → ℝ} {a a' b b' : Fin n → ℝ}
    {y y' : Fin n → Fin (m + 1) → ℝ}
    (hd : Dead (m := m) θ s u a b y) (hd' : Dead (m := m) θ s u' a' b' y')
    (hag : Agree (m := m) s u u' a a' b b' y y') :
    robF θ τ u a b y = robF θ τ u' a' b' y' := by
  simp only [robF, robP_local hθ hd hd' hag,
    Finset.sum_congr rfl fun i _ => robB_local (τ := τ) hθ hd hd' hag i]

noncomputable def prU (r : ℕ) (u : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun j => if pU m j < r then u j else 0
noncomputable def prA (r : ℕ) (a : Fin n → ℝ) : Fin n → ℝ := fun i => if pA m i < r then a i else 0
noncomputable def prB (r : ℕ) (b : Fin n → ℝ) : Fin n → ℝ := fun i => if pB m i < r then b i else 0
noncomputable def prY (r : ℕ) (y : Fin n → Fin (m + 1) → ℝ) : Fin n → Fin (m + 1) → ℝ :=
  fun i k => if pY m i k < r then y i k else 0

lemma agree_pr (s : ℕ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (y : Fin n → Fin (m + 1) → ℝ) :
    Agree (m := m) s u (prU (m := m) (s + 1) u) a (prA (m := m) (s + 1) a) b (prB (m := m) (s + 1) b)
      y (prY (s + 1) y) where
  hu j h := by simp only [prU]; rw [ite_eq_left (by omega)]
  ha i h := by simp only [prA]; rw [ite_eq_left (by omega)]
  hb i h := by simp only [prB]; rw [ite_eq_left (by omega)]
  hy i k h := by simp only [prY]; rw [ite_eq_left (by omega)]

lemma dead_pr {θ : ℝ} (hθ : 0 < θ) {s : ℕ} {u : Fin (n + 1) → ℝ} {a b : Fin n → ℝ}
    {y : Fin n → Fin (m + 1) → ℝ} (hd : Dead (m := m) θ s u a b y) :
    Dead (m := m) θ s (prU (m := m) (s + 1) u) (prA (m := m) (s + 1) a) (prB (m := m) (s + 1) b)
      (prY (s + 1) y) where
  hu j h := by
    simp only [prU]; split_ifs
    · exact hd.hu j h
    · simp [hθ]
  ha i h := by
    simp only [prA]; split_ifs
    · exact hd.ha i h
    · simp [hθ]
  hb i h := by
    simp only [prB]; split_ifs
    · exact hd.hb i h
    · simp [hθ]
  hy i k h := by
    simp only [prY]; split_ifs
    · exact hd.hy i k h
    · simp [hθ]

theorem robF_pr {θ τ : ℝ} (hθ : 0 < θ) {s : ℕ} {u : Fin (n + 1) → ℝ} {a b : Fin n → ℝ}
    {y : Fin n → Fin (m + 1) → ℝ} (hd : Dead (m := m) θ s u a b y) :
    robF θ τ u a b y = robF θ τ (prU (m := m) (s + 1) u) (prA (m := m) (s + 1) a)
      (prB (m := m) (s + 1) b) (prY (s + 1) y) :=
  robF_local hθ hd (dead_pr hθ hd) (agree_pr s u a b y)

end LongTails.Proofs.NcConcaveLocality
