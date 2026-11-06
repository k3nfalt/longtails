import LongTails.Proofs.BallAnchoredRun

open scoped RealInnerProductSpace

namespace LongTails.Proofs.BallAnchoredSearchRun

open LongTails.Setups.HessianStableSkewMonotone
open LongTails.Algorithms.BallAnchoredNewton
open LongTails.Proofs.BallAnchoredInner
open LongTails.Proofs.BallAnchoredSearch
open LongTails.Proofs.BallAnchoredTrial
open LongTails.Proofs.BallAnchoredOuter
open LongTails.Proofs.BallAnchoredRun

noncomputable section

variable {p : Public} {F : p.E → p.E} {S : p.E →L[ℝ] p.E}

def haltBound (p : Public) (Λ : ℝ) : ℕ :=
  Nat.log2 ⌈24 * Λ * rho p * stepMax p / (7 * radius p)⌉₊

def lipBound (p : Public) (Λ : ℝ) : ℝ :=
  2 * Λ * rho p + stepMax p * Λ * ((2 * p.D + radius p) * (48 * Λ * rho p) / (7 * radius p) +
    Λ * rho p)

def bisBound (p : Public) (Λ : ℝ) : ℕ :=
  Nat.log2 ⌈6 * lipBound p Λ * stepMax p / radius p⌉₊

def tickMax (p : Public) (Λ : ℝ) (k : ℕ) : ℕ := 2 * newtonCount k (stepMax p) Λ + 1

lemma le_log2_of_pow_le {h : ℕ} {X : ℝ} (hX : (2 : ℝ) ^ h ≤ X) : h ≤ Nat.log2 ⌈X⌉₊ := by
  have h1 : (2 : ℝ) ^ h ≤ (⌈X⌉₊ : ℝ) := hX.trans (Nat.le_ceil X)
  have h2 : 2 ^ h ≤ ⌈X⌉₊ := by exact_mod_cast h1
  rw [Nat.log2_eq_log_two]
  exact Nat.le_log_of_pow_le (by norm_num) h2

lemma log2_mono {m n : ℕ} (h : m ≤ n) : Nat.log2 m ≤ Nat.log2 n := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right h

lemma newtonCount_mono {k k' : ℕ} {a a' Γ Γ' : ℝ} (hk : k ≤ k') (ha : 0 ≤ a) (hΓ : 0 ≤ Γ)
    (haa : a ≤ a') (hΓΓ : Γ ≤ Γ') : newtonCount k a Γ ≤ newtonCount k' a' Γ' := by
  unfold newtonCount
  have h1 := log2_mono (show k + 1 ≤ k' + 1 by omega)
  have h2 : ⌈1 + 4 * a * Γ⌉₊ ≤ ⌈1 + 4 * a' * Γ'⌉₊ := by
    apply Nat.ceil_mono
    have : a * Γ ≤ a' * Γ' := mul_le_mul haa hΓΓ hΓ (ha.trans haa)
    linarith
  have h3 := log2_mono h2
  omega

lemma stepMax_pos (hreg : Regular p F S) : 0 < stepMax p := by
  unfold stepMax; have := radius_pos hreg; have := hreg.D_pos; have := hreg.ε_pos; positivity

variable (hreg : Regular p F S) {xs : p.E} {Λ : ℝ} (hR : Region p F xs Λ)

include hreg hR in
lemma trial_ticks {k K : ℕ} {A : ℝ} {z g : p.E} (hI : Inv p F xs Λ k A z g) (hk : k ≤ K)
    {a : ℝ} (ha : 0 < a) (hle : a ≤ stepMax p) :
    2 * trialCount F k A z g a + 1 ≤ tickMax p Λ K := by
  unfold trialCount tickMax
  have hc : ‖cOf p A z g a - xs‖ ≤ 3 * p.D + 1 / (4 * p.M) := by
    have := c_dist hreg hR hI.ok ha
    have hr := radius_pos hreg
    rw [rho_eq hreg]; unfold rho; linarith
  have hΓ := hR.bound _ hc
  have := newtonCount_mono hk ha.le (norm_nonneg _) hle hΓ
  omega

lemma phi_close (k : ℕ) (A : ℝ) (z g : p.E) {a : ℝ} (ha : 0 < a) :
    |‖finalPoint F k A z g a - cOf p A z g a‖ - phi hreg A z g a ha| ≤ radius p / 12 :=
  (dhat_phi hreg k A z g ha).trans (tolerance_le hreg k)

include hreg hR in
lemma high_count {k : ℕ} {A : ℝ} {z g : p.E} (hI : Inv p F xs Λ k A z g) (h : ℕ)
    (hpos : 0 < stepMax p / 2 ^ h)
    (hφ : 7 * radius p / 12 ≤ phi hreg A z g (stepMax p / 2 ^ h) hpos) : h ≤ haltBound p Λ := by
  apply le_log2_of_pow_le
  have h1 := phi_le hreg hR hI.ok hpos
  have hr := radius_pos hreg
  have h2 : (0 : ℝ) < 2 ^ h := by positivity
  have h3 : 7 * radius p / 12 ≤ stepMax p / 2 ^ h * (2 * Λ * rho p) := hφ.trans h1
  rw [div_mul_eq_mul_div, le_div_iff₀ h2] at h3
  rw [le_div_iff₀ (by positivity)]
  nlinarith

structure BisOK (hreg : Regular p F S) (A : ℝ) (z g : p.E) (j : ℕ) (lo hi : ℝ) : Prop where
  lo_pos : 0 < lo
  lo_hi : lo < hi
  hi_le : hi ≤ stepMax p
  lo_big : 7 * radius p ≤ 48 * Λ * rho p * lo
  lo_low : ∀ hl : 0 < lo, phi hreg A z g lo hl < 5 * radius p / 12
  hi_high : ∀ hh : 0 < hi, 7 * radius p / 12 ≤ phi hreg A z g hi hh
  width : (hi - lo) * 2 ^ j ≤ stepMax p

include hR in
lemma bis_count {k : ℕ} {A : ℝ} {z g : p.E} (hI : Inv p F xs Λ k A z g) {j : ℕ} {lo hi : ℝ}
    (hB : BisOK (Λ := Λ) hreg A z g j lo hi) : j ≤ bisBound p Λ := by
  apply le_log2_of_pow_le
  have hlo := hB.lo_pos
  have hhi : 0 < hi := lt_trans hlo hB.lo_hi
  have hlip := phi_lip hreg hR hI.ok hlo le_rfl hB.lo_hi.le
  have h1 := hB.lo_low hlo
  have h2 := hB.hi_high hhi
  have hr := radius_pos hreg
  have hΛ := hR.Λ_nonneg
  have hρ : 0 ≤ rho p := by unfold rho; have := hreg.D_pos; positivity
  have hD := hreg.D_pos
  have hinv : (2 * p.D + radius p) / lo ≤ (2 * p.D + radius p) * (48 * Λ * rho p) / (7 * radius p) := by
    rw [div_le_div_iff₀ hlo (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hB.lo_big (by positivity : (0 : ℝ) ≤ 2 * p.D + radius p)]
  have hK : 2 * Λ * rho p + hi * Λ * ((2 * p.D + radius p) / lo + Λ * rho p) ≤ lipBound p Λ := by
    unfold lipBound
    have hhm := hB.hi_le
    have h3 : 0 ≤ (2 * p.D + radius p) / lo + Λ * rho p := by positivity
    have h4 : hi * Λ * ((2 * p.D + radius p) / lo + Λ * rho p) ≤
        stepMax p * Λ * ((2 * p.D + radius p) / lo + Λ * rho p) := by
      apply mul_le_mul_of_nonneg_right _ h3
      exact mul_le_mul_of_nonneg_right hhm hΛ
    have h5 : stepMax p * Λ * ((2 * p.D + radius p) / lo + Λ * rho p) ≤
        stepMax p * Λ * ((2 * p.D + radius p) * (48 * Λ * rho p) / (7 * radius p) +
          Λ * rho p) := by
      apply mul_le_mul_of_nonneg_left _ (by have := stepMax_pos hreg; positivity)
      linarith
    linarith
  have hab : |lo - hi| = hi - lo := by rw [abs_sub_comm, abs_of_pos (by linarith [hB.lo_hi])]
  rw [hab] at hlip
  have hdiff : radius p / 6 < (hi - lo) * lipBound p Λ := by
    have h6 : phi hreg A z g hi (lt_of_lt_of_le hlo hB.lo_hi.le) -
        phi hreg A z g lo (lt_of_lt_of_le hlo le_rfl) ≤
        (hi - lo) * (2 * Λ * rho p + hi * Λ * ((2 * p.D + radius p) / lo + Λ * rho p)) :=
      (le_abs_self _).trans hlip
    have h7 : (hi - lo) * (2 * Λ * rho p + hi * Λ * ((2 * p.D + radius p) / lo + Λ * rho p)) ≤
        (hi - lo) * lipBound p Λ :=
      mul_le_mul_of_nonneg_left hK (by linarith [hB.lo_hi])
    have h8 : 7 * radius p / 12 ≤ phi hreg A z g hi (lt_of_lt_of_le hlo hB.lo_hi.le) := h2
    have h9 : phi hreg A z g lo (lt_of_lt_of_le hlo le_rfl) < 5 * radius p / 12 := h1
    linarith
  have hw := hB.width
  have hp2 : (0 : ℝ) < 2 ^ j := by positivity
  have hL : 0 < lipBound p Λ := by
    by_contra hneg
    have : (hi - lo) * lipBound p Λ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith [hB.lo_hi]) (le_of_not_gt hneg)
    linarith
  rw [le_div_iff₀ hr]
  have : radius p / 6 * 2 ^ j < stepMax p * lipBound p Λ := by
    calc radius p / 6 * 2 ^ j < (hi - lo) * lipBound p Λ * 2 ^ j :=
          mul_lt_mul_of_pos_right hdiff hp2
      _ = (hi - lo) * 2 ^ j * lipBound p Λ := by ring
      _ ≤ stepMax p * lipBound p Λ := mul_le_mul_of_nonneg_right hw hL.le
  nlinarith


lemma phi_congr {A : ℝ} {z g : p.E} {a a' : ℝ} (h : a = a') (ha : 0 < a) (ha' : 0 < a') :
    phi hreg A z g a ha = phi hreg A z g a' ha' := by
  subst h; rfl

structure Accepted (k : ℕ) (A : ℝ) (z g : p.E) (a : ℝ) : Prop where
  pos : 0 < a
  le : a ≤ stepMax p
  big : a = stepMax p ∨ 7 * radius p ≤ 48 * Λ * rho p * a
  res : ∀ ha : 0 < a, phi hreg A z g a ha < radius p
  kind : a = stepMax p ∨ radius p / 3 ≤ ‖finalPoint F k A z g a - cOf p A z g a‖

def Reaches (k : ℕ) (A : ℝ) (z g : p.E) (σ : State p) (N : ℕ) : Prop :=
  ∃ n ≤ N, ∃ a, Accepted (Λ := Λ) hreg k A z g a ∧
    (trueStep F)^[n] σ = outerStart (k + 1) (A + a) (finalPoint F k A z g a)
      (F (finalPoint F k A z g a))

lemma reaches_prepend {k : ℕ} {A : ℝ} {z g : p.E} {σ σ' : State p} {t N : ℕ}
    (hσ : (trueStep F)^[t] σ = σ') (hR : Reaches (Λ := Λ) hreg k A z g σ' N) :
    Reaches (Λ := Λ) hreg k A z g σ (N + t) := by
  obtain ⟨n, hn, a, hacc, he⟩ := hR
  refine ⟨n + t, by omega, a, hacc, ?_⟩
  rw [Function.iterate_add_apply, hσ, he]

lemma low_phi (k : ℕ) (A : ℝ) (z g : p.E) {a : ℝ} (ha : 0 < a)
    (hd : ‖finalPoint F k A z g a - cOf p A z g a‖ < radius p / 3) :
    phi hreg A z g a ha < 5 * radius p / 12 := by
  have := (abs_le.mp (phi_close hreg k A z g ha)).1
  linarith

lemma high_phi (k : ℕ) (A : ℝ) (z g : p.E) {a : ℝ} (ha : 0 < a)
    (hd : 2 * radius p / 3 ≤ ‖finalPoint F k A z g a - cOf p A z g a‖) :
    7 * radius p / 12 ≤ phi hreg A z g a ha := by
  have := (abs_le.mp (phi_close hreg k A z g ha)).2
  linarith

lemma mid_phi (k : ℕ) (A : ℝ) (z g : p.E) {a : ℝ} (ha : 0 < a)
    (hd : ¬ 2 * radius p / 3 ≤ ‖finalPoint F k A z g a - cOf p A z g a‖) :
    phi hreg A z g a ha < radius p := by
  have := (abs_le.mp (phi_close hreg k A z g ha)).1
  have hr := radius_pos hreg
  have hd' := lt_of_not_ge hd
  linarith

include hR in
lemma bis_search {k K : ℕ} {A : ℝ} {z g : p.E} (hI : Inv p F xs Λ k A z g) (hk : k ≤ K)
    (h : ℕ) (m : ℕ) : ∀ j lo hi, BisOK (Λ := Λ) hreg A z g j lo hi →
      bisBound p Λ + 1 ≤ j + m →
        Reaches (Λ := Λ) hreg k A z g (trialStart k A z g h true lo hi ((lo + hi) / 2))
          (m * tickMax p Λ K) := by
  induction m with
  | zero =>
    intro j lo hi hB hj
    have := bis_count hreg hR hI hB
    omega
  | succ m ih =>
    intro j lo hi hB hj
    set a := (lo + hi) / 2 with hadef
    have hlo := hB.lo_pos
    have hlh := hB.lo_hi
    have ha : 0 < a := by rw [hadef]; linarith
    have hla : lo < a := by rw [hadef]; linarith
    have hah : a < hi := by rw [hadef]; linarith
    have hamax : a ≤ stepMax p := le_trans hah.le hB.hi_le
    have hΛρ : 0 ≤ 48 * Λ * rho p := by
      have := hR.Λ_nonneg; unfold rho; have := radius_pos hreg; have := hreg.D_pos; positivity
    have hbig : 7 * radius p ≤ 48 * Λ * rho p * a :=
      hB.lo_big.trans (mul_le_mul_of_nonneg_left hla.le hΛρ)
    have hrun := trial_run F k A z g h true lo hi a
    have htick := trial_ticks hreg hR hI hk ha hamax
    have hbound : m * tickMax p Λ K + (2 * trialCount F k A z g a + 1) ≤
        (m + 1) * tickMax p Λ K := by rw [add_mul, one_mul]; omega
    by_cases hd : ‖finalPoint F k A z g a - cOf p A z g a‖ < radius p / 3
    · rw [trialEnd_low_bis F k A z g h lo hi a hd] at hrun
      have hB' : BisOK (Λ := Λ) hreg A z g (j + 1) a hi :=
        ⟨ha, hah, hB.hi_le, hbig, fun hl => low_phi hreg k A z g hl hd, hB.hi_high,
          by have := hB.width; rw [pow_succ]; rw [hadef]; nlinarith⟩
      have := reaches_prepend hreg hrun (ih (j + 1) a hi hB' (by omega))
      obtain ⟨n, hn, rest⟩ := this
      exact ⟨n, hn.trans hbound, rest⟩
    · by_cases hd' : 2 * radius p / 3 ≤ ‖finalPoint F k A z g a - cOf p A z g a‖
      · rw [trialEnd_high_bis F k A z g h lo hi a hd hd'] at hrun
        have hB' : BisOK (Λ := Λ) hreg A z g (j + 1) lo a :=
          ⟨hlo, hla, hamax, hB.lo_big, hB.lo_low, fun hh => high_phi hreg k A z g hh hd',
            by have := hB.width; rw [pow_succ]; rw [hadef]; nlinarith⟩
        have := reaches_prepend hreg hrun (ih (j + 1) lo a hB' (by omega))
        obtain ⟨n, hn, rest⟩ := this
        exact ⟨n, hn.trans hbound, rest⟩
      · rw [trialEnd_accept F k A z g h true lo hi a hd hd'] at hrun
        refine ⟨2 * trialCount F k A z g a + 1, by rw [add_mul, one_mul]; omega, a,
          ⟨ha, hamax, Or.inr hbig, fun ha' => mid_phi hreg k A z g ha' hd', Or.inr ?_⟩, hrun⟩
        exact le_of_not_gt hd

lemma reaches_mono {k : ℕ} {A : ℝ} {z g : p.E} {σ : State p} {N M : ℕ}
    (hR : Reaches (Λ := Λ) hreg k A z g σ N) (h : N ≤ M) :
    Reaches (Λ := Λ) hreg k A z g σ M := by
  obtain ⟨n, hn, rest⟩ := hR
  exact ⟨n, hn.trans h, rest⟩

include hR in
lemma big_of_double {A : ℝ} {k : ℕ} {z g : p.E} (hI : Inv p F xs Λ k A z g) {a : ℝ}
    (ha : 0 < a) (h2 : 7 * radius p / 12 ≤ phi hreg A z g (2 * a) (by positivity)) :
    7 * radius p ≤ 48 * Λ * rho p * a := by
  have := phi_le hreg hR hI.ok (by positivity : 0 < 2 * a)
  nlinarith

include hR in
lemma halving_core {k K : ℕ} {A : ℝ} {z g : p.E} (hI : Inv p F xs Λ k A z g) (hk : k ≤ K)
    (N M : ℕ) (hM : N + tickMax p Λ K ≤ M) (hM2 : (bisBound p Λ + 2) * tickMax p Λ K ≤ M)
    (h : ℕ)
    (hH : ∀ h', h = h' + 1 → ∀ hp : 0 < stepMax p / 2 ^ h',
      7 * radius p / 12 ≤ phi hreg A z g (stepMax p / 2 ^ h') hp)
    (hcont : h ≤ haltBound p Λ →
      (∀ hp : 0 < stepMax p / 2 ^ h, 7 * radius p / 12 ≤ phi hreg A z g (stepMax p / 2 ^ h) hp) →
      Reaches (Λ := Λ) hreg k A z g
        (trialStart k A z g (h + 1) false 0 0 (stepMax p / 2 ^ (h + 1))) N) :
    Reaches (Λ := Λ) hreg k A z g (trialStart k A z g h false 0 0 (stepMax p / 2 ^ h)) M := by
  have hsm := stepMax_pos hreg
  have hr := radius_pos hreg
  set a := stepMax p / 2 ^ h with hadef
  have ha : 0 < a := by positivity
  have hamax : a ≤ stepMax p := by
    rw [hadef]; exact div_le_self hsm.le (one_le_pow₀ (by norm_num))
  have hrun := trial_run F k A z g h false 0 0 a
  have htick := trial_ticks hreg hR hI hk ha hamax
  have hbig : h ≠ 0 → 7 * radius p ≤ 48 * Λ * rho p * a := by
    intro hh
    obtain ⟨h', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hh
    have e : stepMax p / 2 ^ h' = 2 * a := by rw [hadef, pow_succ]; ring
    have := hH h' rfl (by positivity)
    rw [phi_congr hreg e (by positivity) (by positivity)] at this
    exact big_of_double hreg hR hI ha this
  have htM : 2 * trialCount F k A z g a + 1 ≤ M := by
    have : tickMax p Λ K ≤ (bisBound p Λ + 2) * tickMax p Λ K := by
      calc tickMax p Λ K = 1 * tickMax p Λ K := (one_mul _).symm
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    omega
  by_cases hd : ‖finalPoint F k A z g a - cOf p A z g a‖ < radius p / 3
  · by_cases hh : h = 0
    · have e0 : a = stepMax p := by rw [hadef, hh, pow_zero, div_one]
      rw [hh] at hrun ⊢
      rw [trialEnd_low_term F k A z g 0 0 a hd] at hrun
      refine ⟨_, htM, a, ⟨ha, hamax, Or.inl e0, fun ha' => ?_, Or.inl e0⟩, hrun⟩
      have := low_phi hreg k A z g ha' hd
      linarith
    · obtain ⟨h', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hh
      have e : stepMax p / 2 ^ h' = 2 * a := by rw [hadef, pow_succ]; ring
      have h2 := hH h' rfl (by positivity)
      rw [phi_congr hreg e (by positivity) (by positivity)] at h2
      rw [trialEnd_low_bracket F k A z g (h' + 1) 0 0 a hd hh,
        show 3 * a / 2 = (a + 2 * a) / 2 by ring] at hrun
      have hB : BisOK (Λ := Λ) hreg A z g 0 a (2 * a) :=
        ⟨ha, by linarith, by rw [← e]; exact div_le_self hsm.le (one_le_pow₀ (by norm_num)),
          hbig hh, fun hl => low_phi hreg k A z g hl hd, fun _ => h2,
          by rw [pow_zero, mul_one]; linarith⟩
      have hs := bis_search hreg hR hI hk (h' + 1) (bisBound p Λ + 1) 0 a (2 * a) hB (by omega)
      refine reaches_mono hreg (reaches_prepend hreg hrun hs) ?_
      have : (bisBound p Λ + 1) * tickMax p Λ K + tickMax p Λ K =
          (bisBound p Λ + 2) * tickMax p Λ K := by ring
      omega
  · by_cases hd' : 2 * radius p / 3 ≤ ‖finalPoint F k A z g a - cOf p A z g a‖
    · rw [trialEnd_high_halve F k A z g h 0 0 a hd hd',
        show a / 2 = stepMax p / 2 ^ (h + 1) by rw [hadef, pow_succ, div_div]] at hrun
      have hhigh : ∀ hp : 0 < stepMax p / 2 ^ h,
          7 * radius p / 12 ≤ phi hreg A z g (stepMax p / 2 ^ h) hp :=
        fun hp => high_phi hreg k A z g hp hd'
      have hcount := high_count hreg hR hI h ha (hhigh ha)
      refine reaches_mono hreg (reaches_prepend hreg hrun (hcont hcount hhigh)) ?_
      omega
    · rw [trialEnd_accept F k A z g h false 0 0 a hd hd'] at hrun
      have hbig' : a = stepMax p ∨ 7 * radius p ≤ 48 * Λ * rho p * a := by
        by_cases hh : h = 0
        · left; rw [hadef, hh, pow_zero, div_one]
        · right; exact hbig hh
      refine ⟨_, htM, a, ⟨ha, hamax, hbig', fun ha' => mid_phi hreg k A z g ha' hd',
        Or.inr ?_⟩, hrun⟩
      exact le_of_not_gt hd

include hR in
lemma halving_search {k K : ℕ} {A : ℝ} {z g : p.E} (hI : Inv p F xs Λ k A z g) (hk : k ≤ K)
    (m : ℕ) : ∀ h : ℕ,
      (∀ h', h = h' + 1 → ∀ hp : 0 < stepMax p / 2 ^ h',
        7 * radius p / 12 ≤ phi hreg A z g (stepMax p / 2 ^ h') hp) →
      haltBound p Λ + 1 ≤ h + m →
        Reaches (Λ := Λ) hreg k A z g (trialStart k A z g h false 0 0 (stepMax p / 2 ^ h))
          ((m + bisBound p Λ + 2) * tickMax p Λ K) := by
  induction m with
  | zero =>
    intro h hH hh
    refine halving_core hreg hR hI hk 0 _ ?_ (by rw [zero_add]) h hH (fun hc _ => by omega)
    simp only [zero_add]
    exact Nat.le_mul_of_pos_left _ (by omega)
  | succ m ih =>
    intro h hH hh
    refine halving_core hreg hR hI hk ((m + bisBound p Λ + 2) * tickMax p Λ K) _ (le_of_eq ?_)
      ?_ h hH (fun _ hle => ih (h + 1) (fun h' e hp => ?_) (by omega))
    · ring
    · exact Nat.mul_le_mul_right _ (by omega)
    · have e' : h' = h := by omega
      subst e'
      exact hle hp

include hR in
lemma outer_search {k K : ℕ} {A : ℝ} {z g : p.E} (hI : Inv p F xs Λ k A z g) (hk : k ≤ K)
    (hA : A < stepMax p) :
    Reaches (Λ := Λ) hreg k A z g (outerStart k A z g)
      ((haltBound p Λ + bisBound p Λ + 3) * tickMax p Λ K) := by
  have e : outerStart k A z g = trialStart k A z g 0 false 0 0 (stepMax p / 2 ^ 0) := by
    unfold outerStart
    rw [ite_eq_right (not_le.mpr hA), pow_zero, div_one]
  rw [e]
  have := halving_search hreg hR hI hk (haltBound p Λ + 1) 0 (fun h' e _ => by omega)
    (by omega)
  refine reaches_mono hreg this (le_of_eq ?_)
  ring

end

end LongTails.Proofs.BallAnchoredSearchRun
