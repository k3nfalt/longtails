import LongTails.Proofs.SlidingWirePartial
import LongTails.Proofs.SlidingLowerSim
import LongTails.Proofs.SlidingLowerOracle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingWireSim

open LongTails.Proofs.SlidingLowerChain (Point)

open SlidingWireChain SlidingWireLocal SlidingWirePartial FrontierChainProfiles FrontierChain
open FrontierChainGeometry SmoothConvexFiniteGeometry SmoothConvexFiniteWall SmoothConvexFiniteHiding
open SlidingLowerSim FiniteSumNondualLowerHiding FiniteSumNondualLowerExposure
open FiniteSumNondualLowerAveraging QuasarHardProfiles
open Classical

variable {d k : ℕ} {S : Type*}

lemma ramp_le_max (t : ℝ) : ramp t ≤ max t 0 := by
  rcases le_or_gt t 0 with h | h
  · rw [ramp_of_nonpos h]; exact le_max_right _ _
  · rcases le_or_gt t 1 with h1 | h1
    · rw [ramp_of_mid h.le h1]
      have : t ^ 2 / 2 ≤ t := by nlinarith
      exact this.trans (le_max_left _ _)
    · rw [ramp_of_ge h1.le]
      linarith [le_max_left t 0]

lemma sp_le_abs {δ : ℝ} (hδ : 0 ≤ δ) (e : ℝ) : sp δ e ≤ |e| := by
  unfold sp
  have h1 := ramp_le_max (e - δ)
  have h2 := ramp_le_max (-e - δ)
  rcases le_total 0 e with h | h
  · have : max (-e - δ) 0 = 0 := max_eq_right (by linarith)
    rw [this] at h2
    have : max (e - δ) 0 ≤ e := max_le (by linarith) h
    rw [abs_of_nonneg h]; linarith
  · have : max (e - δ) 0 = 0 := max_eq_right (by linarith)
    rw [this] at h1
    have : max (-e - δ) 0 ≤ -e := max_le (by linarith) (by linarith)
    rw [abs_of_nonpos h]; linarith

lemma link_le (r : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (l : ℕ) (s t : ℝ) :
    link r δ l s t ≤ 4 + ((r : ℝ) ^ 2 + 7) * (|s| + |t|) := by
  have hc := coef_bounds r l
  have h0 : 0 ≤ ((r : ℝ) ^ 2 + 7) * (|s| + |t|) := by positivity
  unfold link
  split_ifs
  · linarith [(edge_bounds s t).2]
  · have h1 := sp_le_abs hδ (stretch r l s t)
    have h2 : |stretch r l s t| ≤ ((r : ℝ) ^ 2 + 7) * (|s| + |t|) := by
      unfold stretch
      calc _ ≤ |cA r l * s| + |cB r l * t| := abs_add_le _ _
        _ = |cA r l| * |s| + |cB r l| * |t| := by rw [abs_mul, abs_mul]
        _ ≤ ((r : ℝ) ^ 2 + 7) * |s| + ((r : ℝ) ^ 2 + 7) * |t| := by
            gcongr
            · exact hc.1
            · exact hc.2
        _ = _ := by ring
    linarith

lemma coord_abs_sum (π : Fin (k + 1) ↪ Fin d) (u : Point d) (c : ℝ) :
    c * ∑ j : Fin (k + 1), |u (π j)| ≤ ‖u‖ ^ 2 + (k + 1) * c ^ 2 / 4 := by
  have h1 : ∀ j : Fin (k + 1), c * |u (π j)| ≤ u (π j) ^ 2 + c ^ 2 / 4 := by
    intro j
    nlinarith [sq_nonneg (|u (π j)| - c / 2), sq_abs (u (π j))]
  have h2 := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (k + 1)))) => h1 j)
  rw [← Finset.mul_sum] at h2
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h2
  have h3 := coordinate_sq_sum_le π u
  push_cast at h2
  nlinarith

lemma links_abs_sum (π : Fin (k + 1) ↪ Fin d) (u : Point d) :
    ∑ i : Fin k, (|u (π i.castSucc)| + |u (π i.succ)|) ≤ 2 * ∑ j : Fin (k + 1), |u (π j)| := by
  rw [Finset.sum_add_distrib]
  have h1 := Fin.sum_univ_castSucc (fun j : Fin (k + 1) => |u (π j)|)
  have h2 := Fin.sum_univ_succ (fun j : Fin (k + 1) => |u (π j)|)
  have h3 := abs_nonneg (u (π (Fin.last k)))
  have h4 := abs_nonneg (u (π 0))
  linarith

lemma pobj_upper (r : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (π : Fin (k + 1) ↪ Fin d) (V : ℕ) (u : Point d) :
    pobj r δ π V u ≤ ‖u‖ ^ 2 + (4 + 4 * k + (k + 1) * ((r : ℝ) ^ 2 + 7) ^ 2) := by
  unfold pobj
  have hp : (if 0 < V then -potential (u (π 0)) else 0) ≤ 0 := by
    split_ifs
    · linarith [(potential_bounds (u (π 0))).1]
    · rfl
  have hs : ∑ i : Fin k, (if i.val + 1 < V then link r δ i.val (u (π i.castSucc)) (u (π i.succ)) else 0)
      ≤ ∑ i : Fin k, (4 + ((r : ℝ) ^ 2 + 7) * (|u (π i.castSucc)| + |u (π i.succ)|)) := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact link_le r hδ _ _ _
    · positivity
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hl := links_abs_sum π u
  have hc := coord_abs_sum π u (2 * ((r : ℝ) ^ 2 + 7))
  have hr : 0 ≤ (r : ℝ) ^ 2 + 7 := by positivity
  nlinarith

lemma obj_eq_pobj (r : ℕ) (δ : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : Point d) :
    obj r δ π u = pobj r δ π (k + 1) u := by
  unfold obj pobj
  rw [ite_eq_left (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [ite_eq_left (by omega)]

lemma field_eq_pfield (r : ℕ) (δ : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : Point d) :
    field r δ π u = pfield r δ π (k + 1) u := by
  unfold SlidingWireChain.field pfield
  rw [ite_eq_left (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [ite_eq_left (by omega)]

noncomputable def wGp (r : ℕ) (δ R Λ : ℝ) (π : Fin (k + 1) ↪ Fin d) (V : ℕ) (u : Point d) :
    Point d :=
  weight (R ^ 2) (pobj r δ π V u / Λ) (wall R u) • pfield r δ π V u +
    (1 - weight (R ^ 2) (pobj r δ π V u / Λ) (wall R u)) • ((4 * Λ) • u)

lemma wGp_full (r : ℕ) (δ R Λ : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : Point d) :
    wGp r δ R Λ π (k + 1) u = wG r δ R Λ π u := by
  unfold wGp wG
  rw [← obj_eq_pobj, ← field_eq_pfield]

lemma wGp_far (r : ℕ) {δ R Λ : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R) (hΛ : 1 ≤ Λ)
    (hRk : 4 + 4 * (k : ℝ) + (k + 1) * ((r : ℝ) ^ 2 + 7) ^ 2 ≤ R ^ 2)
    (π : Fin (k + 1) ↪ Fin d) (V : ℕ) (u : Point d) (hu : 3 * R ≤ ‖u‖) :
    wGp r δ R Λ π V u = (4 * Λ) • u := by
  have hp := pobj_upper r hδ π V u
  have hw : weight (R ^ 2) (pobj r δ π V u / Λ) (wall R u) = 0 := by
    apply (smoothMax_eq_right _ _ _ (by positivity) _).2
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * R) hu 2
    have hq : pobj r δ π V u / Λ ≤ ‖u‖ ^ 2 + R ^ 2 := by
      rcases le_or_gt (pobj r δ π V u) 0 with h | h
      · have : pobj r δ π V u / Λ ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (by linarith)
        nlinarith [sq_nonneg ‖u‖]
      · rw [div_le_iff₀ (by linarith)]
        nlinarith [sq_nonneg ‖u‖]
    unfold wall
    nlinarith
  unfold wGp
  rw [hw]
  simp


structure WScale where
  r : ℕ
  δ : ℝ
  R : ℝ
  Λ : ℝ
  θ : ℝ
  a : ℝ
  s : ℝ
  ℓ : ℝ

open SlidingLowerOracle

noncomputable def partialB (W : WScale) (x0 : Point d) (π : Fin (k + 1) ↪ Fin d) (e : ℕ) (_b : Bool)
    (q : Fin 2 × Point d) : Point d :=
  if q.1 = 0 then (-W.ℓ) • q.2 else
    (W.a / W.s) • wGp W.r W.δ W.R W.Λ π (min (e + 1) (k + 1)) (rescale W.s x0 q.2) + W.ℓ • q.2

noncomputable def trueB (W : WScale) (x0 : Point d) (π : Fin (k + 1) ↪ Fin d) (_b : Bool)
    (q : Fin 2 × Point d) : Point d :=
  if q.1 = 0 then (-W.ℓ) • q.2 else
    (W.a / W.s) • wG W.r W.δ W.R W.Λ π (rescale W.s x0 q.2) + W.ℓ • q.2

def levB (k : ℕ) (e : ℕ) : ℕ := min e (k + 1)

def rvB (i : Fin 2) (_b : Bool) : ℕ := if i = 1 then 1 else 0

def goodB (W : WScale) (x0 : Point d) (π : Fin (k + 1) ↪ Fin d) (V : ℕ) (x : Point d) : Prop :=
  ‖rescale W.s x0 x‖ ≤ 6 * W.R → Good W.θ π V (rescale W.s x0 x)

structure WValid (W : WScale) (k : ℕ) : Prop where
  r_pos : 1 ≤ W.r
  δ_nonneg : 0 ≤ W.δ
  θ_le : 2 * ((W.r : ℝ) ^ 2 + 7) * W.θ ≤ W.δ
  θ_half : W.θ ≤ 1 / 8
  θ_pos : 0 < W.θ
  R_pos : 0 < W.R
  Λ_ge : 1 ≤ W.Λ
  R_big : 4 + 4 * (k : ℝ) + (k + 1) * ((W.r : ℝ) ^ 2 + 7) ^ 2 ≤ W.R ^ 2

lemma partial_prefixB (W : WScale) (x0 : Point d) :
    ∀ π ρ e b q, (∀ j : Fin (k + 1), j.val < levB k (e + rvB q.1 b) → π j = ρ j) →
      partialB W x0 π e b q = partialB W x0 ρ e b q := by
  intro π ρ e b q h
  unfold partialB
  split_ifs with h0
  · rfl
  · have hq : q.1 = 1 := by rcases (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) q.1 with h | h
                            · exact absurd h h0
                            · exact h
    have h' : ∀ j : Fin (k + 1), j.val < min (e + 1) (k + 1) → π j = ρ j := by
      intro j hj
      apply h j
      simpa [levB, rvB, hq] using hj
    unfold wGp
    rw [pobj_congr _ _ π ρ _ _ h', pfield_congr _ _ π ρ _ _ h']

lemma partial_eqB (W : WScale) (hW : WValid W k) (x0 : Point d) :
    ∀ (π : Fin (k + 1) ↪ Fin d) (e : ℕ) (b : Bool) (q : Fin 2 × Point d),
      goodB W x0 π (levB k e) q.2 → partialB W x0 π e b q = trueB W x0 π b q := by
  intro π e b q hg
  unfold partialB trueB
  split_ifs with h0
  · rfl
  · congr 2
    by_cases hn : ‖rescale W.s x0 q.2‖ ≤ 6 * W.R
    · have hgood := hg hn
      have hpe := partial_eq W.r hW.θ_le (by linarith [hW.θ_half]) π (levB k e)
        (min (e + 1) (k + 1)) (rescale W.s x0 q.2) (by omega)
        (fun i hi hle => by unfold levB; omega) hgood
      unfold wGp wG
      rw [hpe.1, hpe.2]
    · push Not at hn
      have hR := hW.R_pos
      rw [wGp_far W.r hW.δ_nonneg hR hW.Λ_ge hW.R_big π _ _ (by linarith),
        ← wGp_full, wGp_far W.r hW.δ_nonneg hR hW.Λ_ge hW.R_big π _ _ (by linarith)]

lemma levB_mono (k : ℕ) : Monotone (levB k) := fun a b h => by unfold levB; omega

noncomputable def observeB (W : WScale) (x0 : Point d) (H : Run S d) (β : ℕ → Bool)
    (budget : Fin 2 → ℕ) (j : ℕ × Fin 2) (π : Fin (k + 1) ↪ Fin d) : Point d :=
  let st := (simSeq H rvB (partialB W x0) π β budget j.1).state
  rescale W.s x0 (if j.2 = 0 then (H.query st).2 else H.output st)

def isBadB (W : WScale) (x0 : Point d) (H : Run S d) (β : ℕ → Bool)
    (budget : Fin 2 → ℕ) (N : ℕ) (π : Fin (k + 1) ↪ Fin d) : Prop :=
  ∃ j : Fin (N + 1) × Fin 2, 0 < hits (largeSet (6 * W.R) W.θ (observeB W x0 H β budget
    (j.1.val, j.2) π)) ((List.ofFn π).drop
      (levB k (simSeq H rvB (partialB W x0) π β budget j.1.val).exposure))

lemma bad_countB (W : WScale) (hW : WValid W k) (x0 : Point d) (H : Run S d)
    (β : ℕ → Bool) (budget : Fin 2 → ℕ) (N : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hDs : D + (k + 1 : ℕ) ≤ d) :
    D * (((distinctWords (k + 1) (Finset.univ : Finset (Fin d))).filter
      (fun w => ∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w ∧
        isBadB W x0 H β budget N π)).card : ℝ) ≤
      (2 * ((N : ℝ) + 1)) * (k + 1 : ℕ) * ((6 * W.R) ^ 2 / W.θ ^ 2) *
        (distinctWords (k + 1) (Finset.univ : Finset (Fin d))).card := by
  let F : Fin (N + 1) × Fin 2 → (Fin (k + 1) ↪ Fin d) → ℕ × Finset (Fin d) :=
    fun j π => (levB k (simSeq H rvB (partialB W x0) π β budget j.1.val).exposure,
      largeSet (6 * W.R) W.θ (observeB W x0 H β budget (j.1.val, j.2) π))
  have hb : ∀ j π, ((F j π).2.card : ℝ) ≤ (6 * W.R) ^ 2 / W.θ ^ 2 :=
    fun j π => largeSet_bound _ _ (by linarith [hW.R_pos]) hW.θ_pos _
  have hk : ∀ j π, (F j π).1 ≤ k + 1 := fun j π => by simp only [F, levB]; omega
  have hf : ∀ j π ρ, (∀ z : Fin (k + 1), z.val < (F j π).1 → π z = ρ z) → F j π = F j ρ := by
    intro j π ρ h
    have he := simSeq_prefix H rvB (levB k) (levB_mono k) (partialB W x0)
      (partial_prefixB W x0) π ρ β budget j.1.val h
    simp only [F, observeB]
    rw [he]
  have hd : D + (k + 1 : ℕ) ≤ ((Finset.univ : Finset (Fin d)).card : ℝ) := by simpa using hDs
  have bound := prefix_family_bad_count_bound F hb (by positivity) hk hf Finset.univ D hD hd
  have hJ : (Fintype.card (Fin (N + 1) × Fin 2) : ℝ) = 2 * ((N : ℝ) + 1) := by
    simp [Fintype.card_prod]; ring
  rw [hJ] at bound
  have hset : ∀ w : List (Fin d), (∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w ∧
      isBadB W x0 H β budget N π) ↔
      ∃ j : Fin (N + 1) × Fin 2, ∃ π : Fin (k + 1) ↪ Fin d, List.ofFn π = w ∧
        0 < hits (F j π).2 (w.drop (F j π).1) := by
    intro w
    constructor
    · rintro ⟨π, hπ, j, hj⟩
      exact ⟨j, π, hπ, by rw [← hπ]; exact hj⟩
    · rintro ⟨j, π, hπ, hj⟩
      exact ⟨π, hπ, j, by rw [hπ]; exact hj⟩
  refine le_trans ?_ bound
  apply mul_le_mul_of_nonneg_left _ hD
  exact_mod_cast Finset.card_le_card (fun w hw => by
    simp only [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, (hset w).mp hw.2⟩)

lemma good_of_not_badB (W : WScale) (x0 : Point d) (H : Run S d)
    (β : ℕ → Bool) (budget : Fin 2 → ℕ) (N : ℕ) (π : Fin (k + 1) ↪ Fin d)
    (hgood : ¬ isBadB W x0 H β budget N π) (t : ℕ) (ht : t ≤ N) (i : Fin 2)
    (hn : ‖observeB W x0 H β budget (t, i) π‖ ≤ 6 * W.R) :
    Good W.θ π (levB k (simSeq H rvB (partialB W x0) π β budget t).exposure)
      (observeB W x0 H β budget (t, i) π) := by
  intro j hj
  apply not_largeSet_small (6 * W.R) W.θ _ hn
  intro hm
  apply hgood
  exact ⟨(⟨t, by omega⟩, i), hits_drop_positive π _ _ j hj hm⟩

lemma coupledB (W : WScale) (hW : WValid W k) (x0 : Point d) (H : Run S d)
    (β : ℕ → Bool) (budget : Fin 2 → ℕ) (N : ℕ) (π : Fin (k + 1) ↪ Fin d)
    (hgood : ¬ isBadB W x0 H β budget N π) :
    (simSeq H rvB (partialB W x0) π β budget N).state =
      (trueSeq H (fun π b q => trueB W x0 π b q) π β budget N).1 := by
  have h := coupling H rvB (levB k) (partialB W x0) (fun π b q => trueB W x0 π b q)
    (goodB W x0) (partial_eqB W hW x0) π β budget N (fun t ht hn => by
      have := good_of_not_badB W x0 H β budget N π hgood t ht.le 0 (by simpa [observeB] using hn)
      simpa [observeB] using this)
  rw [← h]

lemma output_smallB (W : WScale) (hW : WValid W k) (x0 : Point d) (H : Run S d)
    (β : ℕ → Bool) (budget : Fin 2 → ℕ) (N : ℕ) (π : Fin (k + 1) ↪ Fin d)
    (hgood : ¬ isBadB W x0 H β budget N π)
    (hlev : levB k (simSeq H rvB (partialB W x0) π β budget N).exposure ≤ k) :
    6 * W.R < ‖rescale W.s x0 (H.output (trueSeq H (fun π b q => trueB W x0 π b q) π β budget N).1)‖ ∨
      |rescale W.s x0 (H.output (trueSeq H (fun π b q => trueB W x0 π b q) π β budget N).1)
        (π (Fin.last k))| ≤ W.θ := by
  rw [← coupledB W hW x0 H β budget N π hgood]
  by_cases hn : ‖observeB W x0 H β budget (N, 1) π‖ ≤ 6 * W.R
  · right
    have h := good_of_not_badB W x0 H β budget N π hgood N le_rfl 1 hn (Fin.last k)
      (by simp; omega)
    simpa [observeB] using h
  · left
    push Not at hn
    simpa [observeB] using hn

lemma exposure_leB (H : Run S d) (W : WScale) (x0 : Point d) (π : Fin (k + 1) ↪ Fin d)
    (β : ℕ → Bool) (budget : Fin 2 → ℕ) (N : ℕ) :
    (simSeq H rvB (partialB W x0) π β budget N).exposure ≤ budget 1 := by
  have he := exposure_eq H rvB (partialB W x0) π β budget N
  have hs := active_sum_le H rvB (partialB W x0) π β budget 1 N
  have hr : (∑ t ∈ Finset.range N, ∑ i : Fin 2,
      active H rvB (partialB W x0) π β budget i t * (rvB i (β t) : ℝ)) =
      ∑ t ∈ Finset.range N, active H rvB (partialB W x0) π β budget 1 t := by
    apply Finset.sum_congr rfl
    intro t _
    rw [Fin.sum_univ_two]
    simp [rvB]
  rw [hr] at he
  have : ((simSeq H rvB (partialB W x0) π β budget N).exposure : ℝ) ≤ budget 1 := by linarith
  exact_mod_cast this

end LongTails.Proofs.SlidingWireSim
