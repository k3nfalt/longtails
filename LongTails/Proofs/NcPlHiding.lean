import LongTails.Proofs.NcPlOracleStats
import LongTails.Proofs.AbcHardExecution
import LongTails.Proofs.SmoothConvexFiniteHiding
import LongTails.Proofs.FiniteSumNondualLowerBound

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcPlHiding

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Proofs.NcPlFlat LongTails.Proofs.NcPlInstance LongTails.Proofs.NcPlOracle
open LongTails.Proofs.NcPlMoreau
open LongTails.Proofs.AbcHardFunction (Space)
open LongTails.Proofs.MintyChainGeometry (ball)
open LongTails.Proofs.AbcHardExecution (coinCount coinCount_mono)
open LongTails.Proofs.SmoothConvexFiniteHiding LongTails.Proofs.FiniteSumNondualLowerHiding
open LongTails.Proofs.FiniteSumNondualLowerExposure LongTails.Proofs.FiniteSumNondualLowerAveraging

variable (G : Geo)

def nm : ℕ := G.n / 2 + 1

def hpos (c : ℕ) : ℕ := c / nm G * (G.n + 2) + c % nm G

lemma nm_pos : 0 < nm G := Nat.succ_pos _

lemma nm_le : nm G ≤ G.n + 1 := by
  unfold nm
  omega

lemma hpos_lt {c c' : ℕ} (h : c < c') : hpos G c < hpos G c' := by
  have hc := Nat.div_add_mod c (nm G)
  have hc' := Nat.div_add_mod c' (nm G)
  have hb := Nat.mod_lt c (nm_pos G)
  have hb' := Nat.mod_lt c' (nm_pos G)
  have hn := nm_le G
  have hdiv : c / nm G ≤ c' / nm G := Nat.div_le_div_right h.le
  unfold hpos
  rcases Nat.lt_or_ge (c / nm G) (c' / nm G) with hlt | hge
  · have h1 : (c / nm G + 1) * (G.n + 2) ≤ c' / nm G * (G.n + 2) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_one_mul] at h1
    omega
  · have heq : c / nm G = c' / nm G := le_antisymm hdiv hge
    rw [← heq] at hc' ⊢
    omega

lemma hpos_mono {c c' : ℕ} (h : c ≤ c') : hpos G c ≤ hpos G c' := by
  rcases Nat.lt_or_ge c c' with hlt | hge
  · exact (hpos_lt G hlt).le
  · have : c = c' := le_antisymm h hge
    rw [this]

lemma hpos_masked (c : ℕ) : masked G (hpos G c) := by
  have hb := Nat.mod_lt c (nm_pos G)
  have hn := nm_le G
  unfold masked hpos
  rw [pos_mod G.n (c / nm G) (by omega)]
  have hnm : nm G = G.n / 2 + 1 := rfl
  constructor <;> omega

noncomputable def lvl (q : ℝ) (ω : ℕ → ℝ) (t : ℕ) : ℕ :=
  min (G.k + 1) (hpos G (coinCount q ω t))

lemma lvl_le (q : ℝ) (ω : ℕ → ℝ) (t : ℕ) : lvl G q ω t ≤ G.k + 1 := min_le_left _ _

lemma lvl_mono (q : ℝ) (ω : ℕ → ℝ) {s t : ℕ} (h : s ≤ t) : lvl G q ω s ≤ lvl G q ω t :=
  min_le_min le_rfl (hpos_mono G (coinCount_mono q ω h))

lemma lvl_coin (q : ℝ) (ω : ℕ → ℝ) (t : ℕ) (h : lvl G q ω (t + 1) = lvl G q ω t) :
    G.k + 1 ≤ lvl G q ω t ∨ (masked G (lvl G q ω t) ∧ q < ω t) := by
  by_cases hK : G.k + 1 ≤ lvl G q ω t
  · exact Or.inl hK
  · right
    have hl : lvl G q ω t = hpos G (coinCount q ω t) := by
      unfold lvl at hK ⊢
      omega
    refine ⟨by rw [hl]; exact hpos_masked G _, ?_⟩
    by_contra hc
    have hle : ω t ≤ q := not_lt.mp hc
    have hcount : coinCount q ω (t + 1) = coinCount q ω t + 1 := by
      simp [coinCount, hle]
    have hlt := hpos_lt G (show coinCount q ω t < coinCount q ω t + 1 by omega)
    unfold lvl at h hK
    rw [hcount] at h
    omega

lemma lvl_of_count (q : ℝ) (ω : ℕ → ℝ) (t : ℕ)
    (h : coinCount q ω t < (G.m + 1) * nm G) : lvl G q ω t < G.k + 1 := by
  have hc := Nat.div_add_mod (coinCount q ω t) (nm G)
  have hb := Nat.mod_lt (coinCount q ω t) (nm_pos G)
  have hn := nm_le G
  have hdiv : coinCount q ω t / nm G < G.m + 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
  have h1 : (coinCount q ω t / nm G + 1) * (G.n + 2) ≤ (G.m + 1) * (G.n + 2) :=
    Nat.mul_le_mul_right _ hdiv
  rw [Nat.add_one_mul] at h1
  have hk := G.hk
  unfold lvl hpos
  omega

section Sim

variable {G} {d : ℕ} {St : Type*}

noncomputable def simState (θ q : ℝ) (π : Fin (G.k + 1) ↪ Fin d)
    (query : St → Space d × Space d) (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := simState θ q π query update initial ω t
    update s (simX G π θ q (lvl G q ω (t + 1)) (query s).1 (query s).2 (ω t),
      simY G π θ q (lvl G q ω (t + 1)) (query s).1 (query s).2 (ω t))

noncomputable def trueState (θ q : ℝ) (π : Fin (G.k + 1) ↪ Fin d)
    (query : St → Space d × Space d) (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := trueState θ q π query update initial ω t
    update s (replyX G π θ q (query s).1 (query s).2 (ω t),
      replyY G π θ q (query s).1 (query s).2 (ω t))

lemma simState_prefix (θ q : ℝ) (π ρ' : Fin (G.k + 1) ↪ Fin d)
    (query : St → Space d × Space d) (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (t : ℕ) (h : ∀ p : Fin (G.k + 1), p.val < lvl G q ω t → π p = ρ' p) :
    simState θ q π query update initial ω t = simState θ q ρ' query update initial ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm := lvl_mono G q ω (Nat.le_add_right t 1)
    have he := ih (fun p hp => h p (by omega))
    simp only [simState]
    rw [he, (sim_prefix G π ρ' θ q _ _ _ _ h).1, (sim_prefix G π ρ' θ q _ _ _ _ h).2]

lemma coupling {θ q : ℝ} (hθ0 : 0 ≤ θ) (hθρ : θ ≤ G.ρ) (hθ2 : θ ≤ 1 / 2)
    (π : Fin (G.k + 1) ↪ Fin d) (query : St → Space d × Space d)
    (update : St → Space d × Space d → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (hhit : ∀ t < N, ∀ p : Fin (G.k + 1), lvl G q ω t ≤ p.val →
      ¬ big G θ (query (simState θ q π query update initial ω t)).1
        (query (simState θ q π query update initial ω t)).2 (π p)) :
    simState θ q π query update initial ω N = trueState θ q π query update initial ω N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hmono := lvl_mono G q ω (Nat.le_add_right N 1)
    have he := ih (fun t ht => hhit t (by omega))
    simp only [simState, trueState]
    rw [← he]
    have hr := reply_eq_sim G π hθ0 hθρ hθ2
      (query (simState θ q π query update initial ω N)).1
      (query (simState θ q π query update initial ω N)).2 (lvl G q ω N) (lvl G q ω (N + 1))
      hmono (ω N) (hhit N (by omega)) (fun hlev => lvl_coin G q ω N hlev)
    rw [hr.1, hr.2]

noncomputable def observation (θ q : ℝ) (query : St → Space d × Space d)
    (output : St → Space d) (update : St → Space d × Space d → St) (initial : St) (ω : ℕ → ℝ)
    (N : ℕ) (j : Fin (N + 1)) (π : Fin (G.k + 1) ↪ Fin d) : Space d :=
  if j.val < N then
    obsVec G (query (simState θ q π query update initial ω j.val)).1
      (query (simState θ q π query update initial ω j.val)).2
  else obsVec G (output (simState θ q π query update initial ω j.val)) 0

lemma observation_prefix (θ q : ℝ) (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (j : Fin (N + 1)) (π ρ' : Fin (G.k + 1) ↪ Fin d)
    (h : ∀ p : Fin (G.k + 1), p.val < lvl G q ω j.val → π p = ρ' p) :
    observation θ q query output update initial ω N j π =
      observation θ q query output update initial ω N j ρ' := by
  unfold observation
  rw [simState_prefix θ q π ρ' query update initial ω j.val h]

def coordinateBad (θ q : ℝ) (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (π : Fin (G.k + 1) ↪ Fin d) : Prop :=
  ∃ j : Fin (N + 1), 0 < hits
    (largeSet (2 * G.Bx + 2 * G.By) θ (observation θ q query output update initial ω N j π))
    ((List.ofFn π).drop (lvl G q ω j.val))

lemma observation_norm (θ q : ℝ) (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (j : Fin (N + 1)) (π : Fin (G.k + 1) ↪ Fin d) :
    ‖observation θ q query output update initial ω N j π‖ ≤ 2 * G.Bx + 2 * G.By := by
  unfold observation
  split_ifs
  · exact obsVec_norm G _ _
  · exact obsVec_norm G _ _

lemma good_small (θ q : ℝ) (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (π : Fin (G.k + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad θ q query output update initial ω N π)
    (j : Fin (N + 1)) (p : Fin (G.k + 1)) (hp : lvl G q ω j.val ≤ p.val) :
    |observation θ q query output update initial ω N j π (π p)| ≤ θ := by
  apply not_largeSet_small _ _ _ (observation_norm θ q query output update initial ω N j π)
  intro h
  exact hgood ⟨j, hits_drop_positive π _ _ p hp h⟩

lemma bad_sum_bound {θ : ℝ} (hθ : 0 < θ) (q : ℝ) (query : St → Space d × Space d)
    (output : St → Space d) (update : St → Space d × Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (D : ℝ) (hD : 0 ≤ D) (hDs : D + (G.k + 1 : ℕ) ≤ d) :
    D * (∑ w : CoordinateWords d G.k, if coordinateBad θ q query output update initial ω N
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (N + 1 : ℕ) * (G.k + 1 : ℕ) * ((2 * G.Bx + 2 * G.By) ^ 2 / θ ^ 2) *
        Fintype.card (CoordinateWords d G.k) := by
  have hB : 0 ≤ 2 * G.Bx + 2 * G.By := by
    have := G.hBx
    have := G.hBy
    positivity
  let bad := fun π : Fin (G.k + 1) ↪ Fin d =>
    coordinateBad θ q query output update initial ω N π
  have he (w : CoordinateWords d G.k) : bad (coordinateEmbedding w) ↔
      ∃ j : Fin (N + 1), ∃ π : Fin (G.k + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet (2 * G.Bx + 2 * G.By) θ
          (observation θ q query output update initial ω N j π))
          (w.val.drop (lvl G q ω j.val)) := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, coordinateEmbedding w, coordinateEmbedding_labels w,
        by simpa only [coordinateEmbedding_labels] using hj⟩
    · rintro ⟨j, π, hπ, hj⟩
      have hp : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro i
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) i
      exact ⟨j, by simpa only [hp, ← coordinateEmbedding_labels w] using hj⟩
  let P := fun w : List (Fin d) => ∃ j : Fin (N + 1), ∃ π : Fin (G.k + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet (2 * G.Bx + 2 * G.By) θ
      (observation θ q query output update initial ω N j π))
      (w.drop (lvl G q ω j.val))
  have hs : (∑ w : CoordinateWords d G.k, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (G.k + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d G.k, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := G.k + 1) (2 * G.Bx + 2 * G.By) θ D
    hB hθ hD hDs
    (fun j : Fin (N + 1) => lvl G q ω j.val) (fun j => lvl_le G q ω j.val)
    (observation θ q query output update initial ω N)
    (observation_prefix θ q query output update initial ω N)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe] at h ⊢
  convert h using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter, P]

theorem good_output {θ q : ℝ} (hθ0 : 0 ≤ θ) (hθρ : θ ≤ G.ρ) (hθ2 : θ ≤ 1 / 4)
    (query : St → Space d × Space d) (output : St → Space d)
    (update : St → Space d × Space d → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (π : Fin (G.k + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad θ q query output update initial ω N π)
    (hlev : lvl G q ω N < G.k + 1) :
    |ball (2 * G.Bx) (output (trueState θ q π query update initial ω N))
      (π ⟨G.m * (G.n + 2) + (G.n + 1), upos_lt G le_rfl⟩)| ≤ 1 / 4 := by
  have hhit : ∀ t < N, ∀ p : Fin (G.k + 1), lvl G q ω t ≤ p.val →
      ¬ big G θ (query (simState θ q π query update initial ω t)).1
        (query (simState θ q π query update initial ω t)).2 (π p) := by
    intro t ht p hp
    have h := good_small θ q query output update initial ω N π hgood ⟨t, by omega⟩ p hp
    simp only [observation, ht, ↓reduceIte] at h
    unfold big
    exact not_lt.mpr h
  rw [← coupling hθ0 hθρ (by linarith) π query update initial ω N hhit]
  have hk := G.hk
  have hlast : lvl G q ω N ≤ G.m * (G.n + 2) + (G.n + 1) := by
    have e := Nat.add_one_mul G.m (G.n + 2)
    omega
  have h := good_small θ q query output update initial ω N π hgood (Fin.last N)
    ⟨G.m * (G.n + 2) + (G.n + 1), upos_lt G le_rfl⟩ (by simp only [Fin.val_last]; exact hlast)
  simp only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
  have hnb : ¬ big G θ (output (simState θ q π query update initial ω N)) 0
      (π ⟨G.m * (G.n + 2) + (G.n + 1), upos_lt G le_rfl⟩) := by
    unfold big
    exact not_lt.mpr h
  exact ((small_of_not_big G hnb).1).trans hθ2

end Sim

end LongTails.Proofs.NcPlHiding
