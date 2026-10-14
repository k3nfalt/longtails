import LongTails.Proofs.ConstrainedAnchoredRate
import LongTails.Setups.ConstrainedGeneralizedMonotone

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ConstrainedMonotone

open LongTails.Setups.ConstrainedGeneralizedMonotone

def counts {Q Rp O : Type*} {n : ℕ} (A : Algorithm Q Rp O n) (ans : Fin n × Q → Rp) :
    ℕ → A.State → Fin n → ℕ
  | 0, _ => fun _ => 0
  | K + 1, s => fun i => counts A ans K (A.update s (ans (A.query s))) i +
      if (A.query s).1 = i then 1 else 0

lemma counts_sum {Q Rp O : Type*} {n : ℕ} (A : Algorithm Q Rp O n)
    (ans : Fin n × Q → Rp) (K : ℕ) (s : A.State) :
    ∑ i, counts A ans K s i = K := by
  induction K generalizing s with
  | zero => simp [counts]
  | succ K ih =>
    simp only [counts, Finset.sum_add_distrib, ih]
    simp

lemma execute_det {Q Rp O : Type*} {n : ℕ} (oracle : Oracle Q Rp n) (A : Algorithm Q Rp O n)
    (ans : Fin n × Q → Rp) (h : ∀ k query seed, oracle.answer k query seed = ans query)
    (K : ℕ) (seed : A.Seed) (ξ : (k : ℕ) → oracle.Seed k) :
    execute oracle A (counts A ans K (A.initial seed)) seed ξ =
      A.output ((fun s => A.update s (ans (A.query s)))^[K] (A.initial seed)) := by
  unfold execute
  rw [counts_sum]
  generalize A.initial seed = state
  generalize (0 : ℕ) = call
  induction K generalizing state call with
  | zero => rfl
  | succ K ih =>
      have hc : counts A ans (K + 1) state (A.query state).1 =
          counts A ans K (A.update state (ans (A.query state))) (A.query state).1 + 1 := by
        simp [counts]
      change (if counts A ans (K + 1) state (A.query state).1 = 0 then _ else _) = _
      rw [hc]
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      rw [h]
      have hr : Function.update (counts A ans (K + 1) state) (A.query state).1
          (counts A ans K (A.update state (ans (A.query state))) (A.query state).1 + 1 - 1) =
          counts A ans K (A.update state (ans (A.query state))) := by
        funext i
        by_cases hi : i = (A.query state).1
        · subst i; simp
        · simp [Function.update_of_ne hi, counts, Ne.symm hi]
      rw [hr, Function.iterate_succ_apply]
      exact ih _ _

lemma counts_add {Q Rp O : Type*} {n : ℕ} (A : Algorithm Q Rp O n) (ans : Fin n × Q → Rp)
    (K1 K2 : ℕ) (s : A.State) (i : Fin n) :
    counts A ans (K1 + K2) s i = counts A ans K1 s i +
      counts A ans K2 ((fun s => A.update s (ans (A.query s)))^[K1] s) i := by
  induction K1 generalizing s with
  | zero => simp [counts]
  | succ k ih =>
      rw [show k + 1 + K2 = (k + K2) + 1 by omega]
      simp only [counts, Function.iterate_succ_apply]
      rw [ih]
      ring

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def answers (F P : E → E) : Fin 2 × E → E :=
  fun q => if q.1 = 0 then F q.2 else P q.2

lemma block (F P : E → E) (L0 L1 : ℝ) (a : E) (s : AnchoredState E) (h0 : s.stage = 0) :
    let T := fun s => (constrainedAnchored L0 L1 a).update s
      (answers F P ((constrainedAnchored L0 L1 a).query s))
    (T^[3] s).stage = 0 ∧
      ((T^[3] s).x, (T^[3] s).ξ, (T^[3] s).S) = iter F P L0 L1 a (s.x, s.ξ, s.S) ∧
      counts (constrainedAnchored L0 L1 a) (answers F P) 3 s =
        fun i => if i = 0 then 2 else 1 := by
  intro T
  obtain ⟨st, x, ξ, g, w, S⟩ := s
  dsimp only at h0
  subst h0
  refine ⟨rfl, ?_, ?_⟩
  · simp [T, Function.iterate_succ_apply, constrainedAnchored, answers, iter]
  · funext i
    fin_cases i <;> simp [counts, constrainedAnchored, answers]

lemma blocks (F P : E → E) (L0 L1 : ℝ) (a : E) (M : ℕ) :
    let T := fun s => (constrainedAnchored L0 L1 a).update s
      (answers F P ((constrainedAnchored L0 L1 a).query s))
    (T^[3 * M] ((constrainedAnchored L0 L1 a).initial ())).stage = 0 ∧
      ((T^[3 * M] ((constrainedAnchored L0 L1 a).initial ())).x,
        (T^[3 * M] ((constrainedAnchored L0 L1 a).initial ())).ξ,
        (T^[3 * M] ((constrainedAnchored L0 L1 a).initial ())).S) = run F P L0 L1 a M ∧
      counts (constrainedAnchored L0 L1 a) (answers F P) (3 * M)
          ((constrainedAnchored L0 L1 a).initial ()) =
        fun i => if i = 0 then 2 * M else M := by
  intro T
  induction M with
  | zero =>
    refine ⟨rfl, rfl, ?_⟩
    funext i
    simp [counts]
  | succ M ih =>
    obtain ⟨h0, hrun, hcnt⟩ := ih
    obtain ⟨b0, brun, bcnt⟩ := block F P L0 L1 a _ h0
    have hst : T^[3 * (M + 1)] ((constrainedAnchored L0 L1 a).initial ()) =
        T^[3] (T^[3 * M] ((constrainedAnchored L0 L1 a).initial ())) := by
      rw [show 3 * (M + 1) = 3 + 3 * M by ring, Function.iterate_add_apply]
    rw [hst]
    refine ⟨b0, ?_, ?_⟩
    · rw [brun, hrun]
      rfl
    · funext i
      rw [show 3 * (M + 1) = 3 * M + 3 by ring, counts_add, hcnt]
      have := congrFun bcnt i
      rw [this]
      by_cases hi : i = 0 <;> simp [hi]; ring

theorem convergence_main : Convergence spec (fun q i => if i = 0 then 2 * (⌈16 * (q.L0 + q.L1 * q.G) * (1 + 8 * q.L1 * q.R) * q.R / q.ε + (132 * q.L1 * q.R * (1 + q.L1 * q.R) + 4) * Real.log (2 + 8 * q.R * (q.L0 + 2 * q.L1 * q.G0) / q.ε)⌉₊ + 1) else ⌈16 * (q.L0 + q.L1 * q.G) * (1 + 8 * q.L1 * q.R) * q.R / q.ε + (132 * q.L1 * q.R * (1 + q.L1 * q.R) + 4) * Real.log (2 + 8 * q.R * (q.L0 + 2 * q.L1 * q.G0) / q.ε)⌉₊ + 1) := by
  refine ⟨fun p => constrainedAnchored p.L0 p.L1 p.x0, ?_, fun _ _ => trivial⟩
  intro q hq I oracle hadm
  obtain ⟨hL0, hL1, hR, hG, hG0, hε⟩ := hq
  obtain ⟨hF, ⟨P, hPans, hPprop⟩, hconv, hcont, hmono, hlip, hx0, hFx0, xs, hxsX, hvi, hdist,
    hgrad⟩ := hadm
  set B := 16 * (q.L0 + q.L1 * q.G) * (1 + 8 * q.L1 * q.R) * q.R / q.ε +
    (132 * q.L1 * q.R * (1 + q.L1 * q.R) + 4) *
      Real.log (2 + 8 * q.R * (q.L0 + 2 * q.L1 * q.G0) / q.ε) with hB
  set M := ⌈B⌉₊ + 1 with hM
  have hNM : ⌈B⌉₊ + 1 ≤ M := le_refl _
  have hans : ∀ k query seed, oracle.answer k query seed = answers I.F P query := by
    rintro k ⟨i, x⟩ seed
    fin_cases i
    · simp [answers, hF]
    · simp [answers, hPans]
  have c : Ctx I.F P I.X q.L0 q.L1 q.x0 xs q.R q.G :=
    ⟨⟨hL0, hL1, hcont, hmono, hlip⟩, ⟨fun z => (hPprop z).1, fun z => (hPprop z).2⟩, hconv,
      hx0, hxsX, hvi, hdist, hgrad, hR⟩
  obtain ⟨-, hrun, hcnt⟩ := blocks I.F P q.L0 q.L1 q.x0 M
  obtain ⟨n, hn⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  have hnB : B ≤ n := by
    have : ⌈B⌉₊ ≤ n := by omega
    exact (Nat.le_ceil B).trans (by exact_mod_cast this)
  have hnB' : 16 * ((q.L0 + q.L1 * q.G) * (1 + 8 * q.L1 * q.R)) * q.R / q.ε +
      (132 * q.L1 * q.R * (1 + q.L1 * q.R) + 4) *
        Real.log (2 + 8 * q.R * (q.L0 + 2 * q.L1 * q.G0) / q.ε) ≤ n := by
    have e : 16 * ((q.L0 + q.L1 * q.G) * (1 + 8 * q.L1 * q.R)) * q.R / q.ε =
        16 * (q.L0 + q.L1 * q.G) * (1 + 8 * q.L1 * q.R) * q.R / q.ε := by ring
    rw [e]
    exact hnB
  have hacc := run_accuracy c hFx0 hε n hnB'
  have hx : (run I.F P q.L0 q.L1 q.x0 M).1 = (run I.F P q.L0 q.L1 q.x0 (n + 1)).1 := by rw [hn]
  have hexec : ∀ seed : (constrainedAnchored q.L0 q.L1 q.x0).Seed × ((k : ℕ) → oracle.Seed k),
      execute oracle (constrainedAnchored q.L0 q.L1 q.x0)
          (fun i => if i = 0 then 2 * M else M) seed.1 seed.2 =
        (run I.F P q.L0 q.L1 q.x0 M).1 := by
    rintro ⟨⟨⟩, ξ⟩
    erw [← hcnt, execute_det oracle _ (answers I.F P) hans]
    exact congrArg Prod.fst hrun
  apply Filter.Eventually.of_forall
  intro seed
  change (execute oracle (constrainedAnchored q.L0 q.L1 q.x0)
      (fun i => if i = 0 then 2 * M else M) seed.1 seed.2) ∈ I.X ∧
    ∃ ξ : q.E, (∀ w ∈ I.X, ⟪ξ, w - execute oracle (constrainedAnchored q.L0 q.L1 q.x0)
      (fun i => if i = 0 then 2 * M else M) seed.1 seed.2⟫ ≤ 0) ∧
      ‖I.F (execute oracle (constrainedAnchored q.L0 q.L1 q.x0)
        (fun i => if i = 0 then 2 * M else M) seed.1 seed.2) + ξ‖ ≤ q.ε
  rw [hexec, hx]
  obtain ⟨hm, hnorm, hres⟩ := hacc
  exact ⟨hm, _, hnorm, hres⟩

end OracleTemplate.ConstrainedMonotone
