import LongTails.Algorithms.BirchCollectionEuclidean
import LongTails.Proofs.BirchNonEuclideanCausality
import LongTails.Proofs.BirchSgdConvergence
import LongTails.Proofs.BirchNonEuclideanConstruction
import LongTails.Proofs.BirchNonEuclideanEnergy

namespace LongTails.Proofs.BirchCollectionEuclideanTrace

open OracleTemplate Finset
open OracleTemplate.Rennala (Point)
open OracleTemplate.BirchSgd (Tree realize_stable branch_mono vertex_succ)
open LongTails.Algorithms.BirchCollectionEuclidean
open LongTails.Setups.BirchNonEuclidean
open LongTails.Proofs.BirchNonEuclideanExecution (interpret queryCount)
open LongTails.Proofs.BirchNonEuclideanCausality (interpret_append queryCount_append)

lemma trace_calls (T : Tree) (γ : ℝ) (n : ℕ) : queryCount (trace T γ n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [trace, queryCount_append, ih]
    rfl

lemma program_calls (T : Tree) (γ : ℝ) (m : ℕ → ℕ) (N K : ℕ) :
    (LongTails.Algorithms.BirchCollectionEuclidean.program T γ m N K).oracleCalls = N :=
  trace_calls T γ N

structure RegistersReady (s : Layout) (n : ℕ) : Prop where
  next : s.next = replyReg n
  point : ∀ j ≤ n, vertexReg j ∈ s.points 0
  direction : ∀ j < n, directionReg j ∈ s.vectors 0

lemma edge_ready (T : Tree) (γ : ℝ) (n : ℕ) (s : Layout)
    (hs : RegistersReady s n) (hT : T.WellFormed) (hγ : 0 ≤ γ) :
    LegalFrom 1 s (edgeCode T γ n) ∧
      RegistersReady ((edgeCode T γ n).foldl Instruction.layout s) (n + 1) := by
  let s₁ := Instruction.layout s (.query 0 (vertexReg (T.point n)))
  let s₂ := Instruction.layout s₁ (.mix 0 [(-1, replyReg n)])
  let s₃ := Instruction.layout s₂ (.move 0 (vertexReg (T.base n)) (directionReg (T.grad n)) γ)
  obtain ⟨hb, hp, hg⟩ := hT n
  have hn₁ : s₁.next = directionReg n := by
    change s.next + 1 = _
    rw [hs.next]
    rfl
  have hn₂ : s₂.next = vertexReg (n + 1) := by
    change s₁.next + 1 = _
    rw [hn₁]
    simp [vertexReg, directionReg, Nat.mul_succ, Nat.add_assoc]
  have hv₁ : s₁.vectors 0 = insert (replyReg n) (s.vectors 0) := by
    simp [s₁, Instruction.layout, hs.next]
  have hv₂ : s₂.vectors 0 = insert (directionReg n) (s₁.vectors 0) := by
    simp [s₂, Instruction.layout, hn₁]
  have hp₃ : s₃.points 0 = insert (vertexReg (n + 1)) (s.points 0) := by
    change Function.update s₂.points 0 (insert s₂.next (s₂.points 0)) 0 = _
    rw [Function.update_self, hn₂]
    rfl
  constructor
  · refine ⟨⟨by omega, hs.point _ hp⟩, ⟨by omega, ?_⟩, ⟨by omega, hs.point _ hb, ?_, hγ⟩, trivial⟩
    · change ∀ t ∈ ([(-1, replyReg n)] : List (ℝ × ℕ)), t.2 ∈ s₁.vectors 0
      simp [hv₁]
    · change directionReg (T.grad n) ∈ s₂.vectors 0
      rw [hv₂, hv₁]
      rcases hg.lt_or_eq with h | h
      · exact mem_insert_of_mem (mem_insert_of_mem (hs.direction _ h))
      · simp [h]
  · change RegistersReady s₃ (n + 1)
    refine ⟨?_, ?_, ?_⟩
    · change s₂.next + 1 = _
      rw [hn₂]
      rfl
    · intro j hj
      rw [hp₃]
      rcases (Nat.lt_or_eq_of_le hj) with h | h
      · exact mem_insert_of_mem (hs.point _ (by omega))
      · simp [h]
    · intro j hj
      change directionReg j ∈ s₂.vectors 0
      rw [hv₂, hv₁]
      rcases (Nat.lt_succ_iff.mp hj).lt_or_eq with h | h
      · exact mem_insert_of_mem (mem_insert_of_mem (hs.direction _ h))
      · simp [h]

lemma trace_ready (T : Tree) (γ : ℝ) (N : ℕ) (hT : T.WellFormed) (hγ : 0 ≤ γ) :
    LegalFrom 1 {} (trace T γ N) ∧ RegistersReady (finalLayout (trace T γ N)) N := by
  induction N with
  | zero =>
    refine ⟨trivial, rfl, ?_, fun j h => (Nat.not_lt_zero j h).elim⟩
    intro j hj
    have : j = 0 := Nat.le_zero.mp hj
    subst j
    simp [vertexReg, finalLayout, trace]
  | succ n ih =>
    obtain ⟨hl, hr⟩ := edge_ready T γ n _ ih.2 hT hγ
    refine ⟨(LongTails.Proofs.BirchNonEuclideanConstruction.legalFrom_append 1 {} _ _).2 ⟨ih.1, hl⟩, ?_⟩
    simpa only [trace, finalLayout, List.foldl_append] using hr

lemma program_legal (T : Tree) (γ : ℝ) (m : ℕ → ℕ) (N K : ℕ)
    (hT : T.WellFormed) (hγ : 0 ≤ γ) (hm : ∀ j ≤ K, m j ≤ N) :
    (LongTails.Algorithms.BirchCollectionEuclidean.program T γ m N K).Legal 1 := by
  obtain ⟨hl, hr⟩ := trace_ready T γ N hT hγ
  exact ⟨hl, Nat.zero_lt_one, fun j => hr.point _ (hm _ (Nat.lt_succ_iff.mp j.isLt))⟩

structure Replay {Ω : Type} (p : Params) (T : Tree) (γ : ℝ)
    (g : Point p.d → Ω → Point p.d) (ξ : ℕ → Ω) (m : Memory p.d) (n : ℕ) : Prop where
  next : m.next = replyReg n
  count : m.replies = n
  point : ∀ j ≤ n, m.points (vertexReg j) = T.vertex γ p.x0 g ξ j
  raw : ∀ j < n, m.vectors (replyReg j) = T.reply γ p.x0 g ξ j
  direction : ∀ j < n, m.vectors (directionReg j) = -T.reply γ p.x0 g ξ j

lemma edge_replay {Ω : Type} (p : Params) (T : Tree) (γ : ℝ) (g : Point p.d → Ω → Point p.d)
    (ξ : ℕ → Ω) (m : Memory p.d) (n : ℕ) (hT : T.WellFormed)
    (h : Replay p T γ g ξ m n) :
    Replay p T γ g ξ (interpret p (fun _ => 0) (fun j x => g x (ξ j)) (edgeCode T γ n) m) (n + 1) := by
  obtain ⟨hb, hp, hg⟩ := hT n
  let m₁ := perform p (fun _ => 0) m (.query 0 (vertexReg (T.point n)))
    (g (m.points (vertexReg (T.point n))) (ξ m.replies))
  let m₂ := perform p (fun _ => 0) m₁ (.mix 0 [(-1, replyReg n)]) 0
  let m₃ := perform p (fun _ => 0) m₂
    (.move 0 (vertexReg (T.base n)) (directionReg (T.grad n)) γ) 0
  have hn₁ : m₁.next = directionReg n := by
    change m.next + 1 = _
    rw [h.next]
    rfl
  have hn₂ : m₂.next = vertexReg (n + 1) := by
    change m₁.next + 1 = _
    rw [hn₁]
    simp [vertexReg, directionReg, Nat.mul_succ, Nat.add_assoc]
  have hquery : g (m.points (vertexReg (T.point n))) (ξ m.replies) = T.reply γ p.x0 g ξ n := by
    rw [h.point _ hp, h.count]
    rfl
  have hv₁ : m₁.vectors = Function.update m.vectors (replyReg n) (T.reply γ p.x0 g ξ n) := by
    change Function.update m.vectors m.next _ = _
    rw [h.next, hquery]
  have hv₂ : m₂.vectors = Function.update m₁.vectors (directionReg n) (-T.reply γ p.x0 g ξ n) := by
    simp [m₂, perform, storeVector, hn₁, hv₁]
  have hd : m₂.vectors (directionReg (T.grad n)) = -T.reply γ p.x0 g ξ (T.grad n) := by
    rcases hg.lt_or_eq with hg | hg
    · have h₁ : directionReg (T.grad n) ≠ directionReg n := by
        unfold directionReg
        omega
      have h₂ : directionReg (T.grad n) ≠ replyReg n := by
        unfold directionReg replyReg
        omega
      rw [hv₂, Function.update_of_ne h₁, hv₁, Function.update_of_ne h₂, h.direction _ hg]
    · rw [hg, hv₂, Function.update_self]
  have hp₃ : m₃.points = Function.update m.points (vertexReg (n + 1))
      (T.vertex γ p.x0 g ξ (T.base n) - γ • T.reply γ p.x0 g ξ (T.grad n)) := by
    change Function.update m.points m₂.next (m.points (vertexReg (T.base n)) +
      γ • m₂.vectors (directionReg (T.grad n))) = _
    rw [hn₂, h.point _ hb, hd, smul_neg, ← sub_eq_add_neg]
  change Replay p T γ g ξ m₃ (n + 1)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change m₂.next + 1 = _
    rw [hn₂]
    rfl
  · exact congrArg (· + 1) h.count
  · intro j hj
    rcases (Nat.lt_succ_iff.mp (Nat.lt_succ_of_le hj)).lt_or_eq with hj | hj
    · have hne : vertexReg j ≠ vertexReg (n + 1) := by unfold vertexReg; omega
      rw [hp₃, Function.update_of_ne hne, h.point _ (by omega)]
    · rw [hj, hp₃, Function.update_self, vertex_succ T hT]
  · intro j hj
    have hne : replyReg j ≠ directionReg n := by unfold replyReg directionReg; omega
    change m₂.vectors (replyReg j) = _
    rw [hv₂, Function.update_of_ne hne, hv₁]
    rcases (Nat.lt_succ_iff.mp hj).lt_or_eq with hj | hj
    · have hj' : replyReg j ≠ replyReg n := by unfold replyReg; omega
      rw [Function.update_of_ne hj', h.raw _ hj]
    · rw [hj, Function.update_self]
  · intro j hj
    change m₂.vectors (directionReg j) = _
    rw [hv₂]
    rcases (Nat.lt_succ_iff.mp hj).lt_or_eq with hj | hj
    · have h₁ : directionReg j ≠ directionReg n := by unfold directionReg; omega
      have h₂ : directionReg j ≠ replyReg n := by unfold directionReg replyReg; omega
      rw [Function.update_of_ne h₁, hv₁, Function.update_of_ne h₂, h.direction _ hj]
    · rw [hj, Function.update_self]

lemma trace_replay {Ω : Type} (p : Params) (T : Tree) (γ : ℝ) (g : Point p.d → Ω → Point p.d)
    (ξ : ℕ → Ω) (N : ℕ) (hT : T.WellFormed) :
    Replay p T γ g ξ (interpret p (fun _ => 0) (fun j x => g x (ξ j))
      (trace T γ N) (initialMemory p)) N := by
  induction N with
  | zero =>
    refine ⟨rfl, rfl, ?_, fun j h => (Nat.not_lt_zero j h).elim,
      fun j h => (Nat.not_lt_zero j h).elim⟩
    intro j hj
    have : j = 0 := Nat.le_zero.mp hj
    subst j
    rfl
  | succ n ih =>
    rw [trace, interpret_append]
    exact edge_replay p T γ g ξ _ n hT ih

lemma euclidean_sharp_neg {d : ℕ} (lmo : Point d → Point d)
    (hlmo : LongTails.Setups.UscgConstant.IsBallLMO (normSeminorm ℝ (Point d)) 1 lmo)
    (v : Point d) :
    LongTails.Setups.UscgConstant.dualNorm (normSeminorm ℝ (Point d)) v • lmo v = -v := by
  have hR (x : Point d) (hx : normSeminorm ℝ (Point d) x ≤ 1) : ‖x‖ ≤ 1 := hx
  have hd : LongTails.Setups.UscgConstant.dualNorm (normSeminorm ℝ (Point d)) v = ‖v‖ := by
    open LongTails.Setups.UscgConstant OracleTemplate.NormBallLMO in
    apply le_antisymm
    · simpa using dualNorm_le_norm hR v
    · by_cases hv : v = 0
      · subst v
        simpa using dualNorm_nonneg hR (0 : Point d)
      · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
        let u : Point d := ‖v‖⁻¹ • v
        have hu : normSeminorm ℝ (Point d) u ≤ 1 := by
          change ‖u‖ ≤ 1
          simp [u, norm_smul, inv_mul_cancel₀ hn.ne']
        have he : inner ℝ v u = ‖v‖ := by
          rw [show u = ‖v‖⁻¹ • v from rfl, inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp
        simpa only [he] using inner_le_dualNorm hR v hu
  have hn := LongTails.Proofs.BirchNonEuclideanEnergy.sharp_direction_bound hR hlmo v
  have hi := LongTails.Proofs.BirchNonEuclideanEnergy.sharp_inner hR hlmo v
  rw [hd] at hn hi ⊢
  change ‖‖v‖ • lmo v‖ ≤ ‖v‖ at hn
  have hs : ‖v + ‖v‖ • lmo v‖ ^ 2 = 0 := by
    apply le_antisymm _ (sq_nonneg _)
    rw [norm_add_sq_real, hi]
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (add_nonneg (norm_nonneg v)
      (norm_nonneg (‖v‖ • lmo v)))]
  have hz : v + ‖v‖ • lmo v = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (v + ‖v‖ • lmo v)])
  exact (eq_neg_iff_add_eq_zero).2 (by simpa only [add_comm] using hz)

end LongTails.Proofs.BirchCollectionEuclideanTrace
