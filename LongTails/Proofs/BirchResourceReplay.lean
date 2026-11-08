import LongTails.Proofs.BirchResourceForest
import LongTails.Proofs.BirchNonEuclideanCausality

namespace LongTails.Proofs.BirchResourceReplay

open MeasureTheory OracleTemplate
open OracleTemplate.Rennala (Point)
open OracleTemplate.BirchSgd (Tree vertex_succ branch_vertex_succ gradientOracle)
open LongTails.Proofs.BirchResourceForest
open LongTails.Setups.BirchNonEuclidean
open LongTails.Proofs.BirchNonEuclideanExecution (interpret queryCount execute_interpret)
open LongTails.Proofs.BirchNonEuclideanCausality (interpret_append queryCount_append)

def reg (j : ℕ) : ℕ := 2 * j + j % 2

def pairCode (s : Forest) (γ : ℝ) (k : ℕ) : List Instruction :=
  [.query 0 (reg (s.saved k)), .mix 0 [(-1, 4 * k + 1)],
    .move 0 (reg (s.head k)) (4 * k + 2) γ, .move 0 (4 * k) (4 * k + 2) γ]

def prefixCode (s : Forest) (γ : ℝ) : ℕ → List Instruction
  | 0 => []
  | k + 1 => prefixCode s γ k ++ pairCode s γ k

def program (s : Forest) (γ : ℝ) (K : ℕ) : Program :=
  ⟨prefixCode s γ K, 0, K - 1, fun i => 4 * i.val⟩

lemma prefix_calls (s : Forest) (γ : ℝ) (K : ℕ) : (program s γ K).oracleCalls = K := by
  change queryCount (prefixCode s γ K) = K
  induction K with
  | zero => rfl
  | succ k ih => rw [prefixCode, queryCount_append, ih]; rfl

lemma private_value {d : ℕ} {Ω : Type} (s : Forest) (B : ℕ) (hs : s.Valid B)
    (γ : ℝ) (x₀ : Point d) (g : Point d → Ω → Point d) (ξ : ℕ → Ω) (k : ℕ) :
    (tree s).vertex γ x₀ g ξ (2 * k + 1) =
      (tree s).vertex γ x₀ g ξ (s.head k) -
        γ • g ((tree s).vertex γ x₀ g ξ (s.saved k)) (ξ (2 * k)) := by
  rw [vertex_succ _ (tree_wellFormed s B hs), private_base]
  have hg : (tree s).grad (2 * k) = 2 * k := by dsimp only [tree]; omega
  have hp : (tree s).point (2 * k) = s.saved k := by
    rw [← aux_node s k]
    simp only [Tree.auxNode, aux_sample]
  rw [hg, Tree.reply, hp]

lemma global_value {d : ℕ} {Ω : Type} (s : Forest) (B : ℕ) (hs : s.Valid B)
    (γ : ℝ) (x₀ : Point d) (g : Point d → Ω → Point d) (ξ : ℕ → Ω) (k : ℕ) :
    (tree s).vertex γ x₀ g ξ (2 * (k + 1)) =
      (tree s).vertex γ x₀ g ξ (2 * k) -
        γ • g ((tree s).vertex γ x₀ g ξ (s.saved k)) (ξ (2 * k)) := by
  simpa only [branch, aux_node, aux_sample] using
    branch_vertex_succ _ (tree_wellFormed s B hs) _ (main_branch s) γ x₀ g ξ k

structure Replay {Ω : Type} (p : Params) (s : Forest) (γ : ℝ) (g : Point p.d → Ω → Point p.d)
    (ξ : ℕ → Ω) (m : Memory p.d) (k : ℕ) : Prop where
  next : m.next = 4 * k + 1
  replies : m.replies = k
  points : ∀ j ≤ 2 * k, m.points (reg j) = (tree s).vertex γ p.x0 g ξ j

lemma replay {Ω : Type} (p : Params) (s : Forest) (B : ℕ) (hs : s.Valid B)
    (γ : ℝ) (g : Point p.d → Ω → Point p.d) (ξ : ℕ → Ω) (k : ℕ) :
    Replay p s γ g ξ
      (interpret p (fun _ => 0) (fun j x => g x (ξ (2 * j))) (prefixCode s γ k) (initialMemory p)) k := by
  induction k with
  | zero =>
    refine ⟨rfl, rfl, ?_⟩
    intro j hj
    have : j = 0 := by omega
    subst j
    rfl
  | succ k ih =>
    rw [prefixCode, interpret_append]
    let m := interpret p (fun _ => 0) (fun j x => g x (ξ (2 * j))) (prefixCode s γ k) (initialMemory p)
    let X := (tree s).vertex γ p.x0 g ξ
    let v := g (m.points (reg (s.saved k))) (ξ (2 * m.replies))
    let m₁ := perform p (fun _ => 0) m (.query 0 (reg (s.saved k))) v
    let m₂ := perform p (fun _ => 0) m₁ (.mix 0 [(-1, 4 * k + 1)]) 0
    let m₃ := perform p (fun _ => 0) m₂ (.move 0 (reg (s.head k)) (4 * k + 2) γ) 0
    let m₄ := perform p (fun _ => 0) m₃ (.move 0 (4 * k) (4 * k + 2) γ) 0
    change Replay p s γ g ξ m₄ (k + 1)
    have hsav := earlier_le (hs.1 k).1 (hs.2.2 k).2
    have hhead := earlier_le (hs.1 k).1 (hs.2.2 k).1
    have hv : v = g (X (s.saved k)) (ξ (2 * k)) := by
      dsimp only [v, X]
      rw [ih.points _ hsav, ih.replies]
    have hn₁ : m₁.next = 4 * k + 2 := by change m.next + 1 = _; rw [ih.next]
    have hn₂ : m₂.next = 4 * k + 3 := by change m₁.next + 1 = _; rw [hn₁]
    have hn₃ : m₃.next = 4 * k + 4 := by change m₂.next + 1 = _; rw [hn₂]
    have hv₁ : m₁.vectors (4 * k + 1) = v := by
      change Function.update m.vectors m.next v _ = _
      rw [ih.next, Function.update_self]
    have hv₂ : m₂.vectors (4 * k + 2) = -v := by
      simp [m₂, perform, storeVector, hn₁, hv₁]
    have hr₀ : reg (2 * k) = 4 * k := by unfold reg; omega
    have hr₁ : reg (2 * k + 1) = 4 * k + 3 := by unfold reg; omega
    have hr₂ : reg (2 * (k + 1)) = 4 * k + 4 := by unfold reg; omega
    have hp₃ : m₃.points = Function.update m.points (4 * k + 3) (X (2 * k + 1)) := by
      change Function.update m.points m₂.next
        (m.points (reg (s.head k)) + γ • m₂.vectors (4 * k + 2)) = _
      rw [hn₂, ih.points _ hhead, hv₂, hv, smul_neg, ← sub_eq_add_neg]
      congr 1
      exact (private_value s B hs γ p.x0 g ξ k).symm
    have hp₄ : m₄.points = Function.update m₃.points (4 * k + 4) (X (2 * (k + 1))) := by
      change Function.update m₃.points m₃.next (m₃.points (4 * k) + γ • m₂.vectors (4 * k + 2)) = _
      rw [hn₃, hp₃, Function.update_of_ne (by omega : 4 * k ≠ 4 * k + 3)]
      have hg₀ : m.points (4 * k) = X (2 * k) := hr₀ ▸ ih.points _ le_rfl
      rw [hg₀, hv₂, hv, smul_neg, ← sub_eq_add_neg]
      congr 1
      exact (global_value s B hs γ p.x0 g ξ k).symm
    refine ⟨?_, congrArg (· + 1) ih.replies, ?_⟩
    · change m₃.next + 1 = _
      rw [hn₃]
      omega
    · intro j hj
      by_cases he : j = 2 * (k + 1)
      · rw [he, hp₄, hr₂, Function.update_self]
      have hn : reg j < 4 * k + 4 := by unfold reg; omega
      rw [hp₄, Function.update_of_ne (ne_of_lt hn)]
      by_cases he' : j = 2 * k + 1
      · rw [he', hp₃, hr₁, Function.update_self]
      have hn' : reg j < 4 * k + 3 := by unfold reg; omega
      rw [hp₃, Function.update_of_ne (ne_of_lt hn')]
      exact ih.points j (by omega)

lemma execute_replay {Ω : Type} [MeasurableSpace Ω] (p : Params) (s : Forest) (B : ℕ)
    (hs : s.Valid B) (γ : ℝ) (K : ℕ) (hK : 0 < K)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → Point p.d)
    (ξ : ℕ → Ω) (i : Fin ((program s γ K).outputCount + 1)) :
    execute (gradientOracle P g) (programAlgorithm p (program s γ K) (fun _ => 0)) (fun _ => K)
      i (fun k => ξ (2 * k)) = (tree s).vertex γ p.x0 g ξ (2 * i.val) := by
  have he := execute_interpret p (program s γ K) (fun _ => 0) P g (fun k => ξ (2 * k)) i
  rw [prefix_calls] at he
  apply he.trans
  have hi := i.isLt
  change i.val < K - 1 + 1 at hi
  have hp := (replay p s B hs γ g ξ K).points (2 * i.val) (by omega)
  have hr : reg (2 * i.val) = 4 * i.val := by unfold reg; omega
  rw [hr] at hp
  exact hp

end LongTails.Proofs.BirchResourceReplay
