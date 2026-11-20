import LongTails.Algorithms.GraceSgd
import LongTails.Proofs.LeonTermination

namespace LongTails.Proofs.GraceProgramSize

open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms
open GracePacket GraceBatch GraceRouting GraceSgd
open LeonInstructionCount

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n} (A : Routes p S r) (D q : ℕ)
  (phase : Phase) (k : ℕ) (i : Fin p.n)

lemma send_size (values : Values) {next : LeonProtocol.Program p.base} {n : ℕ}
    (h : Size next n) (peers : List (Fin p.n)) :
    Size (A.sendFrame D q phase k i values next peers) (n + peers.length) := by
  induction peers with
  | nil => simpa [Routes.sendFrame] using h
  | cons j peers ih =>
    simp only [Routes.sendFrame, List.length_cons, ← Nat.add_assoc]
    split <;> exact Size.send ih

lemma receive_size {next : Values → LeonProtocol.Program p.base} {n : ℕ} (h : ∀ v, Size (next v) n)
    (peers : List (Fin p.n)) (values : Values) :
    Size (A.receiveFrame D q phase k i next peers values) (n + peers.length) := by
  induction peers generalizing values with
  | nil => simpa [Routes.receiveFrame] using h values
  | cons j peers ih =>
    simp only [Routes.receiveFrame, List.length_cons, ← Nat.add_assoc]
    split
    · exact Size.send (ih _)
    · exact Size.receive fun _ => ih _

lemma frames_size {next : Values → LeonProtocol.Program p.base} {n : ℕ} (h : ∀ v, Size (next v) n)
    (ks : List ℕ) (values : Values) :
    Size (A.frames D q phase i next ks values) (n + ks.length * (2 * p.n)) := by
  induction ks generalizing values with
  | nil => simpa [Routes.frames] using h values
  | cons k ks ih =>
    simp only [Routes.frames, List.length_cons]
    convert send_size A D q phase k i values
      (receive_size A D q phase k i ih (List.finRange p.n) values) (List.finRange p.n) using 1
    simp
    ring

lemma frames_range {next : Values → LeonProtocol.Program p.base} {n : ℕ}
    (h : ∀ v, Size (next v) n) (values : Values) :
    Size (A.frames D q phase i next (List.range (A.slots D)) values)
      (n + A.slots D * (2 * p.n)) := by
  simpa only [List.length_range] using frames_size A D q phase i h (List.range (A.slots D)) values

def instructions (A : Routes p S r) (d w B : ℕ) :=
  1 + 4 * p.n * A.slots (d * limbCount w (limbWidth B))

lemma program_size (i : Fin p.n) (k : ℕ) (x : Point p) :
    Size (program A i k x) (k * instructions A p.d (tuning p S).width (B p)) := by
  induction k generalizing x with
  | zero => simpa [program] using Size.finish x
  | succ k ih =>
    let D := p.d * limbCount (tuning p S).width (limbWidth (B p))
    let n := k * instructions A p.d (tuning p S).width (B p)
    have hround (v : Point p) : Size (GraceSgd.round A i x v (program A i k))
        ((n + (A.slots D) * (2 * p.n)) + (A.slots D) * (2 * p.n)) := by
      unfold GraceSgd.round
      change Size (A.frames D _ .reduce i _ (List.range (A.slots D)) _) _
      apply frames_range A D _ .reduce i
      intro collected
      apply frames_range A D _ .broadcast i
      intro output
      exact ih _
    have he : (k + 1) * instructions A p.d (tuning p S).width (B p) =
        ((n + A.slots D * (2 * p.n)) + A.slots D * (2 * p.n)) + 1 := by
      dsimp [instructions, n, D]; ring
    rw [he, program]
    split
    · exact Size.sample (fun _ => hround _)
    · exact Size.send (hround _)

end LongTails.Proofs.GraceProgramSize
