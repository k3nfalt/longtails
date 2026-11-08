import LongTails.Setups.BirchNonEuclidean

namespace LongTails.Algorithms.BirchNonEuclideanFamilies

open LongTails.Setups.BirchNonEuclidean

structure CodeState where
  instructions : List InstructionTemplate := []
  next : ℕ := 1

def emit (i : InstructionTemplate) : StateM CodeState ℕ := do
  let s : CodeState ← get
  set ({ instructions := s.instructions ++ [i], next := s.next + 1 } : CodeState)
  return s.next

noncomputable def localBatch (worker point B : ℕ) : StateM CodeState ℕ := do
  let mut terms := []
  for _ in List.range B do
    let q ← emit (.query worker point)
    terms := terms ++ [(.constant (1 / (B : ℝ)), q)]
  emit (.mix worker terms)

noncomputable def collectedBatch (worker : ℕ → ℕ) (round point B : ℕ) :
    StateM CodeState ℕ := do
  let mut terms := []
  for h in List.range B do
    let w := worker (round * B + h)
    let _ ← emit (.sendPoint 0 w point)
    let q ← emit (.query w point)
    let _ ← emit (.sendVector w 0 q)
    terms := terms ++ [(.constant (1 / (B : ℝ)), q)]
  emit (.mix 0 terms)

noncomputable def batchCode (worker : ℕ → ℕ) (K B : ℕ) :
    StateM CodeState (ℕ → ℕ) := do
  let mut points := fun _ : ℕ => 0
  for k in List.range K do
    let g ← collectedBatch worker k (points k) B
    let d ← emit (.sharp 0 g)
    let x ← emit (.move 0 (points k) d (.step k))
    points := Function.update points (k + 1) x
  return points

noncomputable def makeTemplate (K : ℕ) (code : StateM CodeState (ℕ → ℕ)) :
    ProgramTemplate :=
  let result := code.run {}
  { instructions := result.2.instructions
    outputWorker := 0
    outputCount := K - 1
    outputPoint := fun j => result.1 j.val }

noncomputable def minibatchFamily (worker : ℕ → ℕ) : ProtocolFamily where
  template K B := makeTemplate K (batchCode worker K B)

noncomputable def localMomentum (worker x m H round : ℕ) :
    StateM CodeState (ℕ × ℕ) := do
  let mut point := x
  let mut momentum := m
  for h in List.range H do
    let q ← emit (.query worker point)
    let α := Coefficient.momentum (round * H + h)
    momentum ← emit (.mix worker [(α, q), (.add (.constant 1) (.neg α), momentum)])
    let d ← emit (.sharp worker momentum)
    point ← emit (.move worker point d (.mul (.constant (1 / (H : ℝ))) (.step round)))
  return (point, momentum)

noncomputable def sharedCode (workers H K B : ℕ) : StateM CodeState (ℕ → ℕ) := do
  let mut points := fun _ : ℕ => 0
  let mut momentum ← localBatch 0 0 (workers * B)
  for k in List.range K do
    let mut displacements := []
    let mut momenta := []
    for i in List.range workers do
      let w := i + 1
      let _ ← emit (.sendPoint 0 w (points k))
      let _ ← emit (.sendVector 0 w momentum)
      let packet ← localMomentum w (points k) momentum H k
      let dx ← emit (.difference w packet.1 (points k))
      let _ ← emit (.sendVector w 0 dx)
      let _ ← emit (.sendVector w 0 packet.2)
      let c := Coefficient.constant (1 / (workers : ℝ))
      displacements := displacements ++ [(c, dx)]
      momenta := momenta ++ [(c, packet.2)]
    let dx ← emit (.mix 0 displacements)
    let x ← emit (.move 0 (points k) dx (.constant 1))
    momentum ← emit (.mix 0 momenta)
    points := Function.update points (k + 1) x
  return points

noncomputable def sharedMomentumFamily (workers H : ℕ) : ProtocolFamily where
  template K B := makeTemplate K (sharedCode workers H K B)

noncomputable def deltaCode (H : ℕ) (dispatch worker : ℕ → ℕ) (K B : ℕ) :
    StateM CodeState (ℕ → ℕ) := do
  let mut points := fun _ : ℕ => 0
  let initial ← localBatch 0 0 B
  let mut momenta := fun _ : ℕ => initial
  for k in List.range K do
    let s := dispatch k
    let w := worker k
    let _ ← emit (.sendPoint 0 w (points s))
    let _ ← emit (.sendVector 0 w (momenta s))
    let packet ← localMomentum w (points s) (momenta s) H k
    let dx ← emit (.difference w packet.1 (points s))
    let dm ← emit (.mix w [(.constant 1, packet.2), (.constant (-1), momenta s)])
    let _ ← emit (.sendVector w 0 dx)
    let _ ← emit (.sendVector w 0 dm)
    let x ← emit (.move 0 (points k) dx (.constant 1))
    let m ← emit (.mix 0 [(.constant 1, momenta k), (.constant 1, dm)])
    points := Function.update points (k + 1) x
    momenta := Function.update momenta (k + 1) m
  return points

noncomputable def deltaMomentumFamily (H : ℕ) (dispatch worker : ℕ → ℕ) :
    ProtocolFamily where
  template K B := makeTemplate K (deltaCode H dispatch worker K B)

end LongTails.Algorithms.BirchNonEuclideanFamilies
