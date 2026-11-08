import LongTails.Setups.BirchCollections

namespace LongTails.Algorithms.BirchCollectionRetune

open LongTails.Setups.BirchCollections

def retune (g : ℝ → ℝ × ℝ) : Event → Event
  | .capture w x b _ movement => .capture w x b (g movement).1 (g movement).2
  | e => e

def collection (g : ℝ → ℝ × ℝ) (c : Collection) : Collection :=
  {c with refresh := (g c.movement).1, movement := (g c.movement).2}

def direction (g : ℝ → ℝ × ℝ) (d : Direction) : Direction :=
  {d with refresh := (g d.movement).1, movement := (g d.movement).2}

def trace (g : ℝ → ℝ × ℝ) (s : TraceState) : TraceState :=
  {s with collections := fun i => collection g (s.collections i)
          directions := fun i => direction g (s.directions i)}

end LongTails.Algorithms.BirchCollectionRetune
