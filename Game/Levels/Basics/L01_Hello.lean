import Game.Metadata

World "Basics"
Level 1

Title "Definition of a group"

Introduction "
In this game we will learn how to write proofs about groups
using the proof assistant Lean.
To get started,
let's do the most simple kind of proof -
proving that an element `x` of a set `G` is equal to itself.
"

variable (G : Type)

Statement (x : G) : x = x := by
  Hint "Try typing `rfl` where it says 'Enter a tactic'."
  rfl

Conclusion "Level completed!"

NewDefinition Eq
NewTactic rfl
