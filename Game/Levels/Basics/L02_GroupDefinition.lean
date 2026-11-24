import Game.Metadata

World "Basics"
Level 1

Title "Definition of a group"

Introduction "
In this level we will learn the definition of a group.
In Lean,
a group is a type `G` (if it helps, you can think of `G` as a set)
with extra bits of structure.
These extra bits of structure are:
an element `one` in `G`,
a multiplication function `mul`
which takes two elements of the group `a` and `b`
and returns an element `mul a b`,
and an inverse function `inv`
which takes an element of the group `a`
and returns an element `inv a`.
"

class MyGroup (G : Type) where
  one : G
  mul (a b : G) : G
  inv (a : G) : G
  mul_assoc : ∀ g h k, mul g (mul h k) = mul (mul g h) k
  mul_one : ∀ g, mul g one = g
  one_mul : ∀ g, mul one g = g
  mul_inv : ∀ g, mul g (inv g) = one
  inv_mul : ∀ g, mul (inv g) g = one

variable (x y : Nat)

Statement MyLevel1 (h : x = 2) (g : y = 4) : x + x = y := by
  Hint "You can either start \
        using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "Maybe you should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  Hint (hidden := true) "Hidden Hint 1"
  Hint (hidden := true) "Hidden Hint 2"
  rw [g]

Conclusion "This last message appears if the level is solved."

NewDefinition Eq Add
NewTactic rw rfl
NewHiddenTactic simp
NewTheorem Nat.add_comm
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
