module

/-!
# Rings, relations and levels

Every object in this file is a ring period (a natural number) or a state below a period.
No definition refers to primes, to factorization, or to a number built from the ring states.

* `pos d t` -- where ring `d` stands after `t` ticks, obtained by ticking alone: the ring
  advances by one tooth per tick and returns to `0` when it completes a turn.
* `relation a b` -- where ring `b` stands when ring `a` completes its first turn, that is
  after `a` ticks.
* `commonPart a b` -- Euclid's procedure run on relations only.
* `commonPartWithTurn radices m` -- the part ring `m` shares with the turn of a drum whose
  levels have sizes `radices`, computed level by level without forming the turn.
* `levels rings` -- the drum built from `rings` in order: each ring contributes a level of
  size `m / commonPartWithTurn (levels so far) m`.
* `IrreducibleAfter before m` -- ring `m` contributes its whole period: nothing of it is
  carried by the rings before it.
-/

namespace Irreducibility

/-- Position of ring `d` after `t` ticks, by ticking: one tooth per tick, back to `0` after
a whole turn. -/
@[expose] public def pos (d : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => if pos d t + 1 = d then 0 else pos d t + 1

/-- Where ring `b` stands when ring `a` completes its first turn. -/
@[expose] public def relation (a b : Nat) : Nat := pos b a

/-- Euclid's procedure on relations, with a fuel bound; `commonPart` supplies enough fuel. -/
@[expose] public def commonPartAux : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | fuel + 1, a, b => if b = 0 then a else commonPartAux fuel b (relation a b)

/-- The common part of rings `a` and `b`: Euclid's procedure on relations. -/
@[expose] public def commonPart (a b : Nat) : Nat := commonPartAux (b + 1) a b

/-- Absorb one level of size `r` into the pair (part found so far `g`, rest of the ring
`rest`): repeatedly take the common part `t` of `r` and `rest`, move it into `g`. -/
@[expose] public def absorb : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, g, rest => (g, rest)
  | fuel + 1, r, g, rest =>
    if commonPart r rest ≤ 1 then (g, rest)
    else absorb fuel (r / commonPart r rest) (g * commonPart r rest) (rest / commonPart r rest)

/-- The part ring `m` shares with the turn of a drum with level sizes `radices`, computed
level by level; the turn itself is never formed. -/
@[expose] public def commonPartWithTurn (radices : List Nat) (m : Nat) : Nat :=
  (radices.foldl (fun acc r => absorb (m + 1) r acc.1 acc.2) (1, m)).1

/-- The level sizes of the drum built from `rings` in order. -/
@[expose] public def levels (rings : List Nat) : List Nat :=
  rings.foldl (fun acc m => acc ++ [m / commonPartWithTurn acc m]) []

/-- The level size ring `m` gets on top of the drum built from `before`. -/
@[expose] public def levelSize (before : List Nat) (m : Nat) : Nat :=
  m / commonPartWithTurn (levels before) m

/-- Ring `m` is irreducible after `before`: it contributes its whole period. -/
@[expose] public def IrreducibleAfter (before : List Nat) (m : Nat) : Prop :=
  levelSize before m = m

/-- The consecutive rings `2, 3, ..., n - 1`. -/
@[expose] public def ringsBelow (n : Nat) : List Nat := (List.range n).drop 2

/-! ## Checks by evaluation (kernel `decide`, no extra axioms) -/

example : relation 17 5 = 2 := by decide
example : commonPart 12 18 = 6 := by decide
example : levels [2, 3, 4, 5, 6, 7, 8, 9, 10] = [2, 3, 2, 5, 1, 7, 2, 3, 1] := by decide
example : levels [6, 35] = [6, 35] := by decide
example : levels [4, 4] = [4, 1] := by decide

end Irreducibility
