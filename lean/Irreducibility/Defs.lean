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

/-! ## Positions on a drum

A drum position is a list of levels `(digit, size)`, lowest level first. -/

/-- Where a drum position stands on ring `c`, read level by level from the top: each level
contributes its digit plus its size's relation to `c` times what the levels above give. -/
@[expose] public def positionOn : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (d, r) :: rest, c => (d + relation r c * positionOn rest c) % c

/-- Where one whole turn of a drum with level sizes `radices` stands on ring `c`. -/
@[expose] public def turnOn : List Nat → Nat → Nat
  | [], c => 1 % c
  | r :: rs, c => (relation r c * turnOn rs c) % c

/-- Step `step` teeth at a time around ring `b` from `pos`, at most `fuel` more steps; the
number of steps taken when the ring first stands at `1`. -/
@[expose] public def inverseAux (step b : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, t, pos =>
    if (pos + step) % b = 1 then t + 1 else inverseAux step b fuel (t + 1) ((pos + step) % b)

/-- The number of `a`-steps around ring `b` that land on `1`. -/
@[expose] public def inverse (a b : Nat) : Nat :=
  if b = 1 then 0 else inverseAux (relation a b) b b 0 0

/-- The level ring `m` in state `s` adds on top of the drum position `acc`; `none` when the
state contradicts the levels below. -/
@[expose] public def digitStep (acc : List (Nat × Nat)) (m s : Nat) : Option (Nat × Nat) :=
  let g := commonPartWithTurn (acc.map Prod.snd) m
  let r := m / g
  let y := (s + m - positionOn acc m) % m
  if y % g = 0 then
    some (if 1 < r then (y / g * inverse (turnOn (acc.map Prod.snd) m / g % r) r % r, r)
      else (0, r))
  else none

/-- The drum position given by ring states, built ring by ring on top of `acc`. -/
@[expose] public def digitsOfAux : List (Nat × Nat) → List Nat → List Nat →
    Option (List (Nat × Nat))
  | acc, m :: ms, s :: ss =>
    match digitStep acc m s with
    | none => none
    | some dr => digitsOfAux (acc ++ [dr]) ms ss
  | acc, _, _ => some acc

/-- The drum position of rings `rings` in states `states`. -/
@[expose] public def digitsOf (rings states : List Nat) : Option (List (Nat × Nat)) :=
  digitsOfAux [] rings states

/-- Compare two drum positions with the same level sizes, digit by digit from the top. -/
@[expose] public def compareTop : List (Nat × Nat) → List (Nat × Nat) → Ordering
  | (a, _) :: as, (b, _) :: bs =>
    match compareTop as bs with
    | .eq => compare a b
    | o => o
  | _, _ => .eq

/-- Compare two sets of states on the same rings: build both drum positions, then compare
from the top. -/
@[expose] public def compareOn (rings xs ys : List Nat) : Option Ordering :=
  match digitsOf rings xs, digitsOf rings ys with
  | some dx, some dy => some (compareTop dx dy)
  | _, _ => none

/-! ## Checks by evaluation (kernel `decide`, no extra axioms) -/

example : relation 17 5 = 2 := by decide
example : commonPart 12 18 = 6 := by decide
example : levels [2, 3, 4, 5, 6, 7, 8, 9, 10] = [2, 3, 2, 5, 1, 7, 2, 3, 1] := by decide
example : levels [6, 35] = [6, 35] := by decide
example : levels [4, 4] = [4, 1] := by decide
example : digitsOf [2, 3, 4, 5] [1, 1, 1, 2] = some [(1, 2), (0, 3), (0, 2), (3, 5)] := by
  decide
example : digitsOf [6, 4, 9] [4, 0, 1] = some [(4, 6), (0, 2), (2, 3)] := by decide
example : digitsOf [4, 4, 6] [3, 3, 1] = some [(3, 4), (0, 1), (1, 3)] := by decide
example : digitsOf [2, 4] [1, 2] = none := by decide
example : compareOn [2, 3, 4, 5] [1, 1, 1, 2] [0, 2, 2, 3] = some .lt := by decide
example : compareOn [2, 3, 4, 5] [1, 1, 1, 2] [1, 1, 1, 2] = some .eq := by decide
example : compareOn [6, 4, 9] [4, 0, 1] [3, 3, 0] = some .gt := by decide

end Irreducibility
