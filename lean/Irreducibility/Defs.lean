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
* `turnOn radices c` -- where one whole turn of a drum with level sizes `radices` stands on
  ring `c`, read level by level without forming the turn.
* `commonPartWithTurn radices m` -- the part ring `m` shares with the turn of a drum whose
  levels have sizes `radices`: `commonPart` of where the turn stands on ring `m` and `m`.
* `levels rings` -- the drum built from `rings` in order: each ring contributes a level of
  size `m / commonPartWithTurn (levels so far) m`.
* `IrreducibleAfter before m` -- ring `m` contributes its whole period: nothing of it is
  carried by the rings before it.
* `windowAtoms lo hi` -- the steps read from pairs of rings of the window `lo, ..., hi` that
  stand at `0` on no smaller step kept before.
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

/-- Where one whole turn of a drum with level sizes `radices` stands on ring `c`. -/
@[expose] public def turnOn : List Nat → Nat → Nat
  | [], c => 1 % c
  | r :: rs, c => (relation r c * turnOn rs c) % c

/-- The part ring `m` shares with the turn of a drum with level sizes `radices`: Euclid's
procedure on ring `m` and where the turn stands on it; the turn itself is never formed. -/
@[expose] public def commonPartWithTurn (radices : List Nat) (m : Nat) : Nat :=
  commonPart (turnOn radices m) m

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

/-! ## Packs

A pack is a group of rings that acts as one ring: its period is the turn of the drum built
from its members, and its state is the position on that turn. A number on a drum of packs is
given by the member states of its packs and, for the number of whole turns of that drum, the
member states of its rotation packs. -/

/-- The position a drum position stands for on the turn of its levels, below that turn. -/
@[expose] public def value : List (Nat × Nat) → Nat
  | [] => 0
  | (d, r) :: rest => d + r * value rest

/-- A pack as one ring: the turn of the drum built from its members and the position on it;
`none` for contradictory member states. -/
@[expose] public def packRing (members states : List Nat) : Option (Nat × Nat) :=
  match digitsOf members states with
  | some ds => some (ds.foldr (fun p acc => p.2 * acc) 1, value ds)
  | none => none

/-- The pack rings and pack states of a drum of packs. -/
@[expose] public def drumOfPacks : List (List Nat) → List (List Nat) →
    Option (List Nat × List Nat)
  | p :: ps, s :: ss =>
    match packRing p s, drumOfPacks ps ss with
    | some (c, x), some (cs, xs) => some (c :: cs, x :: xs)
    | _, _ => none
  | _, _ => some ([], [])

/-- A number on a drum of packs: member states of `packs`, and member states of `rotPacks`
for the number of whole turns of the drum of `packs`. -/
public structure Packed where
  packs : List (List Nat)
  states : List (List Nat)
  rotPacks : List (List Nat)
  rotStates : List (List Nat)

/-- Carry the drum position given by `states` on `rings` onto the rings `target`. -/
@[expose] public def extend (rings states target : List Nat) : Option (List Nat) :=
  match digitsOf rings states with
  | some ds => some (target.map (positionOn ds))
  | none => none

/-- One drum of packs and rotation packs: a rotation pack `c` in state `k` stands at
`k` turns of the drum of packs plus the position of that drum on `c`. -/
@[expose] public def flatten (x : Packed) : Option (List Nat × List Nat) :=
  match drumOfPacks x.packs x.states, drumOfPacks x.rotPacks x.rotStates with
  | some (dr, ds), some (kr, ks) =>
    match digitsOf dr ds with
    | some dd => some (dr ++ kr, ds ++ (kr.zip ks).map fun (c, k) =>
        (k * turnOn (dd.map Prod.snd) c + positionOn dd c) % c)
    | none => none
  | _, _ => none

/-- The rings of `rx` followed by the rings of `ry` not among them. -/
@[expose] public def union (rx ry : List Nat) : List Nat :=
  rx ++ ry.filter fun c => !rx.contains c

/-- Compare two numbers given on different drums of packs: flatten both, carry both onto
the common rings, then compare from the top. -/
@[expose] public def comparePacked (x y : Packed) : Option Ordering :=
  match flatten x, flatten y with
  | some (rx, sx), some (ry, sy) =>
    match extend rx sx (union rx ry), extend ry sy (union rx ry) with
    | some ex, some ey => compareOn (union rx ry) ex ey
    | _, _ => none
  | _, _ => none

/-! ## Primality on a drum

A number is given by its states on a drum. Trial rings `m = 2, 3, ...` are compared with it
through their own states `m % c` and `m * m % c` on the drum's rings, both read from
relations, and the number's state on ring `m` is read from its drum position. -/

/-- Try rings `m, m + 1, ...`, at most `fuel` of them, against the number given by `states`
on `rings` with drum position `ds`: `true` when `m` reaches the number or `m * m` passes
it, `false` when the number is below `m` or stands at `0` on ring `m`; `none` when the fuel
runs out or the states contradict each other. -/
@[expose] public def primeOnAux (rings states : List Nat) (ds : List (Nat × Nat)) :
    Nat → Nat → Option Bool
  | 0, _ => none
  | fuel + 1, m =>
    match compareOn rings (rings.map (relation m)) states with
    | some .eq => some true
    | some .gt => some false
    | some .lt =>
      match compareOn rings (rings.map fun c => relation m c * relation m c % c) states with
      | some .gt => some true
      | some _ =>
        if positionOn ds m = 0 then some false else primeOnAux rings states ds fuel (m + 1)
      | none => none
    | none => none

/-- Whether the number given by `states` on `rings` is prime, trying at most `fuel` rings
from `2` on. -/
@[expose] public def primeOn (fuel : Nat) (rings states : List Nat) : Option Bool :=
  match digitsOf rings states with
  | some ds => primeOnAux rings states ds fuel 2
  | none => none

/-! ## Atoms of a window

A window is the run of consecutive rings `lo, ..., hi`. A step `k` is read from two window
rings `a` and `a + k` with ring `a` at `0` on ring `k`: their difference `k` is a part
they share. -/

/-- The first ring from `lo` on that stands at `0` on ring `k`, from one relation. -/
@[expose] public def firstMultipleFrom (lo k : Nat) : Nat :=
  if relation lo k = 0 then lo else lo + (k - relation lo k)

/-- Take step `k` into the atoms found so far when the window `lo, ..., hi` holds two rings
`a` and `a + k` with `a` at `0` on ring `k`, and `k` stands at `0` on none of those atoms. -/
@[expose] public def atomStep (lo hi : Nat) (atoms : List Nat) (k : Nat) : List Nat :=
  if firstMultipleFrom lo k + k ≤ hi ∧ atoms.all (fun p => relation k p != 0) = true then
    atoms ++ [k]
  else atoms

/-- The atoms of the window `lo, ..., hi`: the steps `2, ..., hi - lo` in order, each kept
by `atomStep`. -/
@[expose] public def windowAtoms (lo hi : Nat) : List Nat :=
  (ringsBelow (hi - lo + 1)).foldl (atomStep lo hi) []

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

example : packRing [2, 3, 4] [1, 2, 3] = some (12, 11) := by decide
example : packRing [4, 6] [3, 1] = some (12, 7) := by decide
example : packRing [2, 4] [1, 2] = none := by decide
example : drumOfPacks [[2, 3], [4, 5]] [[1, 2], [3, 4]] = some ([6, 20], [5, 19]) := by decide
example : extend [6, 20, 7, 8] [4, 0, 2, 4] [9, 5] = some [1, 0] := by decide
example : flatten ⟨[[2, 3], [4, 5]], [[0, 1], [0, 0]], [[7, 8]], [[1, 1]]⟩ =
    some ([6, 20, 56], [4, 0, 44]) := by decide
example : flatten ⟨[[2, 3, 4], [5]], [[1, 2, 1], [1]], [[7], [9]], [[1], [1]]⟩ =
    some ([12, 5, 7, 9], [5, 1, 3, 2]) := by decide
set_option maxRecDepth 20000 in
example : comparePacked ⟨[[2, 3], [4, 5]], [[0, 1], [0, 0]], [[7, 8]], [[1, 1]]⟩
    ⟨[[2, 3, 4], [5]], [[1, 2, 1], [1]], [[7], [9]], [[1], [1]]⟩ = some .lt := by decide
set_option maxRecDepth 20000 in
example : comparePacked ⟨[[2, 3, 4], [5]], [[1, 2, 1], [1]], [[7], [9]], [[1], [1]]⟩
    ⟨[[2, 3], [4, 5]], [[0, 1], [0, 0]], [[7, 8]], [[1, 1]]⟩ = some .gt := by decide
set_option maxRecDepth 20000 in
example : comparePacked ⟨[[2, 3], [4, 5]], [[0, 1], [0, 0]], [[7, 8]], [[1, 1]]⟩
    ⟨[[2, 3, 4], [5]], [[0, 1, 0], [0]], [[7], [9]], [[1], [1]]⟩ = some .eq := by decide

example : primeOn 20 [4, 3, 5, 7] [1, 1, 2, 6] = some true := by decide
example : primeOn 20 [4, 3, 5, 7] [3, 1, 1, 0] = some false := by decide
example : primeOn 20 [4, 3, 5, 7] [1, 1, 1, 2] = some false := by decide
example : primeOn 20 [4, 3, 5, 7] [1, 2, 3, 1] = some true := by decide
example : primeOn 20 [4, 3, 5, 7] [2, 2, 2, 2] = some true := by decide
example : primeOn 20 [4, 3, 5, 7] [1, 1, 1, 1] = some false := by decide
example : primeOn 20 [4, 3, 5, 7] [0, 0, 0, 0] = some false := by decide
example : primeOn 3 [4, 3, 5, 7] [1, 1, 2, 6] = none := by decide
example : primeOn 20 [6, 4, 9, 5] [1, 1, 7, 4] = some false := by decide
example : primeOn 20 [6, 4, 9, 5] [5, 1, 2, 3] = none := by decide
set_option maxRecDepth 20000 in
example : primeOn 200 [6, 4, 9, 5] [5, 1, 2, 3] = some true := by decide
example : primeOn 20 [2, 4] [1, 2] = none := by decide

set_option maxRecDepth 20000 in
example : windowAtoms 50 60 = [2, 3, 5] := by decide
set_option maxRecDepth 20000 in
example : windowAtoms 100 130 = [2, 3, 5, 7, 11, 13, 17] := by decide
set_option maxRecDepth 20000 in
example : windowAtoms 2 60 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29] := by decide
example : windowAtoms 7 7 = [] := by decide
example : windowAtoms 9 3 = [] := by decide

end Irreducibility
