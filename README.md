# Irreducibility

A Lean 4 / Mathlib formalization of a ring (gear) mechanism. Rings of arbitrary periods,
composite periods included, are combined into a drum level by level. Relations between
rings are read by ticking, and common parts by Euclid's procedure run on those relations.
No definition refers to primes, to factorization, or to a number built from the ring
states. Primes appear only in the theorems that describe what the mechanism produces.

Lean/Mathlib `v4.35.0`. `lake build` is green with no `sorry`, `admit` or `native_decide`.
The only axioms used are `propext`, `Quot.sound` and `Classical.choice`.
License: Apache-2.0.

## The mechanism

All definitions are in `lean/Irreducibility/Defs.lean`, which does not import Mathlib.

| Definition | Meaning |
|---|---|
| `pos d t` | position of ring `d` after `t` ticks, by ticking alone |
| `relation a b` | where ring `b` stands when ring `a` completes its first turn |
| `commonPart a b` | Euclid's procedure run on relations |
| `turnOn radices c` | where one whole turn of a drum stands on ring `c`, read level by level without forming the turn |
| `commonPartWithTurn radices m` | the part ring `m` shares with the turn of a drum: `commonPart (turnOn radices m) m` |
| `levels rings` | the drum built from `rings` in order: each ring adds a level of size `m / commonPartWithTurn (levels so far) m` |
| `levelSize before m` | the level ring `m` gets on top of the drum built from `before` |
| `IrreducibleAfter before m` | ring `m` contributes its whole period: `levelSize before m = m` |
| `ringsBelow n` | the consecutive rings `2, 3, ..., n - 1` |
| `positionOn ds c` | where a drum position (levels `(digit, size)`) stands on ring `c`, read from the top |
| `inverse a b` | the number of `a`-steps around ring `b` that land on `1` |
| `digitsOf rings states` | the drum position given by ring states, built ring by ring; `none` for contradictory states |
| `compareOn rings xs ys` | compare two sets of states on the same rings, digit by digit from the top |
| `value ds` | the position a drum position stands for on the turn of its levels |
| `packRing members states` | a pack as one ring: period = turn of the members' drum, state = `value` of their drum position |
| `drumOfPacks packs states` | the pack rings and pack states of a drum of packs |
| `Packed` | a number given by member states of packs, plus member states of rotation packs for the number of whole turns of the drum of packs |
| `extend rings states target` | carry a drum position onto other rings with `positionOn` |
| `flatten x` | one drum of packs and rotation packs: rotation pack `c` in state `k` stands at `k` turns plus the position on `c` |
| `comparePacked x y` | flatten both numbers, carry both onto the union of their rings, compare with `compareOn` |
| `primeOn fuel rings states` | try rings `m = 2, 3, ...` against a number given on a drum: `m` and `m * m` are compared with it through their states on the drum's rings (read from relations), the number's state on ring `m` through `positionOn`; `true` when `m` reaches the number or `m * m` passes it, `false` when ring `m` stands at `0`, `none` when the fuel runs out |

## What is proved

| Step | File | Statement |
|---|---|---|
| T1 Ticking | `Ticking.lean` | `pos d t = t % d` for every `d`, `d = 0` included; hence `relation a b = a % b` |
| T2 Euclid | `Euclid.lean` | `commonPart a b = Nat.gcd a b` |
| T3 Drum | `Drum.lean` | `turnOn radices c = radices.prod % c`; `commonPartWithTurn radices m = gcd (radices.prod) m`; the product of the level sizes of positive rings is their least common multiple; `IrreducibleAfter before m ↔ Nat.Coprime (lcm of before) m` |
| T4 Consecutive rings | `Bridge.lean` | for `n ≥ 2`: `levelSize (ringsBelow n) n` is `p` when `n = p ^ k` is a prime power and `1` otherwise; `IrreducibleAfter (ringsBelow n) n ↔ Nat.Prime n`; `Real.log (levelSize (ringsBelow n) n) = Λ n` (von Mangoldt) |
| T5 Compare | `Compare.lean` | for positive rings and states `n % m`: `digitsOf` returns the mixed-radix digits of `n` modulo the drum's turn, on the levels `levels rings`; `positionOn ds c = value ds % c`; for `n, n'` below the turn, `compareOn rings (states of n) (states of n') = some (compare n n')` |
| T5c Packs | `Packs.lean` | a pack of positive rings in states `n % m` is one ring of period `lcm` in state `n % lcm`; `flatten` gives every ring `c` of the drum of packs and rotation packs the state `n % c`; below the turn, `extend` gives `n % c` on any ring `c`; for `n` below the lcm of all rings of its packing and `n'` below that of its own, `comparePacked (Packed.of n D K) (Packed.of n' D' K') = some (compare n n')` |
| T6 Primality | `Primality.lean` | for positive rings with `n` and `2` below the turn: every answer of `primeOn` on the states `n % c` is `Nat.Prime n`; it answers once `fuel > n`, or once `fuel > Nat.sqrt n` when `(Nat.sqrt n + 1) ^ 2` is below the turn |

T3 holds for any list of positive rings, in any order. T4 is the special case of the
consecutive rings `2, ..., n - 1`.

Each file also contains checks evaluated by the kernel (`decide`), e.g.
`levels [2, 3, 4, 5, 6, 7, 8, 9, 10] = [2, 3, 2, 5, 1, 7, 2, 3, 1]`.

The mechanism forms no number from ring states beyond a ring's period: `value` is formed
only as the state of a pack ring, which is below the pack's period. `Packed.of`, which
writes `n` onto packs, appears only in statements.

## Repository layout

```
lean/                       Lean 4 project (lakefile.toml, lean-toolchain)
  Irreducibility.lean       root module, imports everything below
  Irreducibility/
    Defs.lean               the mechanism (no Mathlib)
    Ticking.lean            T1
    Euclid.lean             T2
    Drum.lean               T3
    Bridge.lean             T4
    Compare.lean            T5
    Packs.lean              T5c
    Primality.lean          T6
Latex/                      paper sources (in preparation)
```

## Build

```
cd lean
lake exe cache get
lake build
```

To list the axioms a theorem depends on, run `lake env lean` on a file containing, for example:

```lean
import Irreducibility
#print axioms Irreducibility.irreducibleAfter_ringsBelow_iff
```
