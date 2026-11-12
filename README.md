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
| `commonPartWithTurn radices m` | the part ring `m` shares with the turn of a drum, computed level by level without forming the turn |
| `levels rings` | the drum built from `rings` in order: each ring adds a level of size `m / commonPartWithTurn (levels so far) m` |
| `levelSize before m` | the level ring `m` gets on top of the drum built from `before` |
| `IrreducibleAfter before m` | ring `m` contributes its whole period: `levelSize before m = m` |
| `ringsBelow n` | the consecutive rings `2, 3, ..., n - 1` |

## What is proved

| Step | File | Statement |
|---|---|---|
| T1 Ticking | `Ticking.lean` | `pos d t = t % d` for every `d`, `d = 0` included; hence `relation a b = a % b` |
| T2 Euclid | `Euclid.lean` | `commonPart a b = Nat.gcd a b` |
| T3 Drum | `Drum.lean` | `commonPartWithTurn radices m = gcd (radices.prod) m`; the product of the level sizes of positive rings is their least common multiple; `IrreducibleAfter before m ↔ Nat.Coprime (lcm of before) m` |
| T4 Consecutive rings | `Bridge.lean` | for `n ≥ 2`: `levelSize (ringsBelow n) n` is `p` when `n = p ^ k` is a prime power and `1` otherwise; `IrreducibleAfter (ringsBelow n) n ↔ Nat.Prime n`; `Real.log (levelSize (ringsBelow n) n) = Λ n` (von Mangoldt) |

T3 holds for any list of positive rings, in any order. T4 is the special case of the
consecutive rings `2, ..., n - 1`.

Each file also contains checks evaluated by the kernel (`decide`), e.g.
`levels [2, 3, 4, 5, 6, 7, 8, 9, 10] = [2, 3, 2, 5, 1, 7, 2, 3, 1]`.

Planned: comparing two numbers held on a drum without forming their values, and a
primality test on a drum without forming values.

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
