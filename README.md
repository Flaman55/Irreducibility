# Irreducibility

A Lean 4 / Mathlib formalization of a residue number system over arbitrary moduli, composite
and not pairwise coprime moduli included. Residues are computed by counting, gcds by
Euclid's algorithm on residues, and the moduli are combined into a mixed-radix system in
which each modulus receives the part of it not covered by the moduli before it. Comparison,
overflow detection, exact division, base extension and primality testing work on residues.
No definition refers to primes, to factorization, or to a number assembled from residues.
Primes appear only in the theorems about the results.

Lean/Mathlib `v4.35.0`. `lake build` is green with no `sorry`, `admit` or `native_decide`.
The only axioms used are `propext`, `Quot.sound` and `Classical.choice`.
License: Apache-2.0.

## Definitions

All definitions except the sech comb are in `lean/Irreducibility/Defs.lean`, which does not
import Mathlib. The sech comb needs real numbers and is defined in `SechComb.lean` and
`SechRatio.lean`.

A mixed-radix representation is a list of pairs `(digit, radix)`, least significant first.

| Definition | Meaning |
|---|---|
| `countMod d t` | the residue of `t` modulo `d`, by counting: add `1` per step, reset to `0` on reaching `d` |
| `resid a b` | the residue of `a` modulo `b` |
| `mulCount g q t` | the residue of `g ^ t` modulo `q`, by multiplicative counting: start at `1`, multiply by `g` per step, take the residue modulo `q` |
| `euclid a b` | the gcd of `a` and `b` by Euclid's algorithm on residues |
| `prodMod radices c` | the residue modulo `c` of the product of `radices`, factor by factor, without forming the product |
| `gcdProd radices m` | the gcd of `m` with the product of `radices`: `euclid (prodMod radices m) m` |
| `radices moduli` | the radices of the mixed-radix system of `moduli` in order: modulus `m` receives `m / gcdProd (radices so far) m` |
| `newRadix before m` | the radix modulus `m` receives after the moduli `before` |
| `IrreducibleAfter before m` | modulus `m` receives its whole value as radix: `newRadix before m = m` |
| `initialModuli n` | the consecutive moduli `2, 3, ..., n - 1` |
| `evalMod ds c` | the value of a mixed-radix representation modulo `c`, by Horner's rule from the most significant digit |
| `invMod a b` | the inverse of `a` modulo `b`, by repeated addition of `a` modulo `b` |
| `toMixedRadix moduli residues` | the mixed-radix representation given by residues (Garner's algorithm on arbitrary moduli); `none` for incompatible residues |
| `compareRes moduli xs ys` | compare two residue vectors on the same moduli, digit by digit from the most significant |
| `eval ds` | the value of a mixed-radix representation |
| `blockModulus moduli residues` | a block of moduli as one modulus: modulus = lcm of the members, residue = `eval` of their mixed-radix representation |
| `blockModuli blocks residues` | the block moduli and block residues of a list of blocks |
| `BlockRep` | a number given by the member residues of blocks, plus the member residues of quotient blocks for the quotient by the lcm of the blocks |
| `baseExtend moduli residues target` | base extension: the residues on `target`, by `evalMod` |
| `flatten x` | one list of moduli for blocks and quotient blocks: quotient block `c` with residue `k` receives `k * L + r` modulo `c` |
| `compareBlocks x y` | flatten both numbers, extend both to the union of their moduli, compare with `compareRes` |
| `isPrimeRes fuel moduli residues` | trial division on residues: divisors `m = 2, 3, ...` are compared with the number through their residue vectors, the residue of the number modulo `m` comes from `evalMod`; `true` when `m` equals the number or `m * m` exceeds it, `false` when `m` divides it, `none` when the fuel runs out |
| `IntervalDifference lo hi k` | `2 ≤ k` and the interval `lo, ..., hi` contains `a` and `a + k` with `k ∣ a` |
| `firstMultipleFrom lo k` | the least multiple of `k` that is at least `lo`, from one residue |
| `atomStep lo hi atoms k` | keep `k` when the interval `lo, ..., hi` contains `a` and `a + k` with `k ∣ a`, and no atom kept before divides `k` |
| `intervalAtoms lo hi` | the differences `2, ..., hi - lo` in order, each kept by `atomStep` |
| `pointwise f moduli xs ys` | apply `f m a b` for each modulus `m` to its residues `a` and `b` |
| `addRes`, `subRes`, `mulRes` | sum, difference and product of two numbers, modulus by modulus |
| `addOverflow`, `subUnderflow` | a sum overflows when its residue vector compares below the first term's; a difference underflows when the first term compares below the second |
| `powRes moduli xs e` | `e` products modulus by modulus, starting from the residues of `1` |
| `divModuli moduli t` | the moduli `m / gcd(m, t)` of the quotient by `t` |
| `exactDivRes moduli residues t` | exact division by `t`: for modulus `m` and `g = gcd(m, t)`, the residue divided by `g` times `invMod (t / g)` modulo `m / g` |
| `divModRes moduli residues T` | division with remainder by `T`: the remainder from `evalMod`, and the quotient by subtracting it and dividing exactly by `T` |
| `addressRes moduli residues T` | the address `(k, i)` with respect to `T`, offsets counted `1, ..., T` |
| `sech x` | hyperbolic secant (`SechComb.lean`) |
| `sechComb s d t` | the sum of the `sech` pulses at scale `s` centred at the multiples of `d` around `t` (`SechComb.lean`) |
| `lastPeak s d t` | the last step up to `t` at which `sechComb s d` exceeds `1 / 2` (`SechComb.lean`) |
| `combResid s a b` | the residue of `a` modulo `b` read from the comb: the steps from the last peak for `b` up to `a` (`SechComb.lean`) |
| `sechRatio x y` | `2 x y / (x ^ 2 + y ^ 2)`, a pulse of the comb written in `x = exp s` (`SechRatio.lean`) |

## What is proved

| Step | File | Statement |
|---|---|---|
| T1 Residues | `Residues.lean` | `countMod d t = t % d` for every `d`, `d = 0` included; hence `resid a b = a % b` |
| T1w Sech comb | `SechComb.lean` | for scale `s ≥ 3` and every modulus `d ≥ 1`: `1 / 2 < sechComb s d t ↔ d ∣ t`; hence `combResid s a b = resid a b` for `b ≥ 1`; at `s = 2` the pulses for `d = 2` overlap and `combResid 2 3 2 ≠ resid 3 2` |
| T1w Ratio form | `SechRatio.lean` | `sech (a - b) = sechRatio (exp a) (exp b)`, so `sech (s (t - u)) = 2XY / (X² + Y²)` for `X = exp (s t)`, `Y = exp (s u)`; for `x, y > 0`: `sechRatio x y ≤ 1`, with equality iff `x = y`, so `sechRatio (x ^ n) y = 1 ↔ y = x ^ n`; the comb at scale `log x` is a sum of `sechRatio` of integer powers of `x`; `3 ≤ log x ↔ exp 3 ≤ x`, and for `x ≥ exp 3`: `1 / 2 < sechComb (log x) d t ↔ d ∣ t` |
| T2 Euclid | `Euclid.lean` | `euclid a b = Nat.gcd a b` |
| T3 Radices | `Radices.lean` | `prodMod radices c = radices.prod % c`; `gcdProd radices m = gcd (radices.prod) m`; the product of the radices of positive moduli is their least common multiple; `IrreducibleAfter before m ↔ Nat.Coprime (lcm of before) m` |
| T4 Consecutive moduli | `InitialModuli.lean` | for `n ≥ 2`: `newRadix (initialModuli n) n` is `p` when `n = p ^ k` is a prime power and `1` otherwise; `IrreducibleAfter (initialModuli n) n ↔ Nat.Prime n`; `Real.log (newRadix (initialModuli n) n) = Λ n` (von Mangoldt) |
| T5 Compare | `Compare.lean` | for positive moduli and residues `n % m`: `toMixedRadix` returns the mixed-radix digits of `n` modulo the lcm, on the radices `radices moduli`; `evalMod ds c = eval ds % c`; for `n, n'` below the lcm, `compareRes moduli (residues of n) (residues of n') = some (compare n n')` |
| T5c Blocks | `Blocks.lean` | a block of positive moduli with residues `n % m` is one modulus `lcm` with residue `n % lcm`; `flatten` gives every modulus `c` of the blocks and quotient blocks the residue `n % c`; below the lcm, `baseExtend` gives `n % c` on any modulus `c`; for `n` below the lcm of all moduli of its blocking and `n'` below that of its own, `compareBlocks (BlockRep.of n D K) (BlockRep.of n' D' K') = some (compare n n')` |
| T6 Primality | `Primality.lean` | for positive moduli with `n` and `2` below the lcm: every answer of `isPrimeRes` on the residues `n % c` is `Nat.Prime n`; it answers once `fuel > n`, or once `fuel > Nat.sqrt n` when `(Nat.sqrt n + 1) ^ 2` is below the lcm |
| T7 Interval atoms | `Atoms.lean` | `k ∈ intervalAtoms lo hi ↔ Nat.Prime k ∧ ∃ a, lo ≤ a ∧ k ∣ a ∧ a + k ≤ hi`: every atom is prime, and every prime with two consecutive multiples in the interval is an atom; an interval of length `L` gives every prime `p` with `2 * p ≤ L`; the atoms are exactly the differences no other difference divides, the atoms of the differences ordered by divisibility |
| T8 Arithmetic | `Arithmetic.lean` | for positive moduli and residues `x % m`, `y % m`: `addRes`, `mulRes`, `powRes` give the residues of `x + y`, `x * y`, `x ^ e`; `subRes` gives those of `x + (W - y)`, and of `x - y` when `y ≤ x` (`W` = the lcm); below the lcm, `addOverflow ↔ W ≤ x + y` and `subUnderflow ↔ x < y`; for `t ∣ x`, `exactDivRes` gives the residues of `x / t` on the moduli `m / gcd m t`, and `x / t` is below their lcm; `divModRes` gives `(x % T, residues of x / T)`; for `0 < x`, `addressRes` gives `i = (x - 1) % T + 1` and the residues of `k = (x - 1) / T + 1`, so `x = T * (k - 1) + i`; when `p ^ v` is the highest power of a prime `p` dividing `W`, the moduli `p ^ (v + 1), ..., p ^ (v + j)` multiply the lcm by `p ^ j` |
| T9 Multiplicative counting | `Multiplicative.lean` | `mulCount g q t = g ^ t % q`; for a prime `q` and a primitive root `g` modulo `q`: `mulCount g q t = mulCount g q u ↔ countMod (q - 1) t = countMod (q - 1) u`; every residue `0 < r < q` equals `mulCount g q t` for some `t < q - 1`; `mulCount g q t = 1 ↔ (q - 1) ∣ t`, which for `s ≥ 3` is `1 / 2 < sechComb s (q - 1) t`; for `q` odd and `q ∤ N`, if `mulCount g q t = N % q`, then `N` is a square modulo `q` iff `t` is even |

`FORMULAS.md` states the same results in standard notation, each with its Lean theorem;
`Latex/irreducibility.pdf` is the paper, with the definitions and the results.

T3 holds for any list of positive moduli, in any order. T4 is the special case of the
consecutive moduli `2, ..., n - 1`.

Each file also contains checks evaluated by the kernel (`decide`), e.g.
`radices [2, 3, 4, 5, 6, 7, 8, 9, 10] = [2, 3, 2, 5, 1, 7, 2, 3, 1]`.

The definitions assemble no number from residues beyond a modulus: `eval` is formed only as
the residue of a block modulus, which is below that modulus. `BlockRep.of`, which writes `n`
into blocks, appears only in statements.

## Repository layout

```
lean/                       Lean 4 project (lakefile.toml, lean-toolchain)
  Irreducibility.lean       root module, imports everything below
  Irreducibility/
    Defs.lean               the definitions (no Mathlib)
    Residues.lean           T1
    SechComb.lean           T1w
    SechRatio.lean          T1w ratio form
    Euclid.lean             T2
    Radices.lean            T3
    InitialModuli.lean      T4
    Compare.lean            T5
    Blocks.lean             T5c
    Primality.lean          T6
    Atoms.lean              T7
    Arithmetic.lean         T8
    Multiplicative.lean     T9
FORMULAS.md                 the proved statements in standard notation
Latex/                      the paper: irreducibility.tex and irreducibility.pdf
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
#print axioms Irreducibility.irreducibleAfter_initialModuli_iff
```
