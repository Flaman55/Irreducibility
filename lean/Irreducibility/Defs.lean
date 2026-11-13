module

/-!
# Moduli, residues and radices

Every object in this file is a modulus (a natural number) or a residue below a modulus.
No definition refers to primes, to factorization, or to a number assembled from residues.

* `countMod d t` -- the residue of `t` modulo `d`, obtained by counting alone: add `1` per
  step and reset to `0` on reaching `d`.
* `resid a b` -- the residue of `a` modulo `b`, that is `countMod b a`.
* `euclid a b` -- Euclid's algorithm computed with `resid` only.
* `prodMod radices c` -- the residue modulo `c` of the product of `radices`, computed factor
  by factor without forming the product.
* `gcdProd radices m` -- `euclid` of `prodMod radices m` and `m`, the gcd of `m` with the
  product of `radices`.
* `radices moduli` -- the mixed-radix system of `moduli` in order: modulus `m` receives the
  radix `m / gcdProd (radices so far) m`.
* `IrreducibleAfter before m` -- modulus `m` receives the radix `m`: no factor of it is
  covered by the moduli before it.
* `intervalAtoms lo hi` -- the differences `k` read from pairs of multiples of `k` in the
  interval `lo, ..., hi` that are divisible by no smaller difference kept before.
* `addRes`, `subRes`, `mulRes`, `powRes`, `exactDivRes`, `divModRes`, `addressRes` --
  arithmetic on residue vectors, modulus by modulus; `addOverflow` and `subUnderflow` detect
  a result outside `[0, lcm)` by comparing residue vectors.
-/

namespace Irreducibility

/-- The residue of `t` modulo `d` by counting: add `1` per step, reset to `0` on reaching
`d`. -/
@[expose] public def countMod (d : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => if countMod d t + 1 = d then 0 else countMod d t + 1

/-- The residue of `a` modulo `b`. -/
@[expose] public def resid (a b : Nat) : Nat := countMod b a

/-- Euclid's algorithm on residues, with a fuel bound; `euclid` supplies enough fuel. -/
@[expose] public def euclidAux : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | fuel + 1, a, b => if b = 0 then a else euclidAux fuel b (resid a b)

/-- The greatest common divisor of `a` and `b` by Euclid's algorithm on residues. -/
@[expose] public def euclid (a b : Nat) : Nat := euclidAux (b + 1) a b

/-- The residue modulo `c` of the product of `radices`, factor by factor. -/
@[expose] public def prodMod : List Nat → Nat → Nat
  | [], c => 1 % c
  | r :: rs, c => (resid r c * prodMod rs c) % c

/-- The gcd of `m` with the product of `radices`: Euclid's algorithm on `m` and the residue
of the product modulo `m`; the product itself is never formed. -/
@[expose] public def gcdProd (radices : List Nat) (m : Nat) : Nat :=
  euclid (prodMod radices m) m

/-- The radices of the mixed-radix system of `moduli` in order: each modulus `m` receives
`m` divided by its gcd with the product of the radices before it. -/
@[expose] public def radices (moduli : List Nat) : List Nat :=
  moduli.foldl (fun acc m => acc ++ [m / gcdProd acc m]) []

/-- The radix modulus `m` receives after the moduli `before`. -/
@[expose] public def newRadix (before : List Nat) (m : Nat) : Nat :=
  m / gcdProd (radices before) m

/-- Modulus `m` is irreducible after `before`: it receives the radix `m`. -/
@[expose] public def IrreducibleAfter (before : List Nat) (m : Nat) : Prop :=
  newRadix before m = m

/-- The consecutive moduli `2, 3, ..., n - 1`. -/
@[expose] public def initialModuli (n : Nat) : List Nat := (List.range n).drop 2

/-! ## Mixed-radix representations

A mixed-radix representation is a list of pairs `(digit, radix)`, least significant first. -/

/-- The residue modulo `c` of the value of a mixed-radix representation, by Horner's rule
from the most significant digit, with every radix reduced modulo `c`. -/
@[expose] public def evalMod : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (d, r) :: rest, c => (d + resid r c * evalMod rest c) % c

/-- Add `step` modulo `b` to `cur`, at most `fuel` more times; the number of additions after
which the residue first equals `1`. -/
@[expose] public def invModAux (step b : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, t, cur =>
    if (cur + step) % b = 1 then t + 1 else invModAux step b fuel (t + 1) ((cur + step) % b)

/-- The least `x ≥ 1` with `x * a ≡ 1 (mod b)`, found by repeated addition of `a` modulo `b`;
`0` when `b = 1` or no such `x ≤ b` exists. -/
@[expose] public def invMod (a b : Nat) : Nat :=
  if b = 1 then 0 else invModAux (resid a b) b b 0 0

/-- The digit and radix that modulus `m` with residue `s` appends to the mixed-radix
representation `acc` (Garner's step on arbitrary moduli); `none` when `s` is incompatible
with the residues already represented. -/
@[expose] public def digitStep (acc : List (Nat × Nat)) (m s : Nat) : Option (Nat × Nat) :=
  let g := gcdProd (acc.map Prod.snd) m
  let r := m / g
  let y := (s + m - evalMod acc m) % m
  if y % g = 0 then
    some (if 1 < r then (y / g * invMod (prodMod (acc.map Prod.snd) m / g % r) r % r, r)
      else (0, r))
  else none

/-- The mixed-radix representation given by residues, extended modulus by modulus from
`acc`. -/
@[expose] public def toMixedRadixAux : List (Nat × Nat) → List Nat → List Nat →
    Option (List (Nat × Nat))
  | acc, m :: ms, s :: ss =>
    match digitStep acc m s with
    | none => none
    | some dr => toMixedRadixAux (acc ++ [dr]) ms ss
  | acc, _, _ => some acc

/-- The mixed-radix representation of the residues `residues` on `moduli`. -/
@[expose] public def toMixedRadix (moduli residues : List Nat) : Option (List (Nat × Nat)) :=
  toMixedRadixAux [] moduli residues

/-- Compare two mixed-radix representations with the same radices, digit by digit from the
most significant. -/
@[expose] public def compareDigits : List (Nat × Nat) → List (Nat × Nat) → Ordering
  | (a, _) :: as, (b, _) :: bs =>
    match compareDigits as bs with
    | .eq => compare a b
    | o => o
  | _, _ => .eq

/-- Compare two residue vectors on the same moduli: convert both to mixed radix, then compare
from the most significant digit. -/
@[expose] public def compareRes (moduli xs ys : List Nat) : Option Ordering :=
  match toMixedRadix moduli xs, toMixedRadix moduli ys with
  | some dx, some dy => some (compareDigits dx dy)
  | _, _ => none

/-! ## Blocks

A block is a list of moduli used as one modulus: its modulus is the lcm of its members, and its
residue is the value of the mixed-radix representation of the member residues. A number in
block representation is given by the member residues of its blocks and, for the quotient of
the number by the lcm of those blocks, the member residues of its quotient blocks. -/

/-- The value of a mixed-radix representation, below the product of its radices. -/
@[expose] public def eval : List (Nat × Nat) → Nat
  | [] => 0
  | (d, r) :: rest => d + r * eval rest

/-- A block as one modulus: the product of the radices of its members and the value of their
mixed-radix representation; `none` for incompatible member residues. -/
@[expose] public def blockModulus (moduli residues : List Nat) : Option (Nat × Nat) :=
  match toMixedRadix moduli residues with
  | some ds => some (ds.foldr (fun p acc => p.2 * acc) 1, eval ds)
  | none => none

/-- The block moduli and block residues of a list of blocks. -/
@[expose] public def blockModuli : List (List Nat) → List (List Nat) →
    Option (List Nat × List Nat)
  | p :: ps, s :: ss =>
    match blockModulus p s, blockModuli ps ss with
    | some (c, x), some (cs, xs) => some (c :: cs, x :: xs)
    | _, _ => none
  | _, _ => some ([], [])

/-- A number in block representation: member residues of `blocks`, and member residues of
`quotBlocks` for the quotient of the number by the lcm of the block moduli of `blocks`. -/
public structure BlockRep where
  blocks : List (List Nat)
  residues : List (List Nat)
  quotBlocks : List (List Nat)
  quotResidues : List (List Nat)

/-- Base extension: the residues on `target` of the number given by `residues` on
`moduli`. -/
@[expose] public def baseExtend (moduli residues target : List Nat) : Option (List Nat) :=
  match toMixedRadix moduli residues with
  | some ds => some (target.map (evalMod ds))
  | none => none

/-- One list of moduli for blocks and quotient blocks: a quotient block of modulus `c` with
residue `k` receives the residue `k * L + r` modulo `c`, where `L` is the lcm of the blocks
and `r` the value of their mixed-radix representation. -/
@[expose] public def flatten (x : BlockRep) : Option (List Nat × List Nat) :=
  match blockModuli x.blocks x.residues, blockModuli x.quotBlocks x.quotResidues with
  | some (dr, ds), some (kr, ks) =>
    match toMixedRadix dr ds with
    | some dd => some (dr ++ kr, ds ++ (kr.zip ks).map fun (c, k) =>
        (k * prodMod (dd.map Prod.snd) c + evalMod dd c) % c)
    | none => none
  | _, _ => none

/-- The moduli of `rx` followed by the moduli of `ry` not among them. -/
@[expose] public def union (rx ry : List Nat) : List Nat :=
  rx ++ ry.filter fun c => !rx.contains c

/-- Compare two numbers in different block representations: flatten both, extend both to the
union of their moduli, then compare residue vectors. -/
@[expose] public def compareBlocks (x y : BlockRep) : Option Ordering :=
  match flatten x, flatten y with
  | some (rx, sx), some (ry, sy) =>
    match baseExtend rx sx (union rx ry), baseExtend ry sy (union rx ry) with
    | some ex, some ey => compareRes (union rx ry) ex ey
    | _, _ => none
  | _, _ => none

/-! ## Primality on residues

A number is given by its residues. Trial divisors `m = 2, 3, ...` are compared with it through
their own residue vectors `m % c` and `m * m % c`, and the residue of the number modulo `m` is
computed from its mixed-radix representation. -/

/-- Try divisors `m, m + 1, ...`, at most `fuel` of them, against the number given by
`residues` on `moduli` with mixed-radix representation `ds`: `true` when `m` equals the number
or `m * m` exceeds it, `false` when the number is below `m` or divisible by `m`; `none` when
the fuel runs out or the residues are incompatible. -/
@[expose] public def isPrimeResAux (moduli residues : List Nat) (ds : List (Nat × Nat)) :
    Nat → Nat → Option Bool
  | 0, _ => none
  | fuel + 1, m =>
    match compareRes moduli (moduli.map (resid m)) residues with
    | some .eq => some true
    | some .gt => some false
    | some .lt =>
      match compareRes moduli (moduli.map fun c => resid m c * resid m c % c) residues with
      | some .gt => some true
      | some _ =>
        if evalMod ds m = 0 then some false else isPrimeResAux moduli residues ds fuel (m + 1)
      | none => none
    | none => none

/-- Whether the number given by `residues` on `moduli` is prime, trying at most `fuel`
divisors from `2` on. -/
@[expose] public def isPrimeRes (fuel : Nat) (moduli residues : List Nat) : Option Bool :=
  match toMixedRadix moduli residues with
  | some ds => isPrimeResAux moduli residues ds fuel 2
  | none => none

/-! ## Atoms of an interval

An interval is the run of consecutive integers `lo, ..., hi`. A difference `k` is read from two
elements `a` and `a + k` of the interval with `k ∣ a`: then `k` divides both. -/

/-- The least multiple of `k` that is at least `lo`, from one residue. -/
@[expose] public def firstMultipleFrom (lo k : Nat) : Nat :=
  if resid lo k = 0 then lo else lo + (k - resid lo k)

/-- Append `k` to the atoms found so far when the interval `lo, ..., hi` contains `a` and
`a + k` with `k ∣ a`, and no atom found so far divides `k`. -/
@[expose] public def atomStep (lo hi : Nat) (atoms : List Nat) (k : Nat) : List Nat :=
  if firstMultipleFrom lo k + k ≤ hi ∧ atoms.all (fun p => resid k p != 0) = true then
    atoms ++ [k]
  else atoms

/-- The atoms of the interval `lo, ..., hi`: the differences `2, ..., hi - lo` in order, each
kept by `atomStep`. -/
@[expose] public def intervalAtoms (lo hi : Nat) : List Nat :=
  (initialModuli (hi - lo + 1)).foldl (atomStep lo hi) []

/-! ## Arithmetic on residues

A number on `moduli` is given by one residue per modulus. Sums, differences, products and
powers are computed modulus by modulus and give the result modulo the lcm of the moduli;
overflow of a sum and underflow of a difference are detected by comparing residue vectors. -/

/-- Apply `f m a b` for each modulus `m` to its residues `a` and `b`. -/
@[expose] public def pointwise (f : Nat → Nat → Nat → Nat) :
    List Nat → List Nat → List Nat → List Nat
  | m :: rs, a :: xs, b :: ys => f m a b :: pointwise f rs xs ys
  | _, _, _ => []

/-- The sum of two numbers, modulus by modulus. -/
@[expose] public def addRes (moduli xs ys : List Nat) : List Nat :=
  pointwise (fun m a b => (a + b) % m) moduli xs ys

/-- The difference of two numbers, modulus by modulus: `(a + (m - b)) % m`. -/
@[expose] public def subRes (moduli xs ys : List Nat) : List Nat :=
  pointwise (fun m a b => (a + (m - b)) % m) moduli xs ys

/-- The sum overflows the lcm of the moduli: its residue vector compares below that of the
first term. -/
@[expose] public def addOverflow (moduli xs ys : List Nat) : Bool :=
  decide (compareRes moduli (addRes moduli xs ys) xs = some .lt)

/-- The difference underflows `0`: the first term compares below the second. -/
@[expose] public def subUnderflow (moduli xs ys : List Nat) : Bool :=
  decide (compareRes moduli xs ys = some .lt)

/-- The product of two numbers, modulus by modulus. -/
@[expose] public def mulRes (moduli xs ys : List Nat) : List Nat :=
  pointwise (fun m a b => a * b % m) moduli xs ys

/-- The `e`-th power of a number: `e` products modulus by modulus, starting from the residues
of `1`. -/
@[expose] public def powRes (moduli xs : List Nat) : Nat → List Nat
  | 0 => moduli.map (resid 1 ·)
  | e + 1 => mulRes moduli (powRes moduli xs e) xs

/-- The moduli of the quotient by `t`: each modulus `m` becomes `m / gcd(m, t)`. -/
@[expose] public def divModuli (moduli : List Nat) (t : Nat) : List Nat :=
  moduli.map fun m => m / euclid m t

/-- Exact division by `t`, modulus by modulus: for modulus `m` and `g = gcd(m, t)`, the
residue divided by `g` is multiplied by the inverse of `t / g` modulo `m / g`. -/
@[expose] public def exactDivRes (moduli residues : List Nat) (t : Nat) : List Nat :=
  List.zipWith (fun m s =>
    let g := euclid m t
    let r := m / g
    s / g * invMod (t / g % r) r % r) moduli residues

/-- Division with remainder by `T` on residues: the remainder `r`, computed from the
mixed-radix representation, and the residues of the quotient, obtained by subtracting `r`
modulus by modulus and dividing exactly by `T`. -/
@[expose] public def divModRes (moduli residues : List Nat) (T : Nat) : Option (Nat × List Nat) :=
  match toMixedRadix moduli residues with
  | some ds =>
    let r := evalMod ds T
    some (r, exactDivRes moduli (subRes moduli residues (moduli.map (resid r ·))) T)
  | none => none

/-- The address `(k, i)` of a number with respect to `T`, offsets counted `1, ..., T`: the
offset `i`, and the residues of the block index `k` on the moduli `divModuli moduli T`. -/
@[expose] public def addressRes (moduli residues : List Nat) (T : Nat) : Option (Nat × List Nat) :=
  match divModRes moduli residues T with
  | some (r, qs) =>
    if r = 0 then some (T, qs)
    else some (r, addRes (divModuli moduli T) qs ((divModuli moduli T).map (resid 1 ·)))
  | none => none

/-! ## Checks by evaluation (kernel `decide`, no extra axioms) -/

example : resid 17 5 = 2 := by decide
example : euclid 12 18 = 6 := by decide
example : radices [2, 3, 4, 5, 6, 7, 8, 9, 10] = [2, 3, 2, 5, 1, 7, 2, 3, 1] := by decide
example : radices [6, 35] = [6, 35] := by decide
example : radices [4, 4] = [4, 1] := by decide
example : toMixedRadix [2, 3, 4, 5] [1, 1, 1, 2] = some [(1, 2), (0, 3), (0, 2), (3, 5)] := by
  decide
example : toMixedRadix [6, 4, 9] [4, 0, 1] = some [(4, 6), (0, 2), (2, 3)] := by decide
example : toMixedRadix [4, 4, 6] [3, 3, 1] = some [(3, 4), (0, 1), (1, 3)] := by decide
example : toMixedRadix [2, 4] [1, 2] = none := by decide
example : compareRes [2, 3, 4, 5] [1, 1, 1, 2] [0, 2, 2, 3] = some .lt := by decide
example : compareRes [2, 3, 4, 5] [1, 1, 1, 2] [1, 1, 1, 2] = some .eq := by decide
example : compareRes [6, 4, 9] [4, 0, 1] [3, 3, 0] = some .gt := by decide

example : blockModulus [2, 3, 4] [1, 2, 3] = some (12, 11) := by decide
example : blockModulus [4, 6] [3, 1] = some (12, 7) := by decide
example : blockModulus [2, 4] [1, 2] = none := by decide
example : blockModuli [[2, 3], [4, 5]] [[1, 2], [3, 4]] = some ([6, 20], [5, 19]) := by decide
example : baseExtend [6, 20, 7, 8] [4, 0, 2, 4] [9, 5] = some [1, 0] := by decide
example : flatten ⟨[[2, 3], [4, 5]], [[0, 1], [0, 0]], [[7, 8]], [[1, 1]]⟩ =
    some ([6, 20, 56], [4, 0, 44]) := by decide
example : flatten ⟨[[2, 3, 4], [5]], [[1, 2, 1], [1]], [[7], [9]], [[1], [1]]⟩ =
    some ([12, 5, 7, 9], [5, 1, 3, 2]) := by decide
set_option maxRecDepth 20000 in
example : compareBlocks ⟨[[2, 3], [4, 5]], [[0, 1], [0, 0]], [[7, 8]], [[1, 1]]⟩
    ⟨[[2, 3, 4], [5]], [[1, 2, 1], [1]], [[7], [9]], [[1], [1]]⟩ = some .lt := by decide
set_option maxRecDepth 20000 in
example : compareBlocks ⟨[[2, 3, 4], [5]], [[1, 2, 1], [1]], [[7], [9]], [[1], [1]]⟩
    ⟨[[2, 3], [4, 5]], [[0, 1], [0, 0]], [[7, 8]], [[1, 1]]⟩ = some .gt := by decide
set_option maxRecDepth 20000 in
example : compareBlocks ⟨[[2, 3], [4, 5]], [[0, 1], [0, 0]], [[7, 8]], [[1, 1]]⟩
    ⟨[[2, 3, 4], [5]], [[0, 1, 0], [0]], [[7], [9]], [[1], [1]]⟩ = some .eq := by decide

example : isPrimeRes 20 [4, 3, 5, 7] [1, 1, 2, 6] = some true := by decide
example : isPrimeRes 20 [4, 3, 5, 7] [3, 1, 1, 0] = some false := by decide
example : isPrimeRes 20 [4, 3, 5, 7] [1, 1, 1, 2] = some false := by decide
example : isPrimeRes 20 [4, 3, 5, 7] [1, 2, 3, 1] = some true := by decide
example : isPrimeRes 20 [4, 3, 5, 7] [2, 2, 2, 2] = some true := by decide
example : isPrimeRes 20 [4, 3, 5, 7] [1, 1, 1, 1] = some false := by decide
example : isPrimeRes 20 [4, 3, 5, 7] [0, 0, 0, 0] = some false := by decide
example : isPrimeRes 3 [4, 3, 5, 7] [1, 1, 2, 6] = none := by decide
example : isPrimeRes 20 [6, 4, 9, 5] [1, 1, 7, 4] = some false := by decide
example : isPrimeRes 20 [6, 4, 9, 5] [5, 1, 2, 3] = none := by decide
set_option maxRecDepth 20000 in
example : isPrimeRes 200 [6, 4, 9, 5] [5, 1, 2, 3] = some true := by decide
example : isPrimeRes 20 [2, 4] [1, 2] = none := by decide

set_option maxRecDepth 20000 in
example : intervalAtoms 50 60 = [2, 3, 5] := by decide
set_option maxRecDepth 20000 in
example : intervalAtoms 100 130 = [2, 3, 5, 7, 11, 13, 17] := by decide
set_option maxRecDepth 20000 in
example : intervalAtoms 2 60 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29] := by decide
example : intervalAtoms 7 7 = [] := by decide
example : intervalAtoms 9 3 = [] := by decide

example : addRes [4, 3, 5] [2, 2, 0] [0, 2, 0] = [2, 1, 0] := by decide
example : addOverflow [4, 3, 5] [2, 2, 0] [0, 2, 0] = true := by decide
example : addOverflow [4, 3, 5] [0, 2, 0] [2, 0, 0] = false := by decide
example : subRes [4, 3, 5] [0, 2, 0] [2, 2, 0] = [2, 0, 0] := by decide
example : subUnderflow [4, 3, 5] [0, 2, 0] [2, 2, 0] = true := by decide
example : subUnderflow [4, 3, 5] [2, 2, 0] [0, 2, 0] = false := by decide
example : mulRes [4, 3, 5] [3, 1, 2] [1, 0, 4] = [3, 0, 3] := by decide
example : powRes [4, 3, 5] [3, 1, 2] 2 = [1, 1, 4] := by decide
example : powRes [4, 3, 5] [3, 1, 2] 0 = [1, 1, 1] := by decide
example : divModuli [4, 3, 5] 6 = [2, 1, 5] := by decide
example : exactDivRes [4, 3, 5] [2, 0, 2] 6 = [1, 0, 2] := by decide
example : divModRes [4, 3, 5] [3, 2, 2] 6 = some (5, [1, 0, 2]) := by decide
example : addressRes [4, 3, 5] [3, 2, 2] 6 = some (5, [0, 0, 3]) := by decide
example : addressRes [4, 3, 5] [2, 0, 2] 6 = some (6, [1, 0, 2]) := by decide

end Irreducibility
