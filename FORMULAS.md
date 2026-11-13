# Formulas

The statements proved in `lean/`, written in standard notation. Each formula names the Lean
theorem that proves it. Hypotheses are listed in full; nothing here is weaker or stronger than
the Lean statement.

## Notation

- $x \bmod 0 = x$ (the Lean convention); $\lfloor \cdot \rfloor$ is integer division.
- $R = (r_1, \dots, r_k)$ is a list of moduli. "Positive moduli" means every $r_i \ge 1$.
- $W(R) = \mathrm{lcm}(r_1, \dots, r_k)$, and $W = 1$ for the empty list.
- The residue vector of $x$ on $R$: $[x]_R = (x \bmod r_1, \dots, x \bmod r_k)$.
- $\prod R = r_1 \cdots r_k$.
- $(R, m_1, \dots, m_j)$ is the list $R$ followed by $m_1, \dots, m_j$.
- A mixed-radix representation is a list $(d_1, s_1), \dots, (d_k, s_k)$ of pairs (digit,
  radix), least significant first.
- $\Lambda$ is the von Mangoldt function.

## T1 Residues (`Residues.lean`)

For every $d$ and $t$, $d = 0$ included:

$$\mathrm{countMod}(d, t) = t \bmod d$$

(`countMod_eq_mod`)

$$\mathrm{resid}(a, b) = a \bmod b$$

(`resid_eq_mod`)

## T1w Sech comb (`SechComb.lean`)

$$\mathrm{sech}(x) = \frac{1}{\cosh(x)}, \qquad
C_{s,d}(t) = \sum_{i=-1}^{2} \mathrm{sech}\Big(s \big(t - d (\lfloor t/d \rfloor + i)\big)\Big)$$

For scale $s \ge 3$, every modulus $d \ge 1$ and every $t$:

$$C_{s,d}(t) > \tfrac{1}{2} \iff d \mid t$$

(`one_half_lt_sechComb_iff`)

Hence the last peak for $d$ up to $t$ is $d \lfloor t/d \rfloor$, and for $b \ge 1$:

$$\mathrm{combResid}_s(a, b) = a - b \lfloor a/b \rfloor = \mathrm{resid}(a, b)$$

(`combResid_eq`)

At $s = 2$ the reading fails: $\mathrm{combResid}_2(3, 2) = 0 \ne 1 = \mathrm{resid}(3, 2)$
(`combResid_two_ne`).

## T2 Euclid (`Euclid.lean`)

$$\mathrm{euclid}(a, b) = \gcd(a, b)$$

(`euclid_eq_gcd`)

## T3 Radices (`Radices.lean`)

For any list $R$ and any $c, m$:

$$\mathrm{prodMod}(R, c) = \textstyle\prod R \bmod c$$

(`prodMod_eq`)

$$\mathrm{gcdProd}(R, m) = \gcd\big(\textstyle\prod R, m\big)$$

(`gcdProd_eq`)

$$\mathrm{radices}(R, m) = \Big(\mathrm{radices}(R),\ \frac{m}{\gcd\big(\prod \mathrm{radices}(R), m\big)}\Big)$$

(`radices_append`)

For positive moduli $R$ and a list $B$ of positive moduli:

$$\textstyle\prod \mathrm{radices}(R) = W(R)$$

(`prod_radices`)

$$\mathrm{newRadix}(B, m) = \frac{m}{\gcd(W(B), m)}$$

(`newRadix_eq`)

and for $m \ge 1$:

$$\mathrm{IrreducibleAfter}(B, m) \iff \gcd(W(B), m) = 1$$

(`irreducibleAfter_iff`)

## T4 Consecutive moduli (`InitialModuli.lean`)

$\mathrm{initialModuli}(n) = (2, 3, \dots, n - 1)$ (`mem_initialModuli`). For $n \ge 2$:

$$\mathrm{newRadix}(\mathrm{initialModuli}(n), n) =
\begin{cases} p & n = p^k,\ p \text{ prime},\ k \ge 1 \cr 1 & \text{otherwise} \end{cases}$$

(`newRadix_initialModuli`)

$$\mathrm{IrreducibleAfter}(\mathrm{initialModuli}(n), n) \iff n \text{ is prime}$$

(`irreducibleAfter_initialModuli_iff`)

$$\log \mathrm{newRadix}(\mathrm{initialModuli}(n), n) = \Lambda(n)$$

(`log_newRadix_initialModuli`)

## T5 Compare (`Compare.lean`)

The value of a mixed-radix representation:

$$\mathrm{eval}\big((d_1, s_1), \dots, (d_k, s_k)\big) = \sum_{i=1}^{k} d_i \prod_{j < i} s_j$$

(`eval_append`)

$$\mathrm{evalMod}(D, c) = \mathrm{eval}(D) \bmod c$$

(`evalMod_eq`)

For $b > 1$ and $\gcd(a, b) = 1$:

$$a \cdot \mathrm{invMod}(a, b) \equiv 1 \pmod b$$

(`invMod_spec`)

For positive moduli $R$ and every $n$ there is a mixed-radix representation
$D = (d_i, s_i)_i$ with

$$\mathrm{toMixedRadix}(R, [n]_R) = D, \quad (s_i)_i = \mathrm{radices}(R), \quad d_i < s_i, \quad
\mathrm{eval}(D) = n \bmod W(R)$$

(`toMixedRadix_spec`)

For positive moduli $R$ and $n, n' < W(R)$:

$$\mathrm{compareRes}(R, [n]_R, [n']_R) = \mathrm{compare}(n, n')$$

(`compareRes_eq`)

## T5c Blocks (`Blocks.lean`)

For positive moduli $M$ (the members of a block):

$$\mathrm{blockModulus}(M, [n]_M) = \big(W(M),\ n \bmod W(M)\big)$$

(`blockModulus_spec`)

and for blocks $P_1, \dots, P_k$ of positive moduli, the block moduli are
$W(P_1), \dots, W(P_k)$ with residues $n \bmod W(P_i)$ (`blockModuli_spec`).

For positive moduli $R$, any moduli $T$ and $n < W(R)$:

$$\mathrm{baseExtend}(R, [n]_R, T) = [n]_T$$

(`baseExtend_spec`)

For blocks $D_1, \dots, D_a$ and quotient blocks $K_1, \dots, K_b$ of positive moduli, with
$Q = \big(W(D_1), \dots, W(D_a), W(K_1), \dots, W(K_b)\big)$:

$$\mathrm{flatten}(\mathrm{BlockRep.of}(n, D, K)) = (Q, [n]_Q)$$

(`flatten_spec`)

If moreover $n$ is below the lcm of all moduli of $D, K$ and $n'$ below the lcm of all moduli of
$D', K'$:

$$\mathrm{compareBlocks}\big(\mathrm{BlockRep.of}(n, D, K),\ \mathrm{BlockRep.of}(n', D', K')\big)
= \mathrm{compare}(n, n')$$

(`compareBlocks_eq`)

## T6 Primality (`Primality.lean`)

For positive moduli $R$ with $n < W(R)$ and $2 < W(R)$: every answer $b$ of
$\mathrm{isPrimeRes}(\mathrm{fuel}, R, [n]_R)$ is true exactly when $n$ is prime (`isPrimeRes_sound`),
and an answer is given once

$$\mathrm{fuel} > n \quad\text{or}\quad
\Big(\mathrm{fuel} > \lfloor\sqrt n\rfloor \ \text{and}\ \big(\lfloor\sqrt n\rfloor + 1\big)^2 < W(R)\Big)$$

(`isPrimeRes_eq`)

## T7 Interval atoms (`Atoms.lean`)

For $k \ge 1$, $\mathrm{firstMultipleFrom}(lo, k)$ is the least multiple of $k$ that is
$\ge lo$, and it lies in $[lo, lo + k)$ (`firstMultipleFrom_spec`).

$$k \in \mathrm{intervalAtoms}(lo, hi) \iff k \text{ is prime} \ \wedge\
\exists a:\ lo \le a,\ k \mid a,\ a + k \le hi$$

(`mem_intervalAtoms`)

So every atom is prime (`prime_of_mem_intervalAtoms`), and for a prime $p$:

$$lo + 2p \le hi + 1 \implies p \in \mathrm{intervalAtoms}(lo, hi)$$

(`prime_mem_intervalAtoms`)

## T8 Arithmetic (`Arithmetic.lean`)

Write $W = W(R)$. For any moduli $R$ and all $x, y, e$:

$$\mathrm{addRes}(R, [x]_R, [y]_R) = [x + y]_R, \quad
\mathrm{mulRes}(R, [x]_R, [y]_R) = [x y]_R, \quad
\mathrm{powRes}(R, [x]_R, e) = [x^e]_R$$

(`addRes_spec`, `mulRes_spec`, `powRes_spec`). From here on $R$ is a list of positive moduli.

$$y \le x \implies \mathrm{subRes}(R, [x]_R, [y]_R) = [x - y]_R$$

(`subRes_spec_of_le`)

$$y \le W \implies \mathrm{subRes}(R, [x]_R, [y]_R) = [x + (W - y)]_R$$

(`subRes_spec`)

For $x, y < W$:

$$\mathrm{addOverflow}(R, [x]_R, [y]_R) \iff W \le x + y, \qquad
\mathrm{subUnderflow}(R, [x]_R, [y]_R) \iff x < y$$

(`addOverflow_iff`, `subUnderflow_iff`). Exact division: for $t \ge 1$ with $t \mid x$, and
$R/t = \big(r_i / \gcd(r_i, t)\big)_i$ (`divModuli`):

$$\mathrm{exactDivRes}(R, [x]_R, t) = [x / t]_{R/t}$$

(`exactDivRes_spec`)

$$x < W \implies x / t < W(R/t)$$

(`div_lt_divModuli`)

For $T \ge 1$ and $x < W$:

$$\mathrm{divModRes}(R, [x]_R, T) = \big(x \bmod T,\ [\lfloor x / T \rfloor]_{R/T}\big)$$

(`divModRes_spec`)

and for $0 < x < W$, with $i = (x - 1) \bmod T + 1$ and $k = \lfloor (x - 1)/T \rfloor + 1$,
so that $x = T (k - 1) + i$ and $1 \le i \le T$:

$$\mathrm{addressRes}(R, [x]_R, T) = \big(i,\ [k]_{R/T}\big)$$

(`addressRes_spec`)

Appending prime powers: for any moduli $R$, a prime $p$ with $p^v \mid W$ and $p^{v+1} \nmid W$, and every $j$:

$$W\big(R, p^{v+1}, p^{v+2}, \dots, p^{v+j}\big) = p^j W(R)$$

(`lcm_append_prime_powers`)
