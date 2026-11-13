# Formulas

The statements proved in `lean/`, written in standard notation. Each formula names the Lean
theorem that proves it. Hypotheses are listed in full; nothing here is weaker or stronger than
the Lean statement.

## Notation

- $x \bmod 0 = x$ (the Lean convention); $\lfloor \cdot \rfloor$ is integer division.
- A drum is a list of rings $R = (r_1, \dots, r_k)$. "Positive rings" means every $r_i \ge 1$.
- The turn of $R$: $W(R) = \operatorname{lcm}(r_1, \dots, r_k)$, with $W(\,) = 1$.
- The states of $x$ on $R$: $[x]_R = (x \bmod r_1, \dots, x \bmod r_k)$.
- $\prod R = r_1 \cdots r_k$.
- A drum position is a list of levels $(d_1, s_1), \dots, (d_k, s_k)$ (digit, size).
- $\Lambda$ is the von Mangoldt function.

## T1 Ticking (`Ticking.lean`)

For every $d$ and $t$, ring $d = 0$ included:

$$\mathrm{pos}(d, t) = t \bmod d \qquad \texttt{pos\_eq\_mod}$$

$$\mathrm{relation}(a, b) = a \bmod b \qquad \texttt{relation\_eq\_mod}$$

## T1w Waves (`Waves.lean`)

$$\operatorname{sech} x = \frac{1}{\cosh x}, \qquad
C_{s,d}(t) = \sum_{i=-1}^{2} \operatorname{sech}\!\Big(s \big(t - d (\lfloor t/d \rfloor + i)\big)\Big)$$

For sharpness $s \ge 3$, every ring $d \ge 1$ and every tick $t$:

$$C_{s,d}(t) > \tfrac{1}{2} \iff d \mid t \qquad \texttt{one\_half\_lt\_comb\_iff}$$

Hence the last peak of ring $d$ up to $t$ is $d \lfloor t/d \rfloor$, and for $b \ge 1$:

$$\mathrm{waveRelation}_s(a, b) = a - b \lfloor a/b \rfloor = \mathrm{relation}(a, b)
\qquad \texttt{waveRelation\_eq}$$

At $s = 2$ the reading fails: $\mathrm{waveRelation}_2(3, 2) = 0 \ne 1 = \mathrm{relation}(3, 2)$
(`waveRelation_two_ne`).

## T2 Euclid (`Euclid.lean`)

$$\mathrm{commonPart}(a, b) = \gcd(a, b) \qquad \texttt{commonPart\_eq\_gcd}$$

## T3 Drum (`Drum.lean`)

For any list $R$ and any $c, m$:

$$\mathrm{turnOn}(R, c) = \textstyle\prod R \bmod c \qquad \texttt{turnOn\_eq}$$

$$\mathrm{commonPartWithTurn}(R, m) = \gcd\!\big(\textstyle\prod R,\, m\big)
\qquad \texttt{commonPartWithTurn\_eq}$$

$$\mathrm{levels}(R \mathbin{+\!\!+} [m]) = \mathrm{levels}(R) \mathbin{+\!\!+}
\Big[\frac{m}{\gcd\!\big(\prod \mathrm{levels}(R),\, m\big)}\Big] \qquad \texttt{levels\_append}$$

For positive rings $R$ and a list $B$ of positive rings:

$$\textstyle\prod \mathrm{levels}(R) = W(R) \qquad \texttt{prod\_levels}$$

$$\mathrm{levelSize}(B, m) = \frac{m}{\gcd(W(B), m)} \qquad \texttt{levelSize\_eq}$$

and for $m \ge 1$:

$$\mathrm{IrreducibleAfter}(B, m) \iff \gcd(W(B), m) = 1 \qquad \texttt{irreducibleAfter\_iff}$$

## T4 Consecutive rings (`Bridge.lean`)

$\mathrm{ringsBelow}(n) = (2, 3, \dots, n - 1)$ (`mem_ringsBelow`). For $n \ge 2$:

$$\mathrm{levelSize}(\mathrm{ringsBelow}(n), n) =
\begin{cases} p & n = p^k,\ p \text{ prime},\ k \ge 1 \\ 1 & \text{otherwise} \end{cases}
\qquad \texttt{levelSize\_ringsBelow}$$

$$\mathrm{IrreducibleAfter}(\mathrm{ringsBelow}(n), n) \iff n \text{ is prime}
\qquad \texttt{irreducibleAfter\_ringsBelow\_iff}$$

$$\log \mathrm{levelSize}(\mathrm{ringsBelow}(n), n) = \Lambda(n)
\qquad \texttt{log\_levelSize\_ringsBelow}$$

## T5 Compare (`Compare.lean`)

The value of a drum position, read in mixed radix from the bottom level:

$$\mathrm{value}\big((d_1, s_1), \dots, (d_k, s_k)\big) = \sum_{i=1}^{k} d_i \prod_{j < i} s_j
\qquad \texttt{value\_append}$$

$$\mathrm{positionOn}(D, c) = \mathrm{value}(D) \bmod c \qquad \texttt{positionOn\_eq}$$

For $b > 1$ and $\gcd(a, b) = 1$:

$$a \cdot \mathrm{inverse}(a, b) \equiv 1 \pmod b \qquad \texttt{inverse\_spec}$$

For positive rings $R$ and every $n$ there is a drum position $D = (d_i, s_i)_i$ with

$$\mathrm{digitsOf}(R, [n]_R) = D, \quad (s_i)_i = \mathrm{levels}(R), \quad d_i < s_i, \quad
\mathrm{value}(D) = n \bmod W(R) \qquad \texttt{digitsOf\_spec}$$

For positive rings $R$ and $n, n' < W(R)$:

$$\mathrm{compareOn}(R, [n]_R, [n']_R) = \mathrm{compare}(n, n') \qquad \texttt{compareOn\_eq}$$

## T5c Packs (`Packs.lean`)

For positive rings $M$ (the members of a pack):

$$\mathrm{packRing}(M, [n]_M) = \big(W(M),\ n \bmod W(M)\big) \qquad \texttt{packRing\_spec}$$

and for packs $P_1, \dots, P_k$ of positive rings, the drum of packs is the drum of rings
$W(P_1), \dots, W(P_k)$ in states $n \bmod W(P_i)$ (`drumOfPacks_spec`).

For positive rings $R$, any rings $T$ and $n < W(R)$:

$$\mathrm{extend}(R, [n]_R, T) = [n]_T \qquad \texttt{extend\_spec}$$

For packs $D_1, \dots, D_a$ and rotation packs $K_1, \dots, K_b$ of positive rings, with
$Q = \big(W(D_1), \dots, W(D_a), W(K_1), \dots, W(K_b)\big)$:

$$\mathrm{flatten}(\mathrm{Packed.of}(n, D, K)) = (Q, [n]_Q) \qquad \texttt{flatten\_spec}$$

If moreover $n$ is below the lcm of all rings of $D, K$ and $n'$ below the lcm of all rings of
$D', K'$:

$$\mathrm{comparePacked}\big(\mathrm{Packed.of}(n, D, K),\ \mathrm{Packed.of}(n', D', K')\big)
= \mathrm{compare}(n, n') \qquad \texttt{comparePacked\_eq}$$

## T6 Primality (`Primality.lean`)

For positive rings $R$ with $n < W(R)$ and $2 < W(R)$: every answer $b$ of
$\mathrm{primeOn}(\mathrm{fuel}, R, [n]_R)$ is true exactly when $n$ is prime (`primeOn_sound`),
and an answer is given once

$$\mathrm{fuel} > n \quad\text{or}\quad
\Big(\mathrm{fuel} > \lfloor\sqrt n\rfloor \ \text{and}\ \big(\lfloor\sqrt n\rfloor + 1\big)^2 < W(R)\Big)
\qquad \texttt{primeOn\_eq}$$

## T7 Window atoms (`Atoms.lean`)

For $k \ge 1$, $\mathrm{firstMultipleFrom}(lo, k)$ is the least multiple of $k$ that is
$\ge lo$, and it lies in $[lo, lo + k)$ (`firstMultipleFrom_spec`).

$$k \in \mathrm{windowAtoms}(lo, hi) \iff k \text{ is prime} \ \wedge\
\exists a:\ lo \le a,\ k \mid a,\ a + k \le hi \qquad \texttt{mem\_windowAtoms}$$

So every atom is prime (`prime_of_mem_windowAtoms`), and for a prime $p$:

$$lo + 2p \le hi + 1 \implies p \in \mathrm{windowAtoms}(lo, hi)
\qquad \texttt{prime\_mem\_windowAtoms}$$

## T8 Arithmetic (`Arithmetic.lean`)

Write $W = W(R)$. For any rings $R$ and all $x, y, e$:

$$\mathrm{addOn}(R, [x]_R, [y]_R) = [x + y]_R, \quad
\mathrm{mulOn}(R, [x]_R, [y]_R) = [x y]_R, \quad
\mathrm{powOn}(R, [x]_R, e) = [x^e]_R$$

(`addOn_spec`, `mulOn_spec`, `powOn_spec`). From here on $R$ is a list of positive rings.

$$y \le x \implies \mathrm{subOn}(R, [x]_R, [y]_R) = [x - y]_R \qquad \texttt{subOn\_spec\_of\_le}$$

$$y \le W \implies \mathrm{subOn}(R, [x]_R, [y]_R) = [x + (W - y)]_R \qquad \texttt{subOn\_spec}$$

For $x, y < W$:

$$\mathrm{addWraps}(R, [x]_R, [y]_R) \iff W \le x + y, \qquad
\mathrm{subWraps}(R, [x]_R, [y]_R) \iff x < y$$

(`addWraps_iff`, `subWraps_iff`). Exact division: for $t \ge 1$ with $t \mid x$, and
$R/t = \big(r_i / \gcd(r_i, t)\big)_i$ (`exactDivRings`):

$$\mathrm{exactDivOn}(R, [x]_R, t) = [x / t]_{R/t} \qquad \texttt{exactDivOn\_spec}$$

$$x < W \implies x / t < W(R/t) \qquad \texttt{div\_lt\_exactDivRings}$$

For $T \ge 1$ and $x < W$:

$$\mathrm{modR}(R, [x]_R, T) = \big(x \bmod T,\ [\lfloor x / T \rfloor]_{R/T}\big) \qquad \texttt{modR\_spec}$$

and for $0 < x < W$, with $i = (x - 1) \bmod T + 1$ and $k = \lfloor (x - 1)/T \rfloor + 1$,
so that $x = T (k - 1) + i$ and $1 \le i \le T$:

$$\mathrm{addressR}(R, [x]_R, T) = \big(i,\ [k]_{R/T}\big) \qquad \texttt{addressR\_spec}$$

Chapters: for any rings $R$, a prime $p$ with $p^v \mid W$ and $p^{v+1} \nmid W$, and every $j$:

$$W\big(R \mathbin{+\!\!+} (p^{v+1}, p^{v+2}, \dots, p^{v+j})\big) = p^j \, W(R) \qquad \texttt{chapters\_spec}$$
