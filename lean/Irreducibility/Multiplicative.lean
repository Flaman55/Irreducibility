module

public import Mathlib
public import Irreducibility.SechComb

/-!
# T9: multiplicative counting

Counting multiplicatively modulo `q` -- start at `1`, multiply by `g` per step -- gives the
residue of `g ^ t`. For a prime `q` and a primitive root `g` modulo `q`, the multiplicative
counter modulo `q` and the additive counter modulo `q - 1` take equal values at the same pairs
of steps: the step `t` is the discrete logarithm of the residue, read modulo `q - 1`.

* `mulCount_eq`: `mulCount g q t = g ^ t % q`.
* `mulCount_eq_mulCount_iff`: for a primitive root `g`, `mulCount g q t = mulCount g q u`
  exactly when `countMod (q - 1) t = countMod (q - 1) u`.
* `exists_mulCount_eq`: every residue `0 < r < q` is reached at a step `t < q - 1`.
* `mulCount_eq_one_iff`, `one_half_lt_sechComb_iff_mulCount_eq_one`: the counter returns to
  `1` exactly at the multiples of `q - 1`, which are the peaks of the sech comb of modulus
  `q - 1` from scale `3` on.
* `isSquare_iff_even`: for an odd prime `q` with `q ∤ N`, `N` is a square modulo `q` exactly
  when the step `t` with `mulCount g q t = N % q` is even.
-/

namespace Irreducibility

public theorem mulCount_eq (g q : ℕ) : ∀ t, mulCount g q t = g ^ t % q
  | 0 => by simp [mulCount, resid_eq_mod]
  | t + 1 => by rw [mulCount, mulCount_eq g q t, resid_eq_mod, Nat.mod_mul_mod, pow_succ]

theorem mulCount_cast (g q t : ℕ) : ((mulCount g q t : ℕ) : ZMod q) = (g : ZMod q) ^ t := by
  rw [mulCount_eq, ZMod.natCast_mod, Nat.cast_pow]

theorem mulCount_lt (g q t : ℕ) (hq : 0 < q) : mulCount g q t < q := by
  rw [mulCount_eq]
  exact Nat.mod_lt _ hq

theorem mulCount_eq_iff_cast {g q t u : ℕ} (hq : 0 < q) :
    mulCount g q t = mulCount g q u ↔ (g : ZMod q) ^ t = (g : ZMod q) ^ u := by
  rw [← mulCount_cast, ← mulCount_cast, ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt (mulCount_lt g q t hq), Nat.mod_eq_of_lt (mulCount_lt g q u hq)]

variable {q : ℕ} [hq : Fact q.Prime]

/-- For a primitive root `g` modulo the prime `q`, the multiplicative counter modulo `q` and
the additive counter modulo `q - 1` take equal values at the same pairs of steps. -/
public theorem mulCount_eq_mulCount_iff {g : ℕ} (hg : IsPrimitiveRoot (g : ZMod q) (q - 1))
    (t u : ℕ) : mulCount g q t = mulCount g q u ↔ countMod (q - 1) t = countMod (q - 1) u := by
  have h2 := hq.out.two_le
  have hfin : IsOfFinOrder (g : ZMod q) := by
    rw [← orderOf_pos_iff, ← hg.eq_orderOf]
    omega
  rw [mulCount_eq_iff_cast (by omega), hfin.pow_inj_mod, ← hg.eq_orderOf, countMod_eq_mod,
    countMod_eq_mod]

/-- Every nonzero residue modulo `q` is a value of the multiplicative counter of a primitive
root before step `q - 1`. -/
public theorem exists_mulCount_eq {g : ℕ} (hg : IsPrimitiveRoot (g : ZMod q) (q - 1)) {r : ℕ}
    (hr0 : 0 < r) (hr : r < q) : ∃ t < q - 1, mulCount g q t = r := by
  have h2 := hq.out.two_le
  have : NeZero (q - 1) := ⟨by omega⟩
  have hne : (r : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd hr0 h) (by omega)
  obtain ⟨t, ht, hgt⟩ := hg.eq_pow_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hne)
  refine ⟨t, ht, ?_⟩
  have := congrArg ZMod.val ((mulCount_cast g q t).trans hgt)
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (mulCount_lt g q t (by omega)),
    Nat.mod_eq_of_lt hr] at this

public theorem mulCount_eq_one_iff {g : ℕ} (hg : IsPrimitiveRoot (g : ZMod q) (q - 1)) (t : ℕ) :
    mulCount g q t = 1 ↔ (q - 1) ∣ t := by
  have h2 := hq.out.two_le
  have h1 : mulCount g q 0 = 1 := by
    rw [mulCount_eq, pow_zero, Nat.mod_eq_of_lt (by omega)]
  rw [show mulCount g q t = 1 ↔ mulCount g q t = mulCount g q 0 by rw [h1],
    mulCount_eq_mulCount_iff hg, countMod_eq_mod, countMod_eq_mod, Nat.zero_mod,
    Nat.dvd_iff_mod_eq_zero]

/-- From scale `3` on, the peaks of the sech comb of modulus `q - 1` are the steps at which
the multiplicative counter of a primitive root modulo `q` returns to `1`. -/
public theorem one_half_lt_sechComb_iff_mulCount_eq_one {s : ℝ} (hs : 3 ≤ s) {g : ℕ}
    (hg : IsPrimitiveRoot (g : ZMod q) (q - 1)) (t : ℕ) :
    1 / 2 < sechComb s (q - 1) t ↔ mulCount g q t = 1 := by
  have h2 := hq.out.two_le
  rw [one_half_lt_sechComb_iff hs (by omega), mulCount_eq_one_iff hg]

/-- For an odd prime `q` and `q ∤ N`, `N` is a square modulo `q` exactly when the step at which
the multiplicative counter of a primitive root reaches `N % q` is even. -/
public theorem isSquare_iff_even (hq2 : q ≠ 2) {g : ℕ} (hg : IsPrimitiveRoot (g : ZMod q) (q - 1))
    {N t : ℕ} (hN : ¬ q ∣ N) (ht : mulCount g q t = N % q) :
    IsSquare (N : ZMod q) ↔ Even t := by
  have h2 := hq.out.two_le
  have hodd : q % 2 = 1 := (hq.out.eq_two_or_odd).resolve_left hq2
  have hNg : (N : ZMod q) = (g : ZMod q) ^ t := by
    rw [← mulCount_cast, ht, ZMod.natCast_mod]
  have hne : (N : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  rw [ZMod.euler_criterion q hne, hNg, ← pow_mul, hg.pow_eq_one_iff_dvd, even_iff_two_dvd]
  have hq1 : q - 1 = 2 * (q / 2) := by omega
  have hpos : 0 < q / 2 := by omega
  rw [hq1, Nat.mul_dvd_mul_iff_right hpos]

end Irreducibility
