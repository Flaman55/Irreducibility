module

public import Mathlib
public import Irreducibility.Residues

/-!
# T7: atoms of an interval

An interval of consecutive integers `lo, ..., hi` gives a difference `k` when it contains `a`
and `a + k` with `k ∣ a`. The differences are taken in order, each kept unless it is divisible
by a difference kept before.

* `firstMultipleFrom_spec`: `firstMultipleFrom lo k` is the least multiple of `k` from `lo`.
* `mem_intervalAtoms`: the atoms are exactly the primes `p` with two consecutive multiples
  `a, a + p` in the interval. An atom is never composite: when `q * r` has two consecutive
  multiples in the interval, so does `q`.
* `prime_mem_intervalAtoms`: an interval of length `L` gives every prime `p` with
  `2 * p ≤ L`.
* `intervalDifference_of_dvd`: every divisor `d ≥ 2` of a difference is a difference.
* `mem_intervalAtoms_iff_minimal`: the atoms are exactly the differences minimal under
  divisibility, the atoms of the differences ordered by divisibility.
-/

namespace Irreducibility

/-- `firstMultipleFrom lo k` is a multiple of `k` in `[lo, lo + k)`, and no multiple of `k`
from `lo` on is smaller. -/
public theorem firstMultipleFrom_spec (lo k : Nat) (hk : 0 < k) :
    k ∣ firstMultipleFrom lo k ∧ lo ≤ firstMultipleFrom lo k ∧
      firstMultipleFrom lo k < lo + k ∧
      ∀ a, lo ≤ a → k ∣ a → firstMultipleFrom lo k ≤ a := by
  have hdm := Nat.div_add_mod lo k
  have hr := Nat.mod_lt lo hk
  simp only [firstMultipleFrom, resid_eq_mod]
  split_ifs with h0
  · exact ⟨Nat.dvd_of_mod_eq_zero h0, le_rfl, by omega, fun _ h _ => h⟩
  · refine ⟨⟨lo / k + 1, by rw [Nat.mul_add]; omega⟩, by omega, by omega, ?_⟩
    rintro a ha ⟨q, rfl⟩
    have hq : lo / k < q := Nat.lt_of_mul_lt_mul_left (a := k) (by omega)
    have := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hq)
    rw [Nat.mul_succ] at this
    omega

/-- The interval `lo, ..., hi` contains `a` and `a + k` with `k ∣ a` exactly when the least
such `a` from `lo` does. -/
theorem firstMultipleFrom_add_le_iff (lo hi k : Nat) (hk : 0 < k) :
    firstMultipleFrom lo k + k ≤ hi ↔ ∃ a, lo ≤ a ∧ k ∣ a ∧ a + k ≤ hi := by
  obtain ⟨hd, hlo, -, hmin⟩ := firstMultipleFrom_spec lo k hk
  constructor
  · exact fun h => ⟨_, hlo, hd, h⟩
  · rintro ⟨a, ha, hka, hah⟩
    have := hmin a ha hka
    omega

theorem initialModuli_succ {n : Nat} (hn : 2 ≤ n) : initialModuli (n + 1) = initialModuli n ++ [n] := by
  simp only [initialModuli, List.range_succ]
  exact List.drop_append_of_le_length (by simp [hn])

theorem initialModuli_of_le_two {n : Nat} (hn : n ≤ 2) : initialModuli n = [] := by
  simp only [initialModuli, List.drop_eq_nil_iff, List.length_range]
  exact hn

/-- After the differences `2, ..., n - 1`, the atoms kept are exactly the primes below `n`
with two consecutive multiples in the interval. -/
theorem mem_foldl_atomStep (lo hi : Nat) :
    ∀ n k, k ∈ (initialModuli n).foldl (atomStep lo hi) [] ↔
      k < n ∧ k.Prime ∧ ∃ a, lo ≤ a ∧ k ∣ a ∧ a + k ≤ hi
  | n, k => by
    rcases Nat.lt_or_ge n 3 with hn | hn
    · rw [initialModuli_of_le_two (by omega)]
      simp only [List.foldl_nil, List.not_mem_nil, false_iff]
      rintro ⟨hk, hp, -⟩
      have := hp.two_le
      omega
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have ih := mem_foldl_atomStep lo hi m
      set A := (initialModuli m).foldl (atomStep lo hi) [] with hA
      have hcond : (firstMultipleFrom lo m + m ≤ hi ∧
          A.all (fun p => resid m p != 0) = true) ↔
          m.Prime ∧ ∃ a, lo ≤ a ∧ m ∣ a ∧ a + m ≤ hi := by
        rw [firstMultipleFrom_add_le_iff lo hi m (by omega)]
        simp only [List.all_eq_true, bne_iff_ne, ne_eq, resid_eq_mod]
        constructor
        · rintro ⟨⟨a, ha, hma, hah⟩, hall⟩
          refine ⟨?_, a, ha, hma, hah⟩
          by_contra hnp
          have hlt := (Nat.not_prime_iff_minFac_lt (by omega)).1 hnp
          have hpp := Nat.minFac_prime (show m ≠ 1 by omega)
          have hpa : m.minFac ∣ a := (Nat.minFac_dvd m).trans hma
          have hpm : m.minFac ∈ A := (ih _).2 ⟨hlt, hpp, a, ha, hpa, by omega⟩
          exact hall _ hpm (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd m))
        · rintro ⟨hp, ha⟩
          refine ⟨ha, fun p hpA hz => ?_⟩
          obtain ⟨hpm, hpp, -⟩ := (ih p).1 hpA
          rcases hp.eq_one_or_self_of_dvd p (Nat.dvd_of_mod_eq_zero hz) with h | h
          · exact hpp.one_lt.ne' h
          · omega
      rw [initialModuli_succ (by omega), List.foldl_append, List.foldl_cons, List.foldl_nil,
        ← hA, atomStep]
      split_ifs with hc
      · rw [List.mem_append, List.mem_singleton, ih]
        obtain ⟨hp, ha⟩ := hcond.1 hc
        constructor
        · rintro (⟨hk, h⟩ | rfl)
          · exact ⟨by omega, h⟩
          · exact ⟨by omega, hp, ha⟩
        · rintro ⟨hk, h⟩
          rcases Nat.lt_or_ge k m with hkm | hkm
          · exact Or.inl ⟨hkm, h⟩
          · exact Or.inr (by omega)
      · rw [ih]
        constructor
        · rintro ⟨hk, h⟩; exact ⟨by omega, h⟩
        · rintro ⟨hk, h⟩
          refine ⟨?_, h⟩
          rcases Nat.lt_or_ge k m with hkm | hkm
          · exact hkm
          · obtain rfl : k = m := by omega
            exact absurd (hcond.2 h) hc

/-- The atoms of the interval `lo, ..., hi` are exactly the primes `p` with two consecutive
multiples `a, a + p` in the interval. -/
public theorem mem_intervalAtoms (lo hi k : Nat) :
    k ∈ intervalAtoms lo hi ↔ k.Prime ∧ ∃ a, lo ≤ a ∧ k ∣ a ∧ a + k ≤ hi := by
  rw [intervalAtoms, mem_foldl_atomStep]
  constructor
  · exact fun h => h.2
  · rintro ⟨hp, a, ha, hka, hah⟩
    exact ⟨by omega, hp, a, ha, hka, hah⟩

/-- Every atom of an interval is prime. -/
public theorem prime_of_mem_intervalAtoms {lo hi k : Nat} (h : k ∈ intervalAtoms lo hi) :
    k.Prime :=
  ((mem_intervalAtoms lo hi k).1 h).1

/-- An interval of length `hi + 1 - lo` gives every prime `p` with `2 * p ≤ hi + 1 - lo`. -/
public theorem prime_mem_intervalAtoms {lo hi p : Nat} (hp : p.Prime) (hL : lo + 2 * p ≤ hi + 1) :
    p ∈ intervalAtoms lo hi := by
  obtain ⟨hd, hlo, hlt, -⟩ := firstMultipleFrom_spec lo p hp.pos
  exact (mem_intervalAtoms lo hi p).2 ⟨hp, _, hlo, hd, by omega⟩

/-- Every divisor `d ≥ 2` of a difference of an interval is a difference of it. -/
public theorem intervalDifference_of_dvd {lo hi k d : Nat} (hk : IntervalDifference lo hi k)
    (hd : 2 ≤ d) (hdk : d ∣ k) : IntervalDifference lo hi d := by
  obtain ⟨hk2, a, ha, hka, hah⟩ := hk
  have := Nat.le_of_dvd (by omega) hdk
  exact ⟨hd, a, ha, hdk.trans hka, by omega⟩

/-- The atoms of an interval are exactly its differences that no other difference divides. -/
public theorem mem_intervalAtoms_iff_minimal (lo hi k : Nat) :
    k ∈ intervalAtoms lo hi ↔
      IntervalDifference lo hi k ∧ ∀ d, IntervalDifference lo hi d → d ∣ k → d = k := by
  rw [mem_intervalAtoms]
  constructor
  · rintro ⟨hp, hex⟩
    refine ⟨⟨hp.two_le, hex⟩, fun d ⟨hd2, _⟩ hdk => ?_⟩
    rcases hp.eq_one_or_self_of_dvd d hdk with h | h
    · omega
    · exact h
  · rintro ⟨⟨hk2, hex⟩, hmin⟩
    refine ⟨?_, hex⟩
    by_contra hnp
    have hlt := (Nat.not_prime_iff_minFac_lt hk2).1 hnp
    have hpp := Nat.minFac_prime (show k ≠ 1 by omega)
    have := hmin _ (intervalDifference_of_dvd ⟨hk2, hex⟩ hpp.two_le (Nat.minFac_dvd k))
      (Nat.minFac_dvd k)
    omega

end Irreducibility
