module

public import Mathlib
public import Irreducibility.Packs

/-!
# T6: primality on a drum without forming values

`primeOn fuel rings states` tries rings `m = 2, 3, ...` against a number given by its states
on a drum. It compares `m` and `m * m` with the number by `compareOn`, from their states on
the drum's rings, and reads the number's state on ring `m` from its drum position.

* `primeOn_sound`: whenever `primeOn` answers, the answer is `Nat.Prime n`.
* `primeOn_eq`: it answers once the fuel exceeds `n`, or exceeds `Nat.sqrt n` when
  `(Nat.sqrt n + 1) ^ 2` is below the turn of the drum.
-/

namespace Irreducibility

/-- Comparing states `x % c` with states `n % c`, for `n` below the turn, compares
`x % turn` with `n`. -/
theorem compareOn_mod (rings : List Nat) (h : ∀ x ∈ rings, 0 < x) (x : Nat) {n : Nat}
    (hn : n < rings.foldl Nat.lcm 1) :
    compareOn rings (rings.map (x % ·)) (rings.map (n % ·)) =
      some (compare (x % rings.foldl Nat.lcm 1) n) := by
  have hx : rings.map (x % ·) = rings.map (x % rings.foldl Nat.lcm 1 % ·) :=
    List.map_congr_left fun c hc => (Nat.mod_mod_of_dvd x (dvd_foldl_lcm hc)).symm
  rw [hx]
  exact compareOn_eq rings h (Nat.mod_lt _ (foldl_lcm_pos h)) hn

theorem states_relation (rings : List Nat) (m : Nat) :
    rings.map (relation m) = rings.map (m % ·) :=
  List.map_congr_left fun c _ => relation_eq_mod m c

theorem states_relation_sq (rings : List Nat) (m : Nat) :
    rings.map (fun c => relation m c * relation m c % c) = rings.map (m * m % ·) :=
  List.map_congr_left fun c _ => by rw [relation_eq_mod, ← Nat.mul_mod]

/-- A number at least `2` with no divisor in `[2, m)` and below `m * m` is prime. -/
theorem prime_of_no_divisor_below {n m : Nat} (hn : 2 ≤ n) (hm : n < m * m)
    (hd : ∀ k, 2 ≤ k → k < m → ¬ k ∣ n) : n.Prime := by
  by_contra hp
  have h1 : n ≠ 1 := by omega
  have hmin := Nat.minFac_sq_le_self (by omega) hp
  have h2 : 2 ≤ n.minFac := (Nat.minFac_prime h1).two_le
  have hlt : n.minFac < m := by
    by_contra hge
    have := Nat.mul_le_mul (not_lt.1 hge) (not_lt.1 hge)
    rw [sq] at hmin
    omega
  exact hd _ h2 hlt (Nat.minFac_dvd n)

section

variable {rings : List Nat} {n : Nat} {ds : List (Nat × Nat)}

/-- Every answer of `primeOnAux` from a ring `m` with no divisor of `n` in `[2, m)` is
`Nat.Prime n`. -/
theorem primeOnAux_sound (h : ∀ x ∈ rings, 0 < x) (hn : n < rings.foldl Nat.lcm 1)
    (h2 : 2 < rings.foldl Nat.lcm 1) (hds : ∀ c, positionOn ds c = n % c) :
    ∀ fuel m b, 2 ≤ m → (m ≤ n ∨ m = 2) → (∀ k, 2 ≤ k → k < m → ¬ k ∣ n) →
      primeOnAux rings (rings.map (n % ·)) ds fuel m = some b → b = decide n.Prime
  | 0, _, _, _, _, _, hb => by simp [primeOnAux] at hb
  | fuel + 1, m, b, hm2, hmn, hd, hb => by
    have hmL : m < rings.foldl Nat.lcm 1 := by omega
    have c1 := compareOn_mod rings h m hn
    rw [Nat.mod_eq_of_lt hmL] at c1
    have c2 := compareOn_mod rings h (m * m) hn
    simp only [primeOnAux, states_relation, states_relation_sq, c1, c2, hds] at hb
    rcases Nat.lt_trichotomy m n with hlt | heq | hgt
    · rw [Nat.compare_eq_lt.2 hlt] at hb
      simp only at hb
      by_cases hsq : compare (m * m % rings.foldl Nat.lcm 1) n = .gt
      · rw [hsq] at hb
        simp only [Option.some.injEq] at hb
        subst hb
        have hgt : n < m * m := lt_of_lt_of_le (Nat.compare_eq_gt.1 hsq) (Nat.mod_le _ _)
        exact (decide_eq_true (prime_of_no_divisor_below (by omega) hgt hd)).symm
      · have hb' : (if n % m = 0 then some false
            else primeOnAux rings (rings.map (n % ·)) ds fuel (m + 1)) = some b := by
          rcases hc : compare (m * m % rings.foldl Nat.lcm 1) n with _ | _ | _
          · rw [hc] at hb; exact hb
          · rw [hc] at hb; exact hb
          · exact absurd hc hsq
        split_ifs at hb' with hz
        · simp only [Option.some.injEq] at hb'
          subst hb'
          refine (decide_eq_false fun hp => ?_).symm
          rcases hp.eq_one_or_self_of_dvd m (Nat.dvd_of_mod_eq_zero hz) with h' | h' <;> omega
        · refine primeOnAux_sound h hn h2 hds fuel (m + 1) b (by omega) (by omega) ?_ hb'
          intro k hk2 hkm
          rcases Nat.lt_or_ge k m with hk | hk
          · exact hd k hk2 hk
          · have : k = m := by omega
            rw [this]
            exact fun hdvd => hz (Nat.mod_eq_zero_of_dvd hdvd)
    · rw [heq, Nat.compare_eq_eq.2 rfl] at hb
      simp only [Option.some.injEq] at hb
      subst hb heq
      exact (decide_eq_true (Nat.prime_def_lt'.2 ⟨hm2, hd⟩)).symm
    · rw [Nat.compare_eq_gt.2 hgt] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      refine (decide_eq_false fun hp => ?_).symm
      have := hp.two_le
      omega

/-- `primeOnAux` answers once it reaches a ring `s` that is `n` itself, or whose square
passes `n` while staying below the turn. -/
theorem primeOnAux_isSome (h : ∀ x ∈ rings, 0 < x) (hn : n < rings.foldl Nat.lcm 1)
    (hds : ∀ c, positionOn ds c = n % c) :
    ∀ fuel m, 2 ≤ m → m ≤ n →
      (∃ s, m ≤ s ∧ s < m + fuel ∧ (s = n ∨ (n < s * s ∧ s * s < rings.foldl Nat.lcm 1))) →
        (primeOnAux rings (rings.map (n % ·)) ds fuel m).isSome
  | 0, _, _, _, ⟨s, h1, h2, _⟩ => by omega
  | fuel + 1, m, hm2, hmn, ⟨s, hs1, hs2, hs⟩ => by
    have hmL : m < rings.foldl Nat.lcm 1 := by omega
    have c1 := compareOn_mod rings h m hn
    rw [Nat.mod_eq_of_lt hmL] at c1
    have c2 := compareOn_mod rings h (m * m) hn
    simp only [primeOnAux, states_relation, states_relation_sq, c1, c2, hds]
    rcases Nat.lt_or_ge m n with hlt | hge
    · rw [Nat.compare_eq_lt.2 hlt]
      simp only
      by_cases hsq : compare (m * m % rings.foldl Nat.lcm 1) n = .gt
      · rw [hsq]; rfl
      · have hsm : m < s := by
          rcases Nat.lt_or_ge m s with h' | h'
          · exact h'
          · exfalso
            have hms : m = s := by omega
            subst hms
            rcases hs with hs | ⟨hs1, hs2⟩
            · omega
            · exact hsq (Nat.compare_eq_gt.2 (by rw [Nat.mod_eq_of_lt hs2]; exact hs1))
        have ih := primeOnAux_isSome h hn hds fuel (m + 1) (by omega) (by omega)
          ⟨s, by omega, by omega, hs⟩
        revert hsq
        cases compare (m * m % rings.foldl Nat.lcm 1) n <;> intro hsq <;>
          simp only [reduceCtorEq, not_true_eq_false] at hsq ⊢ <;> split_ifs <;> simp_all
    · rw [show m = n by omega, Nat.compare_eq_eq.2 rfl]; rfl

end

/-- Whenever `primeOn` answers on the states `n % c` of positive rings, with `n` and `2`
below the turn, the answer is whether `n` is prime. -/
public theorem primeOn_sound {rings : List Nat} (h : ∀ x ∈ rings, 0 < x) {n : Nat}
    (hn : n < rings.foldl Nat.lcm 1) (h2 : 2 < rings.foldl Nat.lcm 1) {fuel : Nat} {b : Bool}
    (hb : primeOn fuel rings (rings.map (n % ·)) = some b) : b = decide n.Prime := by
  obtain ⟨ds, hds, _, _, hval⟩ := digitsOf_spec n rings h
  rw [Nat.mod_eq_of_lt hn] at hval
  have hpos : ∀ c, positionOn ds c = n % c := fun c => by rw [positionOn_eq, hval]
  simp only [primeOn, hds] at hb
  exact primeOnAux_sound h hn h2 hpos fuel 2 b le_rfl (Or.inr rfl)
    (fun k hk hk2 => absurd hk2 (by omega)) hb

/-- On the states `n % c` of positive rings, with `n` and `2` below the turn, `primeOn`
decides whether `n` is prime once the fuel exceeds `n`, or exceeds `Nat.sqrt n` when
`(Nat.sqrt n + 1) ^ 2` is below the turn. -/
public theorem primeOn_eq {rings : List Nat} (h : ∀ x ∈ rings, 0 < x) {n : Nat}
    (hn : n < rings.foldl Nat.lcm 1) (h2 : 2 < rings.foldl Nat.lcm 1) {fuel : Nat}
    (hfuel : n < fuel ∨ (Nat.sqrt n < fuel ∧
      (Nat.sqrt n + 1) * (Nat.sqrt n + 1) < rings.foldl Nat.lcm 1)) :
    primeOn fuel rings (rings.map (n % ·)) = some (decide n.Prime) := by
  obtain ⟨ds, hds, _, _, hval⟩ := digitsOf_spec n rings h
  rw [Nat.mod_eq_of_lt hn] at hval
  have hpos : ∀ c, positionOn ds c = n % c := fun c => by rw [positionOn_eq, hval]
  have hsome : (primeOn fuel rings (rings.map (n % ·))).isSome := by
    simp only [primeOn, hds]
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
        rcases hfuel with hf | ⟨hf, _⟩ <;> omega⟩
      have c1 := compareOn_mod rings h 2 hn
      rw [Nat.mod_eq_of_lt h2] at c1
      simp only [primeOnAux, states_relation, c1, Nat.compare_eq_gt.2 hn2]
      rfl
    · apply primeOnAux_isSome h hn hpos fuel 2 le_rfl hn2
      rcases hfuel with hf | ⟨hf, hL⟩
      · exact ⟨n, hn2, by omega, Or.inl rfl⟩
      · have hs : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.2 (by omega)
        exact ⟨Nat.sqrt n + 1, by omega, by omega, Or.inr ⟨Nat.lt_succ_sqrt n, hL⟩⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
  rw [hb, primeOn_sound h hn h2 hb]

end Irreducibility
