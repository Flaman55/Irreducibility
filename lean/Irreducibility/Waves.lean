module

public import Mathlib
public import Irreducibility.Residues

/-!
# T1w: a sech comb gives the same residue as counting

Modulus `d` is represented by a sum of `sech` pulses centred at the multiples of `d`, of width
`1 / s` for the scale `s`. A step `t` is a peak for `d` when the sum exceeds `1 / 2` there.
The residue of `a` modulo `b` is read backwards from `a` to the last peak for `b`.

* `one_half_lt_sechComb_iff`: from scale `3` on, `t` is a peak for `d` exactly when `d ∣ t`,
  for every modulus `d`.
* `waveResid_eq`: from scale `3` on, the residue read from the comb is `resid a b`.
* `waveResid_two_ne`: at scale `2` the pulses for modulus `2` overlap and the reading
  fails.
-/

namespace Irreducibility

/-- Hyperbolic secant: a pulse of height `1` at `0`, decreasing on both sides. -/
@[expose] public noncomputable def sech (x : ℝ) : ℝ := (Real.cosh x)⁻¹

/-- The sech comb of modulus `d` at scale `s` and step `t`: the pulses at the multiples
`d * j` with `j` from `t / d - 1` to `t / d + 2`. -/
@[expose] public noncomputable def sechComb (s : ℝ) (d t : ℕ) : ℝ :=
  (([-1, 0, 1, 2] : List ℤ).map fun i =>
    sech (s * ((t : ℝ) - d * ((((t / d : ℕ) : ℤ) + i : ℤ) : ℝ)))).sum

/-- The last step up to `t` at which the comb of modulus `d` exceeds `1 / 2`, or `0`. -/
@[expose] public noncomputable def lastPeak (s : ℝ) (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => if 1 / 2 < sechComb s d (t + 1) then t + 1 else lastPeak s d t

/-- The residue of `a` modulo `b` read from the comb: the steps from the last peak for `b`
up to `a`. -/
@[expose] public noncomputable def waveResid (s : ℝ) (a b : ℕ) : ℕ := a - lastPeak s b a

theorem sech_pos (x : ℝ) : 0 < sech x := inv_pos.2 (Real.cosh_pos x)

theorem sech_neg (x : ℝ) : sech (-x) = sech x := by simp [sech]

theorem sech_le_sech {x y : ℝ} (h : |y| ≤ |x|) : sech x ≤ sech y :=
  inv_anti₀ (Real.cosh_pos y) (Real.cosh_le_cosh.2 h)

/-- The comb depends on the step only through `t % d`. -/
theorem sechComb_eq (s : ℝ) (d t : ℕ) :
    sechComb s d t = sech (s * ((t % d : ℕ) + d)) + sech (s * (t % d : ℕ)) +
      sech (s * ((t % d : ℕ) - d)) + sech (s * ((t % d : ℕ) - 2 * d)) := by
  have h : (t : ℝ) = d * ((t / d : ℕ) : ℝ) + ((t % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod t d).symm
  simp only [sechComb, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.cast_add,
    Int.cast_natCast, Int.cast_neg, Int.cast_one, Int.cast_zero, Int.cast_ofNat]
  rw [h]
  ring_nf

theorem eight_lt_cosh_three : 8 < Real.cosh 3 := by
  have he : (2.7 : ℝ) ^ 3 < Real.exp 3 := by
    have h1 := Real.exp_one_gt_d9
    have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    exact pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
  rw [Real.cosh_eq]
  have := Real.exp_pos (-3)
  nlinarith

/-- A pulse at a nonzero integer distance, at scale `3` or more, stays below `1 / 8`. -/
theorem sech_mul_int_lt {s : ℝ} (hs : 3 ≤ s) {z : ℤ} (hz : z ≠ 0) :
    sech (s * z) < 1 / 8 := by
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz
  have h3 : sech (s * z) ≤ sech 3 := by
    apply sech_le_sech
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s), abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  calc sech (s * z) ≤ sech 3 := h3
    _ < 1 / 8 := by
      rw [sech, show (1 : ℝ) / 8 = (8 : ℝ)⁻¹ by norm_num]
      exact inv_strictAnti₀ (by norm_num) eight_lt_cosh_three

/-- From scale `3` on, step `t` is a peak for modulus `d` exactly when `t % d = 0`
(computed by `countMod`). -/
public theorem one_half_lt_sechComb_iff {s : ℝ} (hs : 3 ≤ s) {d : ℕ} (hd : 0 < d) (t : ℕ) :
    1 / 2 < sechComb s d t ↔ d ∣ t := by
  rw [sechComb_eq, Nat.dvd_iff_mod_eq_zero]
  have hr := Nat.mod_lt t hd
  generalize t % d = r at hr ⊢
  constructor
  · intro h
    by_contra hr0
    have cast : ∀ z : ℤ, z ≠ 0 → ∀ x : ℝ, x = z → sech (s * x) < 1 / 8 := by
      rintro z hz x rfl
      exact sech_mul_int_lt hs hz
    have e1 := cast (r + d) (by omega) ((r : ℝ) + d) (by push_cast; ring)
    have e2 := cast r (by omega) (r : ℝ) (by push_cast; ring)
    have e3 := cast (r - d) (by omega) ((r : ℝ) - d) (by push_cast; ring)
    have e4 := cast (r - 2 * d) (by omega) ((r : ℝ) - 2 * d) (by push_cast; ring)
    linarith
  · rintro rfl
    have := sech_pos (s * ((0 : ℕ) + d))
    have := sech_pos (s * ((0 : ℕ) - d))
    have := sech_pos (s * ((0 : ℕ) - 2 * d))
    simp only [Nat.cast_zero, mul_zero, sech, Real.cosh_zero, inv_one] at *
    linarith

/-- From scale `3` on, the last peak for modulus `d` up to step `t` is the last multiple of
`d` up to `t`. -/
theorem lastPeak_eq {s : ℝ} (hs : 3 ≤ s) {d : ℕ} (hd : 0 < d) :
    ∀ t, lastPeak s d t = d * (t / d)
  | 0 => by simp [lastPeak]
  | t + 1 => by
    simp only [lastPeak]
    split_ifs with h <;> rw [one_half_lt_sechComb_iff hs hd] at h
    · exact (Nat.mul_div_cancel' h).symm
    · rw [lastPeak_eq hs hd t, Nat.succ_div_of_not_dvd h]

/-- From scale `3` on, the residue read from the comb is the residue computed by
counting. -/
public theorem waveResid_eq {s : ℝ} (hs : 3 ≤ s) (a : ℕ) {b : ℕ} (hb : 0 < b) :
    waveResid s a b = resid a b := by
  rw [waveResid, lastPeak_eq hs hb, resid_eq_mod]
  have := Nat.div_add_mod a b
  omega

/-- At scale `2`, step `1` is a peak for modulus `2`. -/
theorem one_half_lt_sechComb_two_two_odd (t : ℕ) (ht : t % 2 = 1) : 1 / 2 < sechComb 2 2 t := by
  rw [sechComb_eq, ht]
  have hc : Real.cosh 2 < 4 := by
    have he : Real.exp 2 < 2.72 ^ 2 := by
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      exact pow_lt_pow_left₀ (Real.exp_one_lt_d9.trans (by norm_num)) (Real.exp_pos 1).le
        (by norm_num)
    have hn : Real.exp (-2) ≤ 1 / 3 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
      linarith [Real.add_one_le_exp 2]
    rw [Real.cosh_eq]
    linarith
  have h2 : 1 / 4 < sech 2 := by
    rw [sech, show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num]
    exact inv_strictAnti₀ (Real.cosh_pos 2) hc
  simp only [Nat.cast_one, Nat.cast_ofNat]
  rw [show (2 : ℝ) * (1 + 2) = 6 by norm_num, show (2 : ℝ) * 1 = 2 by norm_num,
    show (2 : ℝ) * (1 - 2) = -2 by norm_num, show (2 : ℝ) * (1 - 2 * 2) = -6 by norm_num,
    sech_neg, sech_neg]
  have := sech_pos 6
  linarith

/-- At scale `2` the pulses for modulus `2` overlap: the comb reading of `3` modulo `2`
gives `0`, while counting gives `1`. -/
public theorem waveResid_two_ne : waveResid 2 3 2 ≠ resid 3 2 := by
  have h : lastPeak 2 2 3 = 3 := by
    simp only [lastPeak]
    exact ite_eq_left_iff.2 fun h => absurd (one_half_lt_sechComb_two_two_odd 3 rfl) h
  rw [waveResid, h, resid_eq_mod]
  decide

end Irreducibility
