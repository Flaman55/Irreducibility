module

public import Mathlib
public import Irreducibility.Ticking

/-!
# T1w: waves read the same relation as ticking

Ring `d` is drawn as a comb: a `sech` tooth at every multiple of `d`, of width `1 / s` for
the sharpness `s`. A tick `t` is a peak of the ring when the comb stands above `1 / 2` there.
The relation of ring `a` to ring `b` is read backwards from tick `a` to the last peak of `b`.

* `one_half_lt_comb_iff`: from sharpness `3` on, tick `t` is a peak of ring `d` exactly when
  `d ∣ t`, for every ring `d`.
* `waveRelation_eq`: from sharpness `3` on, the relation read from the waves is
  `relation a b`.
* `waveRelation_two_ne`: at sharpness `2` the teeth of ring `2` merge and the reading fails.
-/

namespace Irreducibility

/-- Hyperbolic secant: a tooth of height `1` at `0`, falling off on both sides. -/
@[expose] public noncomputable def sech (x : ℝ) : ℝ := (Real.cosh x)⁻¹

/-- The comb of ring `d` at sharpness `s` and tick `t`: the teeth at the multiples `d * j` with
`j` from `t / d - 1` to `t / d + 2`. -/
@[expose] public noncomputable def comb (s : ℝ) (d t : ℕ) : ℝ :=
  (([-1, 0, 1, 2] : List ℤ).map fun i =>
    sech (s * ((t : ℝ) - d * ((((t / d : ℕ) : ℤ) + i : ℤ) : ℝ)))).sum

/-- The last tick up to `t` at which the comb of ring `d` stands above `1 / 2`, or `0`. -/
@[expose] public noncomputable def lastPeak (s : ℝ) (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => if 1 / 2 < comb s d (t + 1) then t + 1 else lastPeak s d t

/-- The relation of ring `a` to ring `b` read from the waves: the ticks from the last peak of
`b` up to tick `a`. -/
@[expose] public noncomputable def waveRelation (s : ℝ) (a b : ℕ) : ℕ := a - lastPeak s b a

theorem sech_pos (x : ℝ) : 0 < sech x := inv_pos.2 (Real.cosh_pos x)

theorem sech_neg (x : ℝ) : sech (-x) = sech x := by simp [sech]

theorem sech_le_sech {x y : ℝ} (h : |y| ≤ |x|) : sech x ≤ sech y :=
  inv_anti₀ (Real.cosh_pos y) (Real.cosh_le_cosh.2 h)

/-- The comb depends on the tick only through `t % d`. -/
theorem comb_eq (s : ℝ) (d t : ℕ) :
    comb s d t = sech (s * ((t % d : ℕ) + d)) + sech (s * (t % d : ℕ)) +
      sech (s * ((t % d : ℕ) - d)) + sech (s * ((t % d : ℕ) - 2 * d)) := by
  have h : (t : ℝ) = d * ((t / d : ℕ) : ℝ) + ((t % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod t d).symm
  simp only [comb, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.cast_add,
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

/-- A tooth at a nonzero integer distance, at sharpness `3` or more, stays below `1 / 8`. -/
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

/-- From sharpness `3` on, tick `t` is a peak of ring `d` exactly when ring `d` stands at `0`
after `t` ticks. -/
public theorem one_half_lt_comb_iff {s : ℝ} (hs : 3 ≤ s) {d : ℕ} (hd : 0 < d) (t : ℕ) :
    1 / 2 < comb s d t ↔ d ∣ t := by
  rw [comb_eq, Nat.dvd_iff_mod_eq_zero]
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

/-- From sharpness `3` on, the last peak of ring `d` up to tick `t` is the last multiple of
`d` up to `t`. -/
theorem lastPeak_eq {s : ℝ} (hs : 3 ≤ s) {d : ℕ} (hd : 0 < d) :
    ∀ t, lastPeak s d t = d * (t / d)
  | 0 => by simp [lastPeak]
  | t + 1 => by
    simp only [lastPeak]
    split_ifs with h <;> rw [one_half_lt_comb_iff hs hd] at h
    · exact (Nat.mul_div_cancel' h).symm
    · rw [lastPeak_eq hs hd t, Nat.succ_div_of_not_dvd h]

/-- From sharpness `3` on, the relation read from the waves is the relation read by
ticking. -/
public theorem waveRelation_eq {s : ℝ} (hs : 3 ≤ s) (a : ℕ) {b : ℕ} (hb : 0 < b) :
    waveRelation s a b = relation a b := by
  rw [waveRelation, lastPeak_eq hs hb, relation_eq_mod]
  have := Nat.div_add_mod a b
  omega

/-- At sharpness `2`, tick `1` is a peak of ring `2`. -/
theorem one_half_lt_comb_two_two_odd (t : ℕ) (ht : t % 2 = 1) : 1 / 2 < comb 2 2 t := by
  rw [comb_eq, ht]
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

/-- At sharpness `2` the teeth of ring `2` merge: the reading from the waves of where ring `2`
stands after `3` ticks gives `0`, while ticking gives `1`. -/
public theorem waveRelation_two_ne : waveRelation 2 3 2 ≠ relation 3 2 := by
  have h : lastPeak 2 2 3 = 3 := by
    simp only [lastPeak]
    exact ite_eq_left_iff.2 fun h => absurd (one_half_lt_comb_two_two_odd 3 rfl) h
  rw [waveRelation, h, relation_eq_mod]
  decide

end Irreducibility
