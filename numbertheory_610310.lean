import Mathlib

#eval (Nat.divisors 6642).filter (fun n => n > 40 ∧ n < 3 * 27 ∧ n ≠ 54)

set_option maxRecDepth 1000000
theorem numbertheory_610310 (f : ℕ → ℕ) (hf : StrictMono f) (hf1 : f 1 = 1) (hfn : ∀ n ≥ 1, f (2 * n) * f (2 * n + 1) = 9 * f n ^ 2 + 3 * f n) : f 137 = 2215 := by
  have : f 2 ≥ 2 := by
    have := hf (show 1 < 2 by norm_num)
    omega
  have hfn1 := hfn 1 (by norm_num)
  norm_num [hf1] at hfn1
  have : f 2 ≤ 3 := by
    apply by_contra
    intro H
    have H : f 2 ≥ 4 := by omega
    have : f 3 ≥ f 2 + 1 := by
      have := hf (show 2 < 3 by norm_num)
      omega
    nlinarith
  have : f 2 ≠ 2 := by
    intro hf2
    have hf3 : f 3 = 6 := by rw [hf2] at hfn1; linarith
    have hf45 := hfn 2 (by norm_num)
    norm_num [hf2] at hf45
    have hf4 : f 4 >= 7 := by
      have := hf (show 3 < 4 by norm_num)
      omega
    have hf5 : f 5 > 7 := by
      have := hf (show 4 < 5 by norm_num)
      omega
    have contra_hf45 : f 4 * f 5 >= 49 := by nlinarith
    omega
  have hf2 : f 2 = 3 := by omega
  have hf3 : f 3 = 4 := by rw [hf2] at hfn1; linarith
  -- calculate f4 f5 f6 f7
  have hfn2 := hfn 2 (by norm_num)
  have hfn3 := hfn 3 (by norm_num)
  norm_num [hf2] at hfn2
  norm_num [hf3] at hfn3
  have hf4_gt_4 : f 4 > 4 := by have := hf (show 3 < 4 by norm_num); omega
  have hf5_gt_5 : f 5 > 5 := by have := hf (show 4 < 5 by norm_num); omega
  have hf6_gt_6 : f 6 > 6 := by have := hf (show 5 < 6 by norm_num); omega
  have hf6 : f 6 = 12 := by
    let s := (Nat.divisors 156).filter (fun n => n > 6 ∧ n < 156 / n)
    have h1 : s = {12} := by rfl
    have h2 : f 6 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; use f 7; rw [hfn3]
      constructor
      · exact hf6_gt_6
      apply lt_of_lt_of_eq (hf (show 6 < 7 by norm_num))
      rw [← hfn3, Nat.mul_div_cancel_left]
      omega
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf7 : f 7 = 13 := by rw [hf6] at hfn3; omega
  have hf5 : f 5 = 10 := by
    let s := (Nat.divisors 90).filter (fun n => n > 5 ∧ n > 90 / n ∧ n < 12)
    have h1 : s = {10} := by rfl
    have h2 : f 5 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; use f 4; rw [← hfn2]; apply mul_comm
      constructor
      · exact hf5_gt_5
      constructor
      · rw [← hfn2, Nat.mul_div_cancel]; apply hf (show 4 < 5 by norm_num); omega
      rw [← hf6]; apply hf (show 5 < 6 by norm_num)
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf4 : f 4 = 9 := by rw [hf5] at hfn2; omega
  -- calculate f8 f9 f10 f11
  have hfn4 := hfn 4 (by norm_num)
  have hfn5 := hfn 5 (by norm_num)
  norm_num [hf4] at hfn4
  norm_num [hf5] at hfn5
  have hf8_gt_13 : f 8 > 13 := by have := hf (show 7 < 8 by norm_num); omega
  have hf9_gt_14 : f 9 > 14 := by have := hf (show 8 < 9 by norm_num); omega
  have hf10_gt_15 : f 10 > 15 := by have := hf (show 9 < 10 by norm_num); omega
  have hf10 : f 10 = 30 := by
    let s := (Nat.divisors 930).filter (fun n => n > 15 ∧ n < 930 / n)
    have h1 : s = {30} := by rfl
    have h2 : f 10 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; use f 11; rw [← hfn5]
      constructor
      · exact hf10_gt_15
      rw [← hfn5, Nat.mul_div_cancel_left]
      exact hf (show 10 < 11 by norm_num)
      omega
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf9 : f 9 = 28 := by
    let s := (Nat.divisors 756).filter (fun n => n > 14 ∧ n > 756 / n ∧ n < 30)
    have h1 : s = {28} := by rfl
    have h2 : f 9 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; use f 8; rw [← hfn4]; apply mul_comm
      constructor
      · exact hf9_gt_14
      constructor
      · rw [← hfn4, Nat.mul_div_cancel]; apply hf (show 8 < 9 by norm_num); omega
      rw [← hf10]; apply hf (show 9 < 10 by norm_num)
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf8 : f 8 = 27 := by rw [hf9] at hfn4; omega
  have hf11 : f 11 = 31 := by rw [hf10] at hfn5; omega
  -- calculate f12 f13 f14 f15
  have hfn6 := hfn 6 (by norm_num)
  have hfn7 := hfn 7 (by norm_num)
  norm_num [hf6] at hfn6
  norm_num [hf7] at hfn7
  have hf12_gt_31 : f 12 > 31 := by have := hf (show 11 < 12 by norm_num); omega
  have hf13_gt_32 : f 13 > 32 := by have := hf (show 12 < 13 by norm_num); omega
  have hf14_gt_33 : f 14 > 33 := by have := hf (show 13 < 14 by norm_num); omega
  have hf14 : f 14 = 39 := by
    let s := (Nat.divisors 1560).filter (fun n => n > 33 ∧ n < 1560 / n)
    have h1 : s = {39} := by rfl
    have h2 : f 14 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; use f 15; rw [← hfn7]
      constructor
      · exact hf14_gt_33
      rw [← hfn7, Nat.mul_div_cancel_left]; apply hf (show 14 < 15 by norm_num); omega
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf15 : f 15 = 40 := by rw [hf14] at hfn7; omega
  have hf13 : f 13 = 37 := by
    let s := (Nat.divisors 1332).filter (fun n => n > 32 ∧ n > 1332 / n ∧ n < 39)
    have h1 : s = {37} := by rfl
    have h2 : f 13 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; use f 12; rw [← hfn6]; apply mul_comm
      constructor
      · exact hf13_gt_32
      constructor
      · rw [← hfn6, Nat.mul_div_cancel]; apply hf (show 12 < 13 by norm_num); omega
      rw [← hf14]; apply hf (show 13 < 14 by norm_num)
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf12 : f 12 = 36 := by rw [hf13] at hfn6; omega
  -- calculate f16 f17 f18 f19
  have hfn8 := hfn 8 (by norm_num)
  have hfn9 := hfn 9 (by norm_num)
  norm_num [hf8] at hfn8
  norm_num [hf9] at hfn9
  have hf16_gt_41 : f 16 > 40 := by have := hf (show 15 < 16 by norm_num); omega
  have hf17_gt_42 : f 17 > 41 := by have := hf (show 16 < 17 by norm_num); omega
  have hf18_gt_43 : f 18 > 42 := by have := hf (show 17 < 18 by norm_num); omega
  have hf16_ne : f 16 ≠ 54 := by
    intro hf16
    rw [hf16] at hfn8
    have hf17 : f 17 = 123 := by omega
    have hf18_gt : 123 < f 18 := by have := hf (show 17 < 18 by norm_num); omega
    have hf19_gt : 124 < f 19 := by have := hf (show 18 < 19 by norm_num); omega
    have hfn9_gt : 7140 < f 18 * f 19 := by
      apply lt_trans (show 7140 < 123 * 124 by norm_num)
      apply mul_lt_mul hf18_gt (le_of_lt hf19_gt) (by norm_num) (by norm_num)
    omega
  have hf16 : f 16 = 81 := by
    let s := (Nat.divisors 6642).filter (fun n => n > 40 ∧ n < 6642 / n ∧ n ≠ 54)
    have h1 : s = {81} := by rfl
    have h2 : f 16 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; use f 17; rw [← hfn8]
      constructor
      · exact hf16_gt_41
      constructor
      · rw [← hfn8, Nat.mul_div_cancel_left]; apply hf (show 16 < 17 by norm_num); omega
      exact hf16_ne
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf17 : f 17 = 82 := by rw [hf16] at hfn8; omega
  have hf18 : f 18 = 84 := by
    let s := (Nat.divisors 7140).filter (fun n => n > 82 ∧ n < 7140 / n)
    have h1 : s = {84} := by rfl
    have h2 : f 18 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; use f 19; rw [← hfn9]
      constructor
      · rw [← hf17]; exact hf (show 17 < 18 by norm_num)
      rw [← hfn9, Nat.mul_div_cancel_left]; apply hf (show 18 < 19 by norm_num); omega
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf19 : f 19 = 85 := by rw [hf18] at hfn9; omega
  -- calculate f20 f21 f22 f23
  have hfn10 := hfn 10 (by norm_num)
  have hfn11 := hfn 11 (by norm_num)
  norm_num [hf10] at hfn10
  norm_num [hf11] at hfn11
  have hf20_gt_84 : f 20 > 84 := by have := hf (show 19 < 20 by norm_num); omega
  have hf21_gt_85 : f 21 > 85 := by have := hf (show 20 < 21 by norm_num); omega
  have hf22_gt_86 : f 22 > 86 := by have := hf (show 21 < 22 by norm_num); omega
  have hf20 : f 20 = 90 := by
    let s := (Nat.divisors 8190).filter (fun n => n > 84 ∧ n < 8190 / n)
    have h1 : s = {90} := by rfl
    have h2 : f 20 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; use f 21; rw [← hfn10]
      constructor
      · exact hf20_gt_84
      rw [← hfn10, Nat.mul_div_cancel_left]; apply hf (show 20 < 21 by norm_num); omega
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf21 : f 21 = 91 := by rw [hf20] at hfn10; omega
  have hf22 : f 22 = 93 := by
    let s := (Nat.divisors 8742).filter (fun n => n > 91 ∧ n < 8742 / n)
    have h1 : s = {93} := by rfl
    have h2 : f 22 ∈ s := by

  -- 137 = 2 * 68 + 1
  -- 68 = 2 * 34
  -- 34 = 2 * 17
  -- 17 = 2 * 8 + 1
  -- 8 = 2 * 4
  -- 4 = 2 * 2
  -- 2 = 2 * 1
