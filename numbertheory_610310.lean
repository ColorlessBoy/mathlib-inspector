import Mathlib

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
  have h_upper : ∀ n ≥ 1, f (2 * n) ≤ 3 * f n := by
    intro n hn
    by_contra h1
    simp at h1
    have h2 : 3 * f n + 1 ≤ f (2 * n + 1) := by
      have := hf (show 2 * n < 2 * n + 1 by norm_num)
      apply lt_trans h1 this
    have h3 : (3 * f n) * (3 * f n + 1) < f (2 * n) * f (2 * n + 1) := by
      apply mul_lt_mul h1 h2
      apply Nat.add_one_pos (3 * f n)
      apply Nat.zero_le
    rw [hfn n hn] at h3
    ring_nf at h3
    apply Nat.lt_irrefl
    exact h3
  have h_lower : ∀ n ≥ 1, f (2 * n + 1) ≥ 3 * f n + 1 := by
    intro n hn
    by_contra h1
    simp at h1
    have h2 : f (2 * n) < 3 * f n := by
      have := hf (show 2 * n < 2 * n + 1 by norm_num)
      omega
    have h3 : f (2 * n) * f (2 * n + 1) < (3 * f n) * (3 * f n + 1) := by
      apply mul_lt_mul' (h_upper n hn) h1
      apply Nat.zero_le
      apply mul_pos (Nat.succ_pos 2)
      have := Nat.eq_or_lt_of_le hn
      apply Or.elim this
      · intro h
        rw [← h, hf1]
        exact Nat.succ_pos 0
      intro h
      apply lt_trans _ (hf h)
      rw [hf1]
      exact Nat.succ_pos 0
    rw [hfn n hn] at h3
    ring_nf at h3
    apply Nat.lt_irrefl _ h3
  have h_lt : ∀ n ≥ 1, f (2 * n + 1) < f (2 * n + 2) := by
    intro n hn
    apply hf
    norm_num
  have h_bound1 : ∀ n ≥ 1, f (2 * n + 1) ≥ 3 * f n + 1 ∧ f (2 * n + 1) < 3 * f (n + 1) := by
    intro n hn
    constructor
    · exact h_lower n hn
    apply lt_of_lt_of_le (h_lt n hn)
    have := h_upper (n + 1) (by norm_num)
    norm_num at this
    exact this
  have h_bound2 : ∀ n ≥ 1, f (2 * n + 2) > 3 * f (n) + 1 ∧ f (2 * n + 2) ≤ 3 * f (n + 1) := by
    intro n hn
    constructor
    · apply lt_of_le_of_lt _ (h_lt n hn)
      exact h_lower n hn
    have := h_upper (n + 1) (by norm_num)
    norm_num at this
    exact this
  -- calculate f4 f5 f6 f7
  have hfn2 := hfn 2 (by norm_num)
  have hfn3 := hfn 3 (by norm_num)
  norm_num [hf2] at hfn2
  norm_num [hf3] at hfn3
  have hf6 : f 6 = 12 := by
    have h_bound := h_bound2 2 (by norm_num)
    norm_num at h_bound
    rw [hf2, hf3] at h_bound
    norm_num at h_bound
    let s := (Finset.Ioc 10 12).filter (fun n => n ∣ 156)
    have h1 : s = {12} := by rfl
    have h2 : f 6 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; exact h_bound
      use f 7; exact hfn3.symm
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf5 : f 5 = 10 := by
    have h_bound := h_bound1 2 (by norm_num)
    norm_num at h_bound
    rw [hf2, hf3] at h_bound
    norm_num at h_bound
    let s := (Finset.Ico 10 12).filter (fun n => n ∣ 90)
    have h1 : s = {10} := by rfl
    have h2 : f 5 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; exact h_bound
      use f 4; rw [← hfn2]; apply mul_comm
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf4 : f 4 = 9 := by rw [hf5] at hfn2; omega
  -- calculate f8 f9 f10 f11
  have hfn4 := hfn 4 (by norm_num)
  have hfn5 := hfn 5 (by norm_num)
  norm_num [hf4] at hfn4
  norm_num [hf5] at hfn5
  have hf10 : f 10 = 30 := by
    have h_bound := h_bound2 4 (by norm_num)
    norm_num at h_bound
    rw [hf4, hf5] at h_bound
    norm_num at h_bound
    let s := (Finset.Ioc 28 30).filter (fun n => n ∣ 930)
    have h1 : s = {30} := by rfl
    have h2 : f 10 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; exact h_bound
      use f 11; exact hfn5.symm
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf9 : f 9 = 28 := by
    have h_bound := h_bound1 4 (by norm_num)
    norm_num at h_bound
    rw [hf4, hf5] at h_bound
    norm_num at h_bound
    let s := (Finset.Ico 28 30).filter (fun n => n ∣ 756)
    have h1 : s = {28} := by rfl
    have h2 : f 9 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; exact h_bound
      use f 8; rw [← hfn4]; apply mul_comm
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf8 : f 8 = 27 := by rw [hf9] at hfn4; omega
  -- calculate f16 f17 f18 f19
  have hfn8 := hfn 8 (by norm_num)
  have hfn9 := hfn 9 (by norm_num)
  norm_num [hf8] at hfn8
  norm_num [hf9] at hfn9
  have hf18 : f 18 = 84 := by
    have h_bound := h_bound2 8 (by norm_num)
    norm_num at h_bound
    rw [hf8, hf9] at h_bound
    norm_num at h_bound
    let s := (Finset.Ioc 82 84).filter (fun n => n ∣ 7140)
    have h1 : s = {84} := by rfl
    have h2 : f 18 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; exact h_bound
      use f 19; rw [← hfn9]
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf17 : f 17 = 82 := by
    have h_bound := h_bound1 8 (by norm_num)
    norm_num at h_bound
    rw [hf8, hf9] at h_bound
    norm_num at h_bound
    let s := (Finset.Ico 82 84).filter (fun n => n ∣ 6642)
    have h1 : s = {82} := by rfl
    have h2 : f 17 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; exact h_bound
      use f 16; rw [← hfn8]; apply mul_comm
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf16 : f 16 = 81 := by rw [hf17] at hfn8; omega
  -- calculate f34 f35 f36 f37
  have hfn17 := hfn 17 (by norm_num)
  have hfn18 := hfn 18 (by norm_num)
  norm_num [hf17] at hfn17
  norm_num [hf18] at hfn18
  have hf36 : f 36 = 252 := by
    have h_bound := h_bound2 17 (by norm_num)
    norm_num at h_bound
    rw [hf17, hf18] at h_bound
    norm_num at h_bound
    let s := (Finset.Ioc 247 252).filter (fun n => n ∣ 63756)
    have h1 : s = {252} := by rfl
    have h2 : f 36 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; exact h_bound
      use f 37; rw [← hfn18]
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf35 : f 35 = 247 := by
    have h_bound := h_bound1 17 (by norm_num)
    norm_num at h_bound
    rw [hf17, hf18] at h_bound
    norm_num at h_bound
    let s := (Finset.Ico 247 252).filter (fun n => n ∣ 60762)
    have h1 : s = {247} := by rfl
    have h2 : f 35 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; exact h_bound
      use f 34; rw [← hfn17]; apply mul_comm
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf34 : f 34 = 246 := by rw [hf35] at hfn17; omega
  -- calculate f68 f69 f70 f71
  have hfn34 := hfn 34 (by norm_num)
  have hfn35 := hfn 35 (by norm_num)
  norm_num [hf34] at hfn34
  norm_num [hf35] at hfn35
  have hf70 : f 70 = 741 := by
    have h_bound := h_bound2 34 (by norm_num)
    norm_num at h_bound
    rw [hf34, hf35] at h_bound
    norm_num at h_bound
    let s := (Finset.Ioc 739 741).filter (fun n => n ∣ 549822)
    have h1 : s = {741} := by rfl
    have h2 : f 70 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; exact h_bound
      use f 71; rw [hfn35]
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf69 : f 69 = 739 := by
    have h_bound := h_bound1 34 (by norm_num)
    norm_num at h_bound
    rw [hf34, hf35] at h_bound
    norm_num at h_bound
    let s := (Finset.Ico 739 741).filter (fun n => n ∣ 545382)
    have h1 : s = {739} := by rfl
    have h2 : f 69 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; exact h_bound
      use f 68; rw [← hfn34]; apply mul_comm
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf68 : f 68 = 738 := by rw [hf69] at hfn34; omega
  -- calculate f136 f137 f138 f139
  have hfn68 := hfn 68 (by norm_num)
  have hfn69 := hfn 69 (by norm_num)
  norm_num [hf68] at hfn68
  norm_num [hf69] at hfn69
  have hf138 : f 138 = 2217 := by
    have h_bound := h_bound2 68 (by norm_num)
    norm_num at h_bound
    rw [hf68, hf69] at h_bound
    norm_num at h_bound
    let s := (Finset.Ioc 2215 2217).filter (fun n => n ∣ 4917306)
    have h1 : s = {2217} := by rfl
    have h2 : f 138 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; exact h_bound
      use f 139; rw [hfn69]
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  have hf137 : f 137 = 2215 := by
    have h_bound := h_bound1 68 (by norm_num)
    norm_num at h_bound
    rw [hf68, hf69] at h_bound
    norm_num at h_bound
    let s := (Finset.Ico 2215 2217).filter (fun n => n ∣ 4904010)
    have h1 : s = {2215} := by rfl
    have h2 : f 137 ∈ s := by
      rw [Finset.mem_filter]
      constructor
      · simp; exact h_bound
      use f 136; rw [← hfn68]; apply mul_comm
    rw [h1] at h2
    apply Finset.mem_singleton.mp h2
  exact hf137
