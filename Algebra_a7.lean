import Mathlib

theorem h_eq (n : ℕ) (n_pos : 0 < n) (a : ℕ → ℝ) (ha : ∀ i, a i ∈ Set.Icc 1 8)
  (M : Finset ℕ) (hM : M = (Finset.range n).filter (fun i => a i ∈ Set.Ioc 2 4))
: ∑ i ∈ M, ((Finset.filter (fun l => l ∈ M) (Finset.range (i + 1))).card)
  = ∑ i ∈ Finset.range (M.card), (i + 1) := by
  sorry

theorem Algebra_a7 (n k : ℕ) (a : ℕ → ℝ) (n_pos : 0 < n) (k_pos : 0 < k) (ha : ∀ i, a i ∈ Set.Icc 1 (2^k)) :
  ∑ i in Finset.range n, a i / Real.sqrt (∑ j in Finset.range (i + 1), (a j)^2) ≤ 4 * Real.sqrt (k * n) := by
  -- 定义 M_j：a_i 落在 [2^{j-1}, 2^j] 的 i 的集合
  -- j 从 1 开始到 k
  let M (j : ℕ) :=
    (Finset.range n).filter (fun i => j = 1 ∧ a i = 1 ∨ a i ∈ Set.Ioc (2^(j-1) : ℝ) (2^j : ℝ))

  have one_le_two_pow (i : ℕ) : (1 : ℝ) ≤ (2: ℝ) ^ i := by
    induction i with
    | zero => simp
    | succ k hk =>
      apply one_le_pow₀
      apply one_le_two

  have pow_two_lt_pow_two {m n : ℕ} : (2: ℝ) ^ m < (2: ℝ) ^ n → m < n := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    rw [Real.rpow_lt_rpow_left_iff one_lt_two]
    simp

  have M_disjoint : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k, i ≠ j → Disjoint (M (i + 1)) (M (j + 1)) := by
    intros i hi j hj inej
    rw [Finset.disjoint_iff_ne]
    intros x hx y hy
    unfold M at hx
    simp at hx
    unfold M at hy
    simp at hy
    intro hxy
    apply inej
    rw [← hxy] at hy
    apply Or.elim hx.right
    · intro ⟨ieq0, axeq1⟩
      apply Or.elim hy.right
      · intro ⟨jeq0, axeq1⟩
        rw [ieq0, jeq0]
      intro ⟨hl, hr⟩
      rw [axeq1] at hl
      apply absurd (lt_of_le_of_lt (one_le_two_pow j) hl) (lt_irrefl 1)
    intro ⟨hi1, hi2⟩
    apply Or.elim hy.right
    intro ⟨hy1, hy2⟩
    rw [hy2] at hi1
    apply absurd (lt_of_le_of_lt (one_le_two_pow i) hi1) (lt_irrefl 1)

    intro ⟨hj1, hj2⟩
    have h1 : (2 : ℝ) ^ j < (2 : ℝ) ^ (i + 1) := lt_of_lt_of_le hj1 hi2
    have h2 : (2 : ℝ) ^ i < (2 : ℝ) ^ (j + 1) := lt_of_lt_of_le hi1 hj2
    have h3 : j < i + 1 := pow_two_lt_pow_two h1
    have h4 : i < j + 1 := pow_two_lt_pow_two h2
    have h5 : j ≤ i := by apply (add_le_add_iff_right 1).mp h3
    have h6 : i ≤ j := by apply (add_le_add_iff_right 1).mp h4
    exact le_antisymm h6 h5

  have M_biUnion: Finset.biUnion (Finset.range k) (fun j => M (j + 1)) = Finset.range n := by
    ext x
    simp
    apply Iff.intro
    · intro h
      obtain ⟨j, ⟨_, hj⟩⟩ := h
      apply Finset.mem_range.mp
      apply Finset.mem_of_mem_filter _ hj
    intro hxn
    specialize ha x
    have ax_ge : 1 ≤ a x := (Set.mem_Icc.mp ha).left
    have ax_le : a x ≤ 2^k := (Set.mem_Icc.mp ha).right
    by_cases h1 : a x = 1
    · use 0; constructor; exact k_pos; simp [M, hxn, h1]
    let j := Nat.findGreatest (fun j => (2:ℝ)^j < a x) k
    have hjlek := Nat.findGreatest_le (P := fun j => (2:ℝ)^j < a x) k
    have hjnek : j ≠ k := by
      intro hjk
      have hlt := Nat.findGreatest_of_ne_zero (P := fun j => (2:ℝ)^j < a x) hjk (Nat.not_eq_zero_of_lt k_pos)
      have hnlt := not_lt_of_ge ax_le
      apply hnlt hlt
    have hjltk := by apply lt_of_le_of_ne hjlek hjnek
    have h_interval : a x ∈ Set.Ioc (2^j : ℝ) (2^(j+1)) := by
      apply And.intro
      by_cases hj : j = 0
      · simp [hj]
        apply lt_of_le_of_ne ax_ge fun h => h1 (Eq.symm h)
      apply Nat.findGreatest_of_ne_zero (P := fun j => (2:ℝ)^j < a x) rfl hj
      apply le_of_not_lt
      apply Nat.findGreatest_is_greatest (P := fun j => (2:ℝ)^j < a x)
      apply Nat.lt_succ_self
      exact hjltk
    use j
    apply And.intro hjltk
    simp [M]
    apply And.intro hxn (Or.inr h_interval)

  have M_card : ∑ j ∈ Finset.range k, (M (j + 1)).card = n := by
    rw [← Finset.card_biUnion M_disjoint, M_biUnion]
    simp [Finset.card_range]

  have H : ∑ i in Finset.range n, a i / Real.sqrt (∑ j in Finset.range (i+1), (a j)^2)
          = ∑ j in Finset.range k, ∑ i in M (j+1), a i / Real.sqrt (∑ j in Finset.range (i+1), (a j)^2) := by
    rw [← Finset.sum_biUnion M_disjoint, M_biUnion]

  have Hbound : ∀ j < k, ∑ i in M (j+1), a i / Real.sqrt (∑ l in Finset.range (i+1), (a l)^2)
                  ≤ 4 * Real.sqrt ((M (j+1)).card) := by
    intro j hjk
    let p := (M j).card
    have h_upper : ∀ i ∈ M (j+1), a i ≤ 2^(j+1) := by
      intros i hi
      apply Finset.mem_filter.mp at hi
      apply Or.elim hi.right
      intro ⟨h1, h2⟩
      rw [h1, h2]
      simp
      intro h
      exact h.out.right
    have h_lower (i : ℕ) (hi : i ∈ M (j+1)) : ((Finset.range (i+1)).filter (fun l => l ∈ M (j+1))).card • (2 ^ j)^2 ≤ ∑ l in Finset.range (i+1), (a l)^2 := by
      rw [← Finset.sum_const, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro l hl
      by_cases h : l ∈ M (j + 1)
      · rw [if_pos h, pow_two, pow_two]
        apply mul_self_le_mul_self
        apply pow_nonneg (by simp)
        simp [M] at h
        apply Or.elim h.right
        · intro ⟨h1, h2⟩
          rw [h1, h2]
          simp
        intro ⟨h1, _⟩
        exact le_of_lt h1
      rw [if_neg]
      apply pow_two_nonneg
      assumption
    have pow_two_nonneg: (0:ℝ) < (2 ^ j) ^ 2 := by
      apply pow_pos
      simp
    have h_lower2 (i : ℕ) (hi : i ∈ M (j + 1)) : (0:ℝ) < ((Finset.range (i+1)).filter (fun l => l ∈ M (j+1))).card • (2 ^ j)^2 := by
      have left_pos : (0:ℝ) < ((Finset.range (i+1)).filter (fun l => l ∈ M (j+1))).card := by
        let S := Finset.filter (fun l => l ∈ M (j + 1)) (Finset.range (i + 1))
        have h₁ : i ∈ Finset.range (i + 1) := Finset.mem_range_succ_iff.mpr (le_refl i)
        have h₂ : i ∈ S := Finset.mem_filter.mpr ⟨h₁, hi⟩
        exact_mod_cast Finset.card_pos.mpr ⟨i, h₂⟩
      have pos := mul_pos left_pos pow_two_nonneg
      simp
      exact pos
    have h_lower3 (i : ℕ) (hi : i ∈ M (j + 1)) : a i / √(∑ l ∈ Finset.range (i + 1), a l ^ 2) ≤ (2 ^ (j + 1)) / √(((Finset.range (i+1)).filter (fun l => l ∈ M (j+1))).card • (2 ^ j)^2) := by
      apply div_le_div₀ (by simp) (h_upper i hi)
      rw [Real.sqrt_pos]
      exact h_lower2 i hi
      exact Real.sqrt_le_sqrt (h_lower i hi)
    have h1 := Finset.sum_le_sum h_lower3
    have h_eq : ∑ i ∈ M (j + 1), 2 ^ (j + 1) / √((Finset.filter (fun l => l ∈ M (j + 1)) (Finset.range (i + 1))).card • (2 ^ j) ^ 2) = ∑ i ∈ Finset.range ((M (j + 1)).card), 2 ^ (j + 1) / √((i + 1) • (2 ^ j) ^ 2) := by sorry
    apply le_trans h1
    apply le_of_eq_of_le h_eq
    let f := fun (i:ℕ) => √i
    have h_upper2 (i: ℕ)(hi : i ∈ Finset.range (M (j + 1)).card): 2 ^ (j + 1) / √((i + 1) • (2 ^ j) ^ 2) ≤ 4 * f (i+1) - 4 * f i := by
      have h0 : 0 < (i: ℝ) + 1 := by exact_mod_cast Nat.add_one_pos i
      have h1 : 0 ≤ (i: ℝ) + 1 := le_of_lt h0
      simp [f]
      rw [div_le_iff₀', Real.sqrt_mul, mul_comm √(↑i + 1), mul_assoc, pow_succ]
      apply mul_le_mul (by simp)
      rw [← mul_sub, ←  mul_assoc _ 4, mul_comm _ 4]
      have : 2 * (√(↑i + 1) +  √↑i) ≤ 4 * √(↑i + 1) := by
        have : (4 : ℝ) = 2 + 2 := by norm_num
        rw [mul_add, this, add_mul]
        apply add_le_add_left
        field_simp
      have : 2 * (√(↑i + 1) +  √↑i) * (√(↑i + 1) - √↑i) ≤ 4 * √(↑i + 1) * (√(↑i + 1) - √↑i) := by
        rw [mul_le_mul_right]
        exact this
        field_simp
      apply le_of_eq_of_le _ this
      rw [mul_assoc, mul_sub, add_mul, add_mul, ← pow_two, ← pow_two, mul_comm √↑i, ← add_sub, ← sub_sub, sub_self, add_sub, add_zero, Real.sq_sqrt, Real.sq_sqrt]
      simp
      simp
      exact h1
      simp
      field_simp
      exact h1
      rw [Real.sqrt_pos]
      apply mul_pos
      exact h0
      exact pow_two_nonneg
    have h_upper3 := Finset.sum_le_sum h_upper2
    apply le_of_le_of_eq h_upper3
    have := Finset.sum_range_sub (fun i => 4 * √i) (M (j + 1)).card
    rw [this]
    simp

  -- Cauchy-Schwarz：∑ sqrt(m_j) ≤ sqrt(k * n)
  have Hsum : ∑ j in Finset.range k, Real.sqrt ((M (j+1)).card)
              ≤ Real.sqrt (k * ∑ j in Finset.range k, (M (j+1)).card) := by
    have : (0 : ℝ) < k := by simp [k_pos]
    rw [Real.sqrt_mul (le_of_lt this) ↑(∑ j ∈ Finset.range k, (M (j + 1)).card)]
    have card_nonneg : ∀ (i : ℕ), (0 : ℝ) ≤ ↑(M (i + 1)).card := by intro i; simp
    have := Real.sum_sqrt_mul_sqrt_le (Finset.range k) (f := fun j => 1) (g := fun j => (M (j + 1)).card) (fun _ => by simp) card_nonneg
    simp at this
    apply le_trans this
    simp

  -- Conclusion
  calc ∑ i in Finset.range n, a i / Real.sqrt (∑ j in Finset.range (i+1), (a j)^2)
      = ∑ j in Finset.range k, ∑ i in M (j+1), a i / Real.sqrt (∑ j in Finset.range (i+1), (a j)^2) := by exact H
    _ ≤ ∑ j in Finset.range k, 4 * Real.sqrt ((M (j+1)).card) := by apply Finset.sum_le_sum; intro j hj; apply Hbound j; apply Finset.mem_range.mp hj
    _ = 4 * ∑ j in Finset.range k, Real.sqrt ((M (j+1)).card) := by rw [Finset.mul_sum]
    _ ≤ 4 * Real.sqrt (k * ∑ j in Finset.range k, (M (j+1)).card) := by apply mul_le_mul_of_nonneg_left Hsum; norm_num
    _ = 4 * Real.sqrt (k * n) := by rw [M_card]
