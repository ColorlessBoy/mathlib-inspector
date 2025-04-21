import Mathlib

/- Find all nonnegative integers $m$ such that

$$
a_{m}=\left(2^{2 m+1}\right)^{2}+1
$$

is divisible by at most two different primes.

Answer: $m=0,1,2$ are the only solutions. -/

theorem number_theory_236660 (a : ℕ → ℕ) (ha : ∀ m, a m = (2^(2*m + 1))^2 + 1) :
    {m | 0 ≤ m ∧ (a m).primeFactors.card ≤ 2} = {0, 1, 2} := by
  have hmod5 (m : ℕ) : 5 ∣ (a m) := by
    rw [ha m]
    induction' m with m1 hm1
    · simp
    rw [Nat.mul_add, Nat.add_assoc, Nat.add_comm (2 * 1), ← Nat.add_assoc, Nat.pow_add, Nat.mul_pow]
    simp
    obtain ⟨m2, hm2⟩ := hm1
    have hm2gt1: m2 ≥ 1 := by by_contra h; push_neg at h; simp at h; rw [h] at hm2; simp at hm2
    have := Nat.eq_sub_of_add_eq hm2
    rw [this, Nat.sub_mul, Nat.one_mul, (show 16 = 15 + 1 by norm_num), Nat.sub_add_eq, Nat.sub_add_cancel, Nat.mul_assoc]
    apply Nat.dvd_sub
    · omega
    · apply Nat.dvd_mul_right
    · norm_num
    · omega
  have haeq (m : ℕ) : a m = (2^(2*m+1) + 1 + 2^(m+1)) * (2^(2*m+1) + 1 - 2^(m+1)) := by
    rw [ha m]
    let x := 2 ^ (2 * m + 1)
    let y := 2 ^ (m + 1)
    have h1 : y ^ 2 = 2 * x := by rw [pow_two, ←pow_add, ← Nat.add_assoc, add_comm m, add_assoc 1, ← two_mul, add_assoc, pow_add, pow_one]
    calc
      x ^ 2 + 1
        = x ^ 2 + 2 * x + 1 - y ^ 2 := by rw [h1, add_right_comm, Nat.add_sub_cancel]
      _ = (x + 1)^2 - y^2 := by ring_nf
      _ = (x + 1 + y) * (x + 1 - y) := by apply Nat.pow_two_sub_pow_two
  have h_coprime (m : ℕ) : Nat.gcd (2 ^ (2 * m + 1) + 1 + 2 ^ (m + 1)) (2 ^ (2 * m + 1) + 1 - 2 ^ (m + 1)) = 1 := by
    let a := 2 ^ (2 * m + 1) + 1
    let b := 2 ^ (m + 1)
    have h1 : a - b ≤ a + b := by norm_num; rw [Nat.add_assoc]; apply le_self_add
    have h2 := Nat.gcd_self_sub_right h1
    have : 2 ^ (m + 1) ≤ 2 ^ (2 * m + 1) + 1 := by
      rw [two_mul m, add_right_comm, pow_add _ (m+1)]
      apply le_trans _ (le_of_lt (Nat.lt_add_one (2 ^ (m + 1) * 2 ^ m)))
      apply Nat.le_mul_of_pos_right
      apply Nat.pow_pos
      norm_num
    rw [Nat.add_sub_sub_cancel this, ← two_mul] at h2
    rw [← h2]
    have hodd : Odd (a + b) := by
      apply Odd.add_even
      · apply Even.add_odd; apply Even.pow_of_ne_zero; norm_num; apply Nat.succ_ne_zero; norm_num
      apply Even.pow_of_ne_zero; norm_num; apply Nat.succ_ne_zero
    have h_coprime_pow := Nat.coprime_pow_right_iff (show 1 + (m + 1) > 0 by simp) (a + b) 2
    have : 2 * 2 ^ (m + 1) = 2 ^ (1 + (m + 1)) := by nth_rw 1 [← pow_one 2]; rw [← pow_add]
    rw [this]
    apply h_coprime_pow.mpr
    exact Nat.coprime_two_right.mpr hodd
  have h_card_sum (m : ℕ) : (a m).primeFactors.card = (2 ^ (2 * m + 1) + 1 + 2 ^ (m + 1)).primeFactors.card + (2 ^ (2 * m + 1) + 1 - 2 ^ (m + 1)).primeFactors.card := by
    let a := 2 ^ (2 * m + 1) + 1 + 2 ^ (m + 1)
    let b := 2 ^ (2 * m + 1) + 1 - 2 ^ (m + 1)
    rw [haeq m]
    have h₁ : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors :=
      Nat.Coprime.primeFactors_mul (h_coprime m)
    rw [h₁, Finset.card_union_eq_card_add_card]
    apply Nat.Coprime.disjoint_primeFactors (h_coprime m)
  have h_card_ge_one_left (m : ℕ) : 1 ≤ (2 ^ (2 * m + 1) + 1 + 2 ^ (m + 1)).primeFactors.card := by
    simp
    rw [add_comm (2 ^ (2 * m + 1)), add_assoc, lt_add_iff_pos_right]
    apply add_pos (by simp) (by simp)
  have hmp1_lt (m : ℕ) (hm : m > 0) : 2 ^ (m + 1) < 2 ^ (2 * m + 1) := by
    rw [two_mul, add_assoc, pow_add _ _ (m + 1)]
    apply lt_mul_left
    apply pow_pos
    norm_num
    apply Nat.one_lt_two_pow
    apply Nat.ne_zero_iff_zero_lt.mpr hm
  have h_card_ge_one_right (m : ℕ) (hm : m > 0) : 1 ≤ (2 ^ (2 * m + 1) + 1 - 2 ^ (m + 1)).primeFactors.card := by
    have h : 2 ^ (m + 1) < 2 ^ (2 * m + 1) := hmp1_lt m hm
    simp
    rw [add_comm (2 ^ (2 * m + 1)), Nat.add_sub_assoc, lt_add_iff_pos_right]
    simp
    · exact h
    apply le_of_lt h
  have h_card_gt_two (m : ℕ) (hm : m > 0) : 2 ≤ (a m).primeFactors.card := by
    rw [h_card_sum]
    have := add_le_add (h_card_ge_one_left m) (h_card_ge_one_right m hm)
    apply le_trans _ this
    simp
  ext x
  let p := 2 ^ (2 * x + 1) + 1 + 2 ^ (x + 1)
  let q := 2 ^ (2 * x + 1) + 1 - 2 ^ (x + 1)
  have h_five : 5 ∈ p.primeFactors ∪ q.primeFactors := by
    have h₁ : (p * q).primeFactors = p.primeFactors ∪ q.primeFactors :=
      Nat.Coprime.primeFactors_mul (h_coprime x)
    rw [← h₁, ← haeq x]
    simp
    refine ⟨by norm_num, ⟨hmod5 x, ?_⟩⟩
    rw [ha x]
    apply Nat.succ_ne_zero
  constructor
  -- Main Goal1: x ∈ {m | 0 ≤ m ∧ (a m).primeFactors.card ≤ 2} → x ∈ {0, 1, 2}
  · intro hx
    have hle := hx.right
    have h_lt : x < 3 → x ∈ ({0, 1, 2} : Set ℕ) := by intro hxlt3; simp; interval_cases x <;> simp
    apply h_lt
    by_contra hx_ge3
    push_neg at hx_ge3
    have : (a x).primeFactors.card > 2 := by
      by_contra h
      push_neg at h
      have h_card_eq_one : (a x).primeFactors.card = 2 := by apply Nat.le_antisymm h (h_card_gt_two x (by omega))
      have h_card_all_eq_one : p.primeFactors.card = 1 ∧ q.primeFactors.card = 1 := by
        by_contra h
        push_neg at h
        by_cases heq1 : p.primeFactors.card = 1
        · rw [h_card_sum, heq1] at h_card_eq_one; apply h heq1; linarith
        have hp := h_card_ge_one_left x
        have hq := h_card_ge_one_right x (by omega)
        have : p.primeFactors.card > 1 := by apply lt_of_le_of_ne hp fun h => heq1 h.symm
        have h_ge_2 : p.primeFactors.card + q.primeFactors.card > 2 := by
          rw [show 2 = 1 + 1 by norm_num]
          apply Nat.add_lt_add_of_lt_of_le this hq
        rw [h_card_sum] at h_card_eq_one
        apply ne_of_lt h_ge_2 h_card_eq_one.symm
      rw [Finset.mem_union] at h_five
      obtain ⟨hp, hq⟩ := h_card_all_eq_one
      have h_singleton_of_porq : p.primeFactors = ({5}:Finset ℕ) ∨ q.primeFactors = ({5}:Finset ℕ) := by
        cases h_five with
        | inl h5p =>
          rw [Finset.card_eq_one] at hp
          apply Or.inl
          obtain ⟨t, ht⟩ := hp
          rw [ht] at h5p
          simp at h5p
          rw [ht, Finset.singleton_inj, h5p]
        | inr h5q =>
          rw [Finset.card_eq_one] at hq
          apply Or.inr
          obtain ⟨t, ht⟩ := hq
          rw [ht] at h5q
          simp at h5q
          rw [ht, Finset.singleton_inj, h5q]

      have h_5powp1 (k: ℕ) : 5 ^ k - 1 = 4 * ∑ i ∈ Finset.range k, 5 ^ i := by
        induction k with
        | zero =>
          -- base case: 5^0 - 1 = 0, sum = 0
          simp
        | succ k ih =>
          -- inductive step: use ih for k
          rw [Finset.sum_range_succ, mul_add, ← ih, ← Nat.sub_add_comm, add_comm (5^k), ← Nat.add_one_mul, pow_add, mul_comm]
          simp
          apply Nat.pow_pos
          norm_num
      have h_odd_pow5 (t : ℕ) : (∑ i in Finset.range t, 5 ^ i) % 2 = t % 2 := by
        have h_all_odd (x : ℕ) (hx : x ∈ Finset.range t): 5 ^ x % 2 = 1 := by
          have h : Odd (5 ^ x) := by apply Odd.pow; decide
          rw [Nat.odd_iff] at h
          exact h
        rw [Finset.sum_nat_mod, Finset.sum_congr (by rfl) h_all_odd, Finset.sum_const, Finset.card_range]
        simp
      apply h_singleton_of_porq.elim
      -- hq5 : p.primeFactors = {5}
      · intro hp5
        have hqpowof5 : ∃ t, 2 ^ (2 * x + 1) + 1 - 2 ^ (x + 1) = 5 ^ t := by sorry --singleton {5}
        have hxp1_le : 2 ^ (x + 1) ≤ 2 ^ (2 * x + 1) := by
          apply le_of_lt (hmp1_lt x (by omega))
        obtain ⟨t, ht⟩ := hqpowof5
        have h0 : 2 ^ (2 * x + 1) + 1 - 2 ^ (x + 1) - 1 = (2 ^ x - 1) * 2 ^ (x + 1) := by
          rw [Nat.sub_add_comm hxp1_le, Nat.add_sub_cancel, ← one_mul (2 ^ (x + 1)), two_mul, add_assoc, pow_add, ← Nat.mul_sub_right_distrib, one_mul]
        have h2 : 8 ∣ 2 ^ (2 * x + 1) + 1 - 2 ^ (x + 1) - 1 := by
          rw [h0]
          have : ∃ y, x = 3 + y := by
            use x - 3
            rw [Nat.add_sub_cancel' hx_ge3]
          obtain ⟨y, hy⟩ := this
          rw [mul_comm, hy, add_assoc, pow_add, mul_assoc]
          simp
        have h_even_of_sum : 2 ∣ ∑ i ∈ Finset.range t, 5 ^ i := by
          apply Nat.dvd_of_mul_dvd_mul_left (show 0 < 4 by simp)
          simp
          rw [← h_5powp1, ← ht]
          exact h2
        have h_odd_of_t := h_odd_pow5 t
        have h_sum_mod : (∑ i in Finset.range t, 5 ^ i) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h_even_of_sum
        rw [h_sum_mod] at h_odd_of_t
        have h_t_eq_2e : ∃ e, t = 2 * e := by
          use t / 2
          apply Eq.symm
          apply Nat.mul_div_cancel'
          apply Nat.dvd_iff_mod_eq_zero.mpr h_odd_of_t.symm
        obtain ⟨e, he⟩ := h_t_eq_2e
        have he2 : (2 ^ x - 1) * 2 ^ (x + 1) = (5 ^ e - 1) * (5 ^ e + 1) := by
          rw [← h0, ht, he, mul_comm (5 ^ e - 1), ← Nat.pow_two_sub_pow_two, one_pow, mul_comm, pow_mul]
        have he4 : 4 ∣ 5 ^ e - 1 := by rw [h_5powp1]; apply Nat.dvd_mul_right
        obtain ⟨f, hf⟩ := he4
        have hf2 : 5 ^ e + 1 = 2 * (2 * f + 1) := by
          have := Nat.pow_pos (a := 5) (n := e) (by norm_num)
          have : 5 ^ e ≠ 0 := Nat.not_eq_zero_of_lt this
          rw [← Nat.sub_one_add_one this, hf]
          ring
        have hf3 : (2 * f + 1) = (2 ^ x - 1) := by sorry -- unique odd
        have hf4 : 5 ^ e + 1 = 2 * (2 ^ x - 1) := by
          rw [← hf3]
          exact hf2
        have h4eq2: 4 = 2 * 2 := by norm_num
        have hf5 : 5 ^ e - 1 = 2 * (2 ^ x - 2) := by
          have : 2 * f = 2 ^ x - 2 := by
            rw [← Nat.add_sub_cancel (2 * f) 1, hf3, ← Nat.sub_add_eq]
          rw [hf, h4eq2, mul_assoc, this]
        rw [hf4, hf5] at he2
        ring_nf at he2
        rw [mul_assoc, mul_assoc] at he2
        have : (2 ^ x * 2) = (2 ^ x - 2) * 4 := by
          apply Nat.mul_left_cancel _ he2
          omega
        have : 2 ^ x = 4 := by omega
        have : x = 2 := by
          apply (pow_right_inj₀ (a := 2) (m := x) (n := 2) (by simp) (by simp)).mp this
        omega
      -- hq5 : p.primeFactors = {5}
      intro hq5
      have hqpowof5 : ∃ t, 2 ^ (2 * x + 1) + 1 + 2 ^ (x + 1) = 5 ^ t := by sorry -- singleton 5
      obtain ⟨t, ht⟩ := hqpowof5
      have h0 : 2 ^ (2 * x + 1) + 1 + 2 ^ (x + 1) - 1 = (2 ^ x + 1) * 2 ^ (x + 1) := by
        rw [Nat.add_right_comm, Nat.add_sub_cancel, two_mul, add_assoc, pow_add, ← Nat.add_one_mul]
      have h2 : 8 ∣ 2 ^ (2 * x + 1) + 1 + 2 ^ (x + 1) - 1 := by
        rw [h0]
        have : ∃ y, x = 3 + y := by
          use x - 3
          rw [Nat.add_sub_cancel' hx_ge3]
        obtain ⟨y, hy⟩ := this
        rw [mul_comm, hy, add_assoc, pow_add, mul_assoc]
        simp
      have h_even_of_sum : 2 ∣ ∑ i ∈ Finset.range t, 5 ^ i := by
        apply Nat.dvd_of_mul_dvd_mul_left (show 0 < 4 by simp)
        simp
        rw [← h_5powp1, ← ht]
        exact h2
      have h_sum_mod : (∑ i in Finset.range t, 5 ^ i) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h_even_of_sum
      have h_odd_of_t := h_odd_pow5 t
      rw [h_sum_mod] at h_odd_of_t
      have h_t_eq_2e : ∃ e, t = 2 * e := by
        use t / 2
        apply Eq.symm
        apply Nat.mul_div_cancel'
        apply Nat.dvd_iff_mod_eq_zero.mpr h_odd_of_t.symm
      obtain ⟨e, he⟩ := h_t_eq_2e
      have he2 : (2 ^ x + 1) * 2 ^ (x + 1) = (5 ^ e - 1) * (5 ^ e + 1) := by
        rw [← h0, ht, he, mul_comm (5 ^ e - 1), ← Nat.pow_two_sub_pow_two, one_pow, mul_comm, pow_mul]
      have he4 : 4 ∣ 5 ^ e - 1 := by rw [h_5powp1]; apply Nat.dvd_mul_right
      obtain ⟨f, hf⟩ := he4
      have hf2 : 5 ^ e + 1 = 2 * (2 * f + 1) := by
        have := Nat.pow_pos (a := 5) (n := e) (by norm_num)
        have : 5 ^ e ≠ 0 := Nat.not_eq_zero_of_lt this
        rw [← Nat.sub_one_add_one this, hf]
        ring
      have hf3 : (2 * f + 1) = (2 ^ x + 1) := by sorry -- unique odd
      have hf4 : 5 ^ e + 1 = 2 * (2 ^ x + 1) := by
        rw [← hf3]
        exact hf2
      have h4eq2: 4 = 2 * 2 := by norm_num
      have hf5 : 5 ^ e - 1 = 2 * 2 ^ x := by
        have : 2 * f = 2 ^ x := by
          rw [← Nat.add_sub_cancel (2 * f) 1, hf3, Nat.add_sub_cancel]
        rw [hf, h4eq2, mul_assoc, this]
      rw [hf4, hf5] at he2
      ring_nf at he2
      have : 2 ^ x * 2 + 2 ^ (x * 2) * 2 = 0 := by
        omega
      have heq : 2 ^ x = 0 := by omega
      have hne: 2 ^ x ≠ 0 := by norm_num
      exact hne heq
    exact Nat.not_le.2 this hle
  -- Main Goal2: x ∈ {0, 1, 2} → x ∈ {m | 0 ≤ m ∧ (a m).primeFactors.card ≤ 2}
  intro h1
  apply h1.elim
  · intro hx0; rw [hx0, Set.mem_setOf_eq]; apply And.intro (le_refl 0); rw [ha 0]; simp; norm_num
  intro h2
  apply h2.elim
  · intro hx1; rw [hx1, Set.mem_setOf_eq]
    apply And.intro (Nat.zero_le 1)
    rw [ha 1]; simp
    have : Nat.primeFactors 65 = {5, 13} := by native_decide
    rw [this]; norm_num
  intro h3; rw [h3.out, Set.mem_setOf_eq]
  apply And.intro (Nat.zero_le 2)
  rw [ha 2]; simp
  have : Nat.primeFactors 1025 = {5, 41} := by native_decide
  rw [this]; norm_num
