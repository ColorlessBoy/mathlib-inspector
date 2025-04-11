import mathlib

/- Find all functions $f: \mathbb{Q} \rightarrow \mathbb{Q}$ such that the equation

$$
f(x f(x)+y)=f(y)+x^{2}
$$

holds for all rational numbers $x$ and $y$.
Here, $\mathbb{Q}$ denotes the set of rational numbers.
(Slovakia, Patrik Bak)

Answer: $f(x)=x$ and $f(x)=-x$. -/

theorem algebra_605624 (f : ℚ → ℚ) :
    (∀ x y, f (x * f x + y) = f y + x ^ 2) ↔
    (∀ x, f x = x) ∨ (∀ x, f x = -x) := by
  apply Iff.intro
  -- Global Goal 1:
  --  (∀ x y, f (x * f x + y) = f y + x ^ 2) →
  --  (∀ x, f x = x) ∨ (∀ x, f x = -x)
  intro h
  -- Step 1: Establish the key translation property
  have key_property : ∀ n : ℤ, ∀ x y: ℚ, f (n * x * f x + y) = f y + n * x ^ 2 := by
    intros n x y
    induction n with
    | ofNat pn =>
      induction pn with
      | zero => simp [h]
      | succ n ih =>
        have h1 : (Int.ofNat (n + 1)) * x * f x = x * f x + (Int.ofNat n) * x * f x := by
          nth_rw 1 [← one_mul (x * f x)]
          rw [mul_assoc, mul_assoc (a := ↑(Int.ofNat n)) (b := x) (c := f x) , ← add_mul, add_comm 1]
          norm_num
        rw [h1, add_assoc, h, ih, add_assoc, add_right_inj, ← add_one_mul]
        norm_num
    | negSucc pn =>
      have h1 (y : ℚ): f y = f (-(x * f x) + y) + x ^ 2 := by
        rw [← h, add_neg_cancel_left]
      have h2 (y : ℚ): f (-(x * f x) + y) = f y - x ^ 2 := by
        rw [h1 y, add_sub_cancel_right]
      induction pn with
      | zero =>
        simp
        rw [h1 y, add_neg_cancel_right]
      | succ n ih =>
        simp at ih
        simp
        rw [add_mul, add_mul, mul_assoc, neg_one_mul, add_assoc, h2, ih, add_sub_assoc]
        ring
  -- Step 2: Show the existence of a zero
  have existzero : ∃ x, f x = 0 := by
    by_contra hforall
    -- hforall : ¬∃ x, f x = 0 → ∀ x, f x ≠ 0
    push_neg at hforall
    -- Choose any x0
    let x0 : ℚ := 1
    have fx0_ne_zero : f x0 ≠ 0 := hforall x0
    let p := (f x0).num
    let q := (f x0).den
    have fx0_eq_neg : f x0 = (p / q) := by
      field_simp
      exact Rat.mul_den_eq_num (f x0)
    have hkey := key_property (-(p * q)) (1 / q) x0
    have haszero : f x0 - ↑(p * ↑q) * (1 / ↑q) ^ 2 = 0 := by
      rw [fx0_eq_neg]
      field_simp
      linarith
    have : f x0 + ↑(-(p * ↑q)) * (1 / ↑q) ^ 2 = f x0 - ↑(p * ↑q) * (1 / ↑q) ^ 2 := by
      field_simp
      linarith
    rw [this, haszero] at hkey
    exact hforall ((-↑(p * ↑q)) * (1 / ↑q) * f (1 / ↑q) + x0) hkey
  obtain ⟨c, fc_eq⟩ := existzero
  have fc_zero : c = 0 := by
    have h1 := h c c
    rw [fc_eq, mul_zero, zero_add, fc_eq, zero_add, pow_two, zero_eq_mul_self] at h1
    exact h1
  rw [fc_zero] at fc_eq
  -- Step 3: Show f 0 = 0
  have f_zero : f 0 = 0 := fc_eq
  have fc_zero (c : ℚ) (fc_eq: f c = 0) : c = 0 := by
    have h1 := h c c
    rw [fc_eq, mul_zero, zero_add, fc_eq, zero_add, pow_two, zero_eq_mul_self] at h1
    exact h1
  have iszero (n : ℤ) (x : ℚ) : n^2 * x * f x + -(n * x) * f (n * x) = 0 := by
    apply fc_zero
    have (n : ℤ) (x y : ℚ) : f (n^2 * x * f x + y) = f ((n * x) * f (n * x) + y) := by
      rw [h (n * x), mul_pow]
      apply key_property (n^2)
    rw [this, ← add_mul, add_neg_cancel, zero_mul, fc_eq]
  -- Step 4: nf(x) = f(nx)
  have iszero_simp (n : ℤ) (x : ℚ) (hx : x ≠ 0) : n * f x = f (n * x) := by
    have h1 := iszero n x
    by_cases hn : n = 0
    · rw [hn]; simp; rw [f_zero]
    rw [pow_two, mul_assoc ↑n ↑n x, mul_comm ↑n (↑n * x), mul_assoc, neg_mul, ← sub_eq_add_neg, ← mul_sub_left_distrib, mul_eq_zero] at h1
    apply Or.elim h1
    · intro h1;
      have : n * x ≠ 0 := by
        rw [mul_ne_zero_iff]
        apply And.intro
        field_simp [hn]
        exact hx
      apply absurd h1 this
    intro h; rw [← sub_eq_zero]; exact h
  -- Step 5: Show f(x) is a linear function
  have feqf1_1 (x : ℚ) (hx : x ≠ 0) : f x = x * (f 1) := by
    obtain ⟨p, q, hq, hpq⟩ := x
    have h1 : 1 = ↑(q : ℤ) * ((1 : ℚ) / q) := by field_simp [hq]
    have h2 := iszero_simp q (1/q) (by field_simp [hq])
    have h3 : (Rat.mk' p q hq hpq) * (q : ℤ) = p := by
      rw [Rat.mul_eq_mkRat]
      field_simp
      rw [Rat.mkRat_eq_div]
      field_simp
    have h4 := iszero_simp p (1/q) (by field_simp [hq])
    rw [h1, ← h2, ← mul_assoc, h3, h4]
    apply congrArg
    field_simp
    rw [← h3]
    field_simp
  have feqf1_2 (x : ℚ) (hx : x = 0) : f x = x * (f 1) := by
    rw [hx, zero_mul]
    exact fc_eq
  have feqf1 (x : ℚ) : f x = x * (f 1) := by
    by_cases hx : x = 0
    · exact feqf1_2 x hx
    · exact feqf1_1 x hx
  -- Step 6: Show f(1) = ±1
  have hf1 (x : ℚ) (hx : x ≠ 0) : f 1 ^ 2 = 1 := by
    have h1 (x y : ℚ) : (x * (x * f 1) + y) * (f 1) = y * f 1 + x ^ 2 := by
      rw [← feqf1 x, ← feqf1 y, ← feqf1 (x * f x + y)]
      exact h x y
    have := h1 x x
    rw [add_mul, add_comm, add_left_cancel_iff, mul_assoc, mul_assoc, mul_comm x, mul_comm x, mul_assoc (f 1 * f 1), pow_two] at this
    nth_rw 2 [← one_mul (x * x)] at this
    rw [pow_two]
    apply mul_right_cancel₀ _ this
    simp
    exact hx
  have hf1' (x : ℚ) (hx : x ≠ 0) : f 1 = 1 ∨ f 1 = -1 := by
    have : f 1 ^ 2 - 1 ^ 2 = 0 := by rw [hf1 _ hx, pow_two, mul_one, sub_self]
    rw [sq_sub_sq, mul_eq_zero] at this
    apply Or.elim this
    intro h1; apply Or.inr; linarith
    intro h2; apply Or.inl; linarith
  have := hf1' 1 (by norm_num)
  -- Step 7: Show f(x) = ±x
  apply Or.elim this
  intro h; apply Or.inl; intro x; rw [feqf1 x, h, mul_one]
  intro h; apply Or.inr; intro x; rw [feqf1 x, h, mul_neg_one]
  -- Global Goal 2:
  --  (∀ x, f x = x) ∨ (∀ x, f x = -x) →
  --  (∀ x y, f (x * f x + y) = f y + x ^ 2)
  intro h
  apply Or.elim h
  intro h1; intro x y; rw [h1, h1, h1]; linarith
  intro h2; intro x y; rw [h2, h2, h2]; linarith
