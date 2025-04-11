import Mathlib
open Real
theorem sin_20_bounds : (20 : ℝ) / 60 < sin (20 * π / 180) ∧ sin (20 * π / 180) < (21 : ℝ) / 60 := by
  let f := fun (x : ℝ) => 3 * x - 4 * (x ^ 3)
  have h_mono : StrictMonoOn f (Set.Icc 0 (1/2)) := by
    intro a arange b brange hab
    have h_deriv : ∀ x, HasDerivAt f (3 - 12 * x^2) x := by
      intro x
      have h₁ : HasDerivAt (fun x => 3 * x) (3 * 1) x :=
        HasDerivAt.const_mul 3 (hasDerivAt_id x)
      have h₂ : HasDerivAt (fun x => x^3) (3 * (id x)^(3-1) * 1) x :=
        HasDerivAt.pow 3 (hasDerivAt_id x)
      have h₆ : 3 * (id x)^(3-1) * 1 = 3 * x ^ 2 := by simp
      rw [h₆] at h₂
      have h₃ : HasDerivAt (fun x => 4 * x^3) (4 * (3 * x^2)) x := HasDerivAt.const_mul 4 h₂
      have h₅ : (3 : ℝ) * 1 = 3 := by simp
      have h₇ : 4 * (3 * x^2) = 12 * x^2 := by ring
      rw [h₅] at h₁
      rw [h₇] at h₃
      exact HasDerivAt.sub h₁ h₃
    have h_deriv_pos : ∀ x ∈ interior (Set.Icc 0 (1/2)), deriv f x > 0 := by
      intro x hx
      rw [(h_deriv x).deriv]
      apply lt_sub_iff_add_lt.mpr
      rw [zero_add]
      have h_sq : x^2 < (1/2)^2 := by
        rw [interior_Icc] at hx
        apply sq_lt_sq' _ hx.2
        apply lt_trans _ hx.1
        simp
      have : 3 = (12:ℝ) * (1/2)^2 := by norm_num
      rw [this]
      apply mul_lt_mul_of_nonneg_of_pos' (by simp) h_sq
      apply pow_two_nonneg
      simp
    have h_diff : DifferentiableOn ℝ f (Set.Icc 0 (1/2)) := by
      intro x hx
      exact (h_deriv x).differentiableAt.differentiableWithinAt
    have h_cont : ContinuousOn f (Set.Icc 0 (1/2)) :=
      DifferentiableOn.continuousOn h_diff
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1/2)) h_cont h_deriv_pos arange brange hab
  have h₀ : (x : ℝ) -> f (sin x) = sin (3 * x) := by
    intro x
    rw [Real.sin_three_mul]
  have h₁ : f (sin (π / 9)) = sqrt 3 / 2 := by
    have : 3 * (π / 9) = π / 3 := by ring
    rw [h₀, this]
    exact sin_pi_div_three
  have h₂ : f (1 / 3) < f (sin (π / 9)) := by
    have : f (1/3) = 23/27 := by ring
    rw [this, h₁]
    apply lt_of_pow_lt_pow_left₀ 2
    apply div_nonneg (by simp) (by simp)
    ring_nf
    norm_num
  have h₃ : f (sin (π / 9)) < f (7/20) := by
    have : f (7/20) = 1757/2000 := by ring_nf
    rw [this, h₁]
    apply lt_of_pow_lt_pow_left₀ 2
    apply div_nonneg (by simp) (by simp)
    ring_nf
    norm_num
  have h₄ : (20 : ℝ) / 60 = 1 / 3 := by ring;
  have h₅ : 20 * π / 180 = π / 9 := by ring;
  have h₆ : (21 : ℝ) / 60 = 7 / 20 := by ring;
  have sin20range : sin (π / 9) ∈ Set.Icc 0 (1/2) := by
    have nonneg_pi_div_nine : 0 ≤ π / 9 := by apply div_nonneg pi_nonneg (by simp);
    have left : 0 ≤ sin (π / 9) := by
      apply sin_nonneg_of_nonneg_of_le_pi nonneg_pi_div_nine
      apply div_le_self pi_nonneg (by simp)
    have right : sin (π / 9) ≤ 1/2 := by
      rw [← sin_pi_div_six]
      apply sin_le_sin_of_le_of_le_pi_div_two
      apply le_trans _ nonneg_pi_div_nine
      apply neg_nonpos_of_nonneg
      apply div_nonneg pi_nonneg (by simp)
      apply div_le_div₀ pi_nonneg (le_refl π) (by simp) (by norm_num)
      apply div_le_div₀ pi_nonneg (le_refl π) (by simp) (by norm_num)
    exact And.intro left right
  rw [h₄, h₅, h₆]
  apply And.intro
  apply (h_mono.lt_iff_lt _ sin20range).mp h₂
  norm_num
  apply (h_mono.lt_iff_lt sin20range _ ).mp h₃
  norm_num
