import Mathlib

open Finset

theorem algebra_634567 {bounded_pairs : Finset (ℤ × ℤ)}
    {mxn : ℕ} (hmxn : mxn = 100)
    (hbp : bounded_pairs = (Icc (-mxn : ℤ) mxn).product (Icc (-mxn : ℤ) mxn)) :
    #({p ∈ bounded_pairs |
      12 * p.1 ^ 2 - p.1 * p.2 - 6 * p.2 ^ 2 = 0}) = 117 := by

  have : ∀ x y : ℤ, 12 * x ^ 2 - x * y - 6 * y ^ 2 = 0 ↔ 3 * x + 2 * y = 0 ∨ 4 * x - 3 * y = 0 := by
    intro x y
    convert Int.mul_eq_zero using 2
    ring
  simp_rw [this]

  rw [filter_or, card_union, ← filter_and]

  have h0 : (bounded_pairs.filter (fun (x, y) => 3 * x + 2 * y = 0) = ((Finset.Icc (-mxn : ℤ) mxn).filter (3 ∣ ·)).image (fun (y : ℤ) => (-2 * (y / 3), y))) ∧
      (bounded_pairs.filter (fun (x, y) => 4 * x - 3 * y = 0) = ((Finset.Icc (-mxn : ℤ) mxn).filter (4 ∣ ·)).image (fun (y : ℤ) => (3 * (y / 4), y))) := by

    have t1 (x y : ℤ) :
        (3 * x + 2 * y = 0 ↔ 3 ∣ y ∧ x = -2 * (y / 3)) ∧
        (4 * x - 3 * y = 0 ↔ 4 ∣ y ∧ x = 3 * (y / 4)) := by
      omega

    constructor
    all_goals
      ext ⟨x, y⟩
      simp [t1, hbp]
      constructor
      . rintro ⟨hxy, hydvd, rfl⟩
        apply mem_product.mp at hxy
        dsimp at hxy
        obtain ⟨_, hly⟩ := hxy
        simp_all only [Nat.cast_ofNat, neg_mul, mem_Icc, neg_le_neg_iff, and_self]
      . rintro ⟨⟨hly, hydvd⟩, rfl⟩
        simp only [hydvd, and_self, and_true]
        apply mem_product.mpr
        simp only [mem_Icc]
        omega

  have h1 : #(bounded_pairs.filter (fun (x, y) => 3 * x + 2 * y = 0)) = 67 := by
    suffices h_suf : bounded_pairs.filter (fun (x, y) => 3 * x + 2 * y = 0) =
        ((Finset.Icc (-mxn : ℤ) mxn).filter (3 ∣ ·)).image (fun (y : ℤ) => (-2 * (y / 3), y))
    . rw [h_suf, hmxn]
      rfl
    exact h0.1

  have h2 : #(bounded_pairs.filter (fun (x, y) => 4 * x - 3 * y = 0)) = 51 := by
    suffices h_suf : bounded_pairs.filter (fun (x, y) => 4 * x - 3 * y = 0) =
        ((Finset.Icc (-mxn : ℤ) mxn).filter (4 ∣ ·)).image (fun (y : ℤ) => (3 * (y / 4), y))
    . rw [h_suf, hmxn]
      rfl
    exact h0.2

  have h3 : #(bounded_pairs.filter (fun (x, y) => 3 * x + 2 * y = 0 ∧ 4 * x - 3 * y = 0)) = 1 := by
    simp_rw [
      show ∀ x y : ℤ, 3 * x + 2 * y = 0 ∧ 4 * x - 3 * y = 0 ↔ x = 0 ∧ y = 0 by omega,
      show ∀ p : (ℤ × ℤ), p.1 = 0 ∧ p.2 = 0 ↔ p = (0, 0) by simp]
    rw [filter_eq']
    apply card_eq_one.mpr
    use (0, 0)
    simp only [Prod.mk_zero_zero, ite_eq_left_iff]
    have : 0 ∈ bounded_pairs := by
      rw [hbp]
      apply mem_product.mpr
      simp
    exact fun a => False.elim (a this)

  norm_num [h1, h2, h3]
