-- This module serves as the root of the `MathlibInspector` library.
-- Import modules here that should be built as part of the library.
import Lean.Meta
import MathlibInspector

open Lean Meta

-- #eval saveAxiomsToFile "axioms.txt"
-- #eval saveInductivesToFile "inductives.txt"
-- #eval saveThmListToFile "thms.txt"
-- #eval saveMathThmListToFile "maththms.txt"
-- #eval saveConstListToFile "consts.txt"
-- #eval saveThmListToFile "thms.txt"
-- #eval saveConstAndSizeToFile "constAndSize.txt" 2048 100000

#check Nat
#eval printConstantDetails `Set
#eval printConstantDetails `setOf
#check Equiv.Perm.signAux_mul
#check mul_le_mul_left
#eval printConstantDetails `Equiv.Perm.signAux_mul 1024 200000
#eval printConstantDetails `tsum_nonneg

#eval printConstantDetails `Iff
#check @Iff.intro
#eval printConstantDetails `Iff.refl
#eval printConstantDetails `Iff.intro

universe u
theorem ax5 {p : Prop} (h : p) (_ : Type u) : p := h
#eval printConstantDetails `ax5
theorem ax5_2 {p : Prop} : p → ∀ (_: Type u), p := fun h _ ↦ h
#eval printConstantDetails `ax5_2

#check Exists
#eval printConstantDetails `Exists

def mp2 {w0 : Prop} {w1 : Prop} {w2 : Prop} (h1 : w1) (h2 : w2) (h3 : w2 -> w1 -> w0) : w0 := h3 h2 h1

#eval printConstantDetails `mp2
