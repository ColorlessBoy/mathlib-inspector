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
#eval saveConstAndSizeToFile "constAndSize.txt" 2048 100000

#eval printConstantDetails `AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap.proof_1
#eval printConstantDetails `AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app_assoc

#eval (parseName "Mathlib.Geometry.Manifold.PartitionOfUnity._auxLemma.16").toString
#eval printConstantDetailsV2 "Mathlib.Geometry.Manifold.PartitionOfUnity._auxLemma.16"
#eval printConstantDetails `eq_iff_eq_cancel_left

#check @Prod
#eval printConstantDetails `Prod.fst

#check @Iff.intro
#eval printConstantDetails `Iff.refl
#eval printConstantDetails `Iff.intro

def e1 : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

#check @e1
#eval printConstantDetails `e1
#eval printConstantDetails `Exists
#eval printConstantDetails `Nat
#eval printConstantDetails `GT.gt
#eval printConstantDetails `instLTNat
#eval printConstantDetails `OfNat.ofNat
#eval printConstantDetails `instOfNatNat
#eval printConstantDetails `letFun
#eval printConstantDetails `Nat.zero_lt_succ
#eval printConstantDetails `Exists.intro

#check LT
#eval printConstantDetails `LT
#check @LT.lt
#eval printConstantDetails `LT.lt

#eval toPrefixExpr (Expr.lit (Literal.natVal 0))

#check Expr.lit
#check @Literal.natVal
