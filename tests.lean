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

#check OfNat.mk
#eval printConstantDetails `Zero.toOfNat0

inductive MySum (α β : Type)  -- 泛型参数 α 和 β
  | inl (a : α) : MySum α β  -- 左分支，包含类型 α 的值
  | inr (b : β) : MySum α β  -- 右分支，包含类型 β 的值

#check MySum
#print MySum
#eval printConstantDetails `MySum.inl

#check of_eq_true
#eval printConstantDetails `of_eq_true
#check trivial
#eval printConstantDetails `ne_of_apply_ne

#check Not
#check implies_congr

universe u v
#check Sort (max (u + 3) v)
#check Sort (imax 0 u)

#check (a:Sort u) -> (_ : Sort v)
#check (a:Sort u) -> Sort v

#check (a:Sort u) -> (Sort 0 : Sort 1)

#check Lean.Level.imax

#check ne_of_apply_ne
#eval printConstantDetails `ne_of_apply_ne

#check exists₂_imp
#eval printConstantDetails `exists₂_imp

#check Decidable.not_imp_self
#eval printConstantDetails `Decidable.not_imp_self
#eval printConstantDetails `letFun
#eval printConstantDetails `Decidable.not_imp_self
#check Membership.mem
#eval printConstantDetails `Membership.mem
#check ne_of_mem_of_not_mem
#check proof_irrel_heq
#eval printConstantDetails `proof_irrel_heq
#check proof_irrel
#eval printConstantDetails `proof_irrel
#eval printConstantDetails `rfl

#check if_pos
#eval printConstantDetails `if_pos

#check ite
#eval printConstantDetails `ite
#check ite_pos
#check ite_neg
#check ite_congr
#eval printConstantDetails `ite
#check dif_pos

#check Bool.noConfusionType
#check Bool.noConfusion
#check Decidable.decide
