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


#check Eq.symm
#eval printConstantDetails `Eq.symm
#check proof_irrel
#eval printConstantDetails `proof_irrel
#eval printConstantDetails `proof_irrel_heq
#check iff_of_true
#check proof_irrel_heq

namespace Follow

theorem Eq.symm : {α : Sort u} → {a : α} → {b : α} → a = b → b = a := by
  intro _ a b
  apply Eq.rec
  apply Eq.refl

axiom proof_irrel : {α : Prop} → {h₁ : α} → {h₂ : α} → h₁ = h₂

theorem HEq.of_eq : {α : Sort u} -> {x : α} -> {y : α} -> Eq x y -> HEq x y := by
  intro _ x y
  apply Eq.rec
  apply HEq.refl

theorem proof_irrel_heq_1 : {α : Prop} -> {x : α} -> {y : α} -> HEq x y := by
  intro _ x y
  apply HEq.of_eq
  apply proof_irrel

theorem proof_irrel_heq : {α : Prop} -> {β : Prop} -> {x : α} -> {y : β} -> HEq x y := by
  intro α β x y
  apply @Eq.casesOn Prop α (fun (e : Prop) (f : Eq α e) => (Eq β e -> HEq (propext (iff_of_true x y)) f -> HEq x y)) β
  intro eqba
  apply @Eq.casesOn Prop α (fun (h : Prop) (_ : Eq α h) => ((i : h) -> HEq (propext (iff_of_true x i)) (Eq.refl α) -> HEq x i)) β
  exact Eq.symm eqba
  intro i h1
  apply proof_irrel_heq_1
  apply Eq.refl
  apply HEq.refl

theorem Iff.refl : {α : Prop} -> Iff α α := by
  intro α
  apply Iff.intro
  apply (fun (h: α) => h)
  apply (fun (h: α) => h)

set_option trace.Meta.debug false

example (P Q : Prop) : P → Q → P := by
  proof_step (fun (h₁ : P) (h₂ : Q) => h₁)

theorem Iff.refl2 : (α : Prop) -> Iff α α := by
  proof_step (fun (β : Prop) => @Iff.intro β β)
  proof_step (fun (α : Prop) (h : α) => h)
  proof_step (fun (α : Prop) (h : α → α ) => h)
