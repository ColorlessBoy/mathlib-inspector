-- This module serves as the root of the `MathlibInspector` library.
-- Import modules here that should be built as part of the library.
import Lean.Meta
import MathlibInspector

open Lean Meta

namespace Follow

#eval transformExpr `Eq.mp
#eval transformExpr `Eq.mpr

def Eq.mp : {α : Sort u} -> {β : Sort u} -> @Eq (Sort u) α β -> α -> β :=
  fun {α : Sort u} => fun {β : Sort u} => fun (h : @Eq (Sort u) α β) => fun (a : α) => @Eq.rec (Sort u) α (fun (x : Sort u) => fun (_ : @Eq (Sort u) α x) => x) a β h
def Eq.mpr : {α : Sort u} -> {β : Sort u} -> @Eq (Sort u) α β -> β -> α :=
  fun {α : Sort u} => fun {β : Sort u} => fun (h : @Eq (Sort u) α β) => fun (b : β) => @Eq.rec (Sort u) β (fun (x : Sort u) => fun (_ : @Eq (Sort u) β x) => x) b α (@Eq.symm (Sort u) α β h)
