-- This module serves as the root of the `MathlibInspector` library.
-- Import modules here that should be built as part of the library.
import MathlibInspector


#print LinearOrderedField
#print Distrib.left_distrib

namespace Flow
universe u v w u_1
#print Eq
set_option pp.all true
#print WType.elim
#print WType.below
-- inductive HEq : {α : Sort u} -> α -> {β : Sort u} -> β -> Prop where
  -- | refl : {α : Sort u} -> (a : α) -> @HEq α a α a
-- inductive Eq : {α : Sort u_1} -> α -> α -> Prop where
  -- | refl : {α : Sort u_1} -> (a : α) -> @Eq α a a
-- ctor Eq.refl : {α : Sort u_1} -> (a : α) -> @Eq α a a
-- recursor Eq.rec : {α : Sort u_1} -> {a : α} -> {motive : (a1 : α) -> @Eq α a a1 -> Sort u} -> motive a (@Eq.refl α a) -> {a1 : α} -> (t : @Eq α a a1) -> motive a1 t
-- def Eq.casesOn : {α : Sort u_1} -> {a : α} -> {motive : (a1 : α) -> @Eq α a a1 -> Sort u} -> {a1 : α} -> (t : @Eq α a a1) -> motive a (@Eq.refl α a) -> motive a1 t :=
--  fun {α : Sort u_1} => fun {a : α} => fun {motive : (a1 : α) -> @Eq α a a1 -> Sort u} => fun {a1 : α} => fun (t : @Eq α a a1) => fun (refl : motive a (@Eq.refl α a)) => @Eq.rec α a motive refl a1 t
-- inductive Iff : Prop -> Prop -> Prop where
  -- | intro : {a : Prop} -> {b : Prop} -> (a -> b) -> (b -> a) -> @Iff a b
axiom propext : {a : Prop} -> {b : Prop} -> @Iff a b -> @Eq Prop a b
-- ctor Iff.intro : {a : Prop} -> {b : Prop} -> (a -> b) -> (b -> a) -> @Iff a b
theorem iff_of_true : {a : Prop} -> {b : Prop} -> a -> b -> @Iff a b :=
  fun {a : Prop} => fun {b : Prop} => fun (ha : a) => fun (hb : b) => @Iff.intro a b (fun (_ : a) => hb) (fun (_ : b) => ha)
def Eq.ndrec : {α : Sort u2} -> {a : α} -> {motive : α -> Sort u1} -> motive a -> {b : α} -> @Eq α a b -> motive b :=
  fun {α : Sort u2} => fun {a : α} => fun {motive : α -> Sort u1} => fun (m : motive a) => fun {b : α} => fun (h : @Eq α a b) => @Eq.rec α a (fun (x : α) => fun (_ : @Eq α a x) => motive x) m b h
-- ctor HEq.refl : {α : Sort u} -> (a : α) -> @HEq α a α a
def HEq.rfl : {α : Sort u} -> {a : α} -> @HEq α a α a :=
  fun {α : Sort u} => fun {a : α} => @HEq.refl α a
def rfl : {α : Sort u} -> {a : α} -> @Eq α a a :=
  fun {α : Sort u} => fun {a : α} => @Eq.refl α a
theorem Eq.symm : {α : Sort u} -> {a : α} -> {b : α} -> @Eq α a b -> @Eq α b a :=
  fun {α : Sort u} => fun {a : α} => fun {b : α} => fun (h : @Eq α a b) => @Eq.rec α a (fun (x : α) => fun (_ : @Eq α a x) => @Eq α x a) (@rfl α a) b h
theorem proof_irrel_heq : {p : Prop} -> {q : Prop} -> (hp : p) -> (hq : q) -> @HEq p hp q hq :=
  fun {p : Prop} => fun {q : Prop} => fun (hp : p) => fun (hq : q) => @Eq.casesOn Prop p (fun (a : Prop) => fun (t : @Eq Prop p a) => @Eq Prop q a -> @HEq (@Eq Prop p q) (@propext p q (@iff_of_true p q hp hq)) (@Eq Prop p a) t -> @HEq p hp q hq) q (@propext p q (@iff_of_true p q hp hq)) (fun (h : @Eq Prop q p) => @Eq.ndrec Prop p (fun {q1 : Prop} => (hq1 : q1) -> (x : @Eq Prop p q1) -> @HEq (@Eq Prop p q1) x (@Eq Prop p p) (@Eq.refl Prop p) -> @HEq p hp q1 hq1) (fun (_ : p) => fun (x : @Eq Prop p p) => fun (_ : @HEq (@Eq Prop p p) x (@Eq Prop p p) (@Eq.refl Prop p)) => @HEq.rfl p hp) q (@Eq.symm Prop q p h) hq (@propext p q (@iff_of_true p q hp hq))) (@Eq.refl Prop q) (@HEq.refl (@Eq Prop p q) (@propext p q (@iff_of_true p q hp hq)))
-- inductive False : Prop
def Not : Prop -> Prop :=
  fun (a : Prop) => a -> False
-- inductive Or : Prop -> Prop -> Prop where
  -- | inl : {a : Prop} -> {b : Prop} -> a -> @Or a b
  -- | inr : {a : Prop} -> {b : Prop} -> b -> @Or a b
-- ctor Or.inr : {a : Prop} -> {b : Prop} -> b -> @Or a b
def Function.comp : {α : Sort u} -> {β : Sort v} -> {δ : Sort w} -> (β -> δ) -> (α -> β) -> α -> δ :=
  fun {α : Sort u} => fun {β : Sort v} => fun {δ : Sort w} => fun (f : β -> δ) => fun (g : α -> β) => fun (x : α) => f (g x)
-- ctor Or.inl : {a : Prop} -> {b : Prop} -> a -> @Or a b
theorem not_not_em : (a : Prop) -> @Not (@Not (@Or a (@Not a))) :=
  fun (a : Prop) => fun (h : @Not (@Or a (@Not a))) => h (@Or.inr a (@Not a) (@Function.comp a (@Or a (@Not a)) False h (@Or.inl a (@Not a))))
-- inductive And : Prop -> Prop -> Prop where
  -- | intro : {a : Prop} -> {b : Prop} -> a -> b -> @And a b
theorem Iff.refl : (a : Prop) -> @Iff a a :=
  fun (a : Prop) => @Iff.intro a a (fun (h : a) => h) (fun (h : a) => h)
theorem Iff.rfl : {a : Prop} -> @Iff a a :=
  fun {a : Prop} => @Iff.refl a
theorem Iff.of_eq : {a : Prop} -> {b : Prop} -> @Eq Prop a b -> @Iff a b :=
  fun {a : Prop} => fun {b : Prop} => fun (h : @Eq Prop a b) => @Eq.rec Prop a (fun (x : Prop) => fun (_ : @Eq Prop a x) => @Iff a x) (@Iff.rfl a) b h
axiom And.left : {a : Prop} -> {b : Prop} -> @And a b -> a
-- ctor And.intro : {a : Prop} -> {b : Prop} -> a -> b -> @And a b
theorem and_self : (p : Prop) -> @Eq Prop (@And p p) p :=
  fun (p : Prop) => @propext (@And p p) p (@Iff.intro (@And p p) p (fun (x : @And p p) => @And.left p p x) (fun (h : p) => @And.intro p p h h))
theorem and_self_iff : {a : Prop} -> @Iff (@And a a) a :=
  fun {a : Prop} => @Iff.of_eq (@And a a) a (@and_self a)
-- recursor False.rec : (motive : False -> Sort u) -> (t : False) -> motive t
def absurd : {a : Prop} -> {b : Sort v} -> a -> @Not a -> b :=
  fun {a : Prop} => fun {b : Sort v} => fun (h₁ : a) => fun (h₂ : @Not a) => @False.rec (fun (_ : False) => b) (h₂ h₁)
def Not.elim : {a : Prop} -> {α : Sort u_1} -> @Not a -> a -> α :=
  fun {a : Prop} => fun {α : Sort u_1} => fun (H1 : @Not a) => fun (H2 : a) => @absurd a α H2 H1
theorem iff_of_false : {a : Prop} -> {b : Prop} -> @Not a -> @Not b -> @Iff a b :=
  fun {a : Prop} => fun {b : Prop} => fun (ha : @Not a) => fun (hb : @Not b) => @Iff.intro a b (@Not.elim a b ha) (@Not.elim b a hb)
def id : {α : Sort u} -> α -> α :=
  fun {α : Sort u} => fun (a : α) => a
theorem iff_false_intro : {a : Prop} -> @Not a -> @Iff a False :=
  fun {a : Prop} => fun (h : @Not a) => @iff_of_false a False h (@id False)
-- recursor And.rec : {a : Prop} -> {b : Prop} -> {motive : @And a b -> Sort u} -> ((left : a) -> (right : b) -> motive (@And.intro a b left right)) -> (t : @And a b) -> motive t
-- def And.casesOn : {a : Prop} -> {b : Prop} -> {motive : @And a b -> Sort u} -> (t : @And a b) -> ((left : a) -> (right : b) -> motive (@And.intro a b left right)) -> motive t :=
--  fun {a : Prop} => fun {b : Prop} => fun {motive : @And a b -> Sort u} => fun (t : @And a b) => fun (intro : (left : a) -> (right : b) -> motive (@And.intro a b left right)) => @And.rec a b motive (fun (left : a) => fun (right : b) => intro left right) t
def and_not_self.match_1 : {a : Prop} -> (motive : @And a (@Not a) -> Prop) -> (x : @And a (@Not a)) -> ((ha : a) -> (hn : @Not a) -> motive (@And.intro a (@Not a) ha hn)) -> motive x :=
  fun {a : Prop} => fun (motive : @And a (@Not a) -> Prop) => fun (x : @And a (@Not a)) => fun (h_1 : (ha : a) -> (hn : @Not a) -> motive (@And.intro a (@Not a) ha hn)) => @And.casesOn a (@Not a) (fun (x1 : @And a (@Not a)) => motive x1) x (fun (left : a) => fun (right : @Not a) => h_1 left right)
theorem and_not_self : {a : Prop} -> @Not (@And a (@Not a)) :=
  fun {a : Prop} => fun (x : @And a (@Not a)) => @and_not_self.match_1 a (fun (_ : @And a (@Not a)) => False) x (fun (ha : a) => fun (hn : @Not a) => @absurd a False ha hn)
theorem and_not_self_iff : (a : Prop) -> @Iff (@And a (@Not a)) False :=
  fun (a : Prop) => @iff_false_intro (@And a (@Not a)) (@and_not_self a)
def And.symm.match_1 : {a : Prop} -> {b : Prop} -> (motive : @And a b -> Prop) -> (x : @And a b) -> ((ha : a) -> (hb : b) -> motive (@And.intro a b ha hb)) -> motive x :=
  fun {a : Prop} => fun {b : Prop} => fun (motive : @And a b -> Prop) => fun (x : @And a b) => fun (h_1 : (ha : a) -> (hb : b) -> motive (@And.intro a b ha hb)) => @And.casesOn a b (fun (x1 : @And a b) => motive x1) x (fun (left : a) => fun (right : b) => h_1 left right)
theorem And.symm : {a : Prop} -> {b : Prop} -> @And a b -> @And b a :=
  fun {a : Prop} => fun {b : Prop} => fun (x : @And a b) => @And.symm.match_1 a b (fun (_ : @And a b) => @And b a) x (fun (ha : a) => fun (hb : b) => @And.intro b a hb ha)
theorem not_and_self : {a : Prop} -> @Not (@And (@Not a) a) :=
  fun {a : Prop} => @Function.comp (@And (@Not a) a) (@And a (@Not a)) False (@and_not_self a) (@And.symm (@Not a) a)
theorem not_and_self_iff : (a : Prop) -> @Iff (@And (@Not a) a) False :=
  fun (a : Prop) => @iff_false_intro (@And (@Not a) a) (@not_and_self a)
axiom And.right : {a : Prop} -> {b : Prop} -> @And a b -> b
theorem And.imp : {a : Prop} -> {c : Prop} -> {b : Prop} -> {d : Prop} -> (a -> c) -> (b -> d) -> @And a b -> @And c d :=
  fun {a : Prop} => fun {c : Prop} => fun {b : Prop} => fun {d : Prop} => fun (f : a -> c) => fun (g : b -> d) => fun (h : @And a b) => @And.intro c d (f (@And.left a b h)) (g (@And.right a b h))
theorem And.imp_left : {a : Prop} -> {b : Prop} -> {c : Prop} -> (a -> b) -> @And a c -> @And b c :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (h : a -> b) => @And.imp a b c c h (@id c)
theorem And.imp_right : {a : Prop} -> {b : Prop} -> {c : Prop} -> (a -> b) -> @And c a -> @And c b :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (h : a -> b) => @And.imp c c a b (@id c) h
axiom Iff.mp : {a : Prop} -> {b : Prop} -> @Iff a b -> a -> b
axiom Iff.mpr : {a : Prop} -> {b : Prop} -> @Iff a b -> b -> a
theorem and_congr : {a : Prop} -> {c : Prop} -> {b : Prop} -> {d : Prop} -> @Iff a c -> @Iff b d -> @Iff (@And a b) (@And c d) :=
  fun {a : Prop} => fun {c : Prop} => fun {b : Prop} => fun {d : Prop} => fun (h₁ : @Iff a c) => fun (h₂ : @Iff b d) => @Iff.intro (@And a b) (@And c d) (@And.imp a c b d (@Iff.mp a c h₁) (@Iff.mp b d h₂)) (@And.imp c a d b (@Iff.mpr a c h₁) (@Iff.mpr b d h₂))
theorem and_congr_left' : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff a b -> @Iff (@And a c) (@And b c) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (h : @Iff a b) => @and_congr a b c c h (@Iff.rfl c)
theorem and_congr_right' : {b : Prop} -> {c : Prop} -> {a : Prop} -> @Iff b c -> @Iff (@And a b) (@And a c) :=
  fun {b : Prop} => fun {c : Prop} => fun {a : Prop} => fun (h : @Iff b c) => @and_congr a a b c (@Iff.rfl a) h
theorem mt : {a : Prop} -> {b : Prop} -> (a -> b) -> @Not b -> @Not a :=
  fun {a : Prop} => fun {b : Prop} => fun (h₁ : a -> b) => fun (h₂ : @Not b) => fun (ha : a) => h₂ (h₁ ha)
theorem not_and_of_not_left : {a : Prop} -> (b : Prop) -> @Not a -> @Not (@And a b) :=
  fun {a : Prop} => fun (b : Prop) => @mt (@And a b) a (@And.left a b)
theorem not_and_of_not_right : (a : Prop) -> {b : Prop} -> @Not b -> @Not (@And a b) :=
  fun (a : Prop) => fun {b : Prop} => @mt (@And a b) b (@And.right a b)
def and_imp.match_1 : {a : Prop} -> {b : Prop} -> (motive : @And a b -> Prop) -> (x : @And a b) -> ((ha : a) -> (hb : b) -> motive (@And.intro a b ha hb)) -> motive x :=
  fun {a : Prop} => fun {b : Prop} => fun (motive : @And a b -> Prop) => fun (x : @And a b) => fun (h_1 : (ha : a) -> (hb : b) -> motive (@And.intro a b ha hb)) => @And.casesOn a b (fun (x1 : @And a b) => motive x1) x (fun (left : a) => fun (right : b) => h_1 left right)
theorem and_congr_right : {a : Prop} -> {b : Prop} -> {c : Prop} -> (a -> @Iff b c) -> @Iff (@And a b) (@And a c) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (h : a -> @Iff b c) => @Iff.intro (@And a b) (@And a c) (fun (x : @And a b) => @and_imp.match_1 a b (fun (_ : @And a b) => @And a c) x (fun (ha : a) => fun (hb : b) => @And.intro a c ha (@Iff.mp b c (h ha) hb))) (fun (x : @And a c) => @and_imp.match_1 a c (fun (_ : @And a c) => @And a b) x (fun (ha : a) => fun (hb : c) => @And.intro a b ha (@Iff.mpr b c (h ha) hb)))
theorem and_congr_right_eq : {a : Prop} -> {b : Prop} -> {c : Prop} -> (a -> @Eq Prop b c) -> @Eq Prop (@And a b) (@And a c) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (h : a -> @Eq Prop b c) => @propext (@And a b) (@And a c) (@and_congr_right a b c (@Function.comp a (@Eq Prop b c) (@Iff b c) (@Iff.of_eq b c) h))
theorem Iff.trans : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff a b -> @Iff b c -> @Iff a c :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (h₁ : @Iff a b) => fun (h₂ : @Iff b c) => @Iff.intro a c (@Function.comp a b c (@Iff.mp b c h₂) (@Iff.mp a b h₁)) (@Function.comp c b a (@Iff.mpr a b h₁) (@Iff.mpr b c h₂))
theorem And.comm : {a : Prop} -> {b : Prop} -> @Iff (@And a b) (@And b a) :=
  fun {a : Prop} => fun {b : Prop} => @Iff.intro (@And a b) (@And b a) (@And.symm a b) (@And.symm b a)
theorem and_comm : {a : Prop} -> {b : Prop} -> @Iff (@And a b) (@And b a) :=
  fun {a : Prop} => fun {b : Prop} => @And.comm a b
theorem and_congr_left : {c : Prop} -> {a : Prop} -> {b : Prop} -> (c -> @Iff a b) -> @Iff (@And a c) (@And b c) :=
  fun {c : Prop} => fun {a : Prop} => fun {b : Prop} => fun (h : c -> @Iff a b) => @Iff.trans (@And a c) (@And c a) (@And b c) (@and_comm a c) (@Iff.trans (@And c a) (@And c b) (@And b c) (@and_congr_right c a b h) (@and_comm c b))
theorem and_congr_left_eq : {c : Prop} -> {a : Prop} -> {b : Prop} -> (c -> @Eq Prop a b) -> @Eq Prop (@And a c) (@And b c) :=
  fun {c : Prop} => fun {a : Prop} => fun {b : Prop} => fun (h : c -> @Eq Prop a b) => @propext (@And a c) (@And b c) (@and_congr_left c a b (@Function.comp c (@Eq Prop a b) (@Iff a b) (@Iff.of_eq a b) h))
def and_left_comm.match_1 : {a : Prop} -> {b : Prop} -> {c : Prop} -> (motive : @And a (@And b c) -> Prop) -> (x : @And a (@And b c)) -> ((ha : a) -> (hb : b) -> (hc : c) -> motive (@And.intro a (@And b c) ha (@And.intro b c hb hc))) -> motive x :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (motive : @And a (@And b c) -> Prop) => fun (x : @And a (@And b c)) => fun (h_1 : (ha : a) -> (hb : b) -> (hc : c) -> motive (@And.intro a (@And b c) ha (@And.intro b c hb hc))) => @And.casesOn a (@And b c) (fun (x1 : @And a (@And b c)) => motive x1) x (fun (left : a) => fun (right : @And b c) => @And.casesOn b c (fun (x1 : @And b c) => motive (@And.intro a (@And b c) left x1)) right (fun (left1 : b) => fun (right1 : c) => h_1 left left1 right1))
def and_left_comm.match_2 : {a : Prop} -> {b : Prop} -> {c : Prop} -> (motive : @And b (@And a c) -> Prop) -> (x : @And b (@And a c)) -> ((hb : b) -> (ha : a) -> (hc : c) -> motive (@And.intro b (@And a c) hb (@And.intro a c ha hc))) -> motive x :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (motive : @And b (@And a c) -> Prop) => fun (x : @And b (@And a c)) => fun (h_1 : (hb : b) -> (ha : a) -> (hc : c) -> motive (@And.intro b (@And a c) hb (@And.intro a c ha hc))) => @And.casesOn b (@And a c) (fun (x1 : @And b (@And a c)) => motive x1) x (fun (left : b) => fun (right : @And a c) => @And.casesOn a c (fun (x1 : @And a c) => motive (@And.intro b (@And a c) left x1)) right (fun (left1 : a) => fun (right1 : c) => h_1 left left1 right1))
theorem and_left_comm : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@And a (@And b c)) (@And b (@And a c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Iff.intro (@And a (@And b c)) (@And b (@And a c)) (fun (x : @And a (@And b c)) => @and_left_comm.match_1 a b c (fun (_ : @And a (@And b c)) => @And b (@And a c)) x (fun (ha : a) => fun (hb : b) => fun (hc : c) => @And.intro b (@And a c) hb (@And.intro a c ha hc))) (fun (x : @And b (@And a c)) => @and_left_comm.match_2 a b c (fun (_ : @And b (@And a c)) => @And a (@And b c)) x (fun (hb : b) => fun (ha : a) => fun (hc : c) => @And.intro a (@And b c) ha (@And.intro b c hb hc)))
def and_right_comm.match_1 : {a : Prop} -> {b : Prop} -> {c : Prop} -> (motive : @And (@And a b) c -> Prop) -> (x : @And (@And a b) c) -> ((ha : a) -> (hb : b) -> (hc : c) -> motive (@And.intro (@And a b) c (@And.intro a b ha hb) hc)) -> motive x :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (motive : @And (@And a b) c -> Prop) => fun (x : @And (@And a b) c) => fun (h_1 : (ha : a) -> (hb : b) -> (hc : c) -> motive (@And.intro (@And a b) c (@And.intro a b ha hb) hc)) => @And.casesOn (@And a b) c (fun (x1 : @And (@And a b) c) => motive x1) x (fun (left : @And a b) => fun (right : c) => @And.casesOn a b (fun (x1 : @And a b) => motive (@And.intro (@And a b) c x1 right)) left (fun (left1 : a) => fun (right1 : b) => h_1 left1 right1 right))
def and_right_comm.match_2 : {a : Prop} -> {b : Prop} -> {c : Prop} -> (motive : @And (@And a c) b -> Prop) -> (x : @And (@And a c) b) -> ((ha : a) -> (hc : c) -> (hb : b) -> motive (@And.intro (@And a c) b (@And.intro a c ha hc) hb)) -> motive x :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (motive : @And (@And a c) b -> Prop) => fun (x : @And (@And a c) b) => fun (h_1 : (ha : a) -> (hc : c) -> (hb : b) -> motive (@And.intro (@And a c) b (@And.intro a c ha hc) hb)) => @And.casesOn (@And a c) b (fun (x1 : @And (@And a c) b) => motive x1) x (fun (left : @And a c) => fun (right : b) => @And.casesOn a c (fun (x1 : @And a c) => motive (@And.intro (@And a c) b x1 right)) left (fun (left1 : a) => fun (right1 : c) => h_1 left1 right1 right))
theorem and_right_comm : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@And (@And a b) c) (@And (@And a c) b) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Iff.intro (@And (@And a b) c) (@And (@And a c) b) (fun (x : @And (@And a b) c) => @and_right_comm.match_1 a b c (fun (_ : @And (@And a b) c) => @And (@And a c) b) x (fun (ha : a) => fun (hb : b) => fun (hc : c) => @And.intro (@And a c) b (@And.intro a c ha hc) hb)) (fun (x : @And (@And a c) b) => @and_right_comm.match_2 a b c (fun (_ : @And (@And a c) b) => @And (@And a b) c) x (fun (ha : a) => fun (hc : c) => fun (hb : b) => @And.intro (@And a b) c (@And.intro a b ha hb) hc))
def Eq.mpr : {α : Sort u} -> {β : Sort u} -> @Eq (Sort u) α β -> β -> α :=
  fun {α : Sort u} => fun {β : Sort u} => fun (h : @Eq (Sort u) α β) => fun (b : β) => @Eq.rec (Sort u) β (fun (x : Sort u) => fun (_ : @Eq (Sort u) β x) => x) b α (@Eq.symm (Sort u) α β h)
theorem congrArg : {α : Sort u} -> {β : Sort v} -> {a₁ : α} -> {a₂ : α} -> (f : α -> β) -> @Eq α a₁ a₂ -> @Eq β (f a₁) (f a₂) :=
  fun {α : Sort u} => fun {β : Sort v} => fun {a₁ : α} => fun {a₂ : α} => fun (f : α -> β) => fun (h : @Eq α a₁ a₂) => @Eq.rec α a₁ (fun (x : α) => fun (_ : @Eq α a₁ x) => @Eq β (f a₁) (f x)) (@rfl β (f a₁)) a₂ h
theorem and_rotate : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@And a (@And b c)) (@And b (@And c a)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Eq.mpr (@Iff (@And a (@And b c)) (@And b (@And c a))) (@Iff (@And b (@And a c)) (@And b (@And c a))) (@id (@Eq Prop (@Iff (@And a (@And b c)) (@And b (@And c a))) (@Iff (@And b (@And a c)) (@And b (@And c a)))) (@congrArg Prop Prop (@And a (@And b c)) (@And b (@And a c)) (fun (_a : Prop) => @Iff _a (@And b (@And c a))) (@propext (@And a (@And b c)) (@And b (@And a c)) (@and_left_comm a b c)))) (@Eq.mpr (@Iff (@And b (@And a c)) (@And b (@And c a))) (@Iff (@And b (@And c a)) (@And b (@And c a))) (@id (@Eq Prop (@Iff (@And b (@And a c)) (@And b (@And c a))) (@Iff (@And b (@And c a)) (@And b (@And c a)))) (@congrArg Prop Prop (@And a c) (@And c a) (fun (_a : Prop) => @Iff (@And b _a) (@And b (@And c a))) (@propext (@And a c) (@And c a) (@and_comm a c)))) (@Iff.rfl (@And b (@And c a))))
def and_assoc.match_1 : {a : Prop} -> {b : Prop} -> {c : Prop} -> (motive : @And (@And a b) c -> Prop) -> (x : @And (@And a b) c) -> ((ha : a) -> (hb : b) -> (hc : c) -> motive (@And.intro (@And a b) c (@And.intro a b ha hb) hc)) -> motive x :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (motive : @And (@And a b) c -> Prop) => fun (x : @And (@And a b) c) => fun (h_1 : (ha : a) -> (hb : b) -> (hc : c) -> motive (@And.intro (@And a b) c (@And.intro a b ha hb) hc)) => @And.casesOn (@And a b) c (fun (x1 : @And (@And a b) c) => motive x1) x (fun (left : @And a b) => fun (right : c) => @And.casesOn a b (fun (x1 : @And a b) => motive (@And.intro (@And a b) c x1 right)) left (fun (left1 : a) => fun (right1 : b) => h_1 left1 right1 right))
def and_assoc.match_2 : {a : Prop} -> {b : Prop} -> {c : Prop} -> (motive : @And a (@And b c) -> Prop) -> (x : @And a (@And b c)) -> ((ha : a) -> (hb : b) -> (hc : c) -> motive (@And.intro a (@And b c) ha (@And.intro b c hb hc))) -> motive x :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (motive : @And a (@And b c) -> Prop) => fun (x : @And a (@And b c)) => fun (h_1 : (ha : a) -> (hb : b) -> (hc : c) -> motive (@And.intro a (@And b c) ha (@And.intro b c hb hc))) => @And.casesOn a (@And b c) (fun (x1 : @And a (@And b c)) => motive x1) x (fun (left : a) => fun (right : @And b c) => @And.casesOn b c (fun (x1 : @And b c) => motive (@And.intro a (@And b c) left x1)) right (fun (left1 : b) => fun (right1 : c) => h_1 left left1 right1))
theorem and_assoc : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@And (@And a b) c) (@And a (@And b c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Iff.intro (@And (@And a b) c) (@And a (@And b c)) (fun (x : @And (@And a b) c) => @and_assoc.match_1 a b c (fun (_ : @And (@And a b) c) => @And a (@And b c)) x (fun (ha : a) => fun (hb : b) => fun (hc : c) => @And.intro a (@And b c) ha (@And.intro b c hb hc))) (fun (x : @And a (@And b c)) => @and_assoc.match_2 a b c (fun (_ : @And a (@And b c)) => @And (@And a b) c) x (fun (ha : a) => fun (hb : b) => fun (hc : c) => @And.intro (@And a b) c (@And.intro a b ha hb) hc))
theorem and_and_and_comm : {a : Prop} -> {b : Prop} -> {c : Prop} -> {d : Prop} -> @Iff (@And (@And a b) (@And c d)) (@And (@And a c) (@And b d)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun {d : Prop} => @Eq.mpr (@Iff (@And (@And a b) (@And c d)) (@And (@And a c) (@And b d))) (@Iff (@And (@And (@And a b) c) d) (@And (@And a c) (@And b d))) (@id (@Eq Prop (@Iff (@And (@And a b) (@And c d)) (@And (@And a c) (@And b d))) (@Iff (@And (@And (@And a b) c) d) (@And (@And a c) (@And b d)))) (@congrArg Prop Prop (@And (@And a b) (@And c d)) (@And (@And (@And a b) c) d) (fun (_a : Prop) => @Iff _a (@And (@And a c) (@And b d))) (@Eq.symm Prop (@And (@And (@And a b) c) d) (@And (@And a b) (@And c d)) (@propext (@And (@And (@And a b) c) d) (@And (@And a b) (@And c d)) (@and_assoc (@And a b) c d))))) (@Eq.mpr (@Iff (@And (@And (@And a b) c) d) (@And (@And a c) (@And b d))) (@Iff (@And (@And (@And a c) b) d) (@And (@And a c) (@And b d))) (@id (@Eq Prop (@Iff (@And (@And (@And a b) c) d) (@And (@And a c) (@And b d))) (@Iff (@And (@And (@And a c) b) d) (@And (@And a c) (@And b d)))) (@congrArg Prop Prop (@And (@And a b) c) (@And (@And a c) b) (fun (_a : Prop) => @Iff (@And _a d) (@And (@And a c) (@And b d))) (@propext (@And (@And a b) c) (@And (@And a c) b) (@and_right_comm a b c)))) (@Eq.mpr (@Iff (@And (@And (@And a c) b) d) (@And (@And a c) (@And b d))) (@Iff (@And (@And a c) (@And b d)) (@And (@And a c) (@And b d))) (@id (@Eq Prop (@Iff (@And (@And (@And a c) b) d) (@And (@And a c) (@And b d))) (@Iff (@And (@And a c) (@And b d)) (@And (@And a c) (@And b d)))) (@congrArg Prop Prop (@And (@And (@And a c) b) d) (@And (@And a c) (@And b d)) (fun (_a : Prop) => @Iff _a (@And (@And a c) (@And b d))) (@propext (@And (@And (@And a c) b) d) (@And (@And a c) (@And b d)) (@and_assoc (@And a c) b d)))) (@Iff.rfl (@And (@And a c) (@And b d)))))
theorem and_and_left : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@And a (@And b c)) (@And (@And a b) (@And a c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Eq.mpr (@Iff (@And a (@And b c)) (@And (@And a b) (@And a c))) (@Iff (@And a (@And b c)) (@And (@And a a) (@And b c))) (@id (@Eq Prop (@Iff (@And a (@And b c)) (@And (@And a b) (@And a c))) (@Iff (@And a (@And b c)) (@And (@And a a) (@And b c)))) (@congrArg Prop Prop (@And (@And a b) (@And a c)) (@And (@And a a) (@And b c)) (fun (_a : Prop) => @Iff (@And a (@And b c)) _a) (@propext (@And (@And a b) (@And a c)) (@And (@And a a) (@And b c)) (@and_and_and_comm a b a c)))) (@Eq.mpr (@Iff (@And a (@And b c)) (@And (@And a a) (@And b c))) (@Iff (@And a (@And b c)) (@And a (@And b c))) (@id (@Eq Prop (@Iff (@And a (@And b c)) (@And (@And a a) (@And b c))) (@Iff (@And a (@And b c)) (@And a (@And b c)))) (@congrArg Prop Prop (@And a a) a (fun (_a : Prop) => @Iff (@And a (@And b c)) (@And _a (@And b c))) (@and_self a))) (@Iff.rfl (@And a (@And b c))))
theorem and_and_right : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@And (@And a b) c) (@And (@And a c) (@And b c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Eq.mpr (@Iff (@And (@And a b) c) (@And (@And a c) (@And b c))) (@Iff (@And (@And a b) c) (@And (@And a b) (@And c c))) (@id (@Eq Prop (@Iff (@And (@And a b) c) (@And (@And a c) (@And b c))) (@Iff (@And (@And a b) c) (@And (@And a b) (@And c c)))) (@congrArg Prop Prop (@And (@And a c) (@And b c)) (@And (@And a b) (@And c c)) (fun (_a : Prop) => @Iff (@And (@And a b) c) _a) (@propext (@And (@And a c) (@And b c)) (@And (@And a b) (@And c c)) (@and_and_and_comm a c b c)))) (@Eq.mpr (@Iff (@And (@And a b) c) (@And (@And a b) (@And c c))) (@Iff (@And (@And a b) c) (@And (@And a b) c)) (@id (@Eq Prop (@Iff (@And (@And a b) c) (@And (@And a b) (@And c c))) (@Iff (@And (@And a b) c) (@And (@And a b) c))) (@congrArg Prop Prop (@And c c) c (fun (_a : Prop) => @Iff (@And (@And a b) c) (@And (@And a b) _a)) (@and_self c))) (@Iff.rfl (@And (@And a b) c)))
theorem and_iff_left : {b : Prop} -> {a : Prop} -> b -> @Iff (@And a b) a :=
  fun {b : Prop} => fun {a : Prop} => fun (hb : b) => @Iff.intro (@And a b) a (@And.left a b) (fun (x : a) => @And.intro a b x hb)
theorem and_iff_right : {a : Prop} -> {b : Prop} -> a -> @Iff (@And a b) b :=
  fun {a : Prop} => fun {b : Prop} => fun (ha : a) => @Iff.intro (@And a b) b (@And.right a b) (fun (x : b) => @And.intro a b ha x)
-- recursor Or.rec : {a : Prop} -> {b : Prop} -> {motive : @Or a b -> Prop} -> ((h : a) -> motive (@Or.inl a b h)) -> ((h : b) -> motive (@Or.inr a b h)) -> (t : @Or a b) -> motive t
-- def Or.casesOn : {a : Prop} -> {b : Prop} -> {motive : @Or a b -> Prop} -> (t : @Or a b) -> ((h : a) -> motive (@Or.inl a b h)) -> ((h : b) -> motive (@Or.inr a b h)) -> motive t :=
--  fun {a : Prop} => fun {b : Prop} => fun {motive : @Or a b -> Prop} => fun (t : @Or a b) => fun (inl : (h : a) -> motive (@Or.inl a b h)) => fun (inr : (h : b) -> motive (@Or.inr a b h)) => @Or.rec a b motive (fun (h : a) => inl h) (fun (h : b) => inr h) t
def or_self.match_1 : (p : Prop) -> (motive : @Or p p -> Prop) -> (x : @Or p p) -> ((h : p) -> motive (@Or.inl p p h)) -> ((h : p) -> motive (@Or.inr p p h)) -> motive x :=
  fun (p : Prop) => fun (motive : @Or p p -> Prop) => fun (x : @Or p p) => fun (h_1 : (h : p) -> motive (@Or.inl p p h)) => fun (h_2 : (h : p) -> motive (@Or.inr p p h)) => @Or.casesOn p p (fun (x1 : @Or p p) => motive x1) x (fun (h : p) => h_1 h) (fun (h : p) => h_2 h)
theorem or_self : (p : Prop) -> @Eq Prop (@Or p p) p :=
  fun (p : Prop) => @propext (@Or p p) p (@Iff.intro (@Or p p) p (fun (x : @Or p p) => @or_self.match_1 p (fun (_ : @Or p p) => p) x (fun (h : p) => h) (fun (h : p) => h)) (@Or.inl p p))
theorem or_self_iff : {a : Prop} -> @Iff (@Or a a) a :=
  fun {a : Prop} => @Eq.rec Prop a (fun (x : Prop) => fun (_ : @Eq Prop a x) => @Iff x a) (@Iff.rfl a) (@Or a a) (@Eq.symm Prop (@Or a a) a (@or_self a))
def Or.elim.match_1 : {a : Prop} -> {b : Prop} -> (motive : @Or a b -> Prop) -> (h : @Or a b) -> ((h1 : a) -> motive (@Or.inl a b h1)) -> ((h1 : b) -> motive (@Or.inr a b h1)) -> motive h :=
  fun {a : Prop} => fun {b : Prop} => fun (motive : @Or a b -> Prop) => fun (h : @Or a b) => fun (h_1 : (h1 : a) -> motive (@Or.inl a b h1)) => fun (h_2 : (h1 : b) -> motive (@Or.inr a b h1)) => @Or.casesOn a b (fun (x : @Or a b) => motive x) h (fun (h1 : a) => h_1 h1) (fun (h1 : b) => h_2 h1)
theorem Or.elim : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Or a b -> (a -> c) -> (b -> c) -> c :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (h : @Or a b) => fun (left : a -> c) => fun (right : b -> c) => @Or.elim.match_1 a b (fun (_ : @Or a b) => c) h (fun (h1 : a) => left h1) (fun (h1 : b) => right h1)
theorem not_or_intro : {a : Prop} -> {b : Prop} -> @Not a -> @Not b -> @Not (@Or a b) :=
  fun {a : Prop} => fun {b : Prop} => fun (ha : @Not a) => fun (hb : @Not b) => fun (x : @Or a b) => @Or.elim a b False x ha hb
theorem Or.imp : {a : Prop} -> {c : Prop} -> {b : Prop} -> {d : Prop} -> (a -> c) -> (b -> d) -> @Or a b -> @Or c d :=
  fun {a : Prop} => fun {c : Prop} => fun {b : Prop} => fun {d : Prop} => fun (f : a -> c) => fun (g : b -> d) => fun (h : @Or a b) => @Or.elim a b (@Or c d) h (@Function.comp a c (@Or c d) (@Or.inl c d) f) (@Function.comp b d (@Or c d) (@Or.inr c d) g)
theorem or_congr : {a : Prop} -> {c : Prop} -> {b : Prop} -> {d : Prop} -> @Iff a c -> @Iff b d -> @Iff (@Or a b) (@Or c d) :=
  fun {a : Prop} => fun {c : Prop} => fun {b : Prop} => fun {d : Prop} => fun (h₁ : @Iff a c) => fun (h₂ : @Iff b d) => @Iff.intro (@Or a b) (@Or c d) (@Or.imp a c b d (@Iff.mp a c h₁) (@Iff.mp b d h₂)) (@Or.imp c a d b (@Iff.mpr a c h₁) (@Iff.mpr b d h₂))
theorem or_congr_left : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff a b -> @Iff (@Or a c) (@Or b c) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (h : @Iff a b) => @or_congr a b c c h (@Iff.rfl c)
theorem or_congr_right : {b : Prop} -> {c : Prop} -> {a : Prop} -> @Iff b c -> @Iff (@Or a b) (@Or a c) :=
  fun {b : Prop} => fun {c : Prop} => fun {a : Prop} => fun (h : @Iff b c) => @or_congr a a b c (@Iff.rfl a) h
theorem Or.imp_right : {b : Prop} -> {c : Prop} -> {a : Prop} -> (b -> c) -> @Or a b -> @Or a c :=
  fun {b : Prop} => fun {c : Prop} => fun {a : Prop} => fun (f : b -> c) => @Or.imp a a b c (@id a) f
theorem Or.imp_left : {a : Prop} -> {b : Prop} -> {c : Prop} -> (a -> b) -> @Or a c -> @Or b c :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (f : a -> b) => @Or.imp a b c c f (@id c)
theorem or_assoc : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@Or (@Or a b) c) (@Or a (@Or b c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Iff.intro (@Or (@Or a b) c) (@Or a (@Or b c)) (fun (t : @Or (@Or a b) c) => @Or.rec (@Or a b) c (fun (_ : @Or (@Or a b) c) => @Or a (@Or b c)) (@Or.imp_right b (@Or b c) a (@Or.inl b c)) (@Function.comp c (@Or b c) (@Or a (@Or b c)) (@Or.inr a (@Or b c)) (@Or.inr b c)) t) (fun (t : @Or a (@Or b c)) => @Or.rec a (@Or b c) (fun (_ : @Or a (@Or b c)) => @Or (@Or a b) c) (@Function.comp a (@Or a b) (@Or (@Or a b) c) (@Or.inl (@Or a b) c) (@Or.inl a b)) (@Or.imp_left b (@Or a b) c (@Or.inr a b)) t)
theorem Or.symm : {a : Prop} -> {b : Prop} -> @Or a b -> @Or b a :=
  fun {a : Prop} => fun {b : Prop} => fun (t : @Or a b) => @Or.rec a b (fun (_ : @Or a b) => @Or b a) (@Or.inr b a) (@Or.inl b a) t
theorem Or.comm : {a : Prop} -> {b : Prop} -> @Iff (@Or a b) (@Or b a) :=
  fun {a : Prop} => fun {b : Prop} => @Iff.intro (@Or a b) (@Or b a) (@Or.symm a b) (@Or.symm b a)
theorem or_comm : {a : Prop} -> {b : Prop} -> @Iff (@Or a b) (@Or b a) :=
  fun {a : Prop} => fun {b : Prop} => @Or.comm a b
theorem or_left_comm : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@Or a (@Or b c)) (@Or b (@Or a c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Eq.mpr (@Iff (@Or a (@Or b c)) (@Or b (@Or a c))) (@Iff (@Or (@Or a b) c) (@Or b (@Or a c))) (@id (@Eq Prop (@Iff (@Or a (@Or b c)) (@Or b (@Or a c))) (@Iff (@Or (@Or a b) c) (@Or b (@Or a c)))) (@congrArg Prop Prop (@Or a (@Or b c)) (@Or (@Or a b) c) (fun (_a : Prop) => @Iff _a (@Or b (@Or a c))) (@Eq.symm Prop (@Or (@Or a b) c) (@Or a (@Or b c)) (@propext (@Or (@Or a b) c) (@Or a (@Or b c)) (@or_assoc a b c))))) (@Eq.mpr (@Iff (@Or (@Or a b) c) (@Or b (@Or a c))) (@Iff (@Or (@Or a b) c) (@Or (@Or b a) c)) (@id (@Eq Prop (@Iff (@Or (@Or a b) c) (@Or b (@Or a c))) (@Iff (@Or (@Or a b) c) (@Or (@Or b a) c))) (@congrArg Prop Prop (@Or b (@Or a c)) (@Or (@Or b a) c) (fun (_a : Prop) => @Iff (@Or (@Or a b) c) _a) (@Eq.symm Prop (@Or (@Or b a) c) (@Or b (@Or a c)) (@propext (@Or (@Or b a) c) (@Or b (@Or a c)) (@or_assoc b a c))))) (@Eq.mpr (@Iff (@Or (@Or a b) c) (@Or (@Or b a) c)) (@Iff (@Or (@Or b a) c) (@Or (@Or b a) c)) (@id (@Eq Prop (@Iff (@Or (@Or a b) c) (@Or (@Or b a) c)) (@Iff (@Or (@Or b a) c) (@Or (@Or b a) c))) (@congrArg Prop Prop (@Or a b) (@Or b a) (fun (_a : Prop) => @Iff (@Or _a c) (@Or (@Or b a) c)) (@propext (@Or a b) (@Or b a) (@or_comm a b)))) (@Iff.rfl (@Or (@Or b a) c))))
theorem or_right_comm : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@Or (@Or a b) c) (@Or (@Or a c) b) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Eq.mpr (@Iff (@Or (@Or a b) c) (@Or (@Or a c) b)) (@Iff (@Or a (@Or b c)) (@Or (@Or a c) b)) (@id (@Eq Prop (@Iff (@Or (@Or a b) c) (@Or (@Or a c) b)) (@Iff (@Or a (@Or b c)) (@Or (@Or a c) b))) (@congrArg Prop Prop (@Or (@Or a b) c) (@Or a (@Or b c)) (fun (_a : Prop) => @Iff _a (@Or (@Or a c) b)) (@propext (@Or (@Or a b) c) (@Or a (@Or b c)) (@or_assoc a b c)))) (@Eq.mpr (@Iff (@Or a (@Or b c)) (@Or (@Or a c) b)) (@Iff (@Or a (@Or b c)) (@Or a (@Or c b))) (@id (@Eq Prop (@Iff (@Or a (@Or b c)) (@Or (@Or a c) b)) (@Iff (@Or a (@Or b c)) (@Or a (@Or c b)))) (@congrArg Prop Prop (@Or (@Or a c) b) (@Or a (@Or c b)) (fun (_a : Prop) => @Iff (@Or a (@Or b c)) _a) (@propext (@Or (@Or a c) b) (@Or a (@Or c b)) (@or_assoc a c b)))) (@Eq.mpr (@Iff (@Or a (@Or b c)) (@Or a (@Or c b))) (@Iff (@Or a (@Or c b)) (@Or a (@Or c b))) (@id (@Eq Prop (@Iff (@Or a (@Or b c)) (@Or a (@Or c b))) (@Iff (@Or a (@Or c b)) (@Or a (@Or c b)))) (@congrArg Prop Prop (@Or b c) (@Or c b) (fun (_a : Prop) => @Iff (@Or a _a) (@Or a (@Or c b))) (@propext (@Or b c) (@Or c b) (@or_comm b c)))) (@Iff.rfl (@Or a (@Or c b)))))
theorem or_or_or_comm : {a : Prop} -> {b : Prop} -> {c : Prop} -> {d : Prop} -> @Iff (@Or (@Or a b) (@Or c d)) (@Or (@Or a c) (@Or b d)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun {d : Prop} => @Eq.mpr (@Iff (@Or (@Or a b) (@Or c d)) (@Or (@Or a c) (@Or b d))) (@Iff (@Or (@Or (@Or a b) c) d) (@Or (@Or a c) (@Or b d))) (@id (@Eq Prop (@Iff (@Or (@Or a b) (@Or c d)) (@Or (@Or a c) (@Or b d))) (@Iff (@Or (@Or (@Or a b) c) d) (@Or (@Or a c) (@Or b d)))) (@congrArg Prop Prop (@Or (@Or a b) (@Or c d)) (@Or (@Or (@Or a b) c) d) (fun (_a : Prop) => @Iff _a (@Or (@Or a c) (@Or b d))) (@Eq.symm Prop (@Or (@Or (@Or a b) c) d) (@Or (@Or a b) (@Or c d)) (@propext (@Or (@Or (@Or a b) c) d) (@Or (@Or a b) (@Or c d)) (@or_assoc (@Or a b) c d))))) (@Eq.mpr (@Iff (@Or (@Or (@Or a b) c) d) (@Or (@Or a c) (@Or b d))) (@Iff (@Or (@Or (@Or a c) b) d) (@Or (@Or a c) (@Or b d))) (@id (@Eq Prop (@Iff (@Or (@Or (@Or a b) c) d) (@Or (@Or a c) (@Or b d))) (@Iff (@Or (@Or (@Or a c) b) d) (@Or (@Or a c) (@Or b d)))) (@congrArg Prop Prop (@Or (@Or a b) c) (@Or (@Or a c) b) (fun (_a : Prop) => @Iff (@Or _a d) (@Or (@Or a c) (@Or b d))) (@propext (@Or (@Or a b) c) (@Or (@Or a c) b) (@or_right_comm a b c)))) (@Eq.mpr (@Iff (@Or (@Or (@Or a c) b) d) (@Or (@Or a c) (@Or b d))) (@Iff (@Or (@Or a c) (@Or b d)) (@Or (@Or a c) (@Or b d))) (@id (@Eq Prop (@Iff (@Or (@Or (@Or a c) b) d) (@Or (@Or a c) (@Or b d))) (@Iff (@Or (@Or a c) (@Or b d)) (@Or (@Or a c) (@Or b d)))) (@congrArg Prop Prop (@Or (@Or (@Or a c) b) d) (@Or (@Or a c) (@Or b d)) (fun (_a : Prop) => @Iff _a (@Or (@Or a c) (@Or b d))) (@propext (@Or (@Or (@Or a c) b) d) (@Or (@Or a c) (@Or b d)) (@or_assoc (@Or a c) b d)))) (@Iff.rfl (@Or (@Or a c) (@Or b d)))))
theorem or_or_distrib_left : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@Or a (@Or b c)) (@Or (@Or a b) (@Or a c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Eq.mpr (@Iff (@Or a (@Or b c)) (@Or (@Or a b) (@Or a c))) (@Iff (@Or a (@Or b c)) (@Or (@Or a a) (@Or b c))) (@id (@Eq Prop (@Iff (@Or a (@Or b c)) (@Or (@Or a b) (@Or a c))) (@Iff (@Or a (@Or b c)) (@Or (@Or a a) (@Or b c)))) (@congrArg Prop Prop (@Or (@Or a b) (@Or a c)) (@Or (@Or a a) (@Or b c)) (fun (_a : Prop) => @Iff (@Or a (@Or b c)) _a) (@propext (@Or (@Or a b) (@Or a c)) (@Or (@Or a a) (@Or b c)) (@or_or_or_comm a b a c)))) (@Eq.mpr (@Iff (@Or a (@Or b c)) (@Or (@Or a a) (@Or b c))) (@Iff (@Or a (@Or b c)) (@Or a (@Or b c))) (@id (@Eq Prop (@Iff (@Or a (@Or b c)) (@Or (@Or a a) (@Or b c))) (@Iff (@Or a (@Or b c)) (@Or a (@Or b c)))) (@congrArg Prop Prop (@Or a a) a (fun (_a : Prop) => @Iff (@Or a (@Or b c)) (@Or _a (@Or b c))) (@or_self a))) (@Iff.rfl (@Or a (@Or b c))))
theorem or_or_distrib_right : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@Or (@Or a b) c) (@Or (@Or a c) (@Or b c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Eq.mpr (@Iff (@Or (@Or a b) c) (@Or (@Or a c) (@Or b c))) (@Iff (@Or (@Or a b) c) (@Or (@Or a b) (@Or c c))) (@id (@Eq Prop (@Iff (@Or (@Or a b) c) (@Or (@Or a c) (@Or b c))) (@Iff (@Or (@Or a b) c) (@Or (@Or a b) (@Or c c)))) (@congrArg Prop Prop (@Or (@Or a c) (@Or b c)) (@Or (@Or a b) (@Or c c)) (fun (_a : Prop) => @Iff (@Or (@Or a b) c) _a) (@propext (@Or (@Or a c) (@Or b c)) (@Or (@Or a b) (@Or c c)) (@or_or_or_comm a c b c)))) (@Eq.mpr (@Iff (@Or (@Or a b) c) (@Or (@Or a b) (@Or c c))) (@Iff (@Or (@Or a b) c) (@Or (@Or a b) c)) (@id (@Eq Prop (@Iff (@Or (@Or a b) c) (@Or (@Or a b) (@Or c c))) (@Iff (@Or (@Or a b) c) (@Or (@Or a b) c))) (@congrArg Prop Prop (@Or c c) c (fun (_a : Prop) => @Iff (@Or (@Or a b) c) (@Or (@Or a b) _a)) (@or_self c))) (@Iff.rfl (@Or (@Or a b) c)))
-- inductive True : Prop where
--  | intro : True
-- ctor True.intro : True
theorem trivial : True :=
  True.intro
theorem of_eq_true : {p : Prop} -> @Eq Prop p True -> p :=
  fun {p : Prop} => fun (h : @Eq Prop p True) => @Eq.rec Prop True (fun (x : Prop) => fun (_ : @Eq Prop True x) => x) trivial p (@Eq.symm Prop p True h)
theorem Eq.trans : {α : Sort u} -> {a : α} -> {b : α} -> {c : α} -> @Eq α a b -> @Eq α b c -> @Eq α a c :=
  fun {α : Sort u} => fun {a : α} => fun {b : α} => fun {c : α} => fun (h₁ : @Eq α a b) => fun (h₂ : @Eq α b c) => @Eq.rec α b (fun (x : α) => fun (_ : @Eq α b x) => @Eq α a x) h₁ c h₂
theorem Init.PropLemmas._auxLemma_3 : {a : Prop} -> {b : Prop} -> @Eq Prop (@Or a b) (@Or b a) :=
  fun {a : Prop} => fun {b : Prop} => @propext (@Or a b) (@Or b a) (@Or.comm a b)
theorem Init.PropLemmas._auxLemma_2 : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Eq Prop (@Or a (@Or b c)) (@Or b (@Or a c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @propext (@Or a (@Or b c)) (@Or b (@Or a c)) (@or_left_comm a b c)
theorem eq_true : {p : Prop} -> p -> @Eq Prop p True :=
  fun {p : Prop} => fun (h : p) => @propext p True (@Iff.intro p True (fun (_ : p) => trivial) (fun (_ : True) => h))
theorem iff_self : (p : Prop) -> @Eq Prop (@Iff p p) True :=
  fun (p : Prop) => @eq_true (@Iff p p) (@Iff.rfl p)
theorem or_rotate : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@Or a (@Or b c)) (@Or b (@Or c a)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @of_eq_true (@Iff (@Or a (@Or b c)) (@Or b (@Or c a))) (@Eq.trans Prop (@Iff (@Or a (@Or b c)) (@Or b (@Or c a))) (@Iff (@Or a (@Or b c)) (@Or a (@Or b c))) True (@congrArg Prop Prop (@Or b (@Or c a)) (@Or a (@Or b c)) (@Iff (@Or a (@Or b c))) (@Eq.trans Prop (@Or b (@Or c a)) (@Or b (@Or a c)) (@Or a (@Or b c)) (@congrArg Prop Prop (@Or c a) (@Or a c) (@Or b) (@Init.PropLemmas._auxLemma_3 c a)) (@Init.PropLemmas._auxLemma_2 b a c))) (@iff_self (@Or a (@Or b c))))
theorem or_iff_left_of_imp : {b : Prop} -> {a : Prop} -> (b -> a) -> @Iff (@Or a b) a :=
  fun {b : Prop} => fun {a : Prop} => fun (hb : b -> a) => @Iff.intro (@Or a b) a (fun (t : @Or a b) => @Or.rec a b (fun (_ : @Or a b) => a) (@id a) hb t) (@Or.inl a b)
theorem or_iff_left_iff_imp : {a : Prop} -> {b : Prop} -> @Iff (@Iff (@Or a b) a) (b -> a) :=
  fun {a : Prop} => fun {b : Prop} => @Iff.intro (@Iff (@Or a b) a) (b -> a) (fun (x : @Iff (@Or a b) a) => @Function.comp b (@Or a b) a (@Iff.mp (@Or a b) a x) (@Or.inr a b)) (@or_iff_left_of_imp b a)
theorem or_iff_left : {b : Prop} -> {a : Prop} -> @Not b -> @Iff (@Or a b) a :=
  fun {b : Prop} => fun {a : Prop} => fun (hb : @Not b) => @Iff.mpr (@Iff (@Or a b) a) (b -> a) (@or_iff_left_iff_imp a b) (@Not.elim b a hb)
theorem or_iff_right_iff_imp : {a : Prop} -> {b : Prop} -> @Iff (@Iff (@Or a b) b) (a -> b) :=
  fun {a : Prop} => fun {b : Prop} => @Eq.mpr (@Iff (@Iff (@Or a b) b) (a -> b)) (@Iff (@Iff (@Or b a) b) (a -> b)) (@id (@Eq Prop (@Iff (@Iff (@Or a b) b) (a -> b)) (@Iff (@Iff (@Or b a) b) (a -> b))) (@congrArg Prop Prop (@Or a b) (@Or b a) (fun (_a : Prop) => @Iff (@Iff _a b) (a -> b)) (@propext (@Or a b) (@Or b a) (@or_comm a b)))) (@Eq.mpr (@Iff (@Iff (@Or b a) b) (a -> b)) (@Iff (a -> b) (a -> b)) (@id (@Eq Prop (@Iff (@Iff (@Or b a) b) (a -> b)) (@Iff (a -> b) (a -> b))) (@congrArg Prop Prop (@Iff (@Or b a) b) (a -> b) (fun (_a : Prop) => @Iff _a (a -> b)) (@propext (@Iff (@Or b a) b) (a -> b) (@or_iff_left_iff_imp b a)))) (@Iff.rfl (a -> b)))
theorem or_iff_right : {a : Prop} -> {b : Prop} -> @Not a -> @Iff (@Or a b) b :=
  fun {a : Prop} => fun {b : Prop} => fun (ha : @Not a) => @Iff.mpr (@Iff (@Or a b) b) (a -> b) (@or_iff_right_iff_imp a b) (@Not.elim a b ha)
def not_imp_of_and_not.match_1 : {a : Prop} -> {b : Prop} -> (motive : @And a (@Not b) -> (a -> b) -> Prop) -> (x : @And a (@Not b)) -> (x1 : a -> b) -> ((ha : a) -> (hb : @Not b) -> (h : a -> b) -> motive (@And.intro a (@Not b) ha hb) h) -> motive x x1 :=
  fun {a : Prop} => fun {b : Prop} => fun (motive : @And a (@Not b) -> (a -> b) -> Prop) => fun (x : @And a (@Not b)) => fun (x1 : a -> b) => fun (h_1 : (ha : a) -> (hb : @Not b) -> (h : a -> b) -> motive (@And.intro a (@Not b) ha hb) h) => @And.casesOn a (@Not b) (fun (x2 : @And a (@Not b)) => motive x2 x1) x (fun (left : a) => fun (right : @Not b) => h_1 left right x1)
theorem not_imp_of_and_not : {a : Prop} -> {b : Prop} -> @And a (@Not b) -> @Not (a -> b) :=
  fun {a : Prop} => fun {b : Prop} => fun (x : @And a (@Not b)) => fun (x1 : a -> b) => @not_imp_of_and_not.match_1 a b (fun (_ : @And a (@Not b)) => fun (_ : a -> b) => False) x x1 (fun (ha : a) => fun (hb : @Not b) => fun (h : a -> b) => hb (h ha))
theorem imp_and : {b : Prop} -> {c : Prop} -> {α : Sort u_1} -> @Iff (α -> @And b c) (@And (α -> b) (α -> c)) :=
  fun {b : Prop} => fun {c : Prop} => fun {α : Sort u_1} => @Iff.intro (α -> @And b c) (@And (α -> b) (α -> c)) (fun (h : α -> @And b c) => @And.intro (α -> b) (α -> c) (fun (ha : α) => @And.left b c (h ha)) (fun (ha : α) => @And.right b c (h ha))) (fun (h : @And (α -> b) (α -> c)) => fun (ha : α) => @And.intro b c (@And.left (α -> b) (α -> c) h ha) (@And.right (α -> b) (α -> c) h ha))
theorem and_imp : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@And a b -> c) (a -> b -> c) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Iff.intro (@And a b -> c) (a -> b -> c) (fun (h : @And a b -> c) => fun (ha : a) => fun (hb : b) => h (@And.intro a b ha hb)) (fun (h : a -> b -> c) => fun (x : @And a b) => @and_imp.match_1 a b (fun (_ : @And a b) => c) x (fun (ha : a) => fun (hb : b) => h ha hb))
theorem not_and : {a : Prop} -> {b : Prop} -> @Iff (@Not (@And a b)) (a -> @Not b) :=
  fun {a : Prop} => fun {b : Prop} => @and_imp a b False
def flip : {α : Sort u} -> {β : Sort v} -> {φ : Sort w} -> (α -> β -> φ) -> β -> α -> φ :=
  fun {α : Sort u} => fun {β : Sort v} => fun {φ : Sort w} => fun (f : α -> β -> φ) => fun (b : β) => fun (a : α) => f a b
theorem imp.swap : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (a -> b -> c) (b -> a -> c) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Iff.intro (a -> b -> c) (b -> a -> c) (@flip a b c) (@flip b a c)
theorem imp_not_comm : {a : Prop} -> {b : Prop} -> @Iff (a -> @Not b) (b -> @Not a) :=
  fun {a : Prop} => fun {b : Prop} => @imp.swap a b False
theorem not_and' : {a : Prop} -> {b : Prop} -> @Iff (@Not (@And a b)) (b -> @Not a) :=
  fun {a : Prop} => fun {b : Prop} => @Iff.trans (@Not (@And a b)) (a -> @Not b) (b -> @Not a) (@not_and a b) (@imp_not_comm a b)
def and_or_left.match_1 : {a : Prop} -> {b : Prop} -> {c : Prop} -> (motive : @And a (@Or b c) -> Prop) -> (x : @And a (@Or b c)) -> ((ha : a) -> (hbc : @Or b c) -> motive (@And.intro a (@Or b c) ha hbc)) -> motive x :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (motive : @And a (@Or b c) -> Prop) => fun (x : @And a (@Or b c)) => fun (h_1 : (ha : a) -> (hbc : @Or b c) -> motive (@And.intro a (@Or b c) ha hbc)) => @And.casesOn a (@Or b c) (fun (x1 : @And a (@Or b c)) => motive x1) x (fun (left : a) => fun (right : @Or b c) => h_1 left right)
theorem and_or_left : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@And a (@Or b c)) (@Or (@And a b) (@And a c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Iff.intro (@And a (@Or b c)) (@Or (@And a b) (@And a c)) (fun (x : @And a (@Or b c)) => @and_or_left.match_1 a b c (fun (_ : @And a (@Or b c)) => @Or (@And a b) (@And a c)) x (fun (ha : a) => fun (hbc : @Or b c) => @Or.imp b (@And a b) c (@And a c) (@And.intro a b ha) (@And.intro a c ha) hbc)) (fun (t : @Or (@And a b) (@And a c)) => @Or.rec (@And a b) (@And a c) (fun (_ : @Or (@And a b) (@And a c)) => @And a (@Or b c)) (@And.imp_right b (@Or b c) a (@Or.inl b c)) (@And.imp_right c (@Or b c) a (@Or.inr b c)) t)
theorem or_and_right : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@And (@Or a b) c) (@Or (@And a c) (@And b c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Eq.mpr (@Iff (@And (@Or a b) c) (@Or (@And a c) (@And b c))) (@Iff (@And c (@Or a b)) (@Or (@And a c) (@And b c))) (@id (@Eq Prop (@Iff (@And (@Or a b) c) (@Or (@And a c) (@And b c))) (@Iff (@And c (@Or a b)) (@Or (@And a c) (@And b c)))) (@congrArg Prop Prop (@And (@Or a b) c) (@And c (@Or a b)) (fun (_a : Prop) => @Iff _a (@Or (@And a c) (@And b c))) (@propext (@And (@Or a b) c) (@And c (@Or a b)) (@and_comm (@Or a b) c)))) (@Eq.mpr (@Iff (@And c (@Or a b)) (@Or (@And a c) (@And b c))) (@Iff (@Or (@And c a) (@And c b)) (@Or (@And a c) (@And b c))) (@id (@Eq Prop (@Iff (@And c (@Or a b)) (@Or (@And a c) (@And b c))) (@Iff (@Or (@And c a) (@And c b)) (@Or (@And a c) (@And b c)))) (@congrArg Prop Prop (@And c (@Or a b)) (@Or (@And c a) (@And c b)) (fun (_a : Prop) => @Iff _a (@Or (@And a c) (@And b c))) (@propext (@And c (@Or a b)) (@Or (@And c a) (@And c b)) (@and_or_left c a b)))) (@Eq.mpr (@Iff (@Or (@And c a) (@And c b)) (@Or (@And a c) (@And b c))) (@Iff (@Or (@And a c) (@And c b)) (@Or (@And a c) (@And b c))) (@id (@Eq Prop (@Iff (@Or (@And c a) (@And c b)) (@Or (@And a c) (@And b c))) (@Iff (@Or (@And a c) (@And c b)) (@Or (@And a c) (@And b c)))) (@congrArg Prop Prop (@And c a) (@And a c) (fun (_a : Prop) => @Iff (@Or _a (@And c b)) (@Or (@And a c) (@And b c))) (@propext (@And c a) (@And a c) (@and_comm c a)))) (@Eq.mpr (@Iff (@Or (@And a c) (@And c b)) (@Or (@And a c) (@And b c))) (@Iff (@Or (@And a c) (@And b c)) (@Or (@And a c) (@And b c))) (@id (@Eq Prop (@Iff (@Or (@And a c) (@And c b)) (@Or (@And a c) (@And b c))) (@Iff (@Or (@And a c) (@And b c)) (@Or (@And a c) (@And b c)))) (@congrArg Prop Prop (@And c b) (@And b c) (fun (_a : Prop) => @Iff (@Or (@And a c) _a) (@Or (@And a c) (@And b c))) (@propext (@And c b) (@And b c) (@and_comm c b)))) (@Iff.rfl (@Or (@And a c) (@And b c))))))
theorem or_and_left : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@Or a (@And b c)) (@And (@Or a b) (@Or a c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Iff.intro (@Or a (@And b c)) (@And (@Or a b) (@Or a c)) (fun (t : @Or a (@And b c)) => @Or.rec a (@And b c) (fun (_ : @Or a (@And b c)) => @And (@Or a b) (@Or a c)) (fun (ha : a) => @And.intro (@Or a b) (@Or a c) (@Or.inl a b ha) (@Or.inl a c ha)) (@And.imp b (@Or a b) c (@Or a c) (@Or.inr a b) (@Or.inr a c)) t) (fun (t : @And (@Or a b) (@Or a c)) => @And.rec (@Or a b) (@Or a c) (fun (_ : @And (@Or a b) (@Or a c)) => @Or a (@And b c)) (fun (t1 : @Or a b) => @Or.rec a b (fun (_ : @Or a b) => @Or a c -> @Or a (@And b c)) (fun (x : a) => fun (_ : @Or a c) => @Or.inl a (@And b c) x) (@Function.comp b (c -> @And b c) (@Or a c -> @Or a (@And b c)) (@Or.imp_right c (@And b c) a) (@And.intro b c)) t1) t)
theorem and_or_right : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@Or (@And a b) c) (@And (@Or a c) (@Or b c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Eq.mpr (@Iff (@Or (@And a b) c) (@And (@Or a c) (@Or b c))) (@Iff (@Or c (@And a b)) (@And (@Or a c) (@Or b c))) (@id (@Eq Prop (@Iff (@Or (@And a b) c) (@And (@Or a c) (@Or b c))) (@Iff (@Or c (@And a b)) (@And (@Or a c) (@Or b c)))) (@congrArg Prop Prop (@Or (@And a b) c) (@Or c (@And a b)) (fun (_a : Prop) => @Iff _a (@And (@Or a c) (@Or b c))) (@propext (@Or (@And a b) c) (@Or c (@And a b)) (@or_comm (@And a b) c)))) (@Eq.mpr (@Iff (@Or c (@And a b)) (@And (@Or a c) (@Or b c))) (@Iff (@And (@Or c a) (@Or c b)) (@And (@Or a c) (@Or b c))) (@id (@Eq Prop (@Iff (@Or c (@And a b)) (@And (@Or a c) (@Or b c))) (@Iff (@And (@Or c a) (@Or c b)) (@And (@Or a c) (@Or b c)))) (@congrArg Prop Prop (@Or c (@And a b)) (@And (@Or c a) (@Or c b)) (fun (_a : Prop) => @Iff _a (@And (@Or a c) (@Or b c))) (@propext (@Or c (@And a b)) (@And (@Or c a) (@Or c b)) (@or_and_left c a b)))) (@Eq.mpr (@Iff (@And (@Or c a) (@Or c b)) (@And (@Or a c) (@Or b c))) (@Iff (@And (@Or a c) (@Or c b)) (@And (@Or a c) (@Or b c))) (@id (@Eq Prop (@Iff (@And (@Or c a) (@Or c b)) (@And (@Or a c) (@Or b c))) (@Iff (@And (@Or a c) (@Or c b)) (@And (@Or a c) (@Or b c)))) (@congrArg Prop Prop (@Or c a) (@Or a c) (fun (_a : Prop) => @Iff (@And _a (@Or c b)) (@And (@Or a c) (@Or b c))) (@propext (@Or c a) (@Or a c) (@or_comm c a)))) (@Eq.mpr (@Iff (@And (@Or a c) (@Or c b)) (@And (@Or a c) (@Or b c))) (@Iff (@And (@Or a c) (@Or b c)) (@And (@Or a c) (@Or b c))) (@id (@Eq Prop (@Iff (@And (@Or a c) (@Or c b)) (@And (@Or a c) (@Or b c))) (@Iff (@And (@Or a c) (@Or b c)) (@And (@Or a c) (@Or b c)))) (@congrArg Prop Prop (@Or c b) (@Or b c) (fun (_a : Prop) => @Iff (@And (@Or a c) _a) (@And (@Or a c) (@Or b c))) (@propext (@Or c b) (@Or b c) (@or_comm c b)))) (@Iff.rfl (@And (@Or a c) (@Or b c))))))
def or_imp.match_1 : {a : Prop} -> {b : Prop} -> {c : Prop} -> (motive : @And (a -> c) (b -> c) -> Prop) -> (x : @And (a -> c) (b -> c)) -> ((ha : a -> c) -> (hb : b -> c) -> motive (@And.intro (a -> c) (b -> c) ha hb)) -> motive x :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => fun (motive : @And (a -> c) (b -> c) -> Prop) => fun (x : @And (a -> c) (b -> c)) => fun (h_1 : (ha : a -> c) -> (hb : b -> c) -> motive (@And.intro (a -> c) (b -> c) ha hb)) => @And.casesOn (a -> c) (b -> c) (fun (x1 : @And (a -> c) (b -> c)) => motive x1) x (fun (left : a -> c) => fun (right : b -> c) => h_1 left right)
theorem or_imp : {a : Prop} -> {b : Prop} -> {c : Prop} -> @Iff (@Or a b -> c) (@And (a -> c) (b -> c)) :=
  fun {a : Prop} => fun {b : Prop} => fun {c : Prop} => @Iff.intro (@Or a b -> c) (@And (a -> c) (b -> c)) (fun (h : @Or a b -> c) => @And.intro (a -> c) (b -> c) (@Function.comp a (@Or a b) c h (@Or.inl a b)) (@Function.comp b (@Or a b) c h (@Or.inr a b))) (fun (x : @And (a -> c) (b -> c)) => @or_imp.match_1 a b c (fun (_ : @And (a -> c) (b -> c)) => @Or a b -> c) x (fun (ha : a -> c) => fun (hb : b -> c) => fun (t : @Or a b) => @Or.rec a b (fun (_ : @Or a b) => c) ha hb t))
theorem not_and_of_not_or_not : {a : Prop} -> {b : Prop} -> @Or (@Not a) (@Not b) -> @Not (@And a b) :=
  fun {a : Prop} => fun {b : Prop} => fun (h : @Or (@Not a) (@Not b)) => @Or.elim (@Not a) (@Not b) (@Not (@And a b)) h (@mt (@And a b) a (fun (x : @And a b) => @And.left a b x)) (@mt (@And a b) b (fun (x : @And a b) => @And.right a b x))
def Ne : {α : Sort u} -> α -> α -> Prop :=
  fun {α : Sort u} => fun (a : α) => fun (b : α) => @Not (@Eq α a b)
theorem ne_of_apply_ne : {α : Sort u_1} -> {β : Sort u_2} -> (f : α -> β) -> {x : α} -> {y : α} -> @Ne β (f x) (f y) -> @Ne α x y :=
  fun {α : Sort u_1} => fun {β : Sort u_2} => fun (f : α -> β) => fun {x : α} => fun {y : α} => @mt (@Eq α x y) (@Eq β (f x) (f y)) (@congrArg α β x y f)
-- inductive Decidable : Prop -> Type where
--  | isFalse : {p : Prop} -> @Not p -> @Decidable p
  --  | isTrue : {p : Prop} -> p -> @Decidable p
-- ctor Decidable.isFalse : {p : Prop} -> @Not p -> @Decidable p
-- ctor Decidable.isTrue : {p : Prop} -> p -> @Decidable p
-- recursor Decidable.rec : {p : Prop} -> {motive : @Decidable p -> Sort u} -> ((h : @Not p) -> motive (@Decidable.isFalse p h)) -> ((h : p) -> motive (@Decidable.isTrue p h)) -> (t : @Decidable p) -> motive t
-- def Decidable.casesOn : {p : Prop} -> {motive : @Decidable p -> Sort u} -> (t : @Decidable p) -> ((h : @Not p) -> motive (@Decidable.isFalse p h)) -> ((h : p) -> motive (@Decidable.isTrue p h)) -> motive t :=
--  fun {p : Prop} => fun {motive : @Decidable p -> Sort u} => fun (t : @Decidable p) => fun (isFalse : (h : @Not p) -> motive (@Decidable.isFalse p h)) => fun (isTrue : (h : p) -> motive (@Decidable.isTrue p h)) => @Decidable.rec p motive (fun (h : @Not p) => isFalse h) (fun (h : p) => isTrue h) t
def ite : {α : Sort u} -> (c : Prop) -> @Decidable c -> α -> α -> α :=
  fun {α : Sort u} => fun (c : Prop) => fun (h : @Decidable c) => fun (t : α) => fun (e : α) => @Decidable.casesOn c (fun (_ : @Decidable c) => α) h (fun (_ : @Not c) => e) (fun (_ : c) => t)
theorem congr : {α : Sort u} -> {β : Sort v} -> {f₁ : α -> β} -> {f₂ : α -> β} -> {a₁ : α} -> {a₂ : α} -> @Eq (α -> β) f₁ f₂ -> @Eq α a₁ a₂ -> @Eq β (f₁ a₁) (f₂ a₂) :=
  fun {α : Sort u} => fun {β : Sort v} => fun {f₁ : α -> β} => fun {f₂ : α -> β} => fun {a₁ : α} => fun {a₂ : α} => fun (h₁ : @Eq (α -> β) f₁ f₂) => fun (h₂ : @Eq α a₁ a₂) => @Eq.rec (α -> β) f₁ (fun (x : α -> β) => fun (_ : @Eq (α -> β) f₁ x) => @Eq β (f₁ a₁) (x a₂)) (@Eq.rec α a₁ (fun (x : α) => fun (_ : @Eq α a₁ x) => @Eq β (f₁ a₁) (f₁ x)) (@rfl β (f₁ a₁)) a₂ h₂) f₂ h₁
theorem not_false : @Not False :=
  @id False
def instDecidableFalse : @Decidable False :=
  @Decidable.isFalse False not_false
def Decidable.byCases.match_1 : {p : Prop} -> (motive : @Decidable p -> Sort u_1) -> (dec : @Decidable p) -> ((h : p) -> motive (@Decidable.isTrue p h)) -> ((h : @Not p) -> motive (@Decidable.isFalse p h)) -> motive dec :=
  fun {p : Prop} => fun (motive : @Decidable p -> Sort u_1) => fun (dec : @Decidable p) => fun (h_1 : (h : p) -> motive (@Decidable.isTrue p h)) => fun (h_2 : (h : @Not p) -> motive (@Decidable.isFalse p h)) => @Decidable.casesOn p (fun (x : @Decidable p) => motive x) dec (fun (h : @Not p) => h_2 h) (fun (h : p) => h_1 h)
def Decidable.byCases : {p : Prop} -> {q : Sort u} -> @Decidable p -> (p -> q) -> (@Not p -> q) -> q :=
  fun {p : Prop} => fun {q : Sort u} => fun (dec : @Decidable p) => fun (h1 : p -> q) => fun (h2 : @Not p -> q) => @Decidable.byCases.match_1 p (fun (_ : @Decidable p) => q) dec (fun (h : p) => h1 h) (fun (h : @Not p) => h2 h)
theorem Decidable.em : (p : Prop) -> @Decidable p -> @Or p (@Not p) :=
  fun (p : Prop) => fun (inst : @Decidable p) => @Decidable.byCases p (@Or p (@Not p)) inst (@Or.inl p (@Not p)) (@Or.inr p (@Not p))
def if_pos.match_1 : {c : Prop} -> (motive : @Decidable c -> Prop) -> (h : @Decidable c) -> ((h1 : c) -> motive (@Decidable.isTrue c h1)) -> ((hnc : @Not c) -> motive (@Decidable.isFalse c hnc)) -> motive h :=
  fun {c : Prop} => fun (motive : @Decidable c -> Prop) => fun (h : @Decidable c) => fun (h_1 : (h1 : c) -> motive (@Decidable.isTrue c h1)) => fun (h_2 : (hnc : @Not c) -> motive (@Decidable.isFalse c hnc)) => @Decidable.casesOn c (fun (x : @Decidable c) => motive x) h (fun (h1 : @Not c) => h_2 h1) (fun (h1 : c) => h_1 h1)
theorem if_pos : {c : Prop} -> {h : @Decidable c} -> c -> {α : Sort u} -> {t : α} -> {e : α} -> @Eq α (@ite α c h t e) t :=
  fun {c : Prop} => fun {h : @Decidable c} => fun (hc : c) => fun {α : Sort u} => fun {t : α} => fun {e : α} => @if_pos.match_1 c (fun (h1 : @Decidable c) => @Eq α (@ite α c h1 t e) t) h (fun (h1 : c) => @rfl α (@ite α c (@Decidable.isTrue c h1) t e)) (fun (hnc : @Not c) => @absurd c (@Eq α (@ite α c (@Decidable.isFalse c hnc) t e) t) hc hnc)
theorem if_neg : {c : Prop} -> {h : @Decidable c} -> @Not c -> {α : Sort u} -> {t : α} -> {e : α} -> @Eq α (@ite α c h t e) e :=
  fun {c : Prop} => fun {h : @Decidable c} => fun (hnc : @Not c) => fun {α : Sort u} => fun {t : α} => fun {e : α} => @if_pos.match_1 c (fun (h1 : @Decidable c) => @Eq α (@ite α c h1 t e) e) h (fun (hc : c) => @absurd c (@Eq α (@ite α c (@Decidable.isTrue c hc) t e) e) hc hnc) (fun (h1 : @Not c) => @rfl α (@ite α c (@Decidable.isFalse c h1) t e))
theorem ite_congr : {α : Sort u_1} -> {b : Prop} -> {c : Prop} -> {x : α} -> {y : α} -> {u : α} -> {v : α} -> {s : @Decidable b} -> (inst : @Decidable c) -> @Eq Prop b c -> (c -> @Eq α x u) -> (@Not c -> @Eq α y v) -> @Eq α (@ite α b s x y) (@ite α c inst u v) :=
  fun {α : Sort u_1} => fun {b : Prop} => fun {c : Prop} => fun {x : α} => fun {y : α} => fun {u : α} => fun {v : α} => fun {s : @Decidable b} => fun (inst : @Decidable c) => fun (h₁ : @Eq Prop b c) => fun (h₂ : c -> @Eq α x u) => fun (h₃ : @Not c -> @Eq α y v) => @Or.casesOn c (@Not c) (fun (t : @Or c (@Not c)) => @Eq (@Or c (@Not c)) (@Decidable.em c inst) t -> @Eq α (@ite α b s x y) (@ite α c inst u v)) (@Decidable.em c inst) (fun (h : c) => fun (_ : @Eq (@Or c (@Not c)) (@Decidable.em c inst) (@Or.inl c (@Not c) h)) => @Eq.mpr (@Eq α (@ite α b s x y) (@ite α c inst u v)) (@Eq α (@ite α b s x y) u) (@id (@Eq Prop (@Eq α (@ite α b s x y) (@ite α c inst u v)) (@Eq α (@ite α b s x y) u)) (@congrArg α Prop (@ite α c inst u v) u (fun (_a : α) => @Eq α (@ite α b s x y) _a) (@if_pos c inst h α u v))) (@Eq.ndrec Prop c (fun {b1 : Prop} => {s1 : @Decidable b1} -> @Eq α (@ite α b1 s1 x y) u) (fun {s1 : @Decidable c} => @Eq.mpr (@Eq α (@ite α c s1 x y) u) (@Eq α x u) (@id (@Eq Prop (@Eq α (@ite α c s1 x y) u) (@Eq α x u)) (@congrArg α Prop (@ite α c s1 x y) x (fun (_a : α) => @Eq α _a u) (@if_pos c s1 h α x y))) (h₂ h)) b (@Eq.symm Prop b c h₁) s)) (fun (h : @Not c) => fun (_ : @Eq (@Or c (@Not c)) (@Decidable.em c inst) (@Or.inr c (@Not c) h)) => @Eq.mpr (@Eq α (@ite α b s x y) (@ite α c inst u v)) (@Eq α (@ite α b s x y) v) (@id (@Eq Prop (@Eq α (@ite α b s x y) (@ite α c inst u v)) (@Eq α (@ite α b s x y) v)) (@congrArg α Prop (@ite α c inst u v) v (fun (_a : α) => @Eq α (@ite α b s x y) _a) (@if_neg c inst h α u v))) (@Eq.ndrec Prop c (fun {b1 : Prop} => {s1 : @Decidable b1} -> @Eq α (@ite α b1 s1 x y) v) (fun {s1 : @Decidable c} => @Eq.mpr (@Eq α (@ite α c s1 x y) v) (@Eq α y v) (@id (@Eq Prop (@Eq α (@ite α c s1 x y) v) (@Eq α y v)) (@congrArg α Prop (@ite α c s1 x y) y (fun (_a : α) => @Eq α _a v) (@if_neg c s1 h α x y))) (h₃ h)) b (@Eq.symm Prop b c h₁) s)) (@Eq.refl (@Or c (@Not c)) (@Decidable.em c inst))
theorem eq_self : {α : Sort u_1} -> (a : α) -> @Eq Prop (@Eq α a a) True :=
  fun {α : Sort u_1} => fun (a : α) => @eq_true (@Eq α a a) (@rfl α a)
theorem ite_cond_eq_false : {α : Sort u} -> {c : Prop} -> {x : @Decidable c} -> (a : α) -> (b : α) -> @Eq Prop c False -> @Eq α (@ite α c x a b) b :=
  fun {α : Sort u} => fun {c : Prop} => fun {x : @Decidable c} => fun (a : α) => fun (b : α) => fun (h : @Eq Prop c False) => @of_eq_true (@Eq α (@ite α c x a b) b) (@Eq.trans Prop (@Eq α (@ite α c x a b) b) (@Eq α (@ite α False instDecidableFalse a b) b) True (@congrArg α Prop (@ite α c x a b) (@ite α False instDecidableFalse a b) (fun (x1 : α) => @Eq α x1 b) (@ite_congr α c False a b a b x instDecidableFalse h (fun (_ : False) => @Eq.refl α a) (fun (_ : @Not False) => @Eq.refl α b))) (@eq_self α b))
def False.elim : {C : Sort u} -> False -> C :=
  fun {C : Sort u} => fun (h : False) => @False.rec (fun (_ : False) => C) h
theorem eq_false : {p : Prop} -> @Not p -> @Eq Prop p False :=
  fun {p : Prop} => fun (h : @Not p) => @propext p False (@Iff.intro p False (fun (h' : p) => @absurd p False h' h) (fun (h' : False) => @False.elim p h'))
theorem not_false_eq_true : @Eq Prop (@Not False) True :=
  @eq_true (@Not False) (@False.elim False)
theorem true_and : (p : Prop) -> @Eq Prop (@And True p) p :=
  fun (p : Prop) => @propext (@And True p) p (@Iff.intro (@And True p) p (fun (x : @And True p) => @And.right True p x) (fun (x : p) => @And.intro True p trivial x))
def instDecidableTrue : @Decidable True :=
  @Decidable.isTrue True trivial
theorem ite_cond_eq_true : {α : Sort u} -> {c : Prop} -> {x : @Decidable c} -> (a : α) -> (b : α) -> @Eq Prop c True -> @Eq α (@ite α c x a b) a :=
  fun {α : Sort u} => fun {c : Prop} => fun {x : @Decidable c} => fun (a : α) => fun (b : α) => fun (h : @Eq Prop c True) => @of_eq_true (@Eq α (@ite α c x a b) a) (@Eq.trans Prop (@Eq α (@ite α c x a b) a) (@Eq α (@ite α True instDecidableTrue a b) a) True (@congrArg α Prop (@ite α c x a b) (@ite α True instDecidableTrue a b) (fun (x1 : α) => @Eq α x1 a) (@ite_congr α c True a b a b x instDecidableTrue h (fun (_ : True) => @Eq.refl α a) (fun (_ : @Not True) => @Eq.refl α b))) (@eq_self α a))
-- inductive Bool : Type where
--  | false : Bool
  --  | true : Bool
-- ctor Bool.false : Bool
-- ctor Bool.true : Bool
def Decidable.decide : (p : Prop) -> @Decidable p -> Bool :=
  fun (p : Prop) => fun (h : @Decidable p) => @Decidable.casesOn p (fun (_ : @Decidable p) => Bool) h (fun (_ : @Not p) => Bool.false) (fun (_ : p) => Bool.true)
def of_decide_eq_true.match_1 : {p : Prop} -> (motive : @Decidable p -> Prop) -> (inst : @Decidable p) -> ((h₁ : p) -> motive (@Decidable.isTrue p h₁)) -> ((h₁ : @Not p) -> motive (@Decidable.isFalse p h₁)) -> motive inst :=
  fun {p : Prop} => fun (motive : @Decidable p -> Prop) => fun (inst : @Decidable p) => fun (h_1 : (h₁ : p) -> motive (@Decidable.isTrue p h₁)) => fun (h_2 : (h₁ : @Not p) -> motive (@Decidable.isFalse p h₁)) => @Decidable.casesOn p (fun (x : @Decidable p) => motive x) inst (fun (h : @Not p) => h_2 h) (fun (h : p) => h_1 h)
-- recursor Bool.rec : {motive : Bool -> Sort u} -> motive Bool.false -> motive Bool.true -> (t : Bool) -> motive t
-- def Bool.casesOn : {motive : Bool -> Sort u} -> (t : Bool) -> motive Bool.false -> motive Bool.true -> motive t :=
--  fun {motive : Bool -> Sort u} => fun (t : Bool) => fun (false : motive Bool.false) => fun (true : motive Bool.true) => @Bool.rec motive false true t
def ne_true_of_eq_false.match_1 : (motive : (x : Bool) -> @Eq Bool x Bool.false -> Prop) -> (x : Bool) -> (x1 : @Eq Bool x Bool.false) -> ((h : @Eq Bool Bool.true Bool.false) -> motive Bool.true h) -> ((x2 : @Eq Bool Bool.false Bool.false) -> motive Bool.false x2) -> motive x x1 :=
  fun (motive : (x : Bool) -> @Eq Bool x Bool.false -> Prop) => fun (x : Bool) => fun (x1 : @Eq Bool x Bool.false) => fun (h_1 : (h : @Eq Bool Bool.true Bool.false) -> motive Bool.true h) => fun (h_2 : (x2 : @Eq Bool Bool.false Bool.false) -> motive Bool.false x2) => @Bool.casesOn (fun (x2 : Bool) => (x3 : @Eq Bool x2 Bool.false) -> motive x2 x3) x (fun (x2 : @Eq Bool Bool.false Bool.false) => h_2 x2) (fun (x2 : @Eq Bool Bool.true Bool.false) => h_1 x2) x1
def Bool.noConfusionType : Sort u -> Bool -> Bool -> Sort u :=
  fun (P : Sort u) => fun (v1 : Bool) => fun (v2 : Bool) => @Bool.casesOn (fun (_ : Bool) => Sort u) v1 (@Bool.casesOn (fun (_ : Bool) => Sort u) v2 (P -> P) P) (@Bool.casesOn (fun (_ : Bool) => Sort u) v2 P (P -> P))
def Bool.noConfusion : {P : Sort u} -> {v1 : Bool} -> {v2 : Bool} -> @Eq Bool v1 v2 -> @Bool.noConfusionType P v1 v2 :=
  fun {P : Sort u} => fun {v1 : Bool} => fun {v2 : Bool} => fun (h12 : @Eq Bool v1 v2) => @Eq.ndrec Bool v1 (fun (a : Bool) => @Eq Bool v1 a -> @Bool.noConfusionType P v1 a) (fun (_ : @Eq Bool v1 v1) => @Bool.casesOn (fun {v11 : Bool} => @Bool.noConfusionType P v11 v11) v1 (fun (a : P) => a) (fun (a : P) => a)) v2 h12 h12

#eval printTransformExpr `ne_true_of_eq_false
theorem ne_true_of_eq_false : ∀ {b : Bool}, @Eq.{1} Bool b Bool.false → Flow.Not (@Eq.{1} Bool b Bool.true) :=
  fun {x : Bool} => fun (x1 : @Eq Bool x Bool.false) => @ne_true_of_eq_false.match_1 (fun (x2 : Bool) => fun (_ : @Eq Bool x2 Bool.false) => @Not (@Eq Bool x2 Bool.true)) x x1 (fun (h : @Eq Bool Bool.true Bool.false) => @Bool.noConfusion (@Not (@Eq Bool Bool.true Bool.true)) Bool.true Bool.false h) (fun (_ : @Eq Bool Bool.false Bool.false) => fun (h : @Eq Bool Bool.false Bool.true) => @Bool.noConfusion False Bool.false Bool.true h)

#print ne_true_of_eq_false
#eval printTransformExpr `ne_true_of_eq_false

#check Decidable.isFalse (fun h => False.elim h)

#eval printTransformExpr `eq_iff_eq_cancel_right
