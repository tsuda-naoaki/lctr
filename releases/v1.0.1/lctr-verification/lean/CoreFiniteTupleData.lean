import Mathlib.Data.List.Basic

namespace LCTR.CoreFiniteTupleData
set_option autoImplicit false
universe u

inductive Tuple : List (Type u) → Type (u+1) where
  | nil : Tuple []
  | cons {A : Type u} {as : List (Type u)} : A → Tuple as → Tuple (A::as)

def concatenate {as bs : List (Type u)} : Tuple as → Tuple bs → Tuple (as++bs)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (concatenate xs ys)

def split : (as : List (Type u)) → {bs : List (Type u)} → Tuple (as++bs) → Tuple as × Tuple bs
  | [], _, ys => (.nil,ys)
  | _::as, _, .cons x xs => (.cons x (split as xs).1,(split as xs).2)

theorem concatenate_empty_left {bs : List (Type u)} (ys : Tuple bs) :
    concatenate .nil ys = ys := rfl

theorem concatenate_cons {A : Type u} {as bs : List (Type u)}
    (x : A) (xs : Tuple as) (ys : Tuple bs) :
    concatenate (.cons x xs) ys = .cons x (concatenate xs ys) := rfl

theorem concatenated_length (as bs : List (Type u)) :
    (as++bs).length = as.length + bs.length := List.length_append

theorem split_concatenate {as bs : List (Type u)} (xs : Tuple as) (ys : Tuple bs) :
    split as (concatenate xs ys) = (xs,ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [concatenate,split,ih]

theorem concatenate_split (as : List (Type u)) {bs : List (Type u)} (zs : Tuple (as++bs)) :
    concatenate (split as zs).1 (split as zs).2 = zs := by
  induction as with
  | nil => rfl
  | cons A as ih =>
    cases zs with
    | cons z zs => simp [split,concatenate,ih]

theorem concatenate_injective {as bs : List (Type u)}
    (xs xs' : Tuple as) (ys ys' : Tuple bs)
    (h : concatenate xs ys = concatenate xs' ys') : xs = xs' ∧ ys = ys' := by
  have same := congrArg (split as) h
  simpa only [split_concatenate,Prod.mk.injEq] using same

theorem seven_components {A B C D E F G : Type u}
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) :
    concatenate (concatenate (.cons a (.cons b (.cons c .nil))) (.cons d (.cons e .nil)))
      (.cons f (.cons g .nil)) =
    .cons a (.cons b (.cons c (.cons d (.cons e (.cons f (.cons g .nil)))))) := rfl

end LCTR.CoreFiniteTupleData
