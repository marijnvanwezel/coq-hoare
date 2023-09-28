(** Simple definitions to represent states for any language. *)

Require Import Coq.Classes.EquivDec.

Section state.
  Definition state T U := T -> option U.
  Definition mod_state {T U} `{EqDec T}
    (st : state T U) (x : T) (y : U) : state T U
  := fun x' => if x == x' then Some y else st x'.
  Definition empty_state {T U} : state T U :=
    fun _ => None.
End state.

Notation "∅" := empty_state.
Notation "x ↦ y ; st" := (mod_state st x y)
  (at level 100, y at next level, right associativity).
Notation "x ↦ y" := (mod_state ∅ x y)
  (at level 100, y at next level, no associativity).