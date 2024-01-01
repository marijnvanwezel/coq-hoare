(** This file defines the syntax for the "Stack" language. *)

From Hoare Require Import Logic.

From Coq Require Export Strings.String.

Inductive type : Set :=
  | TBool : type (* boolean *)
  | TNat : type (* nats *)
  | TStr : type (* strings *)
  | TList : type -> type. (* typed lists *)

Inductive exp : type -> Set :=
  | EBoolConst : bool -> exp TBool
  | ENatConst : nat -> exp TNat
  | EStrConst : string -> exp TStr
  | EListConst : forall t, list (exp t) -> exp (TList t)
  | EBoolVar : string -> exp TBool
  | ENatVar : string -> exp TNat
  | EStrVar : string -> exp TStr
  | EListVar : forall t, string -> exp (TList t)
  | EExp : exp TNat -> exp TNat -> exp TNat (* exponentiation: a1 ** a2 *)
  | EMult : exp TNat -> exp TNat -> exp TNat (* multiplication: a1 * a2 *)
  | EDiv : exp TNat -> exp TNat -> exp TNat (* division: a1 / a2 *)
  | EMod : exp TNat -> exp TNat -> exp TNat (* modulo: a1 % a2 *)
  | EAdd : exp TNat -> exp TNat -> exp TNat (* addition: a1 + a2 *)
  | ESub : exp TNat -> exp TNat -> exp TNat (* subtraction: a1 - a2 *)
  | ETrue : exp TBool (* true *)
  | EFalse : exp TBool (* false *)
  | EEq : forall t, exp t -> exp t -> exp TBool (* equality: e1 == e2 *)
  | ENeq : forall t, exp t -> exp t -> exp TBool (* inequality: e1 != e2 *)
  .

Infix "**" := AExp (in custom lang at level 30, right associativity).
Infix "*" := AMult (in custom lang at level 40, left associativity).
Infix "/" := ADiv (in custom lang at level 40, left associativity).
Infix "%" := AMod (in custom lang at level 40, left associativity).
Infix "+" := AAdd (in custom lang at level 50, left associativity).
Infix "-" := ASub (in custom lang at level 50, left associativity).

Inductive bool_exp :=
  | BTrue : bool_exp (* true *)
  | BFalse : bool_exp (* false *)
  | BEq : arith_exp -> arith_exp -> bool_exp (* equality: a1 == a2 *)
  | BNeq : arith_exp -> arith_exp -> bool_exp
  | BLeq : arith_exp -> arith_exp -> bool_exp (* less-than-or-equals: a1 ≤ a2 *)
  | BNeg : bool_exp -> bool_exp (* negation: ¬b *)
  | BAnd : bool_exp -> bool_exp -> bool_exp. (* conjunction: b1 ∧ b2 *)
Notation "'true'" := BTrue (in custom lang at level 0).
Notation "'false'" := BFalse (in custom lang at level 0).
Infix "=" := BEq (in custom lang at level 70, no associativity).
Infix "<=" := BLeq (in custom lang at level 70, no associativity).
Notation "! b" := (BNeg b) (in custom lang at level 75, right associativity).
Infix "&&" := BAnd (in custom lang at level 80, left associativity).

Inductive stm :=
  | SAsgn : string -> arith_exp -> stm (* assignment: x := a *)
  | SSkip : stm (* skip *)
  | SSeq : stm -> stm -> stm (* sequence: s1 ; s2 *)
  | SIf : bool_exp -> stm -> stm -> stm (* conditional: if b then s1 else s2 end *)
  | SWhile : bool_exp -> stm -> stm. (* looping: while b do s end *)
Notation "'skip'" := SSkip (in custom lang at level 0) : hoare_logic_scope.
Notation "x := a" := (SAsgn x a)
  (in custom lang at level 0, x constr at level 0, a at level 85, no associativity) : hoare_logic_scope.
Notation "s1 ; s2" := (SSeq s1 s2)
  (in custom lang at level 90, right associativity) : hoare_logic_scope.
Notation "'if' b 'then' s1 'else' s2 'end'" := (SIf b s1 s2)
  (in custom lang at level 89, b at level 99, s1 at level 99, s1 at level 99) : hoare_logic_scope.
Notation "'while' b 'do' s 'end'" := (SWhile b s)
  (in custom lang at level 89, b at level 99, s at level 99) : hoare_logic_scope.

