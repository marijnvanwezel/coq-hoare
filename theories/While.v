(** This file defines the syntax and semantics for the "While"
deeply embedded language. It is based on [1].

[1]: Hanne Riis Nielson, Flemming Nielson: Semantics with applications - a
     formal introduction. Wiley professional computing, Wiley 1992,
     ISBN 978-0-471-92980-2, pp. I-XII, 1-240 

This was mostly copied from:

https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html *)

Set Warnings "-notation-overridden".

Require Import Hoare.State.

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Classes.EquivDec.
From Coq Require Import Strings.String.

Declare Custom Entry stm.
Declare Scope stm_scope.

Open Scope stm_scope.

Notation "<{ e }>" := e (at level 0, e custom stm at level 99) : stm_scope.
Notation "( e )" := e (in custom stm, e at level 99) : stm_scope.
Notation "e" := e (in custom stm at level 0, e constr at level 0) : stm_scope.

Reserved Notation "⟨ x , y ⟩ ⇒ z"
  (at level 40, y custom stm at level 99, x constr at level 99, z constr at level 98).

#[universes(template)]
Class Evaluable (T S U : Type) :=
  {
    eval_R : T -> S -> U -> Prop
  }.
Notation "⟦ t ⟧ s ⇒ u" := (eval_R t s u)
  (at level 40,
    t custom stm at level 99,
    s constr at level 99,
    u constr at level 98).

(** State as used in the "While" language. *)
Local Instance string_eq_eqdec : EqDec string eq := string_dec.
Definition while_state := state string nat.

Inductive aexp :=
  | ANum : nat -> aexp (* numeral: n *)
  | AVar : string -> aexp (* variable: x *)
  | AAdd : aexp -> aexp -> aexp (* addition: a1 + a2 *)
  | AMult : aexp -> aexp -> aexp (* multiplication: a1 * a2 *)
  | AMin : aexp -> aexp -> aexp. (* subtraction: a1 - a2 *)
Coercion AVar : string >-> aexp.
Coercion ANum : nat >-> aexp.
Infix "+" := AAdd (in custom stm at level 50, left associativity).
Infix "*" := AMult (in custom stm at level 40, left associativity).
Infix "-" := AMin (in custom stm at level 50, left associativity).
Inductive aexp_R : aexp -> while_state -> nat -> Prop :=
  | ANum_R (s : while_state) (n : nat) : 
    (*────────────*)
      aexp_R n s n
  | AVar_R (s : while_state) (x : string) (n : nat) :
      s x = Some n ->
    (*───────────────*)
        aexp_R x s n
  | AAdd_R (s : while_state) (a1 a2 : aexp) (n1 n2 : nat) :
             aexp_R a1 s n1 ->
             aexp_R a2 s n2 ->
    (*──────────────────────────────*)
      aexp_R <{a1 + a2}> s (n1 + n2)
  | AMult_R (s : while_state) (a1 a2 : aexp) (n1 n2 : nat) :
             aexp_R a1 s n1 ->
             aexp_R a2 s n2 ->
    (*──────────────────────────────*)
      aexp_R <{a1 * a2}> s (n1 * n2)
  | AMin_R (s : while_state) (a1 a2 : aexp) (n1 n2 : nat) :
             aexp_R a1 s n1 ->
             aexp_R a2 s n2 ->
    (*──────────────────────────────*)
      aexp_R <{a1 - a2}> s (n1 - n2).
Local Instance aexp_Evaluable : Evaluable aexp while_state nat :=
  {
    eval_R := aexp_R
  }.

Inductive bexp :=
  | BTrue : bexp (* true *)
  | BFalse : bexp (* false *)
  | BEq : aexp -> aexp -> bexp (* equality: a1 = a2 *)
  | BLeq : aexp -> aexp -> bexp (* less-than-or-equals: a1 ≤ a2 *)
  | BNeg : bexp -> bexp (* negation: ¬b *)
  | BAnd : bexp -> bexp -> bexp. (* conjunction: b1 ∧ b2 *)
Notation "'true'" := BTrue (in custom stm at level 0).
Notation "'false'" := BFalse (in custom stm at level 0).
Infix "=" := BEq (in custom stm at level 70, no associativity).
Infix "≤" := BLeq (in custom stm at level 70, no associativity).
Notation "¬ b" := (BNeg b) (in custom stm at level 75, right associativity).
Infix "∧" := BAnd (in custom stm at level 80, left associativity).
Inductive bexp_R : bexp -> while_state -> bool -> Prop :=
  | BTrue_R (s : while_state) :
    (*────────────────────────*)
      bexp_R (<{true}>) s true
  | BFalse_R (s : while_state) :
    (*──────────────────────────*)
      bexp_R (<{false}>) s false
  | BEq_R (s : while_state) (a1 a2 : aexp) (n1 n2 : nat) :
               ⟦a1⟧s ⇒ n1 ->
               ⟦a2⟧s ⇒ n2 ->
    (*─────────────────────────────────*)
      bexp_R (<{a1 = a2}>) s (n1 =? n2)
  | BLeq_R (s : while_state) (a1 a2 : aexp) (n1 n2 : nat) :
                ⟦a1⟧s ⇒ n1 ->
                ⟦a2⟧s ⇒ n2 ->
    (*──────────────────────────────────*)
      bexp_R (<{a1 ≤ a2}>) s (n1 <=? n2)
  | BNeg_R (s : while_state) (b : bexp) (b' : bool) :
            bexp_R b s b' ->
    (*───────────────────────────*)
      bexp_R (<{¬b}>) s (negb b')
  | BAnd_R (s : while_state) (b1 b2 : bexp) (b1' b2' : bool) :
                bexp_R b1 s b1' ->
                bexp_R b2 s b2' ->
    (*─────────────────────────────────────*)
      bexp_R (<{b1 ∧ b2}>) s (andb b1' b2').
Local Instance bexp_Evaluable : Evaluable bexp while_state bool :=
  {
    eval_R := bexp_R
  }.

Inductive stm :=
  | SAsgn : string -> aexp -> stm (* assignment: x := a *)
  | SSkip : stm (* skip *)
  | SSeq : stm -> stm -> stm (* sequence: s1 ; s2 *)
  | SIf : bexp -> stm -> stm -> stm (* conditional: if b then s1 else s2 end *)
  | SWhile : bexp -> stm -> stm. (* looping: while b do s end *)
Notation "'skip'" := SSkip (in custom stm at level 0) : stm_scope.
Notation "x := a" := (SAsgn x a)
  (in custom stm at level 0, x constr at level 0, a at level 85, no associativity) : stm_scope.
Notation "s1 ; s2" := (SSeq s1 s2)
  (in custom stm at level 90, right associativity) : stm_scope.
Notation "'if' b 'then' s1 'else' s2 'end'" := (SIf b s1 s2)
  (in custom stm at level 89, b at level 99, s1 at level 99, s1 at level 99) : stm_scope.
Notation "'while' b 'do' s 'end'" := (SWhile b s)
  (in custom stm at level 89, b at level 99, s at level 99) : stm_scope.

Reserved Notation "⟨ x , y ⟩ ⇒ z"
  (at level 40, y custom stm at level 99, x constr at level 99, z constr at level 98).

(** Operational semantics of "While" *)
Inductive stm_R : stm -> while_state -> while_state -> Prop :=
  | SAsgn_R s x a n :
               ⟦a⟧s ⇒ n ->
    (*───────────────────────────────*)
      ⟨<{x := a}>, s⟩ ⇒ (x ↦ n ; s)
  | SSkip_R s :
    (*─────────────────*)
      ⟨<{skip}>, s⟩ ⇒ s
  | SSeq_R s s' s'' S1 S2 :
       ⟨<{S1}>, s⟩ ⇒ s' ->
      ⟨<{S2}>, s'⟩ ⇒ s'' ->
    (*──────────────────────*)
      ⟨<{S1; S2}>, s⟩ ⇒ s''
  | SIf_R_True s s' b S1 S2 :
                  ⟦b⟧s ⇒ true ->
               ⟨<{S1}>, s⟩ ⇒ s' ->
    (*───────────────────────────────────────*)
      ⟨<{if b then S1 else S2 end}>, s⟩ ⇒ s'
  | SIf_R_False s s' b S1 S2 :
                  ⟦b⟧s ⇒ false ->
               ⟨<{S2}>, s⟩ ⇒ s' ->
    (*───────────────────────────────────────*)
      ⟨<{if b then S1 else S2 end}>, s⟩ ⇒ s'
  | SWhile_R_True s s' s'' b S :
                 ⟦b⟧s ⇒ true ->
               ⟨<{S}>, s⟩ ⇒ s' ->
      ⟨<{while b do S end}>, s'⟩ ⇒ s'' ->
    (*────────────────────────────────────*)
         ⟨<{while b do S end}>, s⟩ ⇒ s''
  | SWhile_R_False s b S :
            ⟦b⟧s ⇒ false ->
  (*──────────────────────────────*)
    ⟨<{while b do S end}>, s⟩ ⇒ s
where "⟨ stm , st ⟩ ⇒ st'" := (stm_R stm st st').
