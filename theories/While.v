(** This file defines the syntax and semantics for the "Stack" language. *)

Set Warnings "-notation-overridden".

Require Import Hoare.Logic.
Require Import Hoare.State.

From Coq Require Export Arith.Arith.
From Coq Require Export Bool.Bool.
From Coq Require Export Classes.EquivDec.
From Coq Require Export Strings.String.

Open Scope hoare_logic_scope.

Local Instance string_eq_eqdec : EqDec string eq := string_dec.

Inductive aexp :=
  | ANum : nat -> aexp (* numeral: n *)
  | AVar : string -> aexp (* variable: x *)
  | AAdd : aexp -> aexp -> aexp (* addition: a1 + a2 *)
  | AMult : aexp -> aexp -> aexp (* multiplication: a1 * a2 *)
  | AMin : aexp -> aexp -> aexp. (* subtraction: a1 - a2 *)
Coercion AVar : string >-> aexp.
Coercion ANum : nat >-> aexp.
Infix "+" := AAdd (in custom lang at level 50, left associativity).
Infix "*" := AMult (in custom lang at level 40, left associativity).
Infix "-" := AMin (in custom lang at level 50, left associativity).
Inductive aexp_R : aexp -> state string nat -> nat -> Prop :=
  | ANum_R s (n : nat) :
      aexp_R n s n
  | AVar_R s x n :
      s x = Some n ->
      aexp_R x s n
  | AAdd_R s a1 a2 n1 n2 :
      aexp_R a1 s n1 ->
      aexp_R a2 s n2 ->
      aexp_R <{a1 + a2}> s (n1 + n2)
  | AMult_R s a1 a2 n1 n2 :
      aexp_R a1 s n1 ->
      aexp_R a2 s n2 ->
      aexp_R <{a1 * a2}> s (n1 * n2)
  | AMin_R s a1 a2 n1 n2 :
      aexp_R a1 s n1 ->
      aexp_R a2 s n2 ->
      aexp_R <{a1 - a2}> s (n1 - n2).
Global Instance aexp_Expression : Expression aexp := aexp_R.

Inductive bexp :=
  | BTrue : bexp (* true *)
  | BFalse : bexp (* false *)
  | BEq : aexp -> aexp -> bexp (* equality: a1 = a2 *)
  | BLeq : aexp -> aexp -> bexp (* less-than-or-equals: a1 ≤ a2 *)
  | BNeg : bexp -> bexp (* negation: ¬b *)
  | BAnd : bexp -> bexp -> bexp. (* conjunction: b1 ∧ b2 *)
Notation "'true'" := BTrue (in custom lang at level 0).
Notation "'false'" := BFalse (in custom lang at level 0).
Infix "=" := BEq (in custom lang at level 70, no associativity).
Infix "<=" := BLeq (in custom lang at level 70, no associativity).
Notation "! b" := (BNeg b) (in custom lang at level 75, right associativity).
Infix "&&" := BAnd (in custom lang at level 80, left associativity).
Inductive bexp_R : bexp -> state string nat -> bool -> Prop :=
  | BTrue_R s :
      bexp_R <{true}> s true
  | BFalse_R s :
      bexp_R <{false}> s false
  | BEq_R s a1 a2 n1 n2 :
      ⟦a1⟧s ⇒ n1 ->
      ⟦a2⟧s ⇒ n2 ->
      bexp_R (<{a1 = a2}>) s (n1 =? n2)
  | BLeq_R s a1 a2 n1 n2 :
      ⟦a1⟧s ⇒ n1 ->
      ⟦a2⟧s ⇒ n2 ->
      bexp_R <{a1 <= a2}> s (n1 <=? n2)
  | BNeg_R s b b' :
      bexp_R b s b' ->
      bexp_R (<{!b}>) s (negb b')
  | BAnd_R s b1 b2 b1' b2' :
      bexp_R b1 s b1' ->
      bexp_R b2 s b2' ->
      bexp_R (<{b1 && b2}>) s (andb b1' b2').
Global Instance bexp_Expression : Expression bexp := bexp_R.

Inductive stm :=
  | SAsgn : string -> aexp -> stm (* assignment: x := a *)
  | SSkip : stm (* skip *)
  | SSeq : stm -> stm -> stm (* sequence: s1 ; s2 *)
  | SIf : bexp -> stm -> stm -> stm (* conditional: if b then s1 else s2 end *)
  | SWhile : bexp -> stm -> stm. (* looping: while b do s end *)
Notation "'skip'" := SSkip (in custom lang at level 0) : hoare_logic_scope.
Notation "x := a" := (SAsgn x a)
  (in custom lang at level 0, x constr at level 0, a at level 85, no associativity) : hoare_logic_scope.
Notation "s1 ; s2" := (SSeq s1 s2)
  (in custom lang at level 90, right associativity) : hoare_logic_scope.
Notation "'if' b 'then' s1 'else' s2 'end'" := (SIf b s1 s2)
  (in custom lang at level 89, b at level 99, s1 at level 99, s1 at level 99) : hoare_logic_scope.
Notation "'while' b 'do' s 'end'" := (SWhile b s)
  (in custom lang at level 89, b at level 99, s at level 99) : hoare_logic_scope.
Inductive stm_R : stm -> state string nat -> state string nat -> Prop :=
  | SAsgn_R s x a n :
      ⟦a⟧s ⇒ n ->
      stm_R <{x := a}> s (x ↦ n ; s)
  | SSkip_R s :
      stm_R <{skip}> s s
  | SSeq_R s s' s'' S1 S2 :
      stm_R <{S1}> s s' ->
      stm_R <{S2}> s' s'' ->
      stm_R <{S1; S2}> s s''
  | SIf_R_True s s' b S1 S2 :
      ⟦b⟧s ⇒ true ->
      stm_R <{S1}> s s' ->
      stm_R <{if b then S1 else S2 end}> s s'
  | SIf_R_False s s' b S1 S2 :
      ⟦b⟧s ⇒ false ->
      stm_R <{S2}> s s' ->
      stm_R <{if b then S1 else S2 end}> s s'
  | SWhile_R_True s s' s'' b S :
      ⟦b⟧s ⇒ true ->
      stm_R <{S}> s s' ->
      stm_R <{while b do S end}> s' s'' ->
      stm_R <{while b do S end}> s s''
  | SWhile_R_False s b S :
      ⟦b⟧s ⇒ false ->
      stm_R <{while b do S end}> s s.
Global Instance stm_Statement : Statement stm := stm_R.

Section rules.
  Context (P Q : @Assertion string nat).

  Lemma hoare_skip : {{ P }} skip {{ P }}.
  Proof.
    unfold hoare_triple. intros.
    inversion H; subst; assumption.
  Qed.

  Lemma hoare_assn (a : aexp) x : {{ Q[x ↦ a] }} x := a {{ Q }}.
  Proof.
    unfold hoare_triple.
    intros. inversion H. subst.
    unfold assert_sub in H0. auto.
  Qed.

  
