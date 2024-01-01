(** This file defines the semantics for the "Stack" language. *)

Require Import Syntax.

From Hoare Require Import Logic.

From Coq Require Export Arith.Arith.
From Coq Require Export Classes.EquivDec.

Global Instance string_eq_dec : EqDec string eq := string_dec.

Inductive arith_exp_R : arith_exp -> State.state string nat -> nat -> Prop :=
  | ANum_R s (n : nat) :
      arith_exp_R n s n
  | AVar_R s x n :
      s x = Some n ->
      arith_exp_R x s n
  | AAdd_R s a1 a2 n1 n2 :
      arith_exp_R a1 s n1 ->
      arith_exp_R a2 s n2 ->
      arith_exp_R <{a1 + a2}> s (n1 + n2)
  | AMult_R s a1 a2 n1 n2 :
      arith_exp_R a1 s n1 ->
      arith_exp_R a2 s n2 ->
      arith_exp_R <{a1 * a2}> s (n1 * n2)
  | AMin_R s a1 a2 n1 n2 :
      arith_exp_R a1 s n1 ->
      arith_exp_R a2 s n2 ->
      arith_exp_R <{a1 - a2}> s (n1 - n2).
Global Instance arith_exp_Expression : Expression arith_exp := arith_exp_R.

Inductive bool_exp_R : bool_exp -> State.state string nat -> bool -> Prop :=
  | BTrue_R s :
      bool_exp_R <{true}> s true
  | BFalse_R s :
      bool_exp_R <{false}> s false
  | BEq_R s a1 a2 n1 n2 :
      ⟦a1⟧s ⇒ n1 ->
      ⟦a2⟧s ⇒ n2 ->
      bool_exp_R (<{a1 = a2}>) s (n1 =? n2)
  | BLeq_R s a1 a2 n1 n2 :
      ⟦a1⟧s ⇒ n1 ->
      ⟦a2⟧s ⇒ n2 ->
      bool_exp_R <{a1 <= a2}> s (n1 <=? n2)
  | BNeg_R s b b' :
      bool_exp_R b s b' ->
      bool_exp_R (<{!b}>) s (negb b')
  | BAnd_R s b1 b2 b1' b2' :
      bool_exp_R b1 s b1' ->
      bool_exp_R b2 s b2' ->
      bool_exp_R (<{b1 && b2}>) s (andb b1' b2').
Global Instance bool_exp_Expression : Expression bool_exp := bool_exp_R.

Inductive stm_R : stm -> State.state string nat -> State.state string nat -> Prop :=
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
