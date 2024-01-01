Declare Scope hoare_logic_scope.
Declare Custom Entry lang.

Global Open Scope hoare_logic_scope.

From Coq Require Import Classes.EquivDec.

Section state.
  Definition state T U := T -> option U.
  Definition mod_state {T U} `{EqDec T}
    (st : state T U) (x : T) (y : U) : state T U :=
    fun x' => if x == x' then Some y else st x'.
  Definition empty_state {T U} : state T U :=
    fun _ => None.
End state.

Notation "∅" := empty_state : hoare_logic_scope.
Notation "x ↦ y ; st" := (mod_state st x y)
  (at level 100, y at next level, right associativity) : hoare_logic_scope.
Notation "x ↦ y" := (mod_state ∅ x y)
  (at level 100, y at next level, no associativity) : hoare_logic_scope.

Class Expression {T U V} (A : Type) := exp_R (exp : A) (s : state T U) (v : V) : Prop.
Class Statement {T U} (A : Type) := stm_R (stm : A) (s s' : state T U) : Prop.

Section assertion.
  Generalizable Variable Σ.

  Context {T U : Type} `{EqDec T}.

  Definition Assertion := state T U -> Prop.
  Definition assert_implies (P Q : Assertion) : Prop :=
    forall s, P s -> Q s.
  Definition assert_iff (P Q : Assertion) : Prop :=
    forall s, P s -> Q s /\ Q s -> P s.
  Definition assert_and (P Q : Assertion) : Assertion :=
    fun s => P s /\ Q s.
  Definition assert_sub `{@Expression T U U Σ}
    (x : T) (exp : Σ) (P : Assertion) : Assertion :=
    fun s => forall n, exp_R exp s n -> P (x ↦ n ; s).
End assertion.
Global Hint Unfold assert_implies assert_sub : core.
Notation "P [ x ↦ a ]" := (assert_sub x a P)
  (at level 10, x at next level) : hoare_logic_scope.

Section hoare.
  Generalizable Variable Σ.

  Context {T U : Type} `{EqDec T}.

  Definition hoare_triple `{@Statement T U Σ}
    (P : Assertion) (stm : Σ) (Q : Assertion) : Prop :=
    forall s s', stm_R stm s s' -> P s -> Q s'.
End hoare.
Global Hint Unfold hoare_triple : core.
Notation "⟦ exp ⟧ s ⇒ r" := (exp_R exp s r)
  (at level 40,
    exp custom lang at level 99,
    s constr at level 99,
    r constr at level 98).
Notation "P ⇾ Q" := (assert_implies P Q) (at level 80) : hoare_logic_scope.
Notation "P ⇿ Q" := (assert_iff P Q) (at level 80) : hoare_logic_scope.
Notation "⟨ stm , s ⟩ ⇒ s'" := (stm_R stm s s')
    (at level 40, s at level 99,
      stm custom lang at level 99,
      s' constr at level 98).
Notation "{{ P }} stm {{ Q }}" := (hoare_triple P stm Q)
    (at level 90, stm custom lang at level 99) : hoare_logic_scope.
Notation "<{ e }>" := e (at level 0, e custom lang at level 99) : hoare_logic_scope.
Notation "( e )" := e (in custom lang, e at level 99) : hoare_logic_scope.
Notation "e" := e (in custom lang at level 0, e constr at level 0) : hoare_logic_scope.

Section theorems.
  Generalizable Variable Σ.

  Context {T U : Type} `{@Statement T U Σ}.

  Lemma hoare_imp_pre P Q P' (stm : Σ) :
    {{ P' }} stm {{ Q }} -> P ⇾ P' -> {{ P }} stm {{ Q }}.
  Proof. eauto. Qed.

  Lemma hoare_imp_post P Q Q' `{@Statement T U Σ} (stm : Σ) :
    {{ P }} stm {{ Q }} -> Q ⇾ Q' -> {{ P }} stm {{ Q' }}.
  Proof. eauto. Qed.

  Lemma hoare_imp_assert P Q P' Q' `{@Statement T U Σ} (stm : Σ) :
    {{ P' }} stm {{ Q }} -> P ⇾ P' -> Q ⇾ Q' -> {{ P }} stm {{ Q' }}.
  Proof. eauto. Qed.
End theorems.