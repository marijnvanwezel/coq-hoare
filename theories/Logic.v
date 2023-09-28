Require Export Hoare.State.

From Coq Require Import Classes.EquivDec.

Section logic.
  Generalizable Variables Σ.

  Context {T U : Type}.
  Implicit Type s : state T U.

  Class Expression (A : Type) {V} := exp_R (exp : A) (s : state T U) (v : V) : Prop.
  Class Statement (A : Type) := stm_R (stm : A) (s s' : state T U) : Prop.

  Definition Assertion := state T U -> Prop.
  Definition assert_implies (P Q : Assertion) : Prop :=
    forall s, P s -> Q s.
  Definition assert_iff (P Q : Assertion) : Prop :=
    forall s, P s -> Q s /\ Q s -> P s.
  Definition assert_and (P Q : Assertion) : Assertion :=
    fun s => P s /\ Q s.
  Definition hoare_triple `{Statement Σ} (P : Assertion) (stm : Σ) (Q : Assertion) : Prop :=
    forall s s', stm_R stm s s' -> P s -> Q s'.
  Definition assert_sub `{EqDec T} `{Expression Σ U} (x : T) (exp : Σ) (P : Assertion) : Assertion :=
    fun s => forall n, exp_R exp s n -> P (x ↦ n ; s).
End logic.

Global Hint Unfold assert_implies hoare_triple assert_sub : core.

Declare Scope hoare_logic_scope.
Declare Custom Entry lang.

Notation "P [ x ↦ a ]" := (assert_sub x a P)
  (at level 10, x at next level) : hoare_logic_scope.
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

Section lemmas.
  Generalizable Variables Σ.
  Context {T U : Type} (P P' Q Q' : @Assertion T U).
  Open Scope hoare_logic_scope.

  Lemma hoare_imp_pre `{@Statement T U Σ} (stm : Σ) :
    {{ P' }} stm {{ Q }} -> P ⇾ P' -> {{ P }} stm {{ Q }}.
  Proof. eauto. Qed.

  Lemma hoare_imp_post `{@Statement T U Σ} (stm : Σ) :
    {{ P }} stm {{ Q }} -> Q ⇾ Q' -> {{ P }} stm {{ Q' }}.
  Proof. eauto. Qed.

  Lemma hoare_imp_assert `{@Statement T U Σ} (stm : Σ) :
    {{ P' }} stm {{ Q }} -> P ⇾ P' -> Q ⇾ Q' -> {{ P }} stm {{ Q' }}.
  Proof. eauto. Qed.
End lemmas.