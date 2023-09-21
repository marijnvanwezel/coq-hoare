Require Import Hoare.State.

Declare Scope hoare_logic_scope.
Open Scope hoare_logic_scope.

Section logic.
  Generalizable All Variables.

  Context (T U : Type).
  
  Implicit Type s : state T U.

  Definition Assertion := state T U -> Prop.

  Definition assert_implies (P Q : Assertion) : Prop :=
    forall s, P s -> Q s.
  Notation "P ⇾ Q" := (assert_implies P Q) (at level 80) : hoare_logic_scope.

  Definition assert_iff (P Q : Assertion) : Prop :=
    forall s, P s -> Q s /\ Q s -> P s.
  Notation "P ⇿ Q" := (assert_iff P Q) (at level 80) : hoare_logic_scope.

  Class Statement (A : Type) := {
    stm_R (stm : A) s s' : Prop
  }.
  Notation "⟨ x , y ⟩ ⇒ z" := (stm_R x y z)
    (at level 40, y at level 99, x constr at level 99, z constr at level 98).

  Definition hoare_triple `{Statement Σ} (P : Assertion) (stm : Σ) (Q : Assertion) : Prop :=
    forall s s', ⟨stm, s⟩ ⇒ s' -> P s -> Q s'.
  Notation "{{ P }} s {{ Q }}" := (hoare_triple P s Q)
    (at level 90, s at level 99) : hoare_logic_scope.

  Theorem hoare_post_tauto `{Statement Σ} :
    forall (P Q : Assertion) (stm : Σ), (forall s, Q s) -> {{ P }} stm {{ Q }}.
  Proof. unfold hoare_triple. intros. apply H0. Qed.
End logic.