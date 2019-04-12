
Theorem contrapositive:
  forall P Q: Prop, (P -> Q) -> (~Q -> ~P).
Proof.
intros. intro. apply H0. apply H. apply H1.
Qed.

Theorem double_neg_inv: forall P: Prop, P -> ~~P.
Proof.
intros. unfold not. intros. apply H0 in H. auto.
Qed.

Axiom excluded_middle: forall Q, Q \/ ~Q.

Theorem double_neg: forall P, ~~P -> P.
Proof.
intros. destruct (excluded_middle P).
auto. apply H in H0. contradiction.
Qed.

Theorem contrapositive_inv:
  forall P Q: Prop, (~Q -> ~P) -> (P -> Q).
Proof.
intros. apply double_neg. unfold not. intros.
apply H in H1.
destruct (excluded_middle P); contradiction.
Qed.

Section laws.
Variable A: Type.
Variable P: A -> Prop.

Theorem exists_not_forall_not:
  (exists a, P a) -> ~(forall a, ~ (P a)).
Proof.
unfold not.
intros.
destruct H.
eapply H0. eauto.
Qed.

Theorem forall_inv_exists:
  ~(forall a, ~(P a)) -> exists a, P a.
Proof.
apply contrapositive_inv.
intros.
apply double_neg_inv.
unfold not in H. unfold not.
intros.
apply H. exists a. exact H0.
Qed.
