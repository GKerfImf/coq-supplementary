(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Omega.

Inductive id : Type :=
  Id : nat -> id.

Reserved Notation "m <<= n" (at level 70, no associativity).
Reserved Notation "m >>  n" (at level 70, no associativity).
Reserved Notation "m <<  n" (at level 70, no associativity).

Inductive le_id : id -> id -> Prop :=
  le_conv : forall n m, n <= m -> (Id n) <<= (Id m)
where "n <<= m" := (le_id n m).   

Inductive lt_id : id -> id -> Prop :=
  lt_conv : forall n m, n < m -> (Id n) << (Id m)
where "n << m" := (lt_id n m).   

Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) >> (Id m)
where "n >> m" := (gt_id n m).   

Notation "n <<= m" := (le_id n m).
Notation "n >>  m" := (gt_id n m).
Notation "n <<  m" := (lt_id n m).

Lemma lt_eq_lt_id_dec: forall (id1 id2 : id), {id1 << id2} + {id1 = id2} + {id2 << id1}.
Proof.
  intros [n] [m].
  destruct (lt_eq_lt_dec n m) as [[LT|EQ]|GT].
  - left; left; constructor; exact LT.
  - left; right; rewrite EQ; reflexivity.
  - right; constructor; exact GT.
Qed.

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 >> id2} + {id1 = id2} + {id2 >> id1}.
Proof.
  intros.
  destruct (lt_eq_lt_id_dec id1 id2) as [[H|H]|H].
  - right.
    inversion H.
    apply gt_conv; auto.
  - left; right; assumption.
  - left; left.
    inversion H.
    apply gt_conv; auto. 
Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 <<= id2} + {id1 >> id2}.
Proof.
  intros [n] [m].
  destruct (le_gt_dec n m) as [LE|GT].
  - left; apply le_conv; assumption.
  - right; apply gt_conv; assumption.
Qed.

Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n.
  induction n; intros.
  - destruct m as [|m].
     + left; reflexivity.
     + right; trivial.
  - destruct m as [|m].
    + right; apply not_eq_sym; trivial. 
    + destruct (IHn m) as [IH|IH]; clear IHn.
      * rewrite IH; left; reflexivity. 
      * right; intros CONTR; apply IH; inversion CONTR; reflexivity.
Qed.

Lemma eq_dec' : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n.
  induction n; intros.
  - destruct m as [|m]; auto.
  - destruct m as [|m]; auto.
    destruct (IHn m) as [IH|IH]; auto.
Qed.

Lemma eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  intros [n] [m].
  destruct (eq_dec n m) as [EQ|NEQ].
  - left; rewrite EQ; auto.
  - right; intros CONTR; apply NEQ.
    inversion CONTR; reflexivity.
Qed.  

Lemma eq_id : forall (T:Type) x (p q:T), (if eq_id_dec x x then p else q) = p. 
Proof.
  intros.
  destruct (eq_id_dec x x).
  - reflexivity.
  - exfalso; apply n; reflexivity.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if eq_id_dec x y then p else q) = q. 
Proof.
  intros.
  destruct (eq_id_dec x y) as [EQ|NEQ].
  - exfalso; apply H; assumption.
  - reflexivity.
Qed.

Lemma ltnW : forall n m: nat, n < m -> n <= m.
Proof.
  intros n.
  induction n.
  - intros m _.
    apply Peano.le_0_n.
  - intros [|m] H.
    + apply Nat.nlt_0_r in H.
      inversion H.
    + apply le_n_S.
      apply IHn.
      apply lt_S_n.
      assumption.
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id, id1 >> id2 -> id2 >> id1 -> False.
Proof.
  intros ? ? LT GT.
  inversion LT; subst.
  inversion GT; subst.
  apply lt_not_le in H; apply H.
  apply ltnW; auto.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id, id2 <<= id1 -> id2 >> id1 -> False.
Proof.
  intros ? ? LE GT.
  inversion LE; subst.
  inversion GT; subst.
  apply lt_not_le in H2; apply H2.
  assumption.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, id1 <<= id2 -> {id1 = id2} + {id2 >> id1}.
Proof.

  admit.

Admitted.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id, id1 <> id2 -> {id1 >> id2} + {id2 >> id1}.
Proof.
  admit.

Admitted.
    
Lemma eq_gt_id_false : forall id1 id2 : id, id1 = id2 -> id1 >> id2 -> False.
Proof.

  admit.

Admitted.

