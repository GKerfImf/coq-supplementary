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
  intros.
  destruct id1 as [n], id2 as [m].
  destruct (lt_eq_lt_dec n m) as [[LT|EQ]|GT].
  - left; left; constructor; exact LT.
  - left; right; rewrite EQ; reflexivity.
  - right; constructor; exact GT.
Qed.

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 >> id2} + {id1 = id2} + {id2 >> id1}.
Proof. admit. Admitted.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 <<= id2} + {id1 >> id2}.
Proof. admit. Admitted.

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
Proof. admit. Admitted. 

Lemma eq_id : forall (T:Type) x (p q:T), (if eq_id_dec x x then p else q) = p. 
Proof. admit. Admitted.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if eq_id_dec x y then p else q) = q. 
Proof. admit. Admitted.

Lemma lt_gt_id_false : forall id1 id2 : id, id1 >> id2 -> id2 >> id1 -> False.
Proof. admit. Admitted.

Lemma le_gt_id_false : forall id1 id2 : id, id2 <<= id1 -> id2 >> id1 -> False.
Proof. admit. Admitted.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, id1 <<= id2 -> {id1 = id2} + {id2 >> id1}.
Proof. admit. Admitted.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id, id1 <> id2 -> {id1 >> id2} + {id2 >> id1}.
Proof. admit. Admitted.
    
Lemma eq_gt_id_false : forall id1 id2 : id, id1 = id2 -> id1 >> id2 -> False.
Proof. admit. Admitted.

