(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Omega.
Require Export Arith Arith.EqNat.
Require Export Id.

Section S.
  
  Variable A : Set.

  Definition state := list (id * A). 

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
  | st_binds_hd :
      forall st id x,
        ((id, x) :: st) / id => x
  | st_binds_tl :
      forall st id x id' x',
        id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).

  Lemma st_unbind_hd: forall (st: state) (id1 id2: id) (n m: A),
      id1 <> id2 ->
      (((id1, n) :: st) / id2 => (m)) ->
      ((st) / id2 => (m)).
  Proof.
    intros ? ? ? ? ? NEQ EV.
    inversion EV.
    - exfalso; apply NEQ; auto. 
    - assumption.
  Qed.    
    
  Lemma state_deterministic: forall (st : state) (x : id) (n m : A),
    st / x => n -> st / x => m -> n = m.
  Proof.
    intros ? ? ? ? ST1 ST2.
    induction st as [| [id a] st].
    - inversion ST1. 
    - destruct (eq_id_dec id x).
      + inversion ST1; subst.
        inversion ST2; subst.
        reflexivity.
        exfalso; apply H5; auto.
        exfalso; apply H4; auto.  
      + apply st_unbind_hd in ST1; apply st_unbind_hd in ST2; auto.
  Qed.
  

  Lemma update_eq : forall (st : state) (x : id) (n : A),
    st [x <- n] / x => n.
  Proof.
    intros; constructor.
  Qed.

  Lemma update_neq : forall (st : state) (x2 x1 : id) (n m : A),
    x2 <> x1 -> st / x1 => m -> st [x2 <- n] / x1 => m.
  Proof.
    intros ? ? ? ? ? NEQ ST.
    constructor; auto.
  Qed.

  Lemma update_shadow : forall (st : state) (x1 x2 : id) (n1 n2 m : A),
    st[x2 <- n1][x2 <- n2] / x1 => m -> st[x2 <- n2] / x1 => m.
  Proof.
    intros ? ? ? ? ? ? ST.
    inversion ST; subst.
    - apply update_eq.
    - clear ST; rename H5 into ST. 
      apply st_unbind_hd in ST; auto.
      apply update_neq; auto.
  Qed.      

  Lemma update_same : forall (st : state) (x1 x2 : id) (n1 m : A),
    st / x1 => n1 -> st / x2 => m -> st [x1 <- n1] / x2 => m.
  Proof.
    intros ? ? ? ? ? ST1 ST2.
    destruct (eq_id_dec x1 x2) as [EQ|NEQ].
    - subst x2. 
      eapply state_deterministic in ST1; eauto.
      subst n1.
      apply update_eq.
    - apply update_neq; auto.
  Qed.

  Lemma update_permute : forall (st : state) (x1 x2 x3 : id) (n1 n2 m : A),
    x2 <> x1 -> 
    st [x2 <- n1][x1 <- n2] / x3 => m ->
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    intros ? ? ? ? ? ? ? NEQ ST.
    
    

    
    admit. Admitted.  

End S.