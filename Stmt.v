Require Import List.
Import ListNotations.
Require Import Omega.

Require Export BinInt.
Require Export Id.
Require Export State.
Require Export Expr.

(* The type of statements *)
Inductive stmt : Type :=
| SKIP  : stmt
| Assn  : id -> expr -> stmt
| READ  : id -> stmt
| WRITE : expr -> stmt
| Seq   : stmt -> stmt -> stmt
| If    : expr -> stmt -> stmt -> stmt
| While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf :=  (state Z * list Z * list Z)%type.

Reserved Notation "c1 '==' s '==>' c2" (at level 0).

(* Big-step evaluation relation *)
Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop := 
| bs_Skip        : forall (c : conf), c == SKIP ==> c 
| bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z), 
    [| e |] s => z -> (s, i, o) == x ::= e ==> (s [x <- z], i, o)
| bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
    (s, z::i, o) == READ x ==> (s [x <- z], i, o)
| bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z), 
    [| e |] s => z -> (s, i, o) == WRITE e ==> (s, i, z::o)
| bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt),
    c == s1 ==> c' -> c' == s2 ==> c'' -> c ==  s1 ;; s2 ==> c''
| bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt),
    [| e |] s => Z.one -> (s, i, o) == s1 ==> c' -> (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt),
    [| e |] s => Z.zero -> (s, i, o) == s2 ==> c' -> (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt),
    [| e |] st => Z.one -> (st, i, o) == s ==> c' -> c' == WHILE e DO s END ==> c'' ->
                  (st, i, o) == WHILE e DO s END ==> c''
| bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt),
    [| e |] st => Z.zero -> (st, i, o) == WHILE e DO s END ==> (st, i, o)
where "c1 == s ==> c2" := (bs_int s c1 c2).

Hint Constructors bs_int.


(* Big-step semantics is deterministic *)
Lemma bs_int_deterministic:
  forall (c c1 c2 : conf) (s : stmt), c == s ==> c1 -> c == s ==> c2 -> c1 = c2.
Proof.
  intros.
  generalize dependent c2.
  induction H; intros c1 HYP. 
  all: inversion_clear HYP.
  all: try reflexivity.
  all: try (match goal with
            | H1: [| _ |] _ => (Z.zero), H2: [| _ |] _ => (Z.one)  |- _=>
              exfalso; apply (bs_eval_deterministic _ _ _ _ H1) in H2; inversion H2  
            end).
  - apply (bs_eval_deterministic _ _ _ _ H) in H0; subst; reflexivity.
  - apply (bs_eval_deterministic _ _ _ _ H) in H0; subst; reflexivity.
  - apply IHbs_int1 in H1; subst.
    apply IHbs_int2 in H2; subst. reflexivity.
  - apply IHbs_int; assumption.
  - apply IHbs_int; assumption.
  - apply IHbs_int1 in H3; subst.
    apply IHbs_int2 in H4; subst. reflexivity.
Qed.

Reserved Notation "s1 '~~~' s2" (at level 0).

Inductive bs_equivalent: stmt -> stmt -> Prop :=
  bs_eq_intro: forall (s1 s2 : stmt), 
    (forall (c c' : conf), c == s1 ==> c' <-> c == s2 ==> c') -> s1 ~~~ s2
where "s1 '~~~' s2" := (bs_equivalent s1 s2).

Module SmokeTest.

  Lemma seq_assoc : forall (s1 s2 s3 : stmt),
    ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof.
    intros; constructor; intros.
    split; intros HYP.
    { inversion_clear HYP; inversion_clear H.
      eapply bs_Seq; eauto. 
    } 
    { inversion_clear HYP; inversion_clear H0.
      eapply bs_Seq; eauto.
    } 
  Qed.      

  Lemma while_unfolds : forall (e : expr) (s : stmt),
      (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    intros; constructor; intros.
    split; intros HYP.
    { inversion_clear HYP.
      apply bs_If_True; eauto. 
      apply bs_If_False; eauto. 
    }       
    { inversion_clear HYP.
      { inversion_clear H0.
        eapply bs_While_True; eauto. }
      { inversion H0. 
        eapply bs_While_False; eauto. }
    }
  Qed.

  Lemma while_false : forall (e : expr) (s : stmt) (st : state Z) (i o : list Z) (c : conf),
      c == WHILE e DO s END ==> (st, i, o) -> [| e |] st => Z.zero.
  Proof.
    intros e s st i o c1 H.
    remember (st, i, o) as c2.
    remember (WHILE e DO s END).
    induction H; inversion Heqc2; subst; inversion Heqs0; subst; eauto.
  Qed.

  Definition True := Nat 1.

  Lemma loop_eq_undefined:
    (WHILE True DO SKIP END) ~~~ (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    constructor; intros [[st1 i1] o1] [[st2 i2] o2]; split; intros H.
    - remember (WHILE True DO SKIP END).
      induction H; inversion Heqs.
      + subst.
        apply IHbs_int2 in Heqs.
        inversion H0. rewrite H4. assumption.
      + exfalso; subst; inversion H.
    - inversion_clear H; inversion_clear H0.
  Qed.

  Section Factorial.

    Let factorial_imperative :=
      (Id 0 ::= Nat 1);;
      (READ (Id 1));;
      (WHILE Var (Id 1) [>] Nat 0 DO
        (Id 0 ::= (Var (Id 0) [*] Var (Id 1)));;
        (Id 1 ::= (Var (Id 1) [-] Nat 1))
      END);;
      WRITE (Var (Id 0)).


    Lemma factorial_correct:
      forall n, exists state_f,
          (nil, [Z.of_nat n], nil) ==
          factorial_imperative
            ==> (state_f, nil, [Z.of_nat (fact n)]).
    Proof.
      assert (Fact1: Id 0 <> Id 1) by (intros CONTR; inversion CONTR).
      assert (Fact2: Id 1 <> Id 0) by (intros CONTR; inversion CONTR).
      intros n.
      assert (
          Fact: forall m state_s, exists state_f,
              (((state_s [Id 0 <- m%Z]) [Id 1 <- Z.of_nat n], [], [])) ==
              WHILE Var (Id 1) [>] Nat 0 DO
                    (Id 0 ::= (Var (Id 0) [*] Var (Id 1)));;
                    (Id 1 ::= (Var (Id 1) [-] Nat 1))
                    END ==> (state_f [Id 0 <- (m * Z.of_nat (fact n))%Z][Id 1 <- 0%Z],[],[])).
      { induction n.
        { intros; rewrite Z.mul_1_r.
          exists state_s.
          eapply bs_While_False, bs_Gt_F. 
          - apply bs_Var, st_binds_hd.
          - apply bs_Nat.
          - apply Z.le_refl. 
        }
        intros.
        specialize (IHn (m * Z.of_nat (S n))%Z).
        specialize (IHn (((state_s) [Id 0 <- m]) [Id 1 <- Z.of_nat (S n)])).
        destruct IHn as [state_f IHn].
        exists state_f.
        eapply bs_While_True.
        { eapply bs_Gt_T.
          - eapply bs_Var, st_binds_hd.
          - apply bs_Nat.
          - apply Zgt_pos_0. 
        } 
        { eapply bs_Seq.
          { apply bs_Assign, bs_Mul.
            - apply bs_Var, st_binds_tl; auto. 
              apply st_binds_hd.
            - apply bs_Var, st_binds_hd.
          }
          { apply bs_Assign, bs_Sub.
            - apply bs_Var, st_binds_tl; auto.
              apply st_binds_hd.
            - apply bs_Nat.
          }
        }
        { assert(EQ: (Z.of_nat (S n) - Z.of_nat 1)%Z = (Z.of_nat n)%Z).
          { rewrite <- Nat2Z.inj_sub; simpl.
            rewrite <- minus_n_O; auto.
            apply Peano.le_n_S, Nat.le_0_l.
          } rewrite EQ; clear EQ.
          assert (EQ: (m * Z.of_nat (S n) * Z.of_nat (fact n))%Z =
                      (m * Z.of_nat (fact (S n)))%Z).
          { assert(F: fact (S n) = (S n) * fact n) by auto.
            rewrite F; rewrite Nat2Z.inj_mul; rewrite Z.mul_assoc; auto.
          } rewrite <- EQ; clear EQ.
          apply IHn.
        }
      }
      specialize (Fact 1%Z ([])); rewrite Z.mul_1_l in Fact.
      destruct Fact as [state_f Fact].
      exists (state_f[Id 0 <- Z.of_nat (fact n)][Id 1 <- 0%Z]).
      eapply bs_Seq. apply bs_Assign; constructor.
      eapply bs_Seq. eapply bs_Read; constructor.
      eapply bs_Seq. apply Fact.
      eapply bs_Write.
      apply bs_Var.
      apply st_binds_tl; auto.
      apply st_binds_hd.
    Qed.    

  End Factorial.
    
End SmokeTest.

(* Contextual equivalence *)
Inductive Context : Type :=
| Hole 
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt := 
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s) 
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: stmt -> stmt -> Prop :=
  ceq_intro : forall (s1 s2 : stmt),
    (forall (C : Context), (C <~ s1) ~~~ (C <~ s2)) -> s1 ~c~ s2
where "s1 '~c~' s2" := (contextual_equivalent s1 s2).

(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq: forall (s1 s2 : stmt), s1 ~~~ s2 <-> s1 ~c~ s2.
Proof. admit. Admitted.

(* CPS-style semantics *)
Inductive cont : Type := 
| KEmpty : cont
| KStmt  : stmt -> cont.

Definition Kapp (l r : cont) : cont :=
  match (l, r) with
  | (KStmt ls, KStmt rs) => KStmt (ls ;; rs)
  | (KEmpty  , _       ) => r
  | (_       , _       ) => l
  end.

Notation "'!' s" := (KStmt s) (at level 0).
Notation "s1 @ s2" := (Kapp s1 s2) (at level 0).

Reserved Notation "k '|-' c1 '--' s '-->' c2" (at level 0).

Inductive cps_int : cont -> cont -> conf -> conf -> Prop :=
| cps_Empty       : forall (c : conf), KEmpty |- c -- KEmpty --> c
| cps_Skip        : forall (c c' : conf) (k : cont), 
    KEmpty |- c -- k --> c' -> 
              k |- c -- !SKIP --> c'
| cps_Assn        : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (x : id) (e : expr) (n : Z),
    [| e |] s => n ->
                 KEmpty |- (s [x <- n], i, o) -- k --> c' ->
                           k |- (s, i, o) -- !(x ::= e) --> c'
| cps_Read        : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (x : id) (z : Z),
    KEmpty |- (s [x <- z], i, o) -- k --> c' ->
              k |- (s, z::i, o) -- !(READ x) --> c'
| cps_Write       : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (z : Z),
    [| e |] s => z ->
                 KEmpty |- (s, i, z::o) -- k --> c' ->
                           k |- (s, i, o) -- !(WRITE e) --> c'
| cps_Seq         : forall (c c' : conf) (k : cont) (s1 s2 : stmt), 
    !s2 @ k |- c -- !s1 --> c' ->
               k |- c -- !(s1 ;; s2) --> c'
| cps_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s1 s2 : stmt),
    [| e |] s => Z.one ->
                 k |- (s, i, o) -- !s1 --> c' ->
                      k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s1 s2 : stmt),
    [| e |] s => Z.zero ->
                 k |- (s, i, o) -- !s2 --> c' ->
                      k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_While_True  : forall (st : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s : stmt),
    [| e |] st => Z.one ->
                  !(WHILE e DO s END) @ k |- (st, i, o) -- !s --> c' ->
                                             k |- (st, i, o) -- !(WHILE e DO s END) --> c'
| cps_While_False : forall (st : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s : stmt),
    [| e |] st => Z.zero ->
                  KEmpty |- (st, i, o) -- k --> c' ->
                            k |- (st, i, o) -- !(WHILE e DO s END) --> c'
where "k |- c1 -- s --> c2" := (cps_int k s c1 c2).

Lemma bs_int_to_cps_int: forall (st : state Z) (i o : list Z) (c' : conf) (s : stmt),
    (st, i, o) == s ==> c' -> KEmpty |- (st, i, o) -- !s --> c'.
Proof. admit. Admitted.

Lemma cps_int_to_bs_int: forall (st : state Z) (i o : list Z) (c' : conf) (s : stmt),
    KEmpty |- (st, i, o) -- !s --> c' -> (st, i, o) == s ==> c'.
Proof. admit. Admitted.
