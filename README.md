# Big-step Operational Semantics of IMP in Coq

Implements the semantics of IMP and proves some lemmas.

There is also a [proof](https://github.com/GKerfImf/coq-supplementary/blob/master/Stmt.v#L146-L161) that a factorial implementation is correct.


```coq
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
    (nil, [Z.of_nat n], nil) == factorial_imperative ==> (state_f, nil, [Z.of_nat (fact n)]).
(*         ^^^^^^^^^^ -- starts with [n]         terminates with [n!] -- ^^^^^^^^^^^^^^^^^  *)
```
