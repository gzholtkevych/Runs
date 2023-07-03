Require Import Lists.List.
Import ListNotations.


Section Relations.
  Variable U : Type.

  Definition Relation := U -> U -> Prop.

  Variable R : Relation.

  Inductive Reflexive : Prop := 
    reflexivity : forall x:U, R x x -> Reflexive.

  Inductive Irreflexive : Prop := 
    irreflexivity : forall x:U, ~ R x x -> Irreflexive.

  Inductive Transitive : Prop := 
    transitivity : forall x y z:U, R x y -> R y z -> R x z -> Transitive.

  Inductive Symmetric : Prop :=
    symmetry : forall x y:U, R x y -> R y x -> Symmetric.

  Inductive StrictOrder : Prop :=
    sord_rel : Irreflexive -> Transitive -> StrictOrder.

  Inductive Equivalence : Prop :=
    eq_rel : Reflexive -> Transitive -> Symmetric -> Equivalence.

End Relations.
Arguments Reflexive {U} (R).
Arguments Irreflexive {U} (R).
Arguments Transitive {U} (R).
Arguments Symmetric {U} (R).
Arguments StrictOrder {U} (R).
Arguments Equivalence {U} (R).


Inductive increasing : list nat -> Prop :=
    inc0 : increasing []
  | inc1 : forall n, increasing [n]
  | incS : forall n m ns, 
             n < m -> increasing (m :: ns) -> increasing (n :: m :: ns).
