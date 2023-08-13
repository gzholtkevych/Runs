Require Import Lists.List.
Import ListNotations.


Section Relations.
  Variable U : Type.

  Definition Relation := U -> U -> Prop.

  Variable R : Relation.

  Definition Reflexive : Prop := forall x : U, R x x.

  Definition Irreflexive : Prop := forall x : U, ~ R x x.

  Definition Transitive : Prop := forall x y z : U, R x y -> R y z -> R x z.

  Definition Symmetric : Prop := forall x y : U, R x y -> R y x.

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

