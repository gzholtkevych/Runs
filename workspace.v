Require Import Lists.List.
Require Import Runs.Definitions.
Import ListNotations.
Require Import Arith.Lt.
Require Import Arith.PeanoNat.


Section Counter.

  Let oneNameSet : NameSet. Proof. exists [0]. constructor. Defined.
  Let oneTickset := Tick oneNameSet.
  Let onePre := fun x y : oneTickset => idx x < idx y.
  Let oneSync := fun x y : oneTickset => name x = name y /\ idx x = idx y.

  Let O_in_oneNameSet : In 0 oneNameSet.
  Proof. now left. Qed.

  Let init := fix init (n : nat) : list oneTickset :=
     match n with
       0    => []
     | S n' =>
         let x := {| name := 0; idx := n'; name_in_base := O_in_oneNameSet |}
         in init n' ++ [x]
     end.

  Instance counter_constr : aRun oneNameSet onePre oneSync.
  Proof.
    constructor.
    - constructor.
      + unfold Irreflexive. intros * H.
        destruct x. compute in H. now apply Nat.lt_irrefl with idx.
      + unfold Transitive. intros * H1 H2. compute in H1, H2 |-*.
        destruct x, y, z.
        now apply Nat.lt_trans with idx0.
    - constructor.
      + unfold Reflexive. intro. compute.
        destruct x. now split.
      + unfold Transitive. intros * H1 H2.
        destruct x, y, z. compute in H1, H2 |-*. destruct H1, H2.
        split.
        * now rewrite H.
        * now rewrite H0.
      + unfold Symmetric. intros * H.
        destruct x, y. compute in H |-*. destruct H.
        split; now symmetry.
    - intros * H1 H2 H3. destruct t1, t1', t2, t2'.
      compute in H1, H2, H3 |-*.
      destruct H1 as (_, H1'), H2 as (_, H2'). now rewrite <- H1', <- H2'.
    - intros * H1. destruct t1, t2.
      destruct H1. compute. split; intro; assumption.
    - intro. exists (idx t). intros. now unfold onePre in H.
  Defined.

  Definition counter : Run :=
    declareRun oneNameSet onePre oneSync counter_constr.

End Counter.