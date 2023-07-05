Require Import Lists.List.
Import ListNotations.
Require Import Arith.Lt.
Require Import Runs.Definitions.


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
  Admitted.