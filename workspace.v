Require Import Lists.List.
Import ListNotations.
Require Import Arith.Lt.
Require Import Runs.Definitions.


Section Counter.

  Definition oneNameSet : NameSet.
  Proof. exists [0]. constructor. Defined.

  Let oneTick := Tick oneNameSet.
  Let onePre := fun t1 t2 : oneTick => idx t1 < idx t2.
  Let oneSync := fun t1 t2 : oneTick => name t1 = name t2 /\ idx t1 = idx t2.

  Let O_in_oneNameSet : In 0 oneNameSet.
  Proof. now left. Qed.

  Let init := fix init (n : nat) : list oneTick :=
     match n with
       0    => []
     | S n' =>
         let x := {| name := 0; idx := n'; name_in_base := O_in_oneNameSet |}
         in init n' ++ [x]
     end.

  Instance counter_constr : aRun oneNameSet onePre oneSync.
  Proof.
  Admitted.