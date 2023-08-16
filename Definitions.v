Require Import Lists.List.
Import ListNotations.
Require Export Runs.Preliminaries.


(* --------------------------------------------------------------------------
   An inhabitant of 'NameSet' is an ascending list of natural numbers each
   identifying an event source. The condition of the ascendance ensures
   one-to-one correspondence between ascending lists and finite sets.
   -------------------------------------------------------------------------- *)
(*
Definition NameSet : Set := { names : list nat | increasing names }.
Coercion toList := fun s : NameSet => proj1_sig s.
*)
Record Tick (base : NatFinSubset) : Set := declareTick {
  name : nat;  (* name of the tick source *)
  idx  : nat;  (* nmber of the tick       *)
  name_in_base : In name base
}.
Arguments name {base}. 
Arguments idx {base}. 

Section aRun.
  Variable base : NatFinSubset.
  Let tickset := Tick base.
  Variables pre sync : Relation tickset.

  Class aRun := {
    sord_pre : StrictOrder pre;
    eq_sync : Equivalence sync;
    pre_sync : forall t1 t1' t2 t2', 
      sync t1 t1' -> sync t2 t2' -> pre t1 t2 -> pre t1' t2';
    pre_line : forall t1 t2, 
      name t1 = name t2 -> (pre t1 t2 <-> idx t1 < idx t2);
    fin_hist : forall t, 
      exists e : list tickset, forall t', pre t' t -> In t' e
  }.
End aRun.

Structure Run := declareRun {
  base : NatFinSubset;
  tickset := Tick base;
  pre : Relation tickset;
  sync : Relation tickset;
  conc : Relation tickset := fun x y => ~ pre x y /\ ~ pre y x /\ ~ sync x y; 
  certRun : aRun base pre sync 
}.

Notation "x 'pre' y" := (pre _ x y)  (at level 70).
Notation "x 'sync' y" := (sync _ x y)  (at level 70).
Notation "x 'conc' y" := (conc _ x y)  (at level 70).


Section aRunMorphism.
Variables
  (dom cod : Run)
  (map : tickset dom -> tickset cod).

  Class aRunMorphism := {
    preserve_name : forall x y, name x = name y -> name (map x) = name (map y);
    preserve_pre : forall x y, x pre y -> (map x) pre (map y);
    preseve_sync : forall x y, x sync y -> (map x) sync (map y)
  }.

  Class aStrictRunMorphism :=
    reflect_sync : forall x y, (map x) sync (map y) -> x sync y.

End aRunMorphism.

Structure RunMorphism := declareRunMorphism {
  dom : Run;
  cod : Run;
  map : tickset dom -> tickset cod;
  certRunMorphism : aRunMorphism dom cod map
}.
