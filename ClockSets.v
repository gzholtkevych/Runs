(* -----------------------------------------------------------------------------
   This script contains definitions, properties, and certificates for
   the naming of clocks.
   We assume that there is exactly an enumerable set of names and a computable 
   method for distinguishing two different names.
   Therefore, natural numbers are used as name identifiers here.
   -------------------------------------------------------------------------- *)

Require Import Utf8.
Require Import Lists.List.
Require Import Arith.Compare_dec.
Require Import Arith.PeanoNat.
Import ListNotations.


Inductive ClockName : Set := c : nat → ClockName.

Definition idx (cn : ClockName) : nat := let 'c n := cn in n.


(* -----------------------------------------------------------------------------
   The predicate for recognising lists of clock names has been sorted by
   increasing of their identifiers. 
   -------------------------------------------------------------------------- *)
Inductive increasing : list ClockName → Prop :=
  | inc0 : increasing []
  | inc1 : ∀ cn, increasing [cn]
  | incS : ∀ cn cm cs, 
      idx cn < idx cm → increasing (cm :: cs) → increasing (cn :: cm :: cs).

Definition increasing_dec :
(* the predicate is decidable ----------------------------------------------- *)
  ∀ cs : list ClockName, {increasing cs} + {¬ increasing cs}.
Proof.
  intro.
  destruct cs as [| cn cs'].
  - left. constructor.
  - revert cn. induction cs' as [| cm cs'' IHcs''].
    + left. constructor.
    + intro. pose (n := idx cn). pose (m := idx cm).
      destruct (lt_eq_lt_dec n m) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      * { elim (IHcs'' cm); intro H.
        - left. now constructor.
        - right. intro H1. apply H. now inversion_clear H1. }
      * right. intro H. inversion_clear H. subst n m. rewrite Heq in H0.
        now apply Nat.lt_irrefl with (idx cm).
      * right. intro H. inversion_clear H.
        apply Nat.lt_irrefl with (idx cm). now apply Nat.lt_trans with n.
Defined.
(* ========================================================================== *)

(* -----------------------------------------------------------------------------
   The type 'ClockSet' is used for modelling finite subsets of names,
   with the coercion 'toList' ensuring to operate with inhabitants of 
   this type as with lists. 
   -------------------------------------------------------------------------- *)
Definition ClockSet : Set := {cs : list ClockName | increasing cs}.
Coercion toList := fun cs : ClockSet => proj1_sig cs.
(* -------------------------------------------------------------------------- *)

Fixpoint aux_inject (cn : ClockName) (lst : list ClockName) : list ClockName :=
(* the auxiliary function for injecting a clock name 'cn' into a the list
   of clock names 'lst' before such a member of 'lst'  whose identifier is
   greater than the identifier of 'cn'.
   -------------------------------------------------------------------------- *)
    match lst with
    | []        => [cn]
    | cm :: lst' => match (lt_eq_lt_dec (idx cn) (idx cm)) with
        | inleft Hle => match Hle with
            | left _  => cn :: cm :: lst'
            | right _ => cm :: lst'
            end
        | inright _  => cm :: (aux_inject cn lst')
        end
    end.

Definition inject (cn : ClockName) (cs : ClockSet) : ClockSet.
(* the function injects a clock name 'cn' into a clock set 'cs'.
   -------------------------------------------------------------------------- *)
Proof.
  destruct cs as (lst, H). pose (aux_inject cn lst) as nlst.
  exists nlst. subst nlst.
  destruct lst as [| cm lst'].
  - constructor.
  - simpl. destruct (lt_eq_lt_dec (idx cn) (idx cm)) as [Hle | Hgt];
    try destruct Hle as [Hlt | Heq].
    + now constructor.
    + assumption.
    + revert cn cm H Hgt. induction lst' as [| ck lst'' IHlst''].
      * constructor; [assumption | constructor].
      * intros. {
        simpl. destruct (lt_eq_lt_dec (idx cn) (idx ck)) as [Hle | Hgt'];
        try destruct Hle as [Hlt | Heq].
        - constructor; [ assumption | constructor ]; try assumption.
          now inversion_clear H.
        - assumption.
        - inversion_clear H.
          constructor; try assumption. now apply IHlst''. }
Defined.
