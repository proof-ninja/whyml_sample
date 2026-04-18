Require Import Corelib.Numbers.BinNums.
Require Import Stdlib.ZArith.ZArith.
Require Import Lia.

Module Original.
(* loop 関数の停止性証明 *)
(* Why3 goal *)
Theorem loop'vc :
  (0%Z <= 1%Z)%Z /\
  (forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z -> (0%Z < i)%Z ->
   (forall (i1:Numbers.BinNums.Z), (i1 = (i - 1%Z)%Z) ->
    ((0%Z <= i)%Z /\ (i1 < i)%Z) /\ (0%Z <= i1)%Z)).
Proof. 
  split; lia.
Qed.

End Original.


Module Fun_with_spec.
(* loop 関数で仕様を書いた場合 *)

Parameter loop: Init.Datatypes.unit -> Numbers.BinNums.Z.

Axiom loop'spec : forall (us:Init.Datatypes.unit), ((loop us) = 0%Z).

(* Why3 goal *)
Theorem spec'vc : ((loop Init.Datatypes.tt) = 0%Z).
Proof. apply loop'spec. Qed.

(* loop 関数で仕様を書いた場合の loop 関数の停止性証明は，２つが組み合わさった定理として出てくる *)
Theorem loop'vc :
  (0%Z <= 1%Z)%Z /\
  (forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z ->
   ((0%Z < i)%Z ->
    (forall (i1:Numbers.BinNums.Z), (i1 = (i - 1%Z)%Z) ->
     ((0%Z <= i)%Z /\ (i1 < i)%Z) /\ (0%Z <= i1)%Z)) /\
   (~ (0%Z < i)%Z -> (i = 0%Z))).
Proof.
intros. repeat split; lia.
Qed.

End Fun_with_spec.


Module IsPrime.

Theorem is_prime'vc :
(* 元の定理から， int...mod1 を Z.modulo に変更した *)
  forall (n:Numbers.BinNums.Z), ~ (n < 2%Z)%Z -> ~ (2%Z = n) ->
  ~ (2%Z = 0%Z) /\
  (~ ((Z.modulo n 2%Z) = 0%Z) ->
   (let m := (n - 1%Z)%Z in
    (0%Z < 3%Z)%Z /\
    (forall (i:Numbers.BinNums.Z), (0%Z < i)%Z -> ~ (m < i)%Z ->
     ~ (i = 0%Z) /\
     (~ ((Z.modulo n i) = 0%Z) ->
      (forall (i1:Numbers.BinNums.Z), (i1 = (i + 2%Z)%Z) ->
       ((0%Z <= ((m - i)%Z + 2%Z)%Z)%Z /\
        (((m - i1)%Z + 2%Z)%Z < ((m - i)%Z + 2%Z)%Z)%Z) /\
       (0%Z < i1)%Z))))).
Proof.
intros. repeat split; try lia.
Qed.

End IsPrime.


Module IsPrime_with_spec.

Theorem is_prime'vc :
(* 元の定理から， int...mod1 を Z.modulo に変更した *)
  forall (n:Numbers.BinNums.Z), (1%Z < n)%Z ->
  ((n < 2%Z)%Z ->
   (exists m:Numbers.BinNums.Z,
    ((1%Z < m)%Z /\ (m < n)%Z) /\ ((Z.modulo n m) = 0%Z))) /\
  (~ (n < 2%Z)%Z ->
   ((2%Z = n) ->
    (forall (m:Numbers.BinNums.Z), (1%Z < m)%Z /\ (m < n)%Z ->
     (0%Z < (Z.modulo n m))%Z)) /\
   (~ (2%Z = n) ->
    ~ (2%Z = 0%Z) /\
    (((Z.modulo n 2%Z) = 0%Z) ->
     (exists m:Numbers.BinNums.Z,
      ((1%Z < m)%Z /\ (m < n)%Z) /\ ((Z.modulo n m) = 0%Z))) /\
    (~ ((Z.modulo n 2%Z) = 0%Z) ->
     (let m := (n - 1%Z)%Z in
      ((1%Z < 3%Z)%Z /\
       (forall (k:Numbers.BinNums.Z), (1%Z < k)%Z /\ (k < 3%Z)%Z ->
        (0%Z < (Z.modulo n k))%Z)) /\
      (forall (i:Numbers.BinNums.Z),
       (1%Z < i)%Z /\
       (forall (k:Numbers.BinNums.Z), (1%Z < k)%Z /\ (k < i)%Z ->
        (0%Z < (Z.modulo n k))%Z) ->
       ((m < i)%Z ->
        (forall (m1:Numbers.BinNums.Z), (1%Z < m1)%Z /\ (m1 < n)%Z ->
         (0%Z < (Z.modulo n m1))%Z)) /\
       (~ (m < i)%Z ->
        ~ (i = 0%Z) /\
        (((Z.modulo n i) = 0%Z) ->
         (exists m1:Numbers.BinNums.Z,
          ((1%Z < m1)%Z /\ (m1 < n)%Z) /\
          ((Z.modulo n m1) = 0%Z))) /\
        (~ ((Z.modulo n i) = 0%Z) ->
         (forall (i1:Numbers.BinNums.Z), (i1 = (i + 2%Z)%Z) ->
          ((0%Z <= ((m - i)%Z + 2%Z)%Z)%Z /\
           (((m - i1)%Z + 2%Z)%Z < ((m - i)%Z + 2%Z)%Z)%Z) /\
          (1%Z < i1)%Z /\
          (forall (k:Numbers.BinNums.Z), (1%Z < k)%Z /\ (k < i1)%Z ->
           (0%Z < (Z.modulo n k))%Z))))))))).
Proof.
  intros. repeat split; try lia.
  - intros. exists 2%Z. lia.
  - intros. assert (Ha : k = 2%Z). { lia. } subst. admit.
  - intros. admit.
  - intros. exists i%Z. lia.
  - intros. admit.
Admitted.

End IsPrime_with_spec.