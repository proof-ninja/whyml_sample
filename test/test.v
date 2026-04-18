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