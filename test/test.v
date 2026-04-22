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
        (0%Z < (Z.modulo n k))%Z) /\
       (0%Z < (Z.modulo 3%Z 2%Z))%Z) /\
      (forall (i:Numbers.BinNums.Z),
       (1%Z < i)%Z /\
       (forall (k:Numbers.BinNums.Z), (1%Z < k)%Z /\ (k < i)%Z ->
        (0%Z < (Z.modulo n k))%Z) /\
       (0%Z < (Z.modulo i 2%Z))%Z ->
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
           (0%Z < (Z.modulo n k))%Z) /\
          (0%Z < (Z.modulo i1 2%Z))%Z)))))))).
Proof.
  intros. repeat split; try lia.
  - intros. exists 2%Z. lia.
  - intros. assert (k = 2%Z) by lia. subst. 
    assert ((0 <= n mod 2)%Z) by (apply Z.mod_pos_bound; lia). lia.
  - intros. apply H3. lia.
  - intros. exists i%Z. lia.
  - intros. destruct (Z.eq_dec k (i+1)).
    + (* k = i+1 *) subst. destruct H3 as [_ [_ H3]]. 
      assert (Ha : (i mod 2 = 1)%Z). {
        assert ((0 <= i mod 2 < 2)%Z) by (apply Z.mod_pos_bound; lia).
        lia.
      }
      assert (Hb : (i = 2 * (i / 2) + 1)%Z). {
        rewrite <- Ha. apply Z.div_mod. lia.
      } 
      assert (Hc : (i + 1)%Z = (2 * (i / 2 + 1))%Z). {
        rewrite Hb at 1. lia.
      }
      rewrite Hc. set (l := ((i / 2 + 1))%Z).
      assert ((n mod (2 * l) <> 0)%Z). {
        intros Hcontra.
        assert (Hd : (n = 2 * l * (n / (2 * l)) + n mod (2 * l))%Z) by (apply Z.div_mod; lia).
        rewrite Hcontra in Hd. rewrite Z.add_0_r in Hd.
        apply H2.
        rewrite Hd. rewrite <- Z.mul_assoc. rewrite Z.mul_comm. 
        apply Z.mod_mul. discriminate.
      }
      assert ((0 <= n mod (2 * l))%Z) by (apply Z.mod_pos_bound; lia).
      lia.
    + (* k < i+1 *) destruct (Z.eq_dec k i).
      * (* k = i *) subst. 
        assert ((0 <= n mod i)%Z) by (apply Z.mod_pos_bound; lia). lia.
      * (* k < i *) apply H3. lia.
  - rewrite H6. rewrite Z.add_mod; try lia. rewrite Z.mod_same; try lia.
    rewrite Z.add_0_r. rewrite Z.mod_mod; lia.
Qed.

End IsPrime_with_spec.