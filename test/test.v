
(* Why3 goal *)
Theorem loop'vc :
  ((0-1) < 1) /\
  (forall i, ((0-1) < i) -> (0 < i) ->
   (forall i1, (i1 = (i - 1)) ->
    ((0 <= i) /\ (i1 < i)) /\ ((0-1) < i1))).
Proof.
  repeat split.
  auto.
  


Admitted.