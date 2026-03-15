open Why3.Ptree
open Why3.Ity
open Why3.Constant
open Infv.Tools

(* ----- example 1 ----- 
    assert (forall x, x == x) *)
(* 量化子をつける *)
let mk_binder x : binder = (pos, Some (mk_ident x), false, None)
let example1 : expr = mk_assert (~@ (Tquant (DTforall, [mk_binder "x"], [], eq (mk_Tvar "x") (mk_Tvar "x"))))


(* ----- example 2 ----- 
    let n <- true in 
    if n then assert (n == true)
    else assert (n == false) *)

let example2 = Elet (mk_ident "n", false, RKlocal, ~! Etrue, 
  ~! (Eif (mk_Evar "n", 
    mk_assert (eq (mk_Tvar "n") (~@ Ttrue)),
    mk_assert (eq (mk_Tvar "n") (~@ Tfalse)))))


(* ----- example 3 ----- 
    foo = fun n => n + n について forall i, assert (foo i == i + i) *)
let spec3 = {
  sp_pre =[];
  sp_post = [(pos, [(mk_Pvar "res", eq (mk_Tvar "res") (plus (mk_Tvar "i") (mk_Tvar "i")))])]; (* 正しい？ *)
  sp_xpost = [];
  sp_reads = [];  
  sp_writes = [];
  sp_alias = [];
  sp_variant = [];
  sp_checkrw = false;
  sp_diverge = false;
  sp_partial = false
}
let example3 : expr = ~! (Efun ([mk_binder "n"], None, mk_Pvar "n", MaskVisible, spec3, 
  ~! (Epure (plus (mk_Tvar "n") (mk_Tvar "n")))))

(* ----- example 4 -----
    assume (n > 0); assert (n > 0) *)
let example4 : expr = ~! (Esequence (
  mk_assume (ge (mk_Tvar "n") (~@ (Tconst (int_const_of_int 0)))),
  mk_assert (ge (mk_Tvar "n") (~@ (Tconst (int_const_of_int 0))))))
