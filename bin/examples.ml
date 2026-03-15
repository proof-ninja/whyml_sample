open Why3.Ptree
open Why3.Ity
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
let myspec = {
    sp_pre =[];
  	sp_post = [(pos, [(mk_Pvar "i", plus (mk_Tvar "i") (mk_Tvar "i"))])];
  	sp_xpost = [];
  	sp_reads = [];  	
    sp_writes = [];
  	sp_alias = [];
  	sp_variant = [];
  	sp_checkrw = false;
  	sp_diverge = false;
  	sp_partial = false
}
let example3 : expr = ~! (Efun ([mk_binder "n"], None, mk_Pvar "n", MaskVisible, myspec, ~! (Epure (plus (mk_Tvar "n") (mk_Tvar "n")))))
