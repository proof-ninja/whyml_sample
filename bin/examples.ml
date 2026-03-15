open Why3.Ptree
open Infv.Tools

(* ----- example 1 ----- 
    assert (forall x, x == x) *)
(* 量化子をつける *)
let binder_x : binder = (pos, Some (mk_ident "x"), false, None)
let example1 : expr = mk_assert (~@ (Tquant (DTforall, [binder_x], [], eq (mk_Tvar "x") (mk_Tvar "x"))))


(* ----- example 2 ----- 
    let n <- true in 
    if n then assert (n == true)
    else assert (n == false) *)

let example2 = Elet (mk_ident "n", false, RKlocal, ~! Etrue, 
    ~! (Eif (mk_Evar "n", 
      ~! (Eassert (Assert, (eq (mk_Tvar "n") (~@ Ttrue)))),
      ~! (Eassert (Assert, (eq (mk_Tvar "n") (~@ Tfalse)))))))


(* ----- example 3 ----- *)

