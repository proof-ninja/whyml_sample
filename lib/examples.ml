open Why3
open Ptree
open Ptree_helpers
open Tools

(* ----- example 1 ----- 
    assert (forall x, x == x) *)
(* 量化子をつける *)
let expr1 : expr = mk_assert (term (Tquant (
  DTforall, 
  one_binder ~pty:int_type "x", 
  [], (* トリガー？ *)
  tapp eq [(mk_Tvar "x"); (mk_Tvar "x")])))
let example1 = Dlet (ident "foo", false, RKnone, expr1)


(* ----- example 2 ----- 
    let n <- true in 
    if n then assert (n == true)
    else assert (n == false) *)
let expr2 = expr (Elet (ident "n", 
  false, (* goast ではない *)
  RKnone, (* ? *)
  expr Etrue, (*代入される値 *)
  expr (Eif (mk_Evar "n", 
    mk_assert (tapp eq [(mk_Tvar "n"); (term Ttrue)]),
    mk_assert (tapp eq [(mk_Tvar "n"); (term Tfalse)])))))
let example2 = Dlet (ident "foo", false, RKnone, expr2)


(* ----- example 3 ----- 
    foo = fun n => n + n について forall i, assert (foo i == i + i) *)
let expr3 : expr = expr (Efun (
  one_binder ~pty:int_type "n", (* 引数 *)
  None, (* 関数の型 *)
  pat Pwild, (* 返り値パターン（タプルとかの場合もある） *)
  MaskVisible, (* 副作用？ *)
  empty_spec, (* 仕様 *)
  eapp plus [(mk_Evar "n"); (mk_Evar "n")]))
let example3_fun = Dlet (ident "foo", false, RKfunc, expr3)

let spec3 : expr =  mk_assert (term (Tquant (
  DTforall, 
  one_binder ~pty:int_type "n", 
  [], (* トリガー？ *)
  tapp eq [(tapp (qualid ["foo"]) [mk_Tvar "n"]); (tapp plus [mk_Tvar "n"; mk_Tvar "n"])])))  
let example3_spec = Dlet (ident "spec", false, RKnone, spec3)


(* ----- example 4 -----
    assume (n > 0); assert (n > 0) *)
let expr4 : expr = expr (Efun (
  one_binder ~pty:int_type "n", (* 引数 *)
  None, (* 関数の型 *)
  pat Pwild, (* 返り値パターン（タプルとかの場合もある） *)
  MaskVisible, (* 副作用？ *)
  empty_spec, (* 仕様 *)
  expr (Esequence (mk_assume (tapp gt [(mk_Tvar "n"); (tconst 0)]),
  mk_assert (tapp gt [(mk_Tvar "n"); (tconst 0)])))))
let example4 = Dlet (ident "foo", false, RKnone, expr4)


(* ----- example 5 -----
    fn loop () {
      let mut i: u64 = 1;
      while i > 0 {
        i = i-1;
      }
      return i
    } 
*)

let body = 
  let loop = 
    expr (Ewhile ((eapp gt [eapp bng [mk_Evar "i"]; econst 0]), (* while i>0 *)
      [tapp ge [tapp bng [mk_Tvar "i"]; tconst 0]], (* {invariant : i >= 0} 仕様の証明に必要 *)
      [(tapp bng [mk_Tvar "i"], None)], (* {variant : i} *)
    expr (Eassign [(mk_Evar "i", None, eapp minus [eapp bng [mk_Evar "i"]; econst 1])]))) in (* i <- i-1 *)
  expr (Elet (ident "i", false, RKnone, eapply (expr Eref) (econst 1),  (* let i = ref 1; *)
  expr (Esequence (loop, eapp bng [mk_Evar "i"])))) (* loop; return i *)

let expr5 : expr = expr (Efun (
  unit_binder (), (* 引数 *)
  None, (* 関数の型 *)
  pat Pwild, (* 返り値パターン *)
  MaskVisible, (* 副作用？ *)
  {
    sp_pre =[];
    sp_post = [(pos, [(mk_Pvar "res", tapp eq [(mk_Tvar "res"); tconst 0])])];
    sp_xpost = [];
    sp_reads = [];  
    sp_writes = [];
    sp_alias = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
    sp_partial = false
  }
  (* empty_spec *)
  , (* 仕様 *)
  body)) 
let example5_fun = Dlet (ident "loop", false, RKfunc, expr5)

let spec5 = mk_assert (tapp eq_int [(tapp (qualid ["loop"]) [term (Ttuple [])]); tconst 0]) (* loop() = 0 *)
let example5_spec = Dlet (ident "spec", false, RKnone, spec5)
(* let example5_spec = Dprop (Pgoal, ident "spec", tapp eq_int [(tapp (qualid ["loop"]) []); tconst 0]) *)

(* ----- example 6 -----
    fn is_prime(n: u64) -> bool {
      if n < 2 { return false; }
      if n == 2 { return true; }
      if n % 2 == 0 { return false; }

      let m: u64 = n - 1;
      let mut i: u64 = 3;

      loop {
        if i > m { return true; }
        if n % i == 0 { return false; }
        i = i + 2;
      }
    }

    fn prime_spec() forall {
      let n: u64 = @;

      assume { assert(n > 1); }

      if is_prime(n) {
        let m: u64 = @;
        assume { assert(m > 1 && m < n); }
        assert(n % m > 0);
      }

      else exists {
        let m: u64 = @;
        assert(m > 1 && m < n);
        assert(n % m == 0);
      }
    } *)

let body = 
    let body' = 
      let loop = expr (Ewhile (expr Etrue, [], [(tapp minus [mk_Tvar "m"; tapp bng [mk_Tvar "i"]], None)], (* while true *)
        expr (Eif (eapp gt [eapp bng [mk_Evar "i"]; mk_Evar "m"], eapp asgn [mk_Evar "res"; expr Etrue], (* if i > m then res := true *)
        expr (Eif (eapp eq_int [eapp md [mk_Evar "n"; eapp bng [mk_Evar "i"]]; econst 0], eapp asgn [mk_Evar "res"; expr Efalse], (* else if n%i = 0 then res := false *)
        expr (Eassign [(mk_Evar "i", None, eapp plus [eapp bng [mk_Evar "i"]; econst 2])]))))))) in (* else i <- i + 2 *)
    expr (Elet (ident "m", false, RKnone, eapp minus [mk_Evar "n"; econst 1], (* let m = n-1 *)
    expr (Elet (ident "i", false, RKnone, eapply (expr Eref) (econst 3),  (* let i = ref 3; *)
    expr (Elet (ident "res", false, RKnone, eapply (expr Eref) (expr Etrue),  (* let res = ref true (ダミー); *)
    expr (Esequence (loop, eapp bng [mk_Evar "res"])))))))) in (* loop; !res *)
  expr (Eif ((eapp gt [econst 2; mk_Evar "n"]), expr Efalse, (* if n<2 then false *)
  expr (Eif ((eapp eq_int [econst 2; mk_Evar "n"]), expr Etrue, (* if n=2 then true *)
  expr (Eif ((eapp eq_int [eapp md [mk_Evar "n"; econst 2]; econst 0]), expr Efalse, body')))))) (* if n%2=0 then false else body' *)

let expr6 : expr = expr (Efun (
  one_binder ~pty:int_type "n", (* 引数 *)
  None, (* 関数の型 *)
  pat Pwild, (* 返り値パターン（タプルとかの場合もある） *)
  MaskVisible, (* 副作用？ *)
  empty_spec, (* 仕様 *)
  body)) 
let example6_fun = Dlet (ident "is_prime", false, RKfunc, expr6)

let post = term (Tif ((tapp (qualid ["is_prime"]) [mk_Tvar "n"]), (* if is_prime n *)
  term (Tquant (DTforall, one_binder ~pty:int_type "m", [],  (* then forall m, *)
    prop_implies (prop_and
        (tapp gt [(mk_Tvar "m"); (tconst 1)]) (* m > 1 /\ *)
        (tapp gt [(mk_Tvar "n"); (mk_Tvar "m")])) (* n > m -> *)
      (tapp gt [tapp md [mk_Tvar "n"; mk_Tvar "m"]; tconst 0]))), (* mod n m > 0 *)
  term (Tquant (DTexists, one_binder ~pty:int_type "m", [], (* else exists m, *)
    prop_and (prop_and
      (tapp gt [(mk_Tvar "m"); (tconst 1)]) (* m > 1 /\ *)
      (tapp gt [(mk_Tvar "n"); (mk_Tvar "m")])) (* n > m /\ *)
      (tapp eq [tapp md [mk_Tvar "n"; mk_Tvar "m"]; tconst 0]))))) (* mod n m = 0 *)

let spec6 : expr =  mk_assert (term (Tquant (
  DTforall, 
  one_binder ~pty:int_type "n", 
  [], (* トリガー？ *)
  prop_implies (tapp gt [(mk_Tvar "n"); (tconst 1)]) post)))
let example6_spec = Dlet (ident "spec", false, RKnone, spec6)
