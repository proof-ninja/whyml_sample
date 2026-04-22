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

(* 以下の spec は関数項の中の仕様なしでは証明できない（関数が Parameter となるため） *)
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
      let loop = expr (Ewhile (expr Etrue, (* while true *)
        [ tapp gt [tapp bng [mk_Tvar "i"]; tconst 1]; (* {invariant1 : i>1} i で割るために必要．仕様の確認にも使うため 0 ではなく 1 にしている *)
          term (Tquant (DTforall, one_binder ~pty:int_type "k", [], (* {invariant2 : forall k, *)
            prop_implies (prop_and (tapp gt [mk_Tvar "k"; tconst 1]) (tapp gt [tapp bng [mk_Tvar "i"]; mk_Tvar "k"])) (* 1 < k < i -> *)
            (tapp gt [tapp md [mk_Tvar "n"; mk_Tvar "k"]; tconst 0]))); (* mod n k > 0} *)
          tapp gt [tapp md [tapp bng [mk_Tvar "i"]; tconst 2]; tconst 0] (* {invariant3 : mod i 2 > 0} *)
        ],
        [(tapp plus [tapp minus [mk_Tvar "m"; tapp bng [mk_Tvar "i"]]; tconst 2], None)], (* {variant : m-i+2} 0 以上であるようにする *)
        expr (Eif (eapp gt [eapp bng [mk_Evar "i"]; mk_Evar "m"], mk_return (expr Etrue), (* if i > m then return true *)
        expr (Eif (eapp eq_int [eapp md [mk_Evar "n"; eapp bng [mk_Evar "i"]]; econst 0], mk_return (expr Efalse), (* else if n%i = 0 then return false *)
        expr (Eassign [(mk_Evar "i", None, eapp plus [eapp bng [mk_Evar "i"]; econst 2])]))))))) in (* else i <- i + 2 *)
    expr (Elet (ident "m", false, RKnone, eapp minus [mk_Evar "n"; econst 1], (* let m = n-1 *)
    expr (Elet (ident "i", false, RKnone, eapply (expr Eref) (econst 3),  (* let i = ref 3; *)
    expr (Esequence (loop, (* loop; *)
    mk_return (expr Efalse))))))) in (* return false (ダミー) *)
  expr (Eoptexn (ident "Return", MaskVisible, (* return 文を使うために必要か *)
  expr (Eif ((eapp gt [econst 2; mk_Evar "n"]), mk_return (expr Efalse), (* if n<2 then false *)
  expr (Eif ((eapp eq_int [econst 2; mk_Evar "n"]), mk_return (expr Etrue), (* if n=2 then true *)
  expr (Eif ((eapp eq_int [eapp md [mk_Evar "n"; econst 2]; econst 0]), mk_return (expr Efalse), (* if n%2=0 then false *)
  body')))))))) (* else body' *)

let is_prime_spec bool n = 
  term (Tif (bool, (* if bool *)
    term (Tquant (DTforall, one_binder ~pty:int_type "m", [],  (* then forall m, *)
      prop_implies (prop_and
          (tapp gt [(mk_Tvar "m"); (tconst 1)]) (* m > 1 /\ *)
          (tapp gt [n; (mk_Tvar "m")])) (* n > m -> *)
        (tapp gt [tapp md [n; mk_Tvar "m"]; tconst 0]))), (* mod n m > 0 *)
    term (Tquant (DTexists, one_binder ~pty:int_type "m", [], (* else exists m, *)
      prop_and (prop_and
        (tapp gt [(mk_Tvar "m"); (tconst 1)]) (* m > 1 /\ *)
        (tapp gt [n; (mk_Tvar "m")])) (* n > m /\ *)
        (tapp eq [tapp md [n; mk_Tvar "m"]; tconst 0]))))) (* mod n m = 0 *)

let expr6 : expr = expr (Efun (
  one_binder ~pty:int_type "n", (* 引数 *)
  None, (* 関数の型 *)
  pat Pwild, (* 返り値パターン（タプルとかの場合もある） *)
  MaskVisible, (* 副作用？ *)
  {
    sp_pre = [tapp gt [(mk_Tvar "n"); (tconst 1)]];
    sp_post = [(pos, [(mk_Pvar "res", is_prime_spec (mk_Tvar "res") (mk_Tvar "n"))])];
    sp_xpost = [];
    sp_reads = [];  
    sp_writes = [];
    sp_alias = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
    sp_partial = false
  }, (* 仕様 *)
  body)) 
let example6_fun = Dlet (ident "is_prime", false, RKfunc, expr6)

(* 以下の spec は関数項の中の仕様なしでは証明できない（関数が Parameter となるため） *)
let post = is_prime_spec (tapp (qualid ["is_prime"]) [mk_Tvar "n"]) (mk_Tvar "n")

let spec6 : expr =  mk_assert (term (Tquant (
  DTforall, 
  one_binder ~pty:int_type "n", 
  [], (* トリガー？ *)
  prop_implies (tapp gt [(mk_Tvar "n"); (tconst 1)]) post)))
let example6_spec = Dlet (ident "spec", false, RKnone, spec6)
