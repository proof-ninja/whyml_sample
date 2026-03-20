open Why3
open Ptree
open Ptree_helpers
open Tools

(* ----- example 1 ----- 
    assert (forall x, x == x) *)
(* 量化子をつける *)
let example1 : expr = mk_assert (term (Tquant (
  DTforall, 
  one_binder ~pty:int_type "x", 
  [], (* トリガー？ *)
  tapp eq [(mk_Tvar "x"); (mk_Tvar "x")])))


(* ----- example 2 ----- 
    let n <- true in 
    if n then assert (n == true)
    else assert (n == false) *)
let example2 = expr (Elet (ident "n", 
  false, (* goast ではない *)
  RKlocal, (* local 変数 *)
  expr Etrue, (*代入される値 *)
  expr (Eif (mk_Evar "n", 
    mk_assert (tapp eq [(mk_Tvar "n"); (term Ttrue)]),
    mk_assert (tapp eq [(mk_Tvar "n"); (term Tfalse)])))))


(* ----- example 3 ----- 
    foo = fun n => n + n について forall i, assert (foo i == i + i) *)
let spec3 = {
  sp_pre =[];
  sp_post = [(pos, [(mk_Pvar "res", tapp eq [(mk_Tvar "res"); (tapp plus [(mk_Tvar "n"); (mk_Tvar "n")])])])];
  sp_xpost = [];
  sp_reads = [];  
  sp_writes = [];
  sp_alias = [];
  sp_variant = [];
  sp_checkrw = false;
  sp_diverge = false;
  sp_partial = false
}
let example3 : expr = expr (Efun (
  one_binder ~pty:int_type "n", (* 引数 *)
  None, (* 関数の型 *)
  pat Pwild, (* 返り値パターン（タプルとかの場合もある） *)
  MaskVisible, (* 副作用？ *)
  spec3, (* 仕様 *)
  eapp plus [(mk_Evar "n"); (mk_Evar "n")]))

(* ----- example 4 -----
    assume (n > 0); assert (n > 0) *)
let spec4 = {
  sp_pre =[];
  sp_post = [];
  sp_xpost = [];
  sp_reads = [];  
  sp_writes = [];
  sp_alias = [];
  sp_variant = [];
  sp_checkrw = false;
  sp_diverge = false;
  sp_partial = false
}
let example4 : expr = expr (Efun (
  one_binder ~pty:int_type "n", (* 引数 *)
  None, (* 関数の型 *)
  pat Pwild, (* 返り値パターン（タプルとかの場合もある） *)
  MaskVisible, (* 副作用？ *)
  spec4, (* 仕様 *)
  expr (Esequence (mk_assume (tapp ge [(mk_Tvar "n"); (tconst 0)]),
  mk_assert (tapp ge [(mk_Tvar "n"); (tconst 0)])))))

(* ----- example 5 -----
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

let spec5 =  {
  sp_pre =[tapp ge [(mk_Tvar "n"); (tconst 1)]];
  sp_post = [(pos, [])]; (* TODO *)
  sp_xpost = [];
  sp_reads = [];  
  sp_writes = [];
  sp_alias = [];
  sp_variant = [];
  sp_checkrw = false;
  sp_diverge = false;
  sp_partial = false
}