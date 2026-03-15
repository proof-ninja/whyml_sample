open Why3
open Ptree

let pos = Why3.Loc.dummy_position

(* position としてダミーを挿入する単項演算子 *)
let (~!) e = {expr_desc = e; expr_loc = pos}
let (~@) e = {term_desc = e; term_loc = pos}

(* 変数の内部表現？ *)
let mk_ident str = {
  id_str = str;
  id_ats = [];
  id_loc = pos;
}
let mk_qualid str = Qident (mk_ident str) 

(* 変数項 *)
let mk_var str = ~@ (Tident (mk_qualid str))

(* 変数式 *)
let expr_x : expr = ~! (Eident (mk_qualid "x")) 

(* 等式項 *)
let eq s1 s2 = ~@ (Tidapp (mk_qualid "=", [mk_var s1; mk_var s2]))

(* assert x = x *)
let assert_x_x : expr = ~! (Eassert (Assert, eq "x" "x"))

(* 量化子をつける *)
let binder_x : binder = (pos, Some (mk_ident "x"), false, None)
let example1 : expr = ~! (Eassert (Assert, ~@ (Tquant (DTforall, [binder_x], [], eq "x" "x"))))