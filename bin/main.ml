open Why3
open Ptree

let pos = Why3.Loc.dummy_position

(* position としてダミーを挿入する単項演算子 *)
let (~!) e = {expr_desc = e; expr_loc = pos}
let (~@) e = {term_desc = e; term_loc = pos}

(* 変数の内部表現？ *)
let mk_qualid str = Qident {
  id_str = str;
  id_ats = [];
  id_loc = pos;
}

(* 変数項 *)
let mk_var str =
{
  term_desc = Tident (mk_qualid str);
  term_loc  = pos;
}

(* 等式項 *)
let eq s1 s2 =
{
  term_desc = Tidapp (mk_qualid "=", [mk_var s1; mk_var s2]);
  term_loc  = pos;
}

(* 変数式 *)
let expr_x : expr = ~! (Eident (mk_qualid "x")) 

(* assert x = x *)
let assert_x_x: expr = ~! (Eassert (Assert, eq "x" "x"))

(* 量化子をつける *)
(* let example1 = ~! (Eassert (Assert, ~@ (Tquant (Forall, [x_binder], [], eq_term)))) *)