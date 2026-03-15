open Why3.Ptree

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
let mk_Tvar str = ~@ (Tident (mk_qualid str))

(* 変数文？ *)
let mk_Evar str = ~! (Eident (mk_qualid str))

(* 等式項 *)
let eq t1 t2 = ~@ (Tidapp (mk_qualid "=", [t1; t2]))

(* assert 文 *)
let mk_assert t = ~! (Eassert (Assert, t))