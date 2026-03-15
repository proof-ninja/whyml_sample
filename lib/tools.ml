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

(* 変数パターン *)
let mk_pattern str = {
  pat_desc = str;
  pat_loc = pos
}

(* 変数 *)
let mk_Tvar str = ~@ (Tident (mk_qualid str))
let mk_Evar str = ~! (Epure (mk_Tvar str))
let mk_Pvar str = mk_pattern (Pvar (mk_ident str))

(* 二項演算 *)
let eq t1 t2 = ~@ (Tidapp (mk_qualid "=", [t1; t2]))
let plus t1 t2 = ~@ (Tidapp (mk_qualid "+", [t1; t2]))
let ge t1 t2 = ~@ (Tidapp (mk_qualid ">", [t1; t2]))

(* assert 文 *)
let mk_assert t = ~! (Eassert (Assert, t))
(* assume 文 *)
let mk_assume t = ~! (Eassert (Assume, t))