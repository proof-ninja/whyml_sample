open Why3
open Ptree
open Ptree_helpers
let use_int_Int = use ~import:false (["int";"Int"])

let pos = Why3.Loc.dummy_position

(* 変数 *)
let mk_Tvar str = tvar (qualid [str])
let mk_Evar str = evar (qualid [str])
let mk_Pvar str = pat_var (ident str)

(* 二項演算 *)
let eq t1 t2 = tapp (qualid [Ident.op_equ]) [t1; t2]
let plus t1 t2 = 
  let plus_symbol = qualid ["Int";Ident.op_infix "+"] in 
  tapp plus_symbol [t1; t2]
let ge t1 t2 = 
  let plus_symbol = qualid ["Int";Ident.op_infix ">"] in 
  tapp plus_symbol [t1; t2]

(* assert 文 *)
let mk_assert t = expr (Eassert (Assert, t))
(* assume 文 *)
let mk_assume t = expr (Eassert (Assume, t))