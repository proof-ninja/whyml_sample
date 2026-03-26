open Why3
open Ptree
open Ptree_helpers

let int_type = PTtyapp(qualid ["int"],[])

let pos = Why3.Loc.dummy_position

(* 変数 *)
let mk_Tvar str = tvar (qualid [str])
let mk_Evar str = evar (qualid [str])
let mk_Pvar str = pat_var (ident str)

(* 二項演算 *)
let eq = qualid [Ident.op_equ]
let plus = qualid ["Int";Ident.op_infix "+"] 
let ge = qualid ["Int";Ident.op_infix ">"] 
let md = qualid ["EuclideanDivision"; "mod"] 

let prop_and t1 t2 = term (Tbinop (t1, Dterm.DTand, t2))
let prop_implies t1 t2 = term (Tbinop (t1, Dterm.DTimplies, t2))

(* assert 文 *)
let mk_assert t = expr (Eassert (Assert, t))
(* assume 文 *)
let mk_assume t = expr (Eassert (Assume, t))