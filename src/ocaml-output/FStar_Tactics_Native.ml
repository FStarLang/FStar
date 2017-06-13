open Prims
type itac =
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option
type native_primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  tactic: itac;}
let list_all uu____53 = []
let is_native_tactic t = false