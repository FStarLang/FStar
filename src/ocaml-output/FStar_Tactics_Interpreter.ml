
open Prims
open FStar_Pervasives

let tacdbg : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let mk_tactic_interpretation_0 : 'r . Prims.bool  ->  'r FStar_Tactics_Basic.tac  ->  'r FStar_Syntax_Embeddings.embedding  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t er nm psc args -> (match (args) with
| ((embedded_state, uu____94))::[] -> begin
(

let uu____111 = (FStar_Syntax_Embeddings.unembed FStar_Tactics_Embedding.e_proofstate embedded_state)
in (FStar_Util.bind_opt uu____111 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____124 -> (

let uu____125 = (FStar_Ident.string_of_lid nm)
in (

let uu____126 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "Reached %s, args are: %s\n" uu____125 uu____126)))));
(

let res = (

let uu____128 = (FStar_Tactics_Embedding.e_result er)
in (

let uu____133 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____134 = (FStar_Tactics_Basic.run t ps1)
in (FStar_Syntax_Embeddings.embed uu____128 uu____133 uu____134))))
in FStar_Pervasives_Native.Some (res));
)))))
end
| uu____139 -> begin
(failwith "Unexpected application of tactic primitive")
end))


let mk_tactic_interpretation_1 : 'a 'r . Prims.bool  ->  ('a  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.embedding  ->  'r FStar_Syntax_Embeddings.embedding  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t ea er nm psc args -> (match (args) with
| ((a, uu____217))::((embedded_state, uu____219))::[] -> begin
(

let uu____246 = (FStar_Syntax_Embeddings.unembed FStar_Tactics_Embedding.e_proofstate embedded_state)
in (FStar_Util.bind_opt uu____246 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____259 -> (

let uu____260 = (FStar_Ident.string_of_lid nm)
in (

let uu____261 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____260 uu____261)))));
(

let uu____262 = (FStar_Syntax_Embeddings.unembed ea a)
in (FStar_Util.bind_opt uu____262 (fun a1 -> (

let res = (

let uu____272 = (t a1)
in (FStar_Tactics_Basic.run uu____272 ps1))
in (

let uu____275 = (

let uu____276 = (FStar_Tactics_Embedding.e_result er)
in (

let uu____281 = (FStar_TypeChecker_Normalize.psc_range psc)
in (FStar_Syntax_Embeddings.embed uu____276 uu____281 res)))
in FStar_Pervasives_Native.Some (uu____275))))));
)))))
end
| uu____284 -> begin
(

let uu____285 = (

let uu____286 = (FStar_Ident.string_of_lid nm)
in (

let uu____287 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____286 uu____287)))
in (failwith uu____285))
end))


let mk_tactic_interpretation_1_env : 'a 'r . Prims.bool  ->  (FStar_TypeChecker_Normalize.psc  ->  'a  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.embedding  ->  'r FStar_Syntax_Embeddings.embedding  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t ea er nm psc args -> (match (args) with
| ((a, uu____370))::((embedded_state, uu____372))::[] -> begin
(

let uu____399 = (FStar_Syntax_Embeddings.unembed FStar_Tactics_Embedding.e_proofstate embedded_state)
in (FStar_Util.bind_opt uu____399 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____412 -> (

let uu____413 = (FStar_Ident.string_of_lid nm)
in (

let uu____414 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____413 uu____414)))));
(

let uu____415 = (FStar_Syntax_Embeddings.unembed ea a)
in (FStar_Util.bind_opt uu____415 (fun a1 -> (

let res = (

let uu____425 = (t psc a1)
in (FStar_Tactics_Basic.run uu____425 ps1))
in (

let uu____428 = (

let uu____429 = (FStar_Tactics_Embedding.e_result er)
in (

let uu____434 = (FStar_TypeChecker_Normalize.psc_range psc)
in (FStar_Syntax_Embeddings.embed uu____429 uu____434 res)))
in FStar_Pervasives_Native.Some (uu____428))))));
)))))
end
| uu____437 -> begin
(

let uu____438 = (

let uu____439 = (FStar_Ident.string_of_lid nm)
in (

let uu____440 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____439 uu____440)))
in (failwith uu____438))
end))


let mk_tactic_interpretation_2 : 'a 'b 'r . Prims.bool  ->  ('a  ->  'b  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.embedding  ->  'b FStar_Syntax_Embeddings.embedding  ->  'r FStar_Syntax_Embeddings.embedding  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t ea eb er nm psc args -> (match (args) with
| ((a, uu____537))::((b, uu____539))::((embedded_state, uu____541))::[] -> begin
(

let uu____578 = (FStar_Syntax_Embeddings.unembed FStar_Tactics_Embedding.e_proofstate embedded_state)
in (FStar_Util.bind_opt uu____578 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____591 -> (

let uu____592 = (FStar_Ident.string_of_lid nm)
in (

let uu____593 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____592 uu____593)))));
(

let uu____594 = (FStar_Syntax_Embeddings.unembed ea a)
in (FStar_Util.bind_opt uu____594 (fun a1 -> (

let uu____600 = (FStar_Syntax_Embeddings.unembed eb b)
in (FStar_Util.bind_opt uu____600 (fun b1 -> (

let res = (

let uu____610 = (t a1 b1)
in (FStar_Tactics_Basic.run uu____610 ps1))
in (

let uu____613 = (

let uu____614 = (FStar_Tactics_Embedding.e_result er)
in (

let uu____619 = (FStar_TypeChecker_Normalize.psc_range psc)
in (FStar_Syntax_Embeddings.embed uu____614 uu____619 res)))
in FStar_Pervasives_Native.Some (uu____613)))))))));
)))))
end
| uu____622 -> begin
(

let uu____623 = (

let uu____624 = (FStar_Ident.string_of_lid nm)
in (

let uu____625 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____624 uu____625)))
in (failwith uu____623))
end))


let mk_tactic_interpretation_3 : 'a 'b 'c 'r . Prims.bool  ->  ('a  ->  'b  ->  'c  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.embedding  ->  'b FStar_Syntax_Embeddings.embedding  ->  'c FStar_Syntax_Embeddings.embedding  ->  'r FStar_Syntax_Embeddings.embedding  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t ea eb ec er nm psc args -> (match (args) with
| ((a, uu____741))::((b, uu____743))::((c, uu____745))::((embedded_state, uu____747))::[] -> begin
(

let uu____794 = (FStar_Syntax_Embeddings.unembed FStar_Tactics_Embedding.e_proofstate embedded_state)
in (FStar_Util.bind_opt uu____794 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____807 -> (

let uu____808 = (FStar_Ident.string_of_lid nm)
in (

let uu____809 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____808 uu____809)))));
(

let uu____810 = (FStar_Syntax_Embeddings.unembed ea a)
in (FStar_Util.bind_opt uu____810 (fun a1 -> (

let uu____816 = (FStar_Syntax_Embeddings.unembed eb b)
in (FStar_Util.bind_opt uu____816 (fun b1 -> (

let uu____822 = (FStar_Syntax_Embeddings.unembed ec c)
in (FStar_Util.bind_opt uu____822 (fun c1 -> (

let res = (

let uu____832 = (t a1 b1 c1)
in (FStar_Tactics_Basic.run uu____832 ps1))
in (

let uu____835 = (

let uu____836 = (FStar_Tactics_Embedding.e_result er)
in (

let uu____841 = (FStar_TypeChecker_Normalize.psc_range psc)
in (FStar_Syntax_Embeddings.embed uu____836 uu____841 res)))
in FStar_Pervasives_Native.Some (uu____835))))))))))));
)))))
end
| uu____844 -> begin
(

let uu____845 = (

let uu____846 = (FStar_Ident.string_of_lid nm)
in (

let uu____847 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____846 uu____847)))
in (failwith uu____845))
end))


let mk_tactic_interpretation_4 : 'a 'b 'c 'd 'r . Prims.bool  ->  ('a  ->  'b  ->  'c  ->  'd  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.embedding  ->  'b FStar_Syntax_Embeddings.embedding  ->  'c FStar_Syntax_Embeddings.embedding  ->  'd FStar_Syntax_Embeddings.embedding  ->  'r FStar_Syntax_Embeddings.embedding  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t ea eb ec ed er nm psc args -> (match (args) with
| ((a, uu____982))::((b, uu____984))::((c, uu____986))::((d, uu____988))::((embedded_state, uu____990))::[] -> begin
(

let uu____1047 = (FStar_Syntax_Embeddings.unembed FStar_Tactics_Embedding.e_proofstate embedded_state)
in (FStar_Util.bind_opt uu____1047 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____1060 -> (

let uu____1061 = (FStar_Ident.string_of_lid nm)
in (

let uu____1062 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____1061 uu____1062)))));
(

let uu____1063 = (FStar_Syntax_Embeddings.unembed ea a)
in (FStar_Util.bind_opt uu____1063 (fun a1 -> (

let uu____1069 = (FStar_Syntax_Embeddings.unembed eb b)
in (FStar_Util.bind_opt uu____1069 (fun b1 -> (

let uu____1075 = (FStar_Syntax_Embeddings.unembed ec c)
in (FStar_Util.bind_opt uu____1075 (fun c1 -> (

let uu____1081 = (FStar_Syntax_Embeddings.unembed ed d)
in (FStar_Util.bind_opt uu____1081 (fun d1 -> (

let res = (

let uu____1091 = (t a1 b1 c1 d1)
in (FStar_Tactics_Basic.run uu____1091 ps1))
in (

let uu____1094 = (

let uu____1095 = (FStar_Tactics_Embedding.e_result er)
in (

let uu____1100 = (FStar_TypeChecker_Normalize.psc_range psc)
in (FStar_Syntax_Embeddings.embed uu____1095 uu____1100 res)))
in FStar_Pervasives_Native.Some (uu____1094)))))))))))))));
)))))
end
| uu____1103 -> begin
(

let uu____1104 = (

let uu____1105 = (FStar_Ident.string_of_lid nm)
in (

let uu____1106 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____1105 uu____1106)))
in (failwith uu____1104))
end))


let mk_tactic_interpretation_5 : 'a 'b 'c 'd 'e 'r . Prims.bool  ->  ('a  ->  'b  ->  'c  ->  'd  ->  'e  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.embedding  ->  'b FStar_Syntax_Embeddings.embedding  ->  'c FStar_Syntax_Embeddings.embedding  ->  'd FStar_Syntax_Embeddings.embedding  ->  'e FStar_Syntax_Embeddings.embedding  ->  'r FStar_Syntax_Embeddings.embedding  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t ea eb ec ed ee er nm psc args -> (match (args) with
| ((a, uu____1260))::((b, uu____1262))::((c, uu____1264))::((d, uu____1266))::((e, uu____1268))::((embedded_state, uu____1270))::[] -> begin
(

let uu____1337 = (FStar_Syntax_Embeddings.unembed FStar_Tactics_Embedding.e_proofstate embedded_state)
in (FStar_Util.bind_opt uu____1337 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____1350 -> (

let uu____1351 = (FStar_Ident.string_of_lid nm)
in (

let uu____1352 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____1351 uu____1352)))));
(

let uu____1353 = (FStar_Syntax_Embeddings.unembed ea a)
in (FStar_Util.bind_opt uu____1353 (fun a1 -> (

let uu____1359 = (FStar_Syntax_Embeddings.unembed eb b)
in (FStar_Util.bind_opt uu____1359 (fun b1 -> (

let uu____1365 = (FStar_Syntax_Embeddings.unembed ec c)
in (FStar_Util.bind_opt uu____1365 (fun c1 -> (

let uu____1371 = (FStar_Syntax_Embeddings.unembed ed d)
in (FStar_Util.bind_opt uu____1371 (fun d1 -> (

let uu____1377 = (FStar_Syntax_Embeddings.unembed ee e)
in (FStar_Util.bind_opt uu____1377 (fun e1 -> (

let res = (

let uu____1387 = (t a1 b1 c1 d1 e1)
in (FStar_Tactics_Basic.run uu____1387 ps1))
in (

let uu____1390 = (

let uu____1391 = (FStar_Tactics_Embedding.e_result er)
in (

let uu____1396 = (FStar_TypeChecker_Normalize.psc_range psc)
in (FStar_Syntax_Embeddings.embed uu____1391 uu____1396 res)))
in FStar_Pervasives_Native.Some (uu____1390))))))))))))))))));
)))))
end
| uu____1399 -> begin
(

let uu____1400 = (

let uu____1401 = (FStar_Ident.string_of_lid nm)
in (

let uu____1402 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____1401 uu____1402)))
in (failwith uu____1400))
end))


let mk_tactic_interpretation_6 : 'a 'b 'c 'd 'e 'f 'r . Prims.bool  ->  ('a  ->  'b  ->  'c  ->  'd  ->  'e  ->  'f  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.embedding  ->  'b FStar_Syntax_Embeddings.embedding  ->  'c FStar_Syntax_Embeddings.embedding  ->  'd FStar_Syntax_Embeddings.embedding  ->  'e FStar_Syntax_Embeddings.embedding  ->  'f FStar_Syntax_Embeddings.embedding  ->  'r FStar_Syntax_Embeddings.embedding  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t ea eb ec ed ee ef er nm psc args -> (match (args) with
| ((a, uu____1575))::((b, uu____1577))::((c, uu____1579))::((d, uu____1581))::((e, uu____1583))::((f, uu____1585))::((embedded_state, uu____1587))::[] -> begin
(

let uu____1664 = (FStar_Syntax_Embeddings.unembed FStar_Tactics_Embedding.e_proofstate embedded_state)
in (FStar_Util.bind_opt uu____1664 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____1677 -> (

let uu____1678 = (FStar_Ident.string_of_lid nm)
in (

let uu____1679 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____1678 uu____1679)))));
(

let uu____1680 = (FStar_Syntax_Embeddings.unembed ea a)
in (FStar_Util.bind_opt uu____1680 (fun a1 -> (

let uu____1686 = (FStar_Syntax_Embeddings.unembed eb b)
in (FStar_Util.bind_opt uu____1686 (fun b1 -> (

let uu____1692 = (FStar_Syntax_Embeddings.unembed ec c)
in (FStar_Util.bind_opt uu____1692 (fun c1 -> (

let uu____1698 = (FStar_Syntax_Embeddings.unembed ed d)
in (FStar_Util.bind_opt uu____1698 (fun d1 -> (

let uu____1704 = (FStar_Syntax_Embeddings.unembed ee e)
in (FStar_Util.bind_opt uu____1704 (fun e1 -> (

let uu____1710 = (FStar_Syntax_Embeddings.unembed ef f)
in (FStar_Util.bind_opt uu____1710 (fun f1 -> (

let res = (

let uu____1720 = (t a1 b1 c1 d1 e1 f1)
in (FStar_Tactics_Basic.run uu____1720 ps1))
in (

let uu____1723 = (

let uu____1724 = (FStar_Tactics_Embedding.e_result er)
in (

let uu____1729 = (FStar_TypeChecker_Normalize.psc_range psc)
in (FStar_Syntax_Embeddings.embed uu____1724 uu____1729 res)))
in FStar_Pervasives_Native.Some (uu____1723)))))))))))))))))))));
)))))
end
| uu____1732 -> begin
(

let uu____1733 = (

let uu____1734 = (FStar_Ident.string_of_lid nm)
in (

let uu____1735 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____1734 uu____1735)))
in (failwith uu____1733))
end))


let step_from_native_step : FStar_Tactics_Native.native_primitive_step  ->  FStar_TypeChecker_Normalize.primitive_step = (fun s -> {FStar_TypeChecker_Normalize.name = s.FStar_Tactics_Native.name; FStar_TypeChecker_Normalize.arity = s.FStar_Tactics_Native.arity; FStar_TypeChecker_Normalize.auto_reflect = FStar_Pervasives_Native.Some ((s.FStar_Tactics_Native.arity - (Prims.parse_int "1"))); FStar_TypeChecker_Normalize.strong_reduction_ok = s.FStar_Tactics_Native.strong_reduction_ok; FStar_TypeChecker_Normalize.requires_binder_substitution = false; FStar_TypeChecker_Normalize.interpretation = (fun psc args -> (s.FStar_Tactics_Native.tactic psc args))})


let rec e_tactic_0' : 'r . 'r FStar_Syntax_Embeddings.embedding  ->  'r FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding = (fun er -> (FStar_Syntax_Embeddings.mk_emb (fun uu____1879 uu____1880 -> (failwith "Impossible: embedding tactic (0)?")) (fun w t -> (

let uu____1888 = (unembed_tactic_0 er t)
in (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) uu____1888))) FStar_Syntax_Syntax.t_unit))
and e_tactic_1 : 'a 'r . 'a FStar_Syntax_Embeddings.embedding  ->  'r FStar_Syntax_Embeddings.embedding  ->  ('a  ->  'r FStar_Tactics_Basic.tac) FStar_Syntax_Embeddings.embedding = (fun ea er -> (FStar_Syntax_Embeddings.mk_emb (fun uu____1912 uu____1913 -> (failwith "Impossible: embedding tactic (1)?")) (fun w t -> (unembed_tactic_1 ea er t)) FStar_Syntax_Syntax.t_unit))
and primitive_steps : unit  ->  FStar_TypeChecker_Normalize.primitive_step Prims.list = (fun uu____1922 -> (

let mk1 = (fun nm arity interpretation -> (

let nm1 = (FStar_Tactics_Embedding.fstar_tactics_lid' (("Builtins")::(nm)::[]))
in {FStar_TypeChecker_Normalize.name = nm1; FStar_TypeChecker_Normalize.arity = arity; FStar_TypeChecker_Normalize.auto_reflect = FStar_Pervasives_Native.Some ((arity - (Prims.parse_int "1"))); FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.requires_binder_substitution = true; FStar_TypeChecker_Normalize.interpretation = (fun psc args -> (interpretation nm1 psc args))}))
in (

let native_tactics = (FStar_Tactics_Native.list_all ())
in (

let native_tactics_steps = (FStar_List.map step_from_native_step native_tactics)
in (

let mktac1 = (fun name f ea er -> (mk1 name (Prims.parse_int "2") (mk_tactic_interpretation_1 false f ea er)))
in (

let mktac2 = (fun name f ea eb er -> (mk1 name (Prims.parse_int "3") (mk_tactic_interpretation_2 false f ea eb er)))
in (

let mktac3 = (fun name f ea eb ec er -> (mk1 name (Prims.parse_int "4") (mk_tactic_interpretation_3 false f ea eb ec er)))
in (

let mktac5 = (fun name f ea eb ec ed ee er -> (mk1 name (Prims.parse_int "6") (mk_tactic_interpretation_5 false f ea eb ec ed ee er)))
in (

let decr_depth_interp = (fun psc args -> (match (args) with
| ((ps, uu____2328))::[] -> begin
(

let uu____2345 = (FStar_Syntax_Embeddings.unembed FStar_Tactics_Embedding.e_proofstate ps)
in (FStar_Util.bind_opt uu____2345 (fun ps1 -> (

let ps2 = (FStar_Tactics_Types.set_ps_psc psc ps1)
in (

let uu____2353 = (

let uu____2354 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____2355 = (FStar_Tactics_Types.decr_depth ps2)
in (FStar_Syntax_Embeddings.embed FStar_Tactics_Embedding.e_proofstate uu____2354 uu____2355)))
in FStar_Pervasives_Native.Some (uu____2353))))))
end
| uu____2356 -> begin
(failwith "Unexpected application of decr_depth")
end))
in (

let decr_depth_step = (

let uu____2360 = (FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth")
in {FStar_TypeChecker_Normalize.name = uu____2360; FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1"); FStar_TypeChecker_Normalize.auto_reflect = FStar_Pervasives_Native.None; FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.requires_binder_substitution = false; FStar_TypeChecker_Normalize.interpretation = decr_depth_interp})
in (

let incr_depth_interp = (fun psc args -> (match (args) with
| ((ps, uu____2377))::[] -> begin
(

let uu____2394 = (FStar_Syntax_Embeddings.unembed FStar_Tactics_Embedding.e_proofstate ps)
in (FStar_Util.bind_opt uu____2394 (fun ps1 -> (

let ps2 = (FStar_Tactics_Types.set_ps_psc psc ps1)
in (

let uu____2402 = (

let uu____2403 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____2404 = (FStar_Tactics_Types.incr_depth ps2)
in (FStar_Syntax_Embeddings.embed FStar_Tactics_Embedding.e_proofstate uu____2403 uu____2404)))
in FStar_Pervasives_Native.Some (uu____2402))))))
end
| uu____2405 -> begin
(failwith "Unexpected application of incr_depth")
end))
in (

let incr_depth_step = (

let uu____2409 = (FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth")
in {FStar_TypeChecker_Normalize.name = uu____2409; FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1"); FStar_TypeChecker_Normalize.auto_reflect = FStar_Pervasives_Native.None; FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.requires_binder_substitution = false; FStar_TypeChecker_Normalize.interpretation = incr_depth_interp})
in (

let tracepoint_interp = (fun psc args -> (match (args) with
| ((ps, uu____2430))::[] -> begin
(

let uu____2447 = (FStar_Syntax_Embeddings.unembed FStar_Tactics_Embedding.e_proofstate ps)
in (FStar_Util.bind_opt uu____2447 (fun ps1 -> (

let ps2 = (FStar_Tactics_Types.set_ps_psc psc ps1)
in ((FStar_Tactics_Types.tracepoint ps2);
FStar_Pervasives_Native.Some (FStar_Syntax_Util.exp_unit);
)))))
end
| uu____2460 -> begin
(failwith "Unexpected application of tracepoint")
end))
in (

let set_proofstate_range_interp = (fun psc args -> (match (args) with
| ((ps, uu____2481))::((r, uu____2483))::[] -> begin
(

let uu____2510 = (FStar_Syntax_Embeddings.unembed FStar_Tactics_Embedding.e_proofstate ps)
in (FStar_Util.bind_opt uu____2510 (fun ps1 -> (

let uu____2516 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_range r)
in (FStar_Util.bind_opt uu____2516 (fun r1 -> (

let ps' = (FStar_Tactics_Types.set_proofstate_range ps1 r1)
in (

let uu____2524 = (

let uu____2525 = (FStar_TypeChecker_Normalize.psc_range psc)
in (FStar_Syntax_Embeddings.embed FStar_Tactics_Embedding.e_proofstate uu____2525 ps'))
in FStar_Pervasives_Native.Some (uu____2524)))))))))
end
| uu____2526 -> begin
(failwith "Unexpected application of set_proofstate_range")
end))
in (

let push_binder_interp = (fun psc args -> (match (args) with
| ((env_t, uu____2545))::((b, uu____2547))::[] -> begin
(

let uu____2574 = (FStar_Syntax_Embeddings.unembed FStar_Reflection_Embeddings.e_env env_t)
in (FStar_Util.bind_opt uu____2574 (fun env -> (

let uu____2580 = (FStar_Syntax_Embeddings.unembed FStar_Reflection_Embeddings.e_binder b)
in (FStar_Util.bind_opt uu____2580 (fun b1 -> (

let env1 = (FStar_TypeChecker_Env.push_binders env ((b1)::[]))
in (

let uu____2588 = (FStar_Syntax_Embeddings.embed FStar_Reflection_Embeddings.e_env env_t.FStar_Syntax_Syntax.pos env1)
in FStar_Pervasives_Native.Some (uu____2588)))))))))
end
| uu____2589 -> begin
(failwith "Unexpected application of push_binder")
end))
in (

let set_proofstate_range_step = (

let nm = (FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range")
in {FStar_TypeChecker_Normalize.name = nm; FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2"); FStar_TypeChecker_Normalize.auto_reflect = FStar_Pervasives_Native.None; FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.requires_binder_substitution = false; FStar_TypeChecker_Normalize.interpretation = set_proofstate_range_interp})
in (

let tracepoint_step = (

let nm = (FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint")
in {FStar_TypeChecker_Normalize.name = nm; FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1"); FStar_TypeChecker_Normalize.auto_reflect = FStar_Pervasives_Native.None; FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.requires_binder_substitution = true; FStar_TypeChecker_Normalize.interpretation = tracepoint_interp})
in (

let push_binder_step = (

let nm = (FStar_Tactics_Embedding.fstar_tactics_lid' (("Builtins")::("push_binder")::[]))
in {FStar_TypeChecker_Normalize.name = nm; FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2"); FStar_TypeChecker_Normalize.auto_reflect = FStar_Pervasives_Native.None; FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.requires_binder_substitution = true; FStar_TypeChecker_Normalize.interpretation = push_binder_interp})
in (

let uu____2598 = (

let uu____2601 = (mktac2 "fail" (fun uu____2603 -> FStar_Tactics_Basic.fail) FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_any)
in (

let uu____2604 = (

let uu____2607 = (mktac1 "trivial" FStar_Tactics_Basic.trivial FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit)
in (

let uu____2608 = (

let uu____2611 = (

let uu____2612 = (e_tactic_0' FStar_Syntax_Embeddings.e_any)
in (

let uu____2617 = (FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_any)
in (mktac2 "__trytac" (fun uu____2627 -> FStar_Tactics_Basic.trytac) FStar_Syntax_Embeddings.e_any uu____2612 uu____2617)))
in (

let uu____2628 = (

let uu____2631 = (mktac1 "intro" FStar_Tactics_Basic.intro FStar_Syntax_Embeddings.e_unit FStar_Reflection_Embeddings.e_binder)
in (

let uu____2632 = (

let uu____2635 = (

let uu____2636 = (FStar_Syntax_Embeddings.e_tuple2 FStar_Reflection_Embeddings.e_binder FStar_Reflection_Embeddings.e_binder)
in (mktac1 "intro_rec" FStar_Tactics_Basic.intro_rec FStar_Syntax_Embeddings.e_unit uu____2636))
in (

let uu____2647 = (

let uu____2650 = (

let uu____2651 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_norm_step)
in (mktac1 "norm" FStar_Tactics_Basic.norm uu____2651 FStar_Syntax_Embeddings.e_unit))
in (

let uu____2658 = (

let uu____2661 = (

let uu____2662 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_norm_step)
in (mktac3 "norm_term_env" FStar_Tactics_Basic.norm_term_env FStar_Reflection_Embeddings.e_env uu____2662 FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_term))
in (

let uu____2669 = (

let uu____2672 = (

let uu____2673 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_norm_step)
in (mktac2 "norm_binder_type" FStar_Tactics_Basic.norm_binder_type uu____2673 FStar_Reflection_Embeddings.e_binder FStar_Syntax_Embeddings.e_unit))
in (

let uu____2680 = (

let uu____2683 = (mktac2 "rename_to" FStar_Tactics_Basic.rename_to FStar_Reflection_Embeddings.e_binder FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit)
in (

let uu____2684 = (

let uu____2687 = (mktac1 "binder_retype" FStar_Tactics_Basic.binder_retype FStar_Reflection_Embeddings.e_binder FStar_Syntax_Embeddings.e_unit)
in (

let uu____2688 = (

let uu____2691 = (mktac1 "revert" FStar_Tactics_Basic.revert FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit)
in (

let uu____2692 = (

let uu____2695 = (mktac1 "clear_top" FStar_Tactics_Basic.clear_top FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit)
in (

let uu____2696 = (

let uu____2699 = (mktac1 "clear" FStar_Tactics_Basic.clear FStar_Reflection_Embeddings.e_binder FStar_Syntax_Embeddings.e_unit)
in (

let uu____2700 = (

let uu____2703 = (mktac1 "rewrite" FStar_Tactics_Basic.rewrite FStar_Reflection_Embeddings.e_binder FStar_Syntax_Embeddings.e_unit)
in (

let uu____2704 = (

let uu____2707 = (mktac1 "smt" FStar_Tactics_Basic.smt FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit)
in (

let uu____2708 = (

let uu____2711 = (mktac1 "refine_intro" FStar_Tactics_Basic.refine_intro FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit)
in (

let uu____2712 = (

let uu____2715 = (mktac2 "t_exact" FStar_Tactics_Basic.t_exact FStar_Syntax_Embeddings.e_bool FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_unit)
in (

let uu____2716 = (

let uu____2719 = (mktac1 "apply" (FStar_Tactics_Basic.apply true) FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_unit)
in (

let uu____2720 = (

let uu____2723 = (mktac1 "apply_raw" (FStar_Tactics_Basic.apply false) FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_unit)
in (

let uu____2724 = (

let uu____2727 = (mktac1 "apply_lemma" FStar_Tactics_Basic.apply_lemma FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_unit)
in (

let uu____2728 = (

let uu____2731 = (

let uu____2732 = (e_tactic_0' FStar_Syntax_Embeddings.e_any)
in (

let uu____2737 = (e_tactic_0' FStar_Syntax_Embeddings.e_any)
in (

let uu____2742 = (FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_any)
in (mktac5 "__divide" (fun uu____2759 uu____2760 -> FStar_Tactics_Basic.divide) FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_int uu____2732 uu____2737 uu____2742))))
in (

let uu____2761 = (

let uu____2764 = (

let uu____2765 = (e_tactic_0' FStar_Syntax_Embeddings.e_unit)
in (

let uu____2770 = (e_tactic_0' FStar_Syntax_Embeddings.e_unit)
in (mktac2 "__seq" FStar_Tactics_Basic.seq uu____2765 uu____2770 FStar_Syntax_Embeddings.e_unit)))
in (

let uu____2779 = (

let uu____2782 = (mktac1 "set_options" FStar_Tactics_Basic.set_options FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit)
in (

let uu____2783 = (

let uu____2786 = (mktac1 "tc" FStar_Tactics_Basic.tc FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_term)
in (

let uu____2787 = (

let uu____2790 = (mktac1 "unshelve" FStar_Tactics_Basic.unshelve FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_unit)
in (

let uu____2791 = (

let uu____2794 = (mktac2 "unquote" FStar_Tactics_Basic.unquote FStar_Syntax_Embeddings.e_any FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_any)
in (

let uu____2795 = (

let uu____2798 = (mktac1 "prune" FStar_Tactics_Basic.prune FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit)
in (

let uu____2799 = (

let uu____2802 = (mktac1 "addns" FStar_Tactics_Basic.addns FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit)
in (

let uu____2803 = (

let uu____2806 = (mktac1 "print" FStar_Tactics_Basic.print FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit)
in (

let uu____2807 = (

let uu____2810 = (mktac1 "debug" FStar_Tactics_Basic.debug FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit)
in (

let uu____2811 = (

let uu____2814 = (mktac1 "dump" FStar_Tactics_Basic.print_proof_state FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit)
in (

let uu____2815 = (

let uu____2818 = (mktac1 "dump1" FStar_Tactics_Basic.print_proof_state1 FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit)
in (

let uu____2819 = (

let uu____2822 = (

let uu____2823 = (e_tactic_0' FStar_Syntax_Embeddings.e_unit)
in (mktac2 "__pointwise" FStar_Tactics_Basic.pointwise FStar_Tactics_Embedding.e_direction uu____2823 FStar_Syntax_Embeddings.e_unit))
in (

let uu____2830 = (

let uu____2833 = (

let uu____2834 = (

let uu____2846 = (FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_bool FStar_Syntax_Embeddings.e_int)
in (e_tactic_1 FStar_Reflection_Embeddings.e_term uu____2846))
in (

let uu____2857 = (e_tactic_0' FStar_Syntax_Embeddings.e_unit)
in (mktac2 "__topdown_rewrite" FStar_Tactics_Basic.topdown_rewrite uu____2834 uu____2857 FStar_Syntax_Embeddings.e_unit)))
in (

let uu____2873 = (

let uu____2876 = (mktac1 "trefl" FStar_Tactics_Basic.trefl FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit)
in (

let uu____2877 = (

let uu____2880 = (mktac1 "later" FStar_Tactics_Basic.later FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit)
in (

let uu____2881 = (

let uu____2884 = (mktac1 "dup" FStar_Tactics_Basic.dup FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit)
in (

let uu____2885 = (

let uu____2888 = (mktac1 "flip" FStar_Tactics_Basic.flip FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit)
in (

let uu____2889 = (

let uu____2892 = (mktac1 "qed" FStar_Tactics_Basic.qed FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit)
in (

let uu____2893 = (

let uu____2896 = (mktac1 "dismiss" FStar_Tactics_Basic.dismiss FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit)
in (

let uu____2897 = (

let uu____2900 = (mktac1 "tadmit" FStar_Tactics_Basic.tadmit FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit)
in (

let uu____2901 = (

let uu____2904 = (

let uu____2905 = (FStar_Syntax_Embeddings.e_tuple2 FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_term)
in (mktac1 "cases" FStar_Tactics_Basic.cases FStar_Reflection_Embeddings.e_term uu____2905))
in (

let uu____2916 = (

let uu____2919 = (mktac1 "top_env" FStar_Tactics_Basic.top_env FStar_Syntax_Embeddings.e_unit FStar_Reflection_Embeddings.e_env)
in (

let uu____2920 = (

let uu____2923 = (mktac1 "cur_env" FStar_Tactics_Basic.cur_env FStar_Syntax_Embeddings.e_unit FStar_Reflection_Embeddings.e_env)
in (

let uu____2924 = (

let uu____2927 = (mktac1 "cur_goal" FStar_Tactics_Basic.cur_goal' FStar_Syntax_Embeddings.e_unit FStar_Reflection_Embeddings.e_term)
in (

let uu____2928 = (

let uu____2931 = (mktac1 "cur_witness" FStar_Tactics_Basic.cur_witness FStar_Syntax_Embeddings.e_unit FStar_Reflection_Embeddings.e_term)
in (

let uu____2932 = (

let uu____2935 = (mktac1 "inspect" FStar_Tactics_Basic.inspect FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_term_view)
in (

let uu____2936 = (

let uu____2939 = (mktac1 "pack" FStar_Tactics_Basic.pack FStar_Reflection_Embeddings.e_term_view FStar_Reflection_Embeddings.e_term)
in (

let uu____2940 = (

let uu____2943 = (mktac1 "fresh" FStar_Tactics_Basic.fresh FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_int)
in (

let uu____2944 = (

let uu____2947 = (mktac1 "ngoals" FStar_Tactics_Basic.ngoals FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_int)
in (

let uu____2948 = (

let uu____2951 = (mktac1 "ngoals_smt" FStar_Tactics_Basic.ngoals_smt FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_int)
in (

let uu____2952 = (

let uu____2955 = (mktac1 "is_guard" FStar_Tactics_Basic.is_guard FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_bool)
in (

let uu____2956 = (

let uu____2959 = (

let uu____2960 = (FStar_Syntax_Embeddings.e_option FStar_Reflection_Embeddings.e_term)
in (mktac2 "uvar_env" FStar_Tactics_Basic.uvar_env FStar_Reflection_Embeddings.e_env uu____2960 FStar_Reflection_Embeddings.e_term))
in (

let uu____2967 = (

let uu____2970 = (mktac2 "unify" FStar_Tactics_Basic.unify FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_bool)
in (

let uu____2971 = (

let uu____2974 = (

let uu____2975 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string)
in (mktac3 "launch_process" FStar_Tactics_Basic.launch_process FStar_Syntax_Embeddings.e_string uu____2975 FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_string))
in (

let uu____2982 = (

let uu____2985 = (mktac2 "fresh_bv_named" FStar_Tactics_Basic.fresh_bv_named FStar_Syntax_Embeddings.e_string FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_bv)
in (

let uu____2986 = (

let uu____2989 = (mktac1 "change" FStar_Tactics_Basic.change FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_unit)
in (

let uu____2990 = (

let uu____2993 = (mktac1 "get_guard_policy" FStar_Tactics_Basic.get_guard_policy FStar_Syntax_Embeddings.e_unit FStar_Tactics_Embedding.e_guard_policy)
in (

let uu____2994 = (

let uu____2997 = (mktac1 "set_guard_policy" FStar_Tactics_Basic.set_guard_policy FStar_Tactics_Embedding.e_guard_policy FStar_Syntax_Embeddings.e_unit)
in (uu____2997)::(decr_depth_step)::(incr_depth_step)::(tracepoint_step)::(set_proofstate_range_step)::(push_binder_step)::[])
in (uu____2993)::uu____2994))
in (uu____2989)::uu____2990))
in (uu____2985)::uu____2986))
in (uu____2974)::uu____2982))
in (uu____2970)::uu____2971))
in (uu____2959)::uu____2967))
in (uu____2955)::uu____2956))
in (uu____2951)::uu____2952))
in (uu____2947)::uu____2948))
in (uu____2943)::uu____2944))
in (uu____2939)::uu____2940))
in (uu____2935)::uu____2936))
in (uu____2931)::uu____2932))
in (uu____2927)::uu____2928))
in (uu____2923)::uu____2924))
in (uu____2919)::uu____2920))
in (uu____2904)::uu____2916))
in (uu____2900)::uu____2901))
in (uu____2896)::uu____2897))
in (uu____2892)::uu____2893))
in (uu____2888)::uu____2889))
in (uu____2884)::uu____2885))
in (uu____2880)::uu____2881))
in (uu____2876)::uu____2877))
in (uu____2833)::uu____2873))
in (uu____2822)::uu____2830))
in (uu____2818)::uu____2819))
in (uu____2814)::uu____2815))
in (uu____2810)::uu____2811))
in (uu____2806)::uu____2807))
in (uu____2802)::uu____2803))
in (uu____2798)::uu____2799))
in (uu____2794)::uu____2795))
in (uu____2790)::uu____2791))
in (uu____2786)::uu____2787))
in (uu____2782)::uu____2783))
in (uu____2764)::uu____2779))
in (uu____2731)::uu____2761))
in (uu____2727)::uu____2728))
in (uu____2723)::uu____2724))
in (uu____2719)::uu____2720))
in (uu____2715)::uu____2716))
in (uu____2711)::uu____2712))
in (uu____2707)::uu____2708))
in (uu____2703)::uu____2704))
in (uu____2699)::uu____2700))
in (uu____2695)::uu____2696))
in (uu____2691)::uu____2692))
in (uu____2687)::uu____2688))
in (uu____2683)::uu____2684))
in (uu____2672)::uu____2680))
in (uu____2661)::uu____2669))
in (uu____2650)::uu____2658))
in (uu____2635)::uu____2647))
in (uu____2631)::uu____2632))
in (uu____2611)::uu____2628))
in (uu____2607)::uu____2608))
in (uu____2601)::uu____2604))
in (FStar_List.append uu____2598 (FStar_List.append FStar_Reflection_Interpreter.reflection_primops native_tactics_steps)))))))))))))))))))))
and unembed_tactic_1 : 'Aa 'Ar . 'Aa FStar_Syntax_Embeddings.embedding  ->  'Ar FStar_Syntax_Embeddings.embedding  ->  FStar_Syntax_Syntax.term  ->  ('Aa  ->  'Ar FStar_Tactics_Basic.tac) FStar_Pervasives_Native.option = (fun ea er f -> FStar_Pervasives_Native.Some ((fun x -> (

let rng = FStar_Range.dummyRange
in (

let x_tm = (FStar_Syntax_Embeddings.embed ea rng x)
in (

let app = (

let uu____3020 = (

let uu____3025 = (

let uu____3026 = (FStar_Syntax_Syntax.as_arg x_tm)
in (uu____3026)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f uu____3025))
in (uu____3020 FStar_Pervasives_Native.None rng))
in (unembed_tactic_0 er app)))))))
and unembed_tactic_0 : 'Ab . 'Ab FStar_Syntax_Embeddings.embedding  ->  FStar_Syntax_Syntax.term  ->  'Ab FStar_Tactics_Basic.tac = (fun eb embedded_tac_b -> (FStar_Tactics_Basic.bind FStar_Tactics_Basic.get (fun proof_state -> (

let rng = embedded_tac_b.FStar_Syntax_Syntax.pos
in (

let tm = (

let uu____3049 = (

let uu____3054 = (

let uu____3055 = (

let uu____3056 = (FStar_Syntax_Embeddings.embed FStar_Tactics_Embedding.e_proofstate rng proof_state)
in (FStar_Syntax_Syntax.as_arg uu____3056))
in (uu____3055)::[])
in (FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____3054))
in (uu____3049 FStar_Pervasives_Native.None rng))
in (

let steps = (FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Unascribe)::[]
in ((

let uu____3063 = (FStar_TypeChecker_Env.debug proof_state.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacVerbose")))
in (match (uu____3063) with
| true -> begin
(

let uu____3064 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Starting normalizer with %s\n" uu____3064))
end
| uu____3065 -> begin
()
end));
(

let result = (

let uu____3067 = (primitive_steps ())
in (FStar_TypeChecker_Normalize.normalize_with_primitive_steps uu____3067 steps proof_state.FStar_Tactics_Types.main_context tm))
in ((

let uu____3071 = (FStar_TypeChecker_Env.debug proof_state.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacVerbose")))
in (match (uu____3071) with
| true -> begin
(

let uu____3072 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print1 "Reduced tactic: got %s\n" uu____3072))
end
| uu____3073 -> begin
()
end));
(

let res = (

let uu____3079 = (FStar_Tactics_Embedding.e_result eb)
in (FStar_Syntax_Embeddings.unembed uu____3079 result))
in (match (res) with
| FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success (b, ps)) -> begin
(

let uu____3092 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____3092 (fun uu____3096 -> (FStar_Tactics_Basic.ret b))))
end
| FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed (msg, ps)) -> begin
(

let uu____3101 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____3101 (fun uu____3105 -> (FStar_Tactics_Basic.fail msg))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3108 = (

let uu____3113 = (

let uu____3114 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.format1 "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s" uu____3114))
in ((FStar_Errors.Fatal_TacticGotStuck), (uu____3113)))
in (FStar_Errors.raise_error uu____3108 proof_state.FStar_Tactics_Types.main_context.FStar_TypeChecker_Env.range))
end));
));
)))))))
and unembed_tactic_0' : 'Ab . 'Ab FStar_Syntax_Embeddings.embedding  ->  FStar_Syntax_Syntax.term  ->  'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option = (fun eb embedded_tac_b -> (

let uu____3121 = (unembed_tactic_0 eb embedded_tac_b)
in (FStar_All.pipe_left (fun _0_18 -> FStar_Pervasives_Native.Some (_0_18)) uu____3121)))


let report_implicits : FStar_Tactics_Types.proofstate  ->  FStar_TypeChecker_Env.implicits  ->  unit = (fun ps is -> (

let errs = (FStar_List.map (fun uu____3177 -> (match (uu____3177) with
| (r, uu____3197, uv, uu____3199, ty, rng) -> begin
(

let uu____3202 = (

let uu____3203 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____3204 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.format3 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")" uu____3203 uu____3204 r)))
in ((FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic), (uu____3202), (rng)))
end)) is)
in (match (errs) with
| [] -> begin
()
end
| ((e, msg, r))::tl1 -> begin
((FStar_Tactics_Basic.dump_proofstate ps "failing due to uninstantiated implicits");
(FStar_Errors.add_errors tl1);
(FStar_Errors.raise_error ((e), (msg)) r);
)
end)))


let run_tactic_on_typ : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Tactics_Basic.goal Prims.list * FStar_Syntax_Syntax.term) = (fun tactic env typ -> ((

let uu____3259 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3259) with
| true -> begin
(

let uu____3289 = (FStar_Syntax_Print.term_to_string tactic)
in (FStar_Util.print1 "About to reduce uvars on: %s\n" uu____3289))
end
| uu____3290 -> begin
()
end));
(

let tactic1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic)
in ((

let uu____3293 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3293) with
| true -> begin
(

let uu____3323 = (FStar_Syntax_Print.term_to_string tactic1)
in (FStar_Util.print1 "About to check tactic term: %s\n" uu____3323))
end
| uu____3324 -> begin
()
end));
(

let uu____3325 = (FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1)
in (match (uu____3325) with
| (uu____3338, uu____3339, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
(FStar_Errors.stop_if_err ());
(

let tau = (unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic1)
in (

let uu____3346 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3346) with
| (env1, uu____3360) -> begin
(

let env2 = (

let uu___63_3366 = env1
in {FStar_TypeChecker_Env.solver = uu___63_3366.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___63_3366.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___63_3366.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___63_3366.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___63_3366.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___63_3366.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___63_3366.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___63_3366.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___63_3366.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___63_3366.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___63_3366.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___63_3366.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___63_3366.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___63_3366.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___63_3366.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___63_3366.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___63_3366.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___63_3366.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___63_3366.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___63_3366.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___63_3366.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___63_3366.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___63_3366.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___63_3366.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___63_3366.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___63_3366.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___63_3366.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___63_3366.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___63_3366.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___63_3366.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___63_3366.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___63_3366.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___63_3366.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___63_3366.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___63_3366.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___63_3366.FStar_TypeChecker_Env.dep_graph})
in (

let env3 = (

let uu___64_3368 = env2
in {FStar_TypeChecker_Env.solver = uu___64_3368.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___64_3368.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___64_3368.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___64_3368.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___64_3368.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___64_3368.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___64_3368.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___64_3368.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___64_3368.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___64_3368.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___64_3368.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___64_3368.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___64_3368.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___64_3368.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___64_3368.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___64_3368.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___64_3368.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___64_3368.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___64_3368.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.failhard = uu___64_3368.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___64_3368.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___64_3368.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___64_3368.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___64_3368.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___64_3368.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___64_3368.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___64_3368.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___64_3368.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___64_3368.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___64_3368.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___64_3368.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___64_3368.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___64_3368.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___64_3368.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___64_3368.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___64_3368.FStar_TypeChecker_Env.dep_graph})
in (

let uu____3369 = (FStar_Tactics_Basic.proofstate_of_goal_ty env3 typ)
in (match (uu____3369) with
| (ps, w) -> begin
((

let uu____3383 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3383) with
| true -> begin
(

let uu____3413 = (FStar_Syntax_Print.term_to_string typ)
in (FStar_Util.print1 "Running tactic with goal = %s\n" uu____3413))
end
| uu____3414 -> begin
()
end));
(

let uu____3415 = (FStar_Util.record_time (fun uu____3425 -> (FStar_Tactics_Basic.run tau ps)))
in (match (uu____3415) with
| (res, ms) -> begin
((

let uu____3439 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3439) with
| true -> begin
(

let uu____3469 = (FStar_Syntax_Print.term_to_string tactic1)
in (

let uu____3470 = (FStar_Util.string_of_int ms)
in (

let uu____3471 = (FStar_Syntax_Print.lid_to_string env3.FStar_TypeChecker_Env.curmodule)
in (FStar_Util.print3 "Tactic %s ran in %s ms (%s)\n" uu____3469 uu____3470 uu____3471))))
end
| uu____3472 -> begin
()
end));
(match (res) with
| FStar_Tactics_Result.Success (uu____3479, ps1) -> begin
((

let uu____3482 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3482) with
| true -> begin
(

let uu____3512 = (FStar_Syntax_Print.term_to_string w)
in (FStar_Util.print1 "Tactic generated proofterm %s\n" uu____3512))
end
| uu____3513 -> begin
()
end));
(FStar_List.iter (fun g1 -> (

let uu____3519 = (FStar_Tactics_Basic.is_irrelevant g1)
in (match (uu____3519) with
| true -> begin
(

let uu____3520 = (FStar_TypeChecker_Rel.teq_nosmt g1.FStar_Tactics_Types.context g1.FStar_Tactics_Types.witness FStar_Syntax_Util.exp_unit)
in (match (uu____3520) with
| true -> begin
()
end
| uu____3521 -> begin
(

let uu____3522 = (

let uu____3523 = (FStar_Syntax_Print.term_to_string g1.FStar_Tactics_Types.witness)
in (FStar_Util.format1 "Irrelevant tactic witness does not unify with (): %s" uu____3523))
in (failwith uu____3522))
end))
end
| uu____3524 -> begin
()
end))) (FStar_List.append ps1.FStar_Tactics_Types.goals ps1.FStar_Tactics_Types.smt_goals));
(

let g1 = (

let uu___65_3526 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___65_3526.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___65_3526.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___65_3526.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = ps1.FStar_Tactics_Types.all_implicits})
in (

let g2 = (

let uu____3528 = (FStar_TypeChecker_Rel.solve_deferred_constraints env3 g1)
in (FStar_All.pipe_right uu____3528 FStar_TypeChecker_Rel.resolve_implicits_tac))
in ((report_implicits ps1 g2.FStar_TypeChecker_Env.implicits);
(((FStar_List.append ps1.FStar_Tactics_Types.goals ps1.FStar_Tactics_Types.smt_goals)), (w));
)));
)
end
| FStar_Tactics_Result.Failed (s, ps1) -> begin
((

let uu____3535 = (

let uu____3536 = (FStar_TypeChecker_Normalize.psc_subst ps1.FStar_Tactics_Types.psc)
in (FStar_Tactics_Types.subst_proof_state uu____3536 ps1))
in (FStar_Tactics_Basic.dump_proofstate uu____3535 "at the time of failure"));
(

let uu____3537 = (

let uu____3542 = (FStar_Util.format1 "user tactic failed: %s" s)
in ((FStar_Errors.Fatal_ArgumentLengthMismatch), (uu____3542)))
in (FStar_Errors.raise_error uu____3537 typ.FStar_Syntax_Syntax.pos));
)
end);
)
end));
)
end))))
end)));
)
end));
));
))

type pol =
| Pos
| Neg
| Both


let uu___is_Pos : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pos -> begin
true
end
| uu____3554 -> begin
false
end))


let uu___is_Neg : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neg -> begin
true
end
| uu____3560 -> begin
false
end))


let uu___is_Both : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Both -> begin
true
end
| uu____3566 -> begin
false
end))

type 'a tres_m =
| Unchanged of 'a
| Simplified of ('a * FStar_Tactics_Basic.goal Prims.list)
| Dual of ('a * 'a * FStar_Tactics_Basic.goal Prims.list)


let uu___is_Unchanged : 'a . 'a tres_m  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unchanged (_0) -> begin
true
end
| uu____3621 -> begin
false
end))


let __proj__Unchanged__item___0 : 'a . 'a tres_m  ->  'a = (fun projectee -> (match (projectee) with
| Unchanged (_0) -> begin
_0
end))


let uu___is_Simplified : 'a . 'a tres_m  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simplified (_0) -> begin
true
end
| uu____3661 -> begin
false
end))


let __proj__Simplified__item___0 : 'a . 'a tres_m  ->  ('a * FStar_Tactics_Basic.goal Prims.list) = (fun projectee -> (match (projectee) with
| Simplified (_0) -> begin
_0
end))


let uu___is_Dual : 'a . 'a tres_m  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Dual (_0) -> begin
true
end
| uu____3715 -> begin
false
end))


let __proj__Dual__item___0 : 'a . 'a tres_m  ->  ('a * 'a * FStar_Tactics_Basic.goal Prims.list) = (fun projectee -> (match (projectee) with
| Dual (_0) -> begin
_0
end))


type tres =
FStar_Syntax_Syntax.term tres_m


let tpure : 'Auu____3756 . 'Auu____3756  ->  'Auu____3756 tres_m = (fun x -> Unchanged (x))


let flip : pol  ->  pol = (fun p -> (match (p) with
| Pos -> begin
Neg
end
| Neg -> begin
Pos
end
| Both -> begin
Both
end))


let by_tactic_interp : pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  tres = (fun pol e t -> (

let uu____3784 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3784) with
| (hd1, args) -> begin
(

let uu____3821 = (

let uu____3834 = (

let uu____3835 = (FStar_Syntax_Util.un_uinst hd1)
in uu____3835.FStar_Syntax_Syntax.n)
in ((uu____3834), (args)))
in (match (uu____3821) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((rett, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____3848))))::((tactic, FStar_Pervasives_Native.None))::((assertion, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid) -> begin
(match (pol) with
| Pos -> begin
(

let uu____3911 = (run_tactic_on_typ tactic e assertion)
in (match (uu____3911) with
| (gs, uu____3919) -> begin
Simplified (((FStar_Syntax_Util.t_true), (gs)))
end))
end
| Both -> begin
(

let uu____3926 = (run_tactic_on_typ tactic e assertion)
in (match (uu____3926) with
| (gs, uu____3934) -> begin
Dual (((assertion), (FStar_Syntax_Util.t_true), (gs)))
end))
end
| Neg -> begin
Simplified (((assertion), ([])))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((assertion, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.spinoff_lid) -> begin
(match (pol) with
| Pos -> begin
(

let uu____3985 = (

let uu____3992 = (

let uu____3995 = (

let uu____3996 = (FStar_Tactics_Basic.goal_of_goal_ty e assertion)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3996))
in (uu____3995)::[])
in ((FStar_Syntax_Util.t_true), (uu____3992)))
in Simplified (uu____3985))
end
| Both -> begin
(

let uu____4007 = (

let uu____4020 = (

let uu____4023 = (

let uu____4024 = (FStar_Tactics_Basic.goal_of_goal_ty e assertion)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4024))
in (uu____4023)::[])
in ((assertion), (FStar_Syntax_Util.t_true), (uu____4020)))
in Dual (uu____4007))
end
| Neg -> begin
Simplified (((assertion), ([])))
end)
end
| uu____4045 -> begin
Unchanged (t)
end))
end)))


let explode : 'a . 'a tres_m  ->  ('a * 'a * FStar_Tactics_Basic.goal Prims.list) = (fun t -> (match (t) with
| Unchanged (t1) -> begin
((t1), (t1), ([]))
end
| Simplified (t1, gs) -> begin
((t1), (t1), (gs))
end
| Dual (tn, tp, gs) -> begin
((tn), (tp), (gs))
end))


let comb1 : 'a 'b . ('a  ->  'b)  ->  'a tres_m  ->  'b tres_m = (fun f uu___62_4133 -> (match (uu___62_4133) with
| Unchanged (t) -> begin
(

let uu____4139 = (f t)
in Unchanged (uu____4139))
end
| Simplified (t, gs) -> begin
(

let uu____4146 = (

let uu____4153 = (f t)
in ((uu____4153), (gs)))
in Simplified (uu____4146))
end
| Dual (tn, tp, gs) -> begin
(

let uu____4163 = (

let uu____4172 = (f tn)
in (

let uu____4173 = (f tp)
in ((uu____4172), (uu____4173), (gs))))
in Dual (uu____4163))
end))


let comb2 : 'a 'b 'c . ('a  ->  'b  ->  'c)  ->  'a tres_m  ->  'b tres_m  ->  'c tres_m = (fun f x y -> (match (((x), (y))) with
| (Unchanged (t1), Unchanged (t2)) -> begin
(

let uu____4236 = (f t1 t2)
in Unchanged (uu____4236))
end
| (Unchanged (t1), Simplified (t2, gs)) -> begin
(

let uu____4248 = (

let uu____4255 = (f t1 t2)
in ((uu____4255), (gs)))
in Simplified (uu____4248))
end
| (Simplified (t1, gs), Unchanged (t2)) -> begin
(

let uu____4269 = (

let uu____4276 = (f t1 t2)
in ((uu____4276), (gs)))
in Simplified (uu____4269))
end
| (Simplified (t1, gs1), Simplified (t2, gs2)) -> begin
(

let uu____4295 = (

let uu____4302 = (f t1 t2)
in ((uu____4302), ((FStar_List.append gs1 gs2))))
in Simplified (uu____4295))
end
| uu____4305 -> begin
(

let uu____4314 = (explode x)
in (match (uu____4314) with
| (n1, p1, gs1) -> begin
(

let uu____4332 = (explode y)
in (match (uu____4332) with
| (n2, p2, gs2) -> begin
(

let uu____4350 = (

let uu____4359 = (f n1 n2)
in (

let uu____4360 = (f p1 p2)
in ((uu____4359), (uu____4360), ((FStar_List.append gs1 gs2)))))
in Dual (uu____4350))
end))
end))
end))


let comb_list : 'a . 'a tres_m Prims.list  ->  'a Prims.list tres_m = (fun rs -> (

let rec aux = (fun rs1 acc -> (match (rs1) with
| [] -> begin
acc
end
| (hd1)::tl1 -> begin
(

let uu____4432 = (comb2 (fun l r -> (l)::r) hd1 acc)
in (aux tl1 uu____4432))
end))
in (aux (FStar_List.rev rs) (tpure []))))


let emit : 'a . FStar_Tactics_Basic.goal Prims.list  ->  'a tres_m  ->  'a tres_m = (fun gs m -> (comb2 (fun uu____4480 x -> x) (Simplified (((()), (gs)))) m))


let rec traverse : (pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  tres)  ->  pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  tres = (fun f pol e t -> (

let r = (

let uu____4522 = (

let uu____4523 = (FStar_Syntax_Subst.compress t)
in uu____4523.FStar_Syntax_Syntax.n)
in (match (uu____4522) with
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let tr = (traverse f pol e t1)
in (

let uu____4535 = (comb1 (fun t' -> FStar_Syntax_Syntax.Tm_uinst (((t'), (us)))))
in (uu____4535 tr)))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let tr = (traverse f pol e t1)
in (

let uu____4561 = (comb1 (fun t' -> FStar_Syntax_Syntax.Tm_meta (((t'), (m)))))
in (uu____4561 tr)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____4581; FStar_Syntax_Syntax.vars = uu____4582}, ((p, uu____4584))::((q, uu____4586))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid) -> begin
(

let x = (

let uu____4626 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____4626))
in (

let r1 = (traverse f (flip pol) e p)
in (

let r2 = (

let uu____4629 = (FStar_TypeChecker_Env.push_bv e x)
in (traverse f pol uu____4629 q))
in (comb2 (fun l r -> (

let uu____4635 = (FStar_Syntax_Util.mk_imp l r)
in uu____4635.FStar_Syntax_Syntax.n)) r1 r2))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____4639; FStar_Syntax_Syntax.vars = uu____4640}, ((p, uu____4642))::((q, uu____4644))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid) -> begin
(

let xp = (

let uu____4684 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____4684))
in (

let xq = (

let uu____4686 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____4686))
in (

let r1 = (

let uu____4688 = (FStar_TypeChecker_Env.push_bv e xq)
in (traverse f Both uu____4688 p))
in (

let r2 = (

let uu____4690 = (FStar_TypeChecker_Env.push_bv e xp)
in (traverse f Both uu____4690 q))
in (match (((r1), (r2))) with
| (Unchanged (uu____4693), Unchanged (uu____4694)) -> begin
(comb2 (fun l r -> (

let uu____4704 = (FStar_Syntax_Util.mk_iff l r)
in uu____4704.FStar_Syntax_Syntax.n)) r1 r2)
end
| uu____4707 -> begin
(

let uu____4712 = (explode r1)
in (match (uu____4712) with
| (pn, pp, gs1) -> begin
(

let uu____4730 = (explode r2)
in (match (uu____4730) with
| (qn, qp, gs2) -> begin
(

let t1 = (

let uu____4751 = (FStar_Syntax_Util.mk_imp pn qp)
in (

let uu____4752 = (FStar_Syntax_Util.mk_imp qn pp)
in (FStar_Syntax_Util.mk_conj uu____4751 uu____4752)))
in Simplified (((t1.FStar_Syntax_Syntax.n), ((FStar_List.append gs1 gs2)))))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let r0 = (traverse f pol e hd1)
in (

let r1 = (FStar_List.fold_right (fun uu____4804 r -> (match (uu____4804) with
| (a, q) -> begin
(

let r' = (traverse f pol e a)
in (comb2 (fun a1 args1 -> (((a1), (q)))::args1) r' r))
end)) args (tpure []))
in (comb2 (fun hd2 args1 -> FStar_Syntax_Syntax.Tm_app (((hd2), (args1)))) r0 r1)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____4922 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____4922) with
| (bs1, topen) -> begin
(

let e' = (FStar_TypeChecker_Env.push_binders e bs1)
in (

let r0 = (FStar_List.map (fun uu____4956 -> (match (uu____4956) with
| (bv, aq) -> begin
(

let r = (traverse f (flip pol) e bv.FStar_Syntax_Syntax.sort)
in (

let uu____4970 = (comb1 (fun s' -> (((

let uu___66_4996 = bv
in {FStar_Syntax_Syntax.ppname = uu___66_4996.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___66_4996.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s'})), (aq))))
in (uu____4970 r)))
end)) bs1)
in (

let rbs = (comb_list r0)
in (

let rt = (traverse f pol e' topen)
in (comb2 (fun bs2 t2 -> (

let uu____5016 = (FStar_Syntax_Util.abs bs2 t2 k)
in uu____5016.FStar_Syntax_Syntax.n)) rbs rt)))))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, ef) -> begin
(

let uu____5062 = (traverse f pol e t1)
in (

let uu____5067 = (comb1 (fun t2 -> FStar_Syntax_Syntax.Tm_ascribed (((t2), (asc), (ef)))))
in (uu____5067 uu____5062)))
end
| x -> begin
(tpure x)
end))
in (match (r) with
| Unchanged (tn') -> begin
(f pol e (

let uu___67_5107 = t
in {FStar_Syntax_Syntax.n = tn'; FStar_Syntax_Syntax.pos = uu___67_5107.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___67_5107.FStar_Syntax_Syntax.vars}))
end
| Simplified (tn', gs) -> begin
(

let uu____5114 = (f pol e (

let uu___68_5118 = t
in {FStar_Syntax_Syntax.n = tn'; FStar_Syntax_Syntax.pos = uu___68_5118.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___68_5118.FStar_Syntax_Syntax.vars}))
in (emit gs uu____5114))
end
| Dual (tn, tp, gs) -> begin
(

let rp = (f pol e (

let uu___69_5128 = t
in {FStar_Syntax_Syntax.n = tp; FStar_Syntax_Syntax.pos = uu___69_5128.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___69_5128.FStar_Syntax_Syntax.vars}))
in (

let uu____5129 = (explode rp)
in (match (uu____5129) with
| (uu____5138, p', gs') -> begin
Dual ((((

let uu___70_5152 = t
in {FStar_Syntax_Syntax.n = tn; FStar_Syntax_Syntax.pos = uu___70_5152.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___70_5152.FStar_Syntax_Syntax.vars})), (p'), ((FStar_List.append gs gs'))))
end)))
end)))


let getprop : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun e t -> (

let tn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) e t)
in (FStar_Syntax_Util.un_squash tn)))


let preprocess : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term * FStar_Options.optionstate) Prims.list = (fun env goal -> ((

let uu____5195 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____5195));
(

let uu____5226 = (FStar_ST.op_Bang tacdbg)
in (match (uu____5226) with
| true -> begin
(

let uu____5256 = (

let uu____5257 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____5257 (FStar_Syntax_Print.binders_to_string ",")))
in (

let uu____5258 = (FStar_Syntax_Print.term_to_string goal)
in (FStar_Util.print2 "About to preprocess %s |= %s\n" uu____5256 uu____5258)))
end
| uu____5259 -> begin
()
end));
(

let initial = (((Prims.parse_int "1")), ([]))
in (

let uu____5287 = (

let uu____5294 = (traverse by_tactic_interp Pos env goal)
in (match (uu____5294) with
| Unchanged (t') -> begin
((t'), ([]))
end
| Simplified (t', gs) -> begin
((t'), (gs))
end
| uu____5312 -> begin
(failwith "no")
end))
in (match (uu____5287) with
| (t', gs) -> begin
((

let uu____5334 = (FStar_ST.op_Bang tacdbg)
in (match (uu____5334) with
| true -> begin
(

let uu____5364 = (

let uu____5365 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____5365 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let uu____5366 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Main goal simplified to: %s |- %s\n" uu____5364 uu____5366)))
end
| uu____5367 -> begin
()
end));
(

let s = initial
in (

let s1 = (FStar_List.fold_left (fun uu____5413 g -> (match (uu____5413) with
| (n1, gs1) -> begin
(

let phi = (

let uu____5458 = (getprop g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (match (uu____5458) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5461 = (

let uu____5466 = (

let uu____5467 = (FStar_Syntax_Print.term_to_string g.FStar_Tactics_Types.goal_ty)
in (FStar_Util.format1 "Tactic returned proof-relevant goal: %s" uu____5467))
in ((FStar_Errors.Fatal_TacticProofRelevantGoal), (uu____5466)))
in (FStar_Errors.raise_error uu____5461 env.FStar_TypeChecker_Env.range))
end
| FStar_Pervasives_Native.Some (phi) -> begin
phi
end))
in ((

let uu____5470 = (FStar_ST.op_Bang tacdbg)
in (match (uu____5470) with
| true -> begin
(

let uu____5500 = (FStar_Util.string_of_int n1)
in (

let uu____5501 = (FStar_Tactics_Basic.goal_to_string g)
in (FStar_Util.print2 "Got goal #%s: %s\n" uu____5500 uu____5501)))
end
| uu____5502 -> begin
()
end));
(

let gt' = (

let uu____5504 = (

let uu____5505 = (FStar_Util.string_of_int n1)
in (Prims.strcat "Could not prove goal #" uu____5505))
in (FStar_TypeChecker_Util.label uu____5504 goal.FStar_Syntax_Syntax.pos phi))
in (((n1 + (Prims.parse_int "1"))), ((((g.FStar_Tactics_Types.context), (gt'), (g.FStar_Tactics_Types.opts)))::gs1)));
))
end)) s gs)
in (

let uu____5520 = s1
in (match (uu____5520) with
| (uu____5541, gs1) -> begin
(

let uu____5559 = (

let uu____5566 = (FStar_Options.peek ())
in ((env), (t'), (uu____5566)))
in (uu____5559)::gs1)
end))));
)
end)));
))


let reify_tactic : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun a -> (

let r = (

let uu____5579 = (

let uu____5580 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____5580))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5579 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____5581 = (

let uu____5586 = (

let uu____5587 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____5588 = (

let uu____5591 = (FStar_Syntax_Syntax.as_arg a)
in (uu____5591)::[])
in (uu____5587)::uu____5588))
in (FStar_Syntax_Syntax.mk_Tm_app r uu____5586))
in (uu____5581 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos))))


let synthesize : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env typ tau -> ((

let uu____5610 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____5610));
(

let uu____5640 = (

let uu____5647 = (reify_tactic tau)
in (run_tactic_on_typ uu____5647 env typ))
in (match (uu____5640) with
| (gs, w) -> begin
(

let uu____5654 = (FStar_List.existsML (fun g -> (

let uu____5658 = (

let uu____5659 = (getprop g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Option.isSome uu____5659))
in (not (uu____5658)))) gs)
in (match (uu____5654) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_OpenGoalsInSynthesis), ("synthesis left open goals")) typ.FStar_Syntax_Syntax.pos)
end
| uu____5662 -> begin
w
end))
end));
))


let splice : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env tau -> ((

let uu____5678 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____5678));
(

let typ = FStar_Syntax_Syntax.t_decls
in (

let uu____5709 = (

let uu____5716 = (reify_tactic tau)
in (run_tactic_on_typ uu____5716 env typ))
in (match (uu____5709) with
| (gs, w) -> begin
((

let uu____5726 = (FStar_List.existsML (fun g -> (

let uu____5730 = (

let uu____5731 = (getprop g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Option.isSome uu____5731))
in (not (uu____5730)))) gs)
in (match (uu____5726) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_OpenGoalsInSynthesis), ("splice left open goals")) typ.FStar_Syntax_Syntax.pos)
end
| uu____5734 -> begin
()
end));
(

let w1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Unascribe)::(FStar_TypeChecker_Normalize.Unmeta)::[]) env w)
in (

let uu____5736 = (

let uu____5741 = (FStar_Syntax_Embeddings.e_list FStar_Reflection_Embeddings.e_sigelt)
in (FStar_Syntax_Embeddings.unembed uu____5741 w1))
in (FStar_All.pipe_left FStar_Util.must uu____5736)));
)
end)));
))




