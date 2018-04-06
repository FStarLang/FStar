
open Prims
open FStar_Pervasives

let tacdbg : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let mk_tactic_interpretation_0 : 'r . Prims.bool  ->  'r FStar_Tactics_Basic.tac  ->  'r FStar_Syntax_Embeddings.embedder  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t embed_r t_r nm psc args -> (match (args) with
| ((embedded_state, uu____92))::[] -> begin
(

let uu____109 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____109 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____122 -> (

let uu____123 = (FStar_Ident.string_of_lid nm)
in (

let uu____124 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "Reached %s, args are: %s\n" uu____123 uu____124)))));
(

let res = (

let uu____126 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____127 = (FStar_Tactics_Basic.run t ps1)
in (

let uu____130 = (FStar_Tactics_Embedding.embed_result embed_r t_r)
in (uu____130 uu____126 uu____127))))
in FStar_Pervasives_Native.Some (res));
)))))
end
| uu____144 -> begin
(failwith "Unexpected application of tactic primitive")
end))


let mk_tactic_interpretation_1 : 'a 'r . Prims.bool  ->  ('a  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.unembedder  ->  'r FStar_Syntax_Embeddings.embedder  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t unembed_a embed_r t_r nm psc args -> (match (args) with
| ((a, uu____221))::((embedded_state, uu____223))::[] -> begin
(

let uu____250 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____250 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____263 -> (

let uu____264 = (FStar_Ident.string_of_lid nm)
in (

let uu____265 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____264 uu____265)))));
(

let uu____266 = (unembed_a a)
in (FStar_Util.bind_opt uu____266 (fun a1 -> (

let res = (

let uu____278 = (t a1)
in (FStar_Tactics_Basic.run uu____278 ps1))
in (

let uu____281 = (

let uu____282 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____283 = (FStar_Tactics_Embedding.embed_result embed_r t_r)
in (uu____283 uu____282 res)))
in FStar_Pervasives_Native.Some (uu____281))))));
)))))
end
| uu____297 -> begin
(

let uu____298 = (

let uu____299 = (FStar_Ident.string_of_lid nm)
in (

let uu____300 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____299 uu____300)))
in (failwith uu____298))
end))


let mk_tactic_interpretation_1_env : 'a 'r . Prims.bool  ->  (FStar_TypeChecker_Normalize.psc  ->  'a  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.unembedder  ->  'r FStar_Syntax_Embeddings.embedder  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t unembed_a embed_r t_r nm psc args -> (match (args) with
| ((a, uu____382))::((embedded_state, uu____384))::[] -> begin
(

let uu____411 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____411 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____424 -> (

let uu____425 = (FStar_Ident.string_of_lid nm)
in (

let uu____426 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____425 uu____426)))));
(

let uu____427 = (unembed_a a)
in (FStar_Util.bind_opt uu____427 (fun a1 -> (

let res = (

let uu____439 = (t psc a1)
in (FStar_Tactics_Basic.run uu____439 ps1))
in (

let uu____442 = (

let uu____443 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____444 = (FStar_Tactics_Embedding.embed_result embed_r t_r)
in (uu____444 uu____443 res)))
in FStar_Pervasives_Native.Some (uu____442))))));
)))))
end
| uu____458 -> begin
(

let uu____459 = (

let uu____460 = (FStar_Ident.string_of_lid nm)
in (

let uu____461 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____460 uu____461)))
in (failwith uu____459))
end))


let mk_tactic_interpretation_2 : 'a 'b 'r . Prims.bool  ->  ('a  ->  'b  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.unembedder  ->  'b FStar_Syntax_Embeddings.unembedder  ->  'r FStar_Syntax_Embeddings.embedder  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t unembed_a unembed_b embed_r t_r nm psc args -> (match (args) with
| ((a, uu____558))::((b, uu____560))::((embedded_state, uu____562))::[] -> begin
(

let uu____599 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____599 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____612 -> (

let uu____613 = (FStar_Ident.string_of_lid nm)
in (

let uu____614 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____613 uu____614)))));
(

let uu____615 = (unembed_a a)
in (FStar_Util.bind_opt uu____615 (fun a1 -> (

let uu____623 = (unembed_b b)
in (FStar_Util.bind_opt uu____623 (fun b1 -> (

let res = (

let uu____635 = (t a1 b1)
in (FStar_Tactics_Basic.run uu____635 ps1))
in (

let uu____638 = (

let uu____639 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____640 = (FStar_Tactics_Embedding.embed_result embed_r t_r)
in (uu____640 uu____639 res)))
in FStar_Pervasives_Native.Some (uu____638)))))))));
)))))
end
| uu____654 -> begin
(

let uu____655 = (

let uu____656 = (FStar_Ident.string_of_lid nm)
in (

let uu____657 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____656 uu____657)))
in (failwith uu____655))
end))


let mk_tactic_interpretation_3 : 'a 'b 'c 'r . Prims.bool  ->  ('a  ->  'b  ->  'c  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.unembedder  ->  'b FStar_Syntax_Embeddings.unembedder  ->  'c FStar_Syntax_Embeddings.unembedder  ->  'r FStar_Syntax_Embeddings.embedder  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t unembed_a unembed_b unembed_c embed_r t_r nm psc args -> (match (args) with
| ((a, uu____774))::((b, uu____776))::((c, uu____778))::((embedded_state, uu____780))::[] -> begin
(

let uu____827 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____827 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____840 -> (

let uu____841 = (FStar_Ident.string_of_lid nm)
in (

let uu____842 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____841 uu____842)))));
(

let uu____843 = (unembed_a a)
in (FStar_Util.bind_opt uu____843 (fun a1 -> (

let uu____851 = (unembed_b b)
in (FStar_Util.bind_opt uu____851 (fun b1 -> (

let uu____859 = (unembed_c c)
in (FStar_Util.bind_opt uu____859 (fun c1 -> (

let res = (

let uu____871 = (t a1 b1 c1)
in (FStar_Tactics_Basic.run uu____871 ps1))
in (

let uu____874 = (

let uu____875 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____876 = (FStar_Tactics_Embedding.embed_result embed_r t_r)
in (uu____876 uu____875 res)))
in FStar_Pervasives_Native.Some (uu____874))))))))))));
)))))
end
| uu____890 -> begin
(

let uu____891 = (

let uu____892 = (FStar_Ident.string_of_lid nm)
in (

let uu____893 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____892 uu____893)))
in (failwith uu____891))
end))


let mk_tactic_interpretation_4 : 'a 'b 'c 'd 'r . Prims.bool  ->  ('a  ->  'b  ->  'c  ->  'd  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.unembedder  ->  'b FStar_Syntax_Embeddings.unembedder  ->  'c FStar_Syntax_Embeddings.unembedder  ->  'd FStar_Syntax_Embeddings.unembedder  ->  'r FStar_Syntax_Embeddings.embedder  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t unembed_a unembed_b unembed_c unembed_d embed_r t_r nm psc args -> (match (args) with
| ((a, uu____1030))::((b, uu____1032))::((c, uu____1034))::((d, uu____1036))::((embedded_state, uu____1038))::[] -> begin
(

let uu____1095 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____1095 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____1108 -> (

let uu____1109 = (FStar_Ident.string_of_lid nm)
in (

let uu____1110 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____1109 uu____1110)))));
(

let uu____1111 = (unembed_a a)
in (FStar_Util.bind_opt uu____1111 (fun a1 -> (

let uu____1119 = (unembed_b b)
in (FStar_Util.bind_opt uu____1119 (fun b1 -> (

let uu____1127 = (unembed_c c)
in (FStar_Util.bind_opt uu____1127 (fun c1 -> (

let uu____1135 = (unembed_d d)
in (FStar_Util.bind_opt uu____1135 (fun d1 -> (

let res = (

let uu____1147 = (t a1 b1 c1 d1)
in (FStar_Tactics_Basic.run uu____1147 ps1))
in (

let uu____1150 = (

let uu____1151 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____1152 = (FStar_Tactics_Embedding.embed_result embed_r t_r)
in (uu____1152 uu____1151 res)))
in FStar_Pervasives_Native.Some (uu____1150)))))))))))))));
)))))
end
| uu____1166 -> begin
(

let uu____1167 = (

let uu____1168 = (FStar_Ident.string_of_lid nm)
in (

let uu____1169 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____1168 uu____1169)))
in (failwith uu____1167))
end))


let mk_tactic_interpretation_5 : 'a 'b 'c 'd 'e 'r . Prims.bool  ->  ('a  ->  'b  ->  'c  ->  'd  ->  'e  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.unembedder  ->  'b FStar_Syntax_Embeddings.unembedder  ->  'c FStar_Syntax_Embeddings.unembedder  ->  'd FStar_Syntax_Embeddings.unembedder  ->  'e FStar_Syntax_Embeddings.unembedder  ->  'r FStar_Syntax_Embeddings.embedder  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t unembed_a unembed_b unembed_c unembed_d unembed_e embed_r t_r nm psc args -> (match (args) with
| ((a, uu____1326))::((b, uu____1328))::((c, uu____1330))::((d, uu____1332))::((e, uu____1334))::((embedded_state, uu____1336))::[] -> begin
(

let uu____1403 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____1403 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____1416 -> (

let uu____1417 = (FStar_Ident.string_of_lid nm)
in (

let uu____1418 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____1417 uu____1418)))));
(

let uu____1419 = (unembed_a a)
in (FStar_Util.bind_opt uu____1419 (fun a1 -> (

let uu____1427 = (unembed_b b)
in (FStar_Util.bind_opt uu____1427 (fun b1 -> (

let uu____1435 = (unembed_c c)
in (FStar_Util.bind_opt uu____1435 (fun c1 -> (

let uu____1443 = (unembed_d d)
in (FStar_Util.bind_opt uu____1443 (fun d1 -> (

let uu____1451 = (unembed_e e)
in (FStar_Util.bind_opt uu____1451 (fun e1 -> (

let res = (

let uu____1463 = (t a1 b1 c1 d1 e1)
in (FStar_Tactics_Basic.run uu____1463 ps1))
in (

let uu____1466 = (

let uu____1467 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____1468 = (FStar_Tactics_Embedding.embed_result embed_r t_r)
in (uu____1468 uu____1467 res)))
in FStar_Pervasives_Native.Some (uu____1466))))))))))))))))));
)))))
end
| uu____1482 -> begin
(

let uu____1483 = (

let uu____1484 = (FStar_Ident.string_of_lid nm)
in (

let uu____1485 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____1484 uu____1485)))
in (failwith uu____1483))
end))


let mk_tactic_interpretation_6 : 'a 'b 'c 'd 'e 'f 'r . Prims.bool  ->  ('a  ->  'b  ->  'c  ->  'd  ->  'e  ->  'f  ->  'r FStar_Tactics_Basic.tac)  ->  'a FStar_Syntax_Embeddings.unembedder  ->  'b FStar_Syntax_Embeddings.unembedder  ->  'c FStar_Syntax_Embeddings.unembedder  ->  'd FStar_Syntax_Embeddings.unembedder  ->  'e FStar_Syntax_Embeddings.unembedder  ->  'f FStar_Syntax_Embeddings.unembedder  ->  'r FStar_Syntax_Embeddings.embedder  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_TypeChecker_Normalize.psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun reflect t unembed_a unembed_b unembed_c unembed_d unembed_e unembed_f embed_r t_r nm psc args -> (match (args) with
| ((a, uu____1662))::((b, uu____1664))::((c, uu____1666))::((d, uu____1668))::((e, uu____1670))::((f, uu____1672))::((embedded_state, uu____1674))::[] -> begin
(

let uu____1751 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____1751 (fun ps -> (

let ps1 = (FStar_Tactics_Types.set_ps_psc psc ps)
in ((FStar_Tactics_Basic.log ps1 (fun uu____1764 -> (

let uu____1765 = (FStar_Ident.string_of_lid nm)
in (

let uu____1766 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____1765 uu____1766)))));
(

let uu____1767 = (unembed_a a)
in (FStar_Util.bind_opt uu____1767 (fun a1 -> (

let uu____1775 = (unembed_b b)
in (FStar_Util.bind_opt uu____1775 (fun b1 -> (

let uu____1783 = (unembed_c c)
in (FStar_Util.bind_opt uu____1783 (fun c1 -> (

let uu____1791 = (unembed_d d)
in (FStar_Util.bind_opt uu____1791 (fun d1 -> (

let uu____1799 = (unembed_e e)
in (FStar_Util.bind_opt uu____1799 (fun e1 -> (

let uu____1807 = (unembed_f f)
in (FStar_Util.bind_opt uu____1807 (fun f1 -> (

let res = (

let uu____1819 = (t a1 b1 c1 d1 e1 f1)
in (FStar_Tactics_Basic.run uu____1819 ps1))
in (

let uu____1822 = (

let uu____1823 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____1824 = (FStar_Tactics_Embedding.embed_result embed_r t_r)
in (uu____1824 uu____1823 res)))
in FStar_Pervasives_Native.Some (uu____1822)))))))))))))))))))));
)))))
end
| uu____1838 -> begin
(

let uu____1839 = (

let uu____1840 = (FStar_Ident.string_of_lid nm)
in (

let uu____1841 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____1840 uu____1841)))
in (failwith uu____1839))
end))


let step_from_native_step : FStar_Tactics_Native.native_primitive_step  ->  FStar_TypeChecker_Normalize.primitive_step = (fun s -> {FStar_TypeChecker_Normalize.name = s.FStar_Tactics_Native.name; FStar_TypeChecker_Normalize.arity = s.FStar_Tactics_Native.arity; FStar_TypeChecker_Normalize.auto_reflect = FStar_Pervasives_Native.Some ((s.FStar_Tactics_Native.arity - (Prims.parse_int "1"))); FStar_TypeChecker_Normalize.strong_reduction_ok = s.FStar_Tactics_Native.strong_reduction_ok; FStar_TypeChecker_Normalize.requires_binder_substitution = false; FStar_TypeChecker_Normalize.interpretation = (fun psc args -> (s.FStar_Tactics_Native.tactic psc args))})


let rec primitive_steps : Prims.unit  ->  FStar_TypeChecker_Normalize.primitive_step Prims.list = (fun uu____1927 -> (

let mk1 = (fun nm arity interpretation -> (

let nm1 = (FStar_Tactics_Embedding.fstar_tactics_lid' (("Builtins")::(nm)::[]))
in {FStar_TypeChecker_Normalize.name = nm1; FStar_TypeChecker_Normalize.arity = arity; FStar_TypeChecker_Normalize.auto_reflect = FStar_Pervasives_Native.Some ((arity - (Prims.parse_int "1"))); FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.requires_binder_substitution = true; FStar_TypeChecker_Normalize.interpretation = (fun psc args -> (interpretation nm1 psc args))}))
in (

let native_tactics = (FStar_Tactics_Native.list_all ())
in (

let native_tactics_steps = (FStar_List.map step_from_native_step native_tactics)
in (

let mktac1 = (fun a r name f u_a e_r tr -> (mk1 name (Prims.parse_int "2") (mk_tactic_interpretation_1 false f u_a e_r tr)))
in (

let mktac2 = (fun a b r name f u_a u_b e_r tr -> (mk1 name (Prims.parse_int "3") (mk_tactic_interpretation_2 false f u_a u_b e_r tr)))
in (

let mktac3 = (fun a b c r name f u_a u_b u_c e_r tr -> (mk1 name (Prims.parse_int "4") (mk_tactic_interpretation_3 false f u_a u_b u_c e_r tr)))
in (

let mktac5 = (fun a b c d e r name f u_a u_b u_c u_d u_e e_r tr -> (mk1 name (Prims.parse_int "6") (mk_tactic_interpretation_5 false f u_a u_b u_c u_d u_e e_r tr)))
in (

let decr_depth_interp = (fun psc args -> (match (args) with
| ((ps, uu____2379))::[] -> begin
(

let uu____2396 = (FStar_Tactics_Embedding.unembed_proofstate ps)
in (FStar_Util.bind_opt uu____2396 (fun ps1 -> (

let ps2 = (FStar_Tactics_Types.set_ps_psc psc ps1)
in (

let uu____2404 = (

let uu____2405 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____2406 = (FStar_Tactics_Types.decr_depth ps2)
in (FStar_Tactics_Embedding.embed_proofstate uu____2405 uu____2406)))
in FStar_Pervasives_Native.Some (uu____2404))))))
end
| uu____2407 -> begin
(failwith "Unexpected application of decr_depth")
end))
in (

let decr_depth_step = (

let uu____2411 = (FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth")
in {FStar_TypeChecker_Normalize.name = uu____2411; FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1"); FStar_TypeChecker_Normalize.auto_reflect = FStar_Pervasives_Native.None; FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.requires_binder_substitution = false; FStar_TypeChecker_Normalize.interpretation = decr_depth_interp})
in (

let incr_depth_interp = (fun psc args -> (match (args) with
| ((ps, uu____2424))::[] -> begin
(

let uu____2441 = (FStar_Tactics_Embedding.unembed_proofstate ps)
in (FStar_Util.bind_opt uu____2441 (fun ps1 -> (

let ps2 = (FStar_Tactics_Types.set_ps_psc psc ps1)
in (

let uu____2449 = (

let uu____2450 = (FStar_TypeChecker_Normalize.psc_range psc)
in (

let uu____2451 = (FStar_Tactics_Types.incr_depth ps2)
in (FStar_Tactics_Embedding.embed_proofstate uu____2450 uu____2451)))
in FStar_Pervasives_Native.Some (uu____2449))))))
end
| uu____2452 -> begin
(failwith "Unexpected application of incr_depth")
end))
in (

let incr_depth_step = (

let uu____2456 = (FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth")
in {FStar_TypeChecker_Normalize.name = uu____2456; FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1"); FStar_TypeChecker_Normalize.auto_reflect = FStar_Pervasives_Native.None; FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.requires_binder_substitution = false; FStar_TypeChecker_Normalize.interpretation = incr_depth_interp})
in (

let tracepoint_interp = (fun psc args -> (match (args) with
| ((ps, uu____2473))::[] -> begin
(

let uu____2490 = (FStar_Tactics_Embedding.unembed_proofstate ps)
in (FStar_Util.bind_opt uu____2490 (fun ps1 -> (

let ps2 = (FStar_Tactics_Types.set_ps_psc psc ps1)
in ((FStar_Tactics_Types.tracepoint ps2);
FStar_Pervasives_Native.Some (FStar_Syntax_Util.exp_unit);
)))))
end
| uu____2503 -> begin
(failwith "Unexpected application of tracepoint")
end))
in (

let set_proofstate_range_interp = (fun psc args -> (match (args) with
| ((ps, uu____2520))::((r, uu____2522))::[] -> begin
(

let uu____2549 = (FStar_Tactics_Embedding.unembed_proofstate ps)
in (FStar_Util.bind_opt uu____2549 (fun ps1 -> (

let uu____2555 = (FStar_Syntax_Embeddings.unembed_range r)
in (FStar_Util.bind_opt uu____2555 (fun r1 -> (

let ps' = (FStar_Tactics_Types.set_proofstate_range ps1 r1)
in (

let uu____2563 = (

let uu____2564 = (FStar_TypeChecker_Normalize.psc_range psc)
in (FStar_Tactics_Embedding.embed_proofstate uu____2564 ps'))
in FStar_Pervasives_Native.Some (uu____2563)))))))))
end
| uu____2565 -> begin
(failwith "Unexpected application of set_proofstate_range")
end))
in (

let push_binder_interp = (fun psc args -> (match (args) with
| ((env_t, uu____2580))::((b, uu____2582))::[] -> begin
(

let uu____2609 = (FStar_Reflection_Embeddings.unembed_env env_t)
in (FStar_Util.bind_opt uu____2609 (fun env -> (

let uu____2615 = (FStar_Reflection_Embeddings.unembed_binder b)
in (FStar_Util.bind_opt uu____2615 (fun b1 -> (

let env1 = (FStar_TypeChecker_Env.push_binders env ((b1)::[]))
in (

let uu____2623 = (FStar_Reflection_Embeddings.embed_env env_t.FStar_Syntax_Syntax.pos env1)
in FStar_Pervasives_Native.Some (uu____2623)))))))))
end
| uu____2624 -> begin
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

let put1 = (fun rng t -> (

let uu___61_2640 = t
in {FStar_Syntax_Syntax.n = uu___61_2640.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___61_2640.FStar_Syntax_Syntax.vars}))
in (

let get1 = (fun t -> FStar_Pervasives_Native.Some (t))
in (

let uu____2647 = (

let uu____2650 = (mktac2 () () () "fail" (fun a438 a439 -> ((Obj.magic ((fun uu____2652 -> FStar_Tactics_Basic.fail))) a438 a439)) (Obj.magic (get1)) (Obj.magic (FStar_Syntax_Embeddings.unembed_string)) (Obj.magic (put1)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2653 = (

let uu____2656 = (mktac1 () () "trivial" (fun a440 -> ((Obj.magic (FStar_Tactics_Basic.trivial)) a440)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2657 = (

let uu____2660 = (

let uu____2661 = (FStar_Syntax_Embeddings.embed_option put1 FStar_Syntax_Syntax.t_unit)
in (mktac2 () () () "__trytac" (fun a441 a442 -> ((Obj.magic ((fun uu____2667 -> FStar_Tactics_Basic.trytac))) a441 a442)) (Obj.magic (get1)) (Obj.magic ((unembed_tactic_0' get1))) (Obj.magic (uu____2661)) FStar_Syntax_Syntax.t_unit))
in (

let uu____2674 = (

let uu____2677 = (mktac1 () () "intro" (fun a443 -> ((Obj.magic (FStar_Tactics_Basic.intro)) a443)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Reflection_Embeddings.embed_binder)) FStar_Reflection_Data.fstar_refl_binder)
in (

let uu____2678 = (

let uu____2681 = (

let uu____2682 = (FStar_Syntax_Embeddings.embed_tuple2 FStar_Reflection_Embeddings.embed_binder FStar_Reflection_Data.fstar_refl_binder FStar_Reflection_Embeddings.embed_binder FStar_Reflection_Data.fstar_refl_binder)
in (

let uu____2689 = (FStar_Tactics_Embedding.pair_typ FStar_Reflection_Data.fstar_refl_binder FStar_Reflection_Data.fstar_refl_binder)
in (mktac1 () () "intro_rec" (fun a444 -> ((Obj.magic (FStar_Tactics_Basic.intro_rec)) a444)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (uu____2682)) uu____2689)))
in (

let uu____2696 = (

let uu____2699 = (

let uu____2700 = (FStar_Syntax_Embeddings.unembed_list FStar_Syntax_Embeddings.unembed_norm_step)
in (mktac1 () () "norm" (fun a445 -> ((Obj.magic (FStar_Tactics_Basic.norm)) a445)) (Obj.magic (uu____2700)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit))
in (

let uu____2709 = (

let uu____2712 = (

let uu____2713 = (FStar_Syntax_Embeddings.unembed_list FStar_Syntax_Embeddings.unembed_norm_step)
in (mktac3 () () () () "norm_term_env" (fun a446 a447 a448 -> ((Obj.magic (FStar_Tactics_Basic.norm_term_env)) a446 a447 a448)) (Obj.magic (FStar_Reflection_Embeddings.unembed_env)) (Obj.magic (uu____2713)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (FStar_Reflection_Embeddings.embed_term)) FStar_Syntax_Syntax.t_term))
in (

let uu____2722 = (

let uu____2725 = (

let uu____2726 = (FStar_Syntax_Embeddings.unembed_list FStar_Syntax_Embeddings.unembed_norm_step)
in (mktac2 () () () "norm_binder_type" (fun a449 a450 -> ((Obj.magic (FStar_Tactics_Basic.norm_binder_type)) a449 a450)) (Obj.magic (uu____2726)) (Obj.magic (FStar_Reflection_Embeddings.unembed_binder)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit))
in (

let uu____2735 = (

let uu____2738 = (mktac2 () () () "rename_to" (fun a451 a452 -> ((Obj.magic (FStar_Tactics_Basic.rename_to)) a451 a452)) (Obj.magic (FStar_Reflection_Embeddings.unembed_binder)) (Obj.magic (FStar_Syntax_Embeddings.unembed_string)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2739 = (

let uu____2742 = (mktac1 () () "binder_retype" (fun a453 -> ((Obj.magic (FStar_Tactics_Basic.binder_retype)) a453)) (Obj.magic (FStar_Reflection_Embeddings.unembed_binder)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2743 = (

let uu____2746 = (mktac1 () () "revert" (fun a454 -> ((Obj.magic (FStar_Tactics_Basic.revert)) a454)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2747 = (

let uu____2750 = (mktac1 () () "clear_top" (fun a455 -> ((Obj.magic (FStar_Tactics_Basic.clear_top)) a455)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2751 = (

let uu____2754 = (mktac1 () () "clear" (fun a456 -> ((Obj.magic (FStar_Tactics_Basic.clear)) a456)) (Obj.magic (FStar_Reflection_Embeddings.unembed_binder)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2755 = (

let uu____2758 = (mktac1 () () "rewrite" (fun a457 -> ((Obj.magic (FStar_Tactics_Basic.rewrite)) a457)) (Obj.magic (FStar_Reflection_Embeddings.unembed_binder)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2759 = (

let uu____2762 = (mktac1 () () "smt" (fun a458 -> ((Obj.magic (FStar_Tactics_Basic.smt)) a458)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2763 = (

let uu____2766 = (mktac1 () () "refine_intro" (fun a459 -> ((Obj.magic (FStar_Tactics_Basic.refine_intro)) a459)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2767 = (

let uu____2770 = (mktac2 () () () "t_exact" (fun a460 a461 -> ((Obj.magic (FStar_Tactics_Basic.t_exact)) a460 a461)) (Obj.magic (FStar_Syntax_Embeddings.unembed_bool)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2771 = (

let uu____2774 = (mktac1 () () "apply" (fun a462 -> ((Obj.magic ((FStar_Tactics_Basic.apply true))) a462)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2775 = (

let uu____2778 = (mktac1 () () "apply_raw" (fun a463 -> ((Obj.magic ((FStar_Tactics_Basic.apply false))) a463)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2779 = (

let uu____2782 = (mktac1 () () "apply_lemma" (fun a464 -> ((Obj.magic (FStar_Tactics_Basic.apply_lemma)) a464)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2783 = (

let uu____2786 = (

let uu____2787 = (FStar_Syntax_Embeddings.embed_tuple2 put1 FStar_Syntax_Syntax.t_unit put1 FStar_Syntax_Syntax.t_unit)
in (mktac5 () () () () () () "__divide" (fun a465 a466 a467 a468 a469 -> ((Obj.magic ((fun uu____2796 uu____2797 -> FStar_Tactics_Basic.divide))) a465 a466 a467 a468 a469)) (Obj.magic (get1)) (Obj.magic (get1)) (Obj.magic (FStar_Syntax_Embeddings.unembed_int)) (Obj.magic ((unembed_tactic_0' get1))) (Obj.magic ((unembed_tactic_0' get1))) (Obj.magic (uu____2787)) FStar_Syntax_Syntax.t_unit))
in (

let uu____2804 = (

let uu____2807 = (mktac2 () () () "__seq" (fun a470 a471 -> ((Obj.magic (FStar_Tactics_Basic.seq)) a470 a471)) (Obj.magic ((unembed_tactic_0' FStar_Syntax_Embeddings.unembed_unit))) (Obj.magic ((unembed_tactic_0' FStar_Syntax_Embeddings.unembed_unit))) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2808 = (

let uu____2811 = (mktac1 () () "set_options" (fun a472 -> ((Obj.magic (FStar_Tactics_Basic.set_options)) a472)) (Obj.magic (FStar_Syntax_Embeddings.unembed_string)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2812 = (

let uu____2815 = (mktac1 () () "tc" (fun a473 -> ((Obj.magic (FStar_Tactics_Basic.tc)) a473)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (FStar_Reflection_Embeddings.embed_term)) FStar_Syntax_Syntax.t_term)
in (

let uu____2816 = (

let uu____2819 = (mktac1 () () "unshelve" (fun a474 -> ((Obj.magic (FStar_Tactics_Basic.unshelve)) a474)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2820 = (

let uu____2823 = (mktac2 () () () "unquote" (fun a475 a476 -> ((Obj.magic (FStar_Tactics_Basic.unquote)) a475 a476)) (Obj.magic (get1)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (put1)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2824 = (

let uu____2827 = (mktac1 () () "prune" (fun a477 -> ((Obj.magic (FStar_Tactics_Basic.prune)) a477)) (Obj.magic (FStar_Syntax_Embeddings.unembed_string)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2828 = (

let uu____2831 = (mktac1 () () "addns" (fun a478 -> ((Obj.magic (FStar_Tactics_Basic.addns)) a478)) (Obj.magic (FStar_Syntax_Embeddings.unembed_string)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2832 = (

let uu____2835 = (mktac1 () () "print" (fun a479 -> ((Obj.magic (FStar_Tactics_Basic.print)) a479)) (Obj.magic (FStar_Syntax_Embeddings.unembed_string)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2836 = (

let uu____2839 = (mktac1 () () "dump" (fun a480 -> ((Obj.magic (FStar_Tactics_Basic.print_proof_state)) a480)) (Obj.magic (FStar_Syntax_Embeddings.unembed_string)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2840 = (

let uu____2843 = (mktac1 () () "dump1" (fun a481 -> ((Obj.magic (FStar_Tactics_Basic.print_proof_state1)) a481)) (Obj.magic (FStar_Syntax_Embeddings.unembed_string)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2844 = (

let uu____2847 = (mktac2 () () () "__pointwise" (fun a482 a483 -> ((Obj.magic (FStar_Tactics_Basic.pointwise)) a482 a483)) (Obj.magic (FStar_Tactics_Embedding.unembed_direction)) (Obj.magic ((unembed_tactic_0' FStar_Syntax_Embeddings.unembed_unit))) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2848 = (

let uu____2851 = (

let uu____2852 = (

let uu____2863 = (FStar_Syntax_Embeddings.unembed_tuple2 FStar_Syntax_Embeddings.unembed_bool FStar_Syntax_Embeddings.unembed_int)
in (unembed_tactic_1 FStar_Reflection_Embeddings.embed_term uu____2863))
in (mktac2 () () () "__topdown_rewrite" (fun a484 a485 -> ((Obj.magic (FStar_Tactics_Basic.topdown_rewrite)) a484 a485)) (Obj.magic (uu____2852)) (Obj.magic ((unembed_tactic_0' FStar_Syntax_Embeddings.unembed_unit))) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit))
in (

let uu____2882 = (

let uu____2885 = (mktac1 () () "trefl" (fun a486 -> ((Obj.magic (FStar_Tactics_Basic.trefl)) a486)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2886 = (

let uu____2889 = (mktac1 () () "later" (fun a487 -> ((Obj.magic (FStar_Tactics_Basic.later)) a487)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2890 = (

let uu____2893 = (mktac1 () () "dup" (fun a488 -> ((Obj.magic (FStar_Tactics_Basic.dup)) a488)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2894 = (

let uu____2897 = (mktac1 () () "flip" (fun a489 -> ((Obj.magic (FStar_Tactics_Basic.flip)) a489)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2898 = (

let uu____2901 = (mktac1 () () "qed" (fun a490 -> ((Obj.magic (FStar_Tactics_Basic.qed)) a490)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2902 = (

let uu____2905 = (mktac1 () () "dismiss" (fun a491 -> ((Obj.magic (FStar_Tactics_Basic.dismiss)) a491)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2906 = (

let uu____2909 = (mktac1 () () "tadmit" (fun a492 -> ((Obj.magic (FStar_Tactics_Basic.tadmit)) a492)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2910 = (

let uu____2913 = (

let uu____2914 = (FStar_Syntax_Embeddings.embed_tuple2 FStar_Reflection_Embeddings.embed_term FStar_Syntax_Syntax.t_term FStar_Reflection_Embeddings.embed_term FStar_Syntax_Syntax.t_term)
in (

let uu____2921 = (FStar_Tactics_Embedding.pair_typ FStar_Syntax_Syntax.t_term FStar_Syntax_Syntax.t_term)
in (mktac1 () () "cases" (fun a493 -> ((Obj.magic (FStar_Tactics_Basic.cases)) a493)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (uu____2914)) uu____2921)))
in (

let uu____2928 = (

let uu____2931 = (mktac1 () () "top_env" (fun a494 -> ((Obj.magic (FStar_Tactics_Basic.top_env)) a494)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Reflection_Embeddings.embed_env)) FStar_Reflection_Data.fstar_refl_env)
in (

let uu____2932 = (

let uu____2935 = (mktac1 () () "cur_env" (fun a495 -> ((Obj.magic (FStar_Tactics_Basic.cur_env)) a495)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Reflection_Embeddings.embed_env)) FStar_Reflection_Data.fstar_refl_env)
in (

let uu____2936 = (

let uu____2939 = (mktac1 () () "cur_goal" (fun a496 -> ((Obj.magic (FStar_Tactics_Basic.cur_goal')) a496)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Reflection_Embeddings.embed_term)) FStar_Syntax_Syntax.t_term)
in (

let uu____2940 = (

let uu____2943 = (mktac1 () () "cur_witness" (fun a497 -> ((Obj.magic (FStar_Tactics_Basic.cur_witness)) a497)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Reflection_Embeddings.embed_term)) FStar_Syntax_Syntax.t_term)
in (

let uu____2944 = (

let uu____2947 = (mktac1 () () "inspect" (fun a498 -> ((Obj.magic (FStar_Tactics_Basic.inspect)) a498)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (FStar_Reflection_Embeddings.embed_term_view)) FStar_Reflection_Data.fstar_refl_term_view)
in (

let uu____2948 = (

let uu____2951 = (mktac1 () () "pack" (fun a499 -> ((Obj.magic (FStar_Tactics_Basic.pack)) a499)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term_view)) (Obj.magic (FStar_Reflection_Embeddings.embed_term)) FStar_Syntax_Syntax.t_term)
in (

let uu____2952 = (

let uu____2955 = (mktac1 () () "fresh" (fun a500 -> ((Obj.magic (FStar_Tactics_Basic.fresh)) a500)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_int)) FStar_Syntax_Syntax.t_int)
in (

let uu____2956 = (

let uu____2959 = (mktac1 () () "ngoals" (fun a501 -> ((Obj.magic (FStar_Tactics_Basic.ngoals)) a501)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_int)) FStar_Syntax_Syntax.t_int)
in (

let uu____2960 = (

let uu____2963 = (mktac1 () () "ngoals_smt" (fun a502 -> ((Obj.magic (FStar_Tactics_Basic.ngoals_smt)) a502)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_int)) FStar_Syntax_Syntax.t_int)
in (

let uu____2964 = (

let uu____2967 = (mktac1 () () "is_guard" (fun a503 -> ((Obj.magic (FStar_Tactics_Basic.is_guard)) a503)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Syntax_Embeddings.embed_bool)) FStar_Syntax_Syntax.t_bool)
in (

let uu____2968 = (

let uu____2971 = (

let uu____2972 = (FStar_Syntax_Embeddings.unembed_option FStar_Reflection_Embeddings.unembed_term)
in (mktac2 () () () "uvar_env" (fun a504 a505 -> ((Obj.magic (FStar_Tactics_Basic.uvar_env)) a504 a505)) (Obj.magic (FStar_Reflection_Embeddings.unembed_env)) (Obj.magic (uu____2972)) (Obj.magic (FStar_Reflection_Embeddings.embed_term)) FStar_Syntax_Syntax.t_term))
in (

let uu____2981 = (

let uu____2984 = (mktac2 () () () "unify" (fun a506 a507 -> ((Obj.magic (FStar_Tactics_Basic.unify)) a506 a507)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (FStar_Syntax_Embeddings.embed_bool)) FStar_Syntax_Syntax.t_bool)
in (

let uu____2985 = (

let uu____2988 = (mktac3 () () () () "launch_process" (fun a508 a509 a510 -> ((Obj.magic (FStar_Tactics_Basic.launch_process)) a508 a509 a510)) (Obj.magic (FStar_Syntax_Embeddings.unembed_string)) (Obj.magic (FStar_Syntax_Embeddings.unembed_string)) (Obj.magic (FStar_Syntax_Embeddings.unembed_string)) (Obj.magic (FStar_Syntax_Embeddings.embed_string)) FStar_Syntax_Syntax.t_string)
in (

let uu____2989 = (

let uu____2992 = (mktac2 () () () "fresh_bv_named" (fun a511 a512 -> ((Obj.magic (FStar_Tactics_Basic.fresh_bv_named)) a511 a512)) (Obj.magic (FStar_Syntax_Embeddings.unembed_string)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (FStar_Reflection_Embeddings.embed_bv)) FStar_Syntax_Syntax.t_bv)
in (

let uu____2993 = (

let uu____2996 = (mktac1 () () "change" (fun a513 -> ((Obj.magic (FStar_Tactics_Basic.change)) a513)) (Obj.magic (FStar_Reflection_Embeddings.unembed_term)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (

let uu____2997 = (

let uu____3000 = (mktac1 () () "get_guard_policy" (fun a514 -> ((Obj.magic (FStar_Tactics_Basic.get_guard_policy)) a514)) (Obj.magic (FStar_Syntax_Embeddings.unembed_unit)) (Obj.magic (FStar_Tactics_Embedding.embed_guard_policy)) FStar_Tactics_Embedding.t_guard_policy)
in (

let uu____3001 = (

let uu____3004 = (mktac1 () () "set_guard_policy" (fun a515 -> ((Obj.magic (FStar_Tactics_Basic.set_guard_policy)) a515)) (Obj.magic (FStar_Tactics_Embedding.unembed_guard_policy)) (Obj.magic (FStar_Syntax_Embeddings.embed_unit)) FStar_Syntax_Syntax.t_unit)
in (uu____3004)::(decr_depth_step)::(incr_depth_step)::(tracepoint_step)::(set_proofstate_range_step)::(push_binder_step)::[])
in (uu____3000)::uu____3001))
in (uu____2996)::uu____2997))
in (uu____2992)::uu____2993))
in (uu____2988)::uu____2989))
in (uu____2984)::uu____2985))
in (uu____2971)::uu____2981))
in (uu____2967)::uu____2968))
in (uu____2963)::uu____2964))
in (uu____2959)::uu____2960))
in (uu____2955)::uu____2956))
in (uu____2951)::uu____2952))
in (uu____2947)::uu____2948))
in (uu____2943)::uu____2944))
in (uu____2939)::uu____2940))
in (uu____2935)::uu____2936))
in (uu____2931)::uu____2932))
in (uu____2913)::uu____2928))
in (uu____2909)::uu____2910))
in (uu____2905)::uu____2906))
in (uu____2901)::uu____2902))
in (uu____2897)::uu____2898))
in (uu____2893)::uu____2894))
in (uu____2889)::uu____2890))
in (uu____2885)::uu____2886))
in (uu____2851)::uu____2882))
in (uu____2847)::uu____2848))
in (uu____2843)::uu____2844))
in (uu____2839)::uu____2840))
in (uu____2835)::uu____2836))
in (uu____2831)::uu____2832))
in (uu____2827)::uu____2828))
in (uu____2823)::uu____2824))
in (uu____2819)::uu____2820))
in (uu____2815)::uu____2816))
in (uu____2811)::uu____2812))
in (uu____2807)::uu____2808))
in (uu____2786)::uu____2804))
in (uu____2782)::uu____2783))
in (uu____2778)::uu____2779))
in (uu____2774)::uu____2775))
in (uu____2770)::uu____2771))
in (uu____2766)::uu____2767))
in (uu____2762)::uu____2763))
in (uu____2758)::uu____2759))
in (uu____2754)::uu____2755))
in (uu____2750)::uu____2751))
in (uu____2746)::uu____2747))
in (uu____2742)::uu____2743))
in (uu____2738)::uu____2739))
in (uu____2725)::uu____2735))
in (uu____2712)::uu____2722))
in (uu____2699)::uu____2709))
in (uu____2681)::uu____2696))
in (uu____2677)::uu____2678))
in (uu____2660)::uu____2674))
in (uu____2656)::uu____2657))
in (uu____2650)::uu____2653))
in (FStar_List.append uu____2647 (FStar_List.append FStar_Reflection_Interpreter.reflection_primops native_tactics_steps)))))))))))))))))))))))
and unembed_tactic_1 : 'Aa 'Ab . 'Aa FStar_Syntax_Embeddings.embedder  ->  'Ab FStar_Syntax_Embeddings.unembedder  ->  FStar_Syntax_Syntax.term  ->  ('Aa  ->  'Ab FStar_Tactics_Basic.tac) FStar_Pervasives_Native.option = (fun arg res f -> FStar_Pervasives_Native.Some ((fun x -> (

let rng = FStar_Range.dummyRange
in (

let x_tm = (arg rng x)
in (

let app = (

let uu____3034 = (

let uu____3035 = (

let uu____3036 = (FStar_Syntax_Syntax.as_arg x_tm)
in (uu____3036)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f uu____3035))
in (uu____3034 FStar_Pervasives_Native.None rng))
in (unembed_tactic_0 res app)))))))
and unembed_tactic_0 : 'Ab . 'Ab FStar_Syntax_Embeddings.unembedder  ->  FStar_Syntax_Syntax.term  ->  'Ab FStar_Tactics_Basic.tac = (fun unembed_b embedded_tac_b -> (FStar_Tactics_Basic.bind FStar_Tactics_Basic.get (fun proof_state -> (

let rng = embedded_tac_b.FStar_Syntax_Syntax.pos
in (

let tm = (

let uu____3065 = (

let uu____3066 = (

let uu____3067 = (

let uu____3068 = (FStar_Tactics_Embedding.embed_proofstate rng proof_state)
in (FStar_Syntax_Syntax.as_arg uu____3068))
in (uu____3067)::[])
in (FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____3066))
in (uu____3065 FStar_Pervasives_Native.None rng))
in (

let steps = (FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Unascribe)::[]
in ((

let uu____3075 = (FStar_TypeChecker_Env.debug proof_state.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacVerbose")))
in (match (uu____3075) with
| true -> begin
(

let uu____3076 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Starting normalizer with %s\n" uu____3076))
end
| uu____3077 -> begin
()
end));
(

let result = (

let uu____3079 = (primitive_steps ())
in (FStar_TypeChecker_Normalize.normalize_with_primitive_steps uu____3079 steps proof_state.FStar_Tactics_Types.main_context tm))
in ((

let uu____3083 = (FStar_TypeChecker_Env.debug proof_state.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacVerbose")))
in (match (uu____3083) with
| true -> begin
(

let uu____3084 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print1 "Reduced tactic: got %s\n" uu____3084))
end
| uu____3085 -> begin
()
end));
(

let res = (FStar_Tactics_Embedding.unembed_result result unembed_b)
in (match (res) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (b, ps)) -> begin
(

let uu____3129 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____3129 (fun uu____3133 -> (FStar_Tactics_Basic.ret b))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (msg, ps)) -> begin
(

let uu____3156 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____3156 (fun uu____3160 -> (FStar_Tactics_Basic.fail msg))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3173 = (

let uu____3178 = (

let uu____3179 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.format1 "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s" uu____3179))
in ((FStar_Errors.Fatal_TacticGotStuck), (uu____3178)))
in (FStar_Errors.raise_error uu____3173 proof_state.FStar_Tactics_Types.main_context.FStar_TypeChecker_Env.range))
end));
));
)))))))
and unembed_tactic_0' : 'Ab . 'Ab FStar_Syntax_Embeddings.unembedder  ->  FStar_Syntax_Syntax.term  ->  'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option = (fun unembed_b embedded_tac_b -> (

let uu____3188 = (unembed_tactic_0 unembed_b embedded_tac_b)
in (FStar_All.pipe_left (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40)) uu____3188)))


let report_implicits : FStar_Tactics_Types.proofstate  ->  FStar_TypeChecker_Env.implicits  ->  Prims.unit = (fun ps is -> (

let errs = (FStar_List.map (fun uu____3244 -> (match (uu____3244) with
| (r, uu____3264, uv, uu____3266, ty, rng) -> begin
(

let uu____3269 = (

let uu____3270 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____3271 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.format3 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")" uu____3270 uu____3271 r)))
in ((FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic), (uu____3269), (rng)))
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

let uu____3320 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3320) with
| true -> begin
(

let uu____3346 = (FStar_Syntax_Print.term_to_string tactic)
in (FStar_Util.print1 "About to reduce uvars on: %s\n" uu____3346))
end
| uu____3347 -> begin
()
end));
(

let tactic1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic)
in ((

let uu____3350 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3350) with
| true -> begin
(

let uu____3376 = (FStar_Syntax_Print.term_to_string tactic1)
in (FStar_Util.print1 "About to check tactic term: %s\n" uu____3376))
end
| uu____3377 -> begin
()
end));
(

let uu____3378 = (FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1)
in (match (uu____3378) with
| (uu____3391, uu____3392, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
(FStar_Errors.stop_if_err ());
(

let tau = (unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic1)
in (

let uu____3399 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____3399) with
| (env1, uu____3413) -> begin
(

let env2 = (

let uu___62_3419 = env1
in {FStar_TypeChecker_Env.solver = uu___62_3419.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___62_3419.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___62_3419.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___62_3419.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___62_3419.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___62_3419.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___62_3419.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___62_3419.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___62_3419.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___62_3419.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___62_3419.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___62_3419.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___62_3419.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___62_3419.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___62_3419.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___62_3419.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___62_3419.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___62_3419.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___62_3419.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___62_3419.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___62_3419.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___62_3419.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___62_3419.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___62_3419.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___62_3419.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___62_3419.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___62_3419.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___62_3419.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___62_3419.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___62_3419.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___62_3419.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___62_3419.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___62_3419.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___62_3419.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___62_3419.FStar_TypeChecker_Env.dep_graph})
in (

let env3 = (

let uu___63_3421 = env2
in {FStar_TypeChecker_Env.solver = uu___63_3421.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___63_3421.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___63_3421.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___63_3421.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___63_3421.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___63_3421.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___63_3421.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___63_3421.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___63_3421.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___63_3421.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___63_3421.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___63_3421.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___63_3421.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___63_3421.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___63_3421.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___63_3421.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___63_3421.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___63_3421.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___63_3421.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.failhard = uu___63_3421.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___63_3421.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___63_3421.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___63_3421.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___63_3421.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___63_3421.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___63_3421.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___63_3421.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___63_3421.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___63_3421.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___63_3421.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___63_3421.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___63_3421.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___63_3421.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___63_3421.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___63_3421.FStar_TypeChecker_Env.dep_graph})
in (

let uu____3422 = (FStar_Tactics_Basic.proofstate_of_goal_ty env3 typ)
in (match (uu____3422) with
| (ps, w) -> begin
((

let uu____3436 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3436) with
| true -> begin
(

let uu____3462 = (FStar_Syntax_Print.term_to_string typ)
in (FStar_Util.print1 "Running tactic with goal = %s\n" uu____3462))
end
| uu____3463 -> begin
()
end));
(

let uu____3464 = (FStar_Util.record_time (fun uu____3474 -> (FStar_Tactics_Basic.run tau ps)))
in (match (uu____3464) with
| (res, ms) -> begin
((

let uu____3488 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3488) with
| true -> begin
(

let uu____3514 = (FStar_Syntax_Print.term_to_string tactic1)
in (

let uu____3515 = (FStar_Util.string_of_int ms)
in (

let uu____3516 = (FStar_Syntax_Print.lid_to_string env3.FStar_TypeChecker_Env.curmodule)
in (FStar_Util.print3 "Tactic %s ran in %s ms (%s)\n" uu____3514 uu____3515 uu____3516))))
end
| uu____3517 -> begin
()
end));
(match (res) with
| FStar_Tactics_Result.Success (uu____3524, ps1) -> begin
((

let uu____3527 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3527) with
| true -> begin
(

let uu____3553 = (FStar_Syntax_Print.term_to_string w)
in (FStar_Util.print1 "Tactic generated proofterm %s\n" uu____3553))
end
| uu____3554 -> begin
()
end));
(FStar_List.iter (fun g1 -> (

let uu____3560 = (FStar_Tactics_Basic.is_irrelevant g1)
in (match (uu____3560) with
| true -> begin
(

let uu____3561 = (FStar_TypeChecker_Rel.teq_nosmt g1.FStar_Tactics_Types.context g1.FStar_Tactics_Types.witness FStar_Syntax_Util.exp_unit)
in (match (uu____3561) with
| true -> begin
()
end
| uu____3562 -> begin
(

let uu____3563 = (

let uu____3564 = (FStar_Syntax_Print.term_to_string g1.FStar_Tactics_Types.witness)
in (FStar_Util.format1 "Irrelevant tactic witness does not unify with (): %s" uu____3564))
in (failwith uu____3563))
end))
end
| uu____3565 -> begin
()
end))) (FStar_List.append ps1.FStar_Tactics_Types.goals ps1.FStar_Tactics_Types.smt_goals));
(

let g1 = (

let uu___64_3567 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___64_3567.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___64_3567.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___64_3567.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = ps1.FStar_Tactics_Types.all_implicits})
in (

let g2 = (

let uu____3569 = (FStar_TypeChecker_Rel.solve_deferred_constraints env3 g1)
in (FStar_All.pipe_right uu____3569 FStar_TypeChecker_Rel.resolve_implicits_tac))
in ((report_implicits ps1 g2.FStar_TypeChecker_Env.implicits);
(((FStar_List.append ps1.FStar_Tactics_Types.goals ps1.FStar_Tactics_Types.smt_goals)), (w));
)));
)
end
| FStar_Tactics_Result.Failed (s, ps1) -> begin
((

let uu____3576 = (

let uu____3577 = (FStar_TypeChecker_Normalize.psc_subst ps1.FStar_Tactics_Types.psc)
in (FStar_Tactics_Types.subst_proof_state uu____3577 ps1))
in (FStar_Tactics_Basic.dump_proofstate uu____3576 "at the time of failure"));
(

let uu____3578 = (

let uu____3583 = (FStar_Util.format1 "user tactic failed: %s" s)
in ((FStar_Errors.Fatal_ArgumentLengthMismatch), (uu____3583)))
in (FStar_Errors.raise_error uu____3578 typ.FStar_Syntax_Syntax.pos));
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
| uu____3593 -> begin
false
end))


let uu___is_Neg : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neg -> begin
true
end
| uu____3597 -> begin
false
end))


let uu___is_Both : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Both -> begin
true
end
| uu____3601 -> begin
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
| uu____3650 -> begin
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
| uu____3686 -> begin
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
| uu____3736 -> begin
false
end))


let __proj__Dual__item___0 : 'a . 'a tres_m  ->  ('a * 'a * FStar_Tactics_Basic.goal Prims.list) = (fun projectee -> (match (projectee) with
| Dual (_0) -> begin
_0
end))


type tres =
FStar_Syntax_Syntax.term tres_m


let tpure : 'Auu____3774 . 'Auu____3774  ->  'Auu____3774 tres_m = (fun x -> Unchanged (x))


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

let uu____3793 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3793) with
| (hd1, args) -> begin
(

let uu____3830 = (

let uu____3843 = (

let uu____3844 = (FStar_Syntax_Util.un_uinst hd1)
in uu____3844.FStar_Syntax_Syntax.n)
in ((uu____3843), (args)))
in (match (uu____3830) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((rett, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____3857))))::((tactic, FStar_Pervasives_Native.None))::((assertion, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid) -> begin
(match (pol) with
| Pos -> begin
(

let uu____3920 = (run_tactic_on_typ tactic e assertion)
in (match (uu____3920) with
| (gs, uu____3928) -> begin
Simplified (((FStar_Syntax_Util.t_true), (gs)))
end))
end
| Both -> begin
(

let uu____3935 = (run_tactic_on_typ tactic e assertion)
in (match (uu____3935) with
| (gs, uu____3943) -> begin
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

let uu____3994 = (

let uu____4001 = (

let uu____4004 = (

let uu____4005 = (FStar_Tactics_Basic.goal_of_goal_ty e assertion)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4005))
in (uu____4004)::[])
in ((FStar_Syntax_Util.t_true), (uu____4001)))
in Simplified (uu____3994))
end
| Both -> begin
(

let uu____4016 = (

let uu____4029 = (

let uu____4032 = (

let uu____4033 = (FStar_Tactics_Basic.goal_of_goal_ty e assertion)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4033))
in (uu____4032)::[])
in ((assertion), (FStar_Syntax_Util.t_true), (uu____4029)))
in Dual (uu____4016))
end
| Neg -> begin
Simplified (((assertion), ([])))
end)
end
| uu____4054 -> begin
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


let comb1 : 'a 'b . ('a  ->  'b)  ->  'a tres_m  ->  'b tres_m = (fun f uu___60_4134 -> (match (uu___60_4134) with
| Unchanged (t) -> begin
(

let uu____4140 = (f t)
in Unchanged (uu____4140))
end
| Simplified (t, gs) -> begin
(

let uu____4147 = (

let uu____4154 = (f t)
in ((uu____4154), (gs)))
in Simplified (uu____4147))
end
| Dual (tn, tp, gs) -> begin
(

let uu____4164 = (

let uu____4173 = (f tn)
in (

let uu____4174 = (f tp)
in ((uu____4173), (uu____4174), (gs))))
in Dual (uu____4164))
end))


let comb2 : 'a 'b 'c . ('a  ->  'b  ->  'c)  ->  'a tres_m  ->  'b tres_m  ->  'c tres_m = (fun f x y -> (match (((x), (y))) with
| (Unchanged (t1), Unchanged (t2)) -> begin
(

let uu____4228 = (f t1 t2)
in Unchanged (uu____4228))
end
| (Unchanged (t1), Simplified (t2, gs)) -> begin
(

let uu____4240 = (

let uu____4247 = (f t1 t2)
in ((uu____4247), (gs)))
in Simplified (uu____4240))
end
| (Simplified (t1, gs), Unchanged (t2)) -> begin
(

let uu____4261 = (

let uu____4268 = (f t1 t2)
in ((uu____4268), (gs)))
in Simplified (uu____4261))
end
| (Simplified (t1, gs1), Simplified (t2, gs2)) -> begin
(

let uu____4287 = (

let uu____4294 = (f t1 t2)
in ((uu____4294), ((FStar_List.append gs1 gs2))))
in Simplified (uu____4287))
end
| uu____4297 -> begin
(

let uu____4306 = (explode x)
in (match (uu____4306) with
| (n1, p1, gs1) -> begin
(

let uu____4324 = (explode y)
in (match (uu____4324) with
| (n2, p2, gs2) -> begin
(

let uu____4342 = (

let uu____4351 = (f n1 n2)
in (

let uu____4352 = (f p1 p2)
in ((uu____4351), (uu____4352), ((FStar_List.append gs1 gs2)))))
in Dual (uu____4342))
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

let uu____4417 = (comb2 (fun l r -> (l)::r) hd1 acc)
in (aux tl1 uu____4417))
end))
in (aux (FStar_List.rev rs) (tpure []))))


let emit : 'a . FStar_Tactics_Basic.goal Prims.list  ->  'a tres_m  ->  'a tres_m = (fun gs m -> (comb2 (fun uu____4460 x -> x) (Simplified (((()), (gs)))) m))


let rec traverse : (pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  tres)  ->  pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  tres = (fun f pol e t -> (

let r = (

let uu____4494 = (

let uu____4495 = (FStar_Syntax_Subst.compress t)
in uu____4495.FStar_Syntax_Syntax.n)
in (match (uu____4494) with
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let tr = (traverse f pol e t1)
in (

let uu____4507 = (comb1 (fun t' -> FStar_Syntax_Syntax.Tm_uinst (((t'), (us)))))
in (uu____4507 tr)))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let tr = (traverse f pol e t1)
in (

let uu____4531 = (comb1 (fun t' -> FStar_Syntax_Syntax.Tm_meta (((t'), (m)))))
in (uu____4531 tr)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____4549; FStar_Syntax_Syntax.vars = uu____4550}, ((p, uu____4552))::((q, uu____4554))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid) -> begin
(

let x = (

let uu____4594 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____4594))
in (

let r1 = (traverse f (flip pol) e p)
in (

let r2 = (

let uu____4597 = (FStar_TypeChecker_Env.push_bv e x)
in (traverse f pol uu____4597 q))
in (comb2 (fun l r -> (

let uu____4603 = (FStar_Syntax_Util.mk_imp l r)
in uu____4603.FStar_Syntax_Syntax.n)) r1 r2))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____4607; FStar_Syntax_Syntax.vars = uu____4608}, ((p, uu____4610))::((q, uu____4612))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid) -> begin
(

let xp = (

let uu____4652 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____4652))
in (

let xq = (

let uu____4654 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____4654))
in (

let r1 = (

let uu____4656 = (FStar_TypeChecker_Env.push_bv e xq)
in (traverse f Both uu____4656 p))
in (

let r2 = (

let uu____4658 = (FStar_TypeChecker_Env.push_bv e xp)
in (traverse f Both uu____4658 q))
in (match (((r1), (r2))) with
| (Unchanged (uu____4661), Unchanged (uu____4662)) -> begin
(comb2 (fun l r -> (

let uu____4672 = (FStar_Syntax_Util.mk_iff l r)
in uu____4672.FStar_Syntax_Syntax.n)) r1 r2)
end
| uu____4675 -> begin
(

let uu____4680 = (explode r1)
in (match (uu____4680) with
| (pn, pp, gs1) -> begin
(

let uu____4698 = (explode r2)
in (match (uu____4698) with
| (qn, qp, gs2) -> begin
(

let t1 = (

let uu____4719 = (FStar_Syntax_Util.mk_imp pn qp)
in (

let uu____4720 = (FStar_Syntax_Util.mk_imp qn pp)
in (FStar_Syntax_Util.mk_conj uu____4719 uu____4720)))
in Simplified (((t1.FStar_Syntax_Syntax.n), ((FStar_List.append gs1 gs2)))))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let r0 = (traverse f pol e hd1)
in (

let r1 = (FStar_List.fold_right (fun uu____4772 r -> (match (uu____4772) with
| (a, q) -> begin
(

let r' = (traverse f pol e a)
in (comb2 (fun a1 args1 -> (((a1), (q)))::args1) r' r))
end)) args (tpure []))
in (comb2 (fun hd2 args1 -> FStar_Syntax_Syntax.Tm_app (((hd2), (args1)))) r0 r1)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____4890 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____4890) with
| (bs1, topen) -> begin
(

let e' = (FStar_TypeChecker_Env.push_binders e bs1)
in (

let r0 = (FStar_List.map (fun uu____4924 -> (match (uu____4924) with
| (bv, aq) -> begin
(

let r = (traverse f (flip pol) e bv.FStar_Syntax_Syntax.sort)
in (

let uu____4938 = (comb1 (fun s' -> (((

let uu___65_4962 = bv
in {FStar_Syntax_Syntax.ppname = uu___65_4962.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___65_4962.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s'})), (aq))))
in (uu____4938 r)))
end)) bs1)
in (

let rbs = (comb_list r0)
in (

let rt = (traverse f pol e' topen)
in (comb2 (fun bs2 t2 -> (

let uu____4982 = (FStar_Syntax_Util.abs bs2 t2 k)
in uu____4982.FStar_Syntax_Syntax.n)) rbs rt)))))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, ef) -> begin
(

let uu____5028 = (traverse f pol e t1)
in (

let uu____5033 = (comb1 (fun t2 -> FStar_Syntax_Syntax.Tm_ascribed (((t2), (asc), (ef)))))
in (uu____5033 uu____5028)))
end
| x -> begin
(tpure x)
end))
in (match (r) with
| Unchanged (tn') -> begin
(f pol e (

let uu___66_5071 = t
in {FStar_Syntax_Syntax.n = tn'; FStar_Syntax_Syntax.pos = uu___66_5071.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___66_5071.FStar_Syntax_Syntax.vars}))
end
| Simplified (tn', gs) -> begin
(

let uu____5078 = (f pol e (

let uu___67_5082 = t
in {FStar_Syntax_Syntax.n = tn'; FStar_Syntax_Syntax.pos = uu___67_5082.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___67_5082.FStar_Syntax_Syntax.vars}))
in (emit gs uu____5078))
end
| Dual (tn, tp, gs) -> begin
(

let rp = (f pol e (

let uu___68_5092 = t
in {FStar_Syntax_Syntax.n = tp; FStar_Syntax_Syntax.pos = uu___68_5092.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___68_5092.FStar_Syntax_Syntax.vars}))
in (

let uu____5093 = (explode rp)
in (match (uu____5093) with
| (uu____5102, p', gs') -> begin
Dual ((((

let uu___69_5116 = t
in {FStar_Syntax_Syntax.n = tn; FStar_Syntax_Syntax.pos = uu___69_5116.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___69_5116.FStar_Syntax_Syntax.vars})), (p'), ((FStar_List.append gs gs'))))
end)))
end)))


let getprop : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun e t -> (

let tn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) e t)
in (FStar_Syntax_Util.un_squash tn)))


let preprocess : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term * FStar_Options.optionstate) Prims.list = (fun env goal -> ((

let uu____5151 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____5151));
(

let uu____5178 = (FStar_ST.op_Bang tacdbg)
in (match (uu____5178) with
| true -> begin
(

let uu____5204 = (

let uu____5205 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____5205 (FStar_Syntax_Print.binders_to_string ",")))
in (

let uu____5206 = (FStar_Syntax_Print.term_to_string goal)
in (FStar_Util.print2 "About to preprocess %s |= %s\n" uu____5204 uu____5206)))
end
| uu____5207 -> begin
()
end));
(

let initial = (((Prims.parse_int "1")), ([]))
in (

let uu____5235 = (

let uu____5242 = (traverse by_tactic_interp Pos env goal)
in (match (uu____5242) with
| Unchanged (t') -> begin
((t'), ([]))
end
| Simplified (t', gs) -> begin
((t'), (gs))
end
| uu____5260 -> begin
(failwith "no")
end))
in (match (uu____5235) with
| (t', gs) -> begin
((

let uu____5282 = (FStar_ST.op_Bang tacdbg)
in (match (uu____5282) with
| true -> begin
(

let uu____5308 = (

let uu____5309 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____5309 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let uu____5310 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Main goal simplified to: %s |- %s\n" uu____5308 uu____5310)))
end
| uu____5311 -> begin
()
end));
(

let s = initial
in (

let s1 = (FStar_List.fold_left (fun uu____5357 g -> (match (uu____5357) with
| (n1, gs1) -> begin
(

let phi = (

let uu____5402 = (getprop g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (match (uu____5402) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5405 = (

let uu____5410 = (

let uu____5411 = (FStar_Syntax_Print.term_to_string g.FStar_Tactics_Types.goal_ty)
in (FStar_Util.format1 "Tactic returned proof-relevant goal: %s" uu____5411))
in ((FStar_Errors.Fatal_TacticProofRelevantGoal), (uu____5410)))
in (FStar_Errors.raise_error uu____5405 env.FStar_TypeChecker_Env.range))
end
| FStar_Pervasives_Native.Some (phi) -> begin
phi
end))
in ((

let uu____5414 = (FStar_ST.op_Bang tacdbg)
in (match (uu____5414) with
| true -> begin
(

let uu____5440 = (FStar_Util.string_of_int n1)
in (

let uu____5441 = (FStar_Tactics_Basic.goal_to_string g)
in (FStar_Util.print2 "Got goal #%s: %s\n" uu____5440 uu____5441)))
end
| uu____5442 -> begin
()
end));
(

let gt' = (

let uu____5444 = (

let uu____5445 = (FStar_Util.string_of_int n1)
in (Prims.strcat "Could not prove goal #" uu____5445))
in (FStar_TypeChecker_Util.label uu____5444 goal.FStar_Syntax_Syntax.pos phi))
in (((n1 + (Prims.parse_int "1"))), ((((g.FStar_Tactics_Types.context), (gt'), (g.FStar_Tactics_Types.opts)))::gs1)));
))
end)) s gs)
in (

let uu____5460 = s1
in (match (uu____5460) with
| (uu____5481, gs1) -> begin
(

let uu____5499 = (

let uu____5506 = (FStar_Options.peek ())
in ((env), (t'), (uu____5506)))
in (uu____5499)::gs1)
end))));
)
end)));
))


let reify_tactic : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun a -> (

let r = (

let uu____5517 = (

let uu____5518 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____5518))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5517 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____5519 = (

let uu____5520 = (

let uu____5521 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____5522 = (

let uu____5525 = (FStar_Syntax_Syntax.as_arg a)
in (uu____5525)::[])
in (uu____5521)::uu____5522))
in (FStar_Syntax_Syntax.mk_Tm_app r uu____5520))
in (uu____5519 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos))))


let synthesize : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env typ tau -> ((

let uu____5538 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____5538));
(

let uu____5564 = (

let uu____5571 = (reify_tactic tau)
in (run_tactic_on_typ uu____5571 env typ))
in (match (uu____5564) with
| (gs, w) -> begin
(

let uu____5578 = (FStar_List.existsML (fun g -> (

let uu____5582 = (

let uu____5583 = (getprop g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Option.isSome uu____5583))
in (not (uu____5582)))) gs)
in (match (uu____5578) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_OpenGoalsInSynthesis), ("synthesis left open goals")) typ.FStar_Syntax_Syntax.pos)
end
| uu____5586 -> begin
w
end))
end));
))


let splice : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env tau -> ((

let uu____5598 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____5598));
(

let typ = FStar_Syntax_Syntax.t_decls
in (

let uu____5625 = (

let uu____5632 = (reify_tactic tau)
in (run_tactic_on_typ uu____5632 env typ))
in (match (uu____5625) with
| (gs, w) -> begin
((

let uu____5642 = (FStar_List.existsML (fun g -> (

let uu____5646 = (

let uu____5647 = (getprop g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Option.isSome uu____5647))
in (not (uu____5646)))) gs)
in (match (uu____5642) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_OpenGoalsInSynthesis), ("splice left open goals")) typ.FStar_Syntax_Syntax.pos)
end
| uu____5650 -> begin
()
end));
(

let w1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Unascribe)::(FStar_TypeChecker_Normalize.Unmeta)::[]) env w)
in (

let uu____5652 = (

let uu____5657 = (FStar_Syntax_Embeddings.unembed_list FStar_Reflection_Embeddings.unembed_sigelt)
in (uu____5657 w1))
in (FStar_All.pipe_left FStar_Util.must uu____5652)));
)
end)));
))




