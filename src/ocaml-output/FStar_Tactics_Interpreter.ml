
open Prims
open FStar_Pervasives

let tacdbg : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let mk_tactic_interpretation_0 : 'a . FStar_Tactics_Basic.proofstate  ->  'a FStar_Tactics_Basic.tac  ->  ('a  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ps t embed_a t_a nm args -> (match (args) with
| ((embedded_state, uu____55))::[] -> begin
((FStar_Tactics_Basic.log ps (fun uu____76 -> (

let uu____77 = (FStar_Ident.string_of_lid nm)
in (

let uu____78 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "Reached %s, args are: %s\n" uu____77 uu____78)))));
(

let ps1 = (FStar_Tactics_Embedding.unembed_proofstate ps embedded_state)
in (

let res = (FStar_Tactics_Basic.run t ps1)
in (

let uu____83 = (FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a)
in FStar_Pervasives_Native.Some (uu____83))));
)
end
| uu____84 -> begin
(failwith "Unexpected application of tactic primitive")
end))


let mk_tactic_interpretation_1 : 'a 'b . FStar_Tactics_Basic.proofstate  ->  ('b  ->  'a FStar_Tactics_Basic.tac)  ->  (FStar_Syntax_Syntax.term  ->  'b)  ->  ('a  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ps t unembed_b embed_a t_a nm args -> (match (args) with
| ((b, uu____157))::((embedded_state, uu____159))::[] -> begin
((FStar_Tactics_Basic.log ps (fun uu____190 -> (

let uu____191 = (FStar_Ident.string_of_lid nm)
in (

let uu____192 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____191 uu____192)))));
(

let ps1 = (FStar_Tactics_Embedding.unembed_proofstate ps embedded_state)
in (

let res = (

let uu____197 = (

let uu____200 = (unembed_b b)
in (t uu____200))
in (FStar_Tactics_Basic.run uu____197 ps1))
in (

let uu____201 = (FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a)
in FStar_Pervasives_Native.Some (uu____201))));
)
end
| uu____202 -> begin
(

let uu____203 = (

let uu____204 = (FStar_Ident.string_of_lid nm)
in (

let uu____205 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____204 uu____205)))
in (failwith uu____203))
end))


let mk_tactic_interpretation_2 : 'a 'b 'c . FStar_Tactics_Basic.proofstate  ->  ('a  ->  'b  ->  'c FStar_Tactics_Basic.tac)  ->  (FStar_Syntax_Syntax.term  ->  'a)  ->  (FStar_Syntax_Syntax.term  ->  'b)  ->  ('c  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ps t unembed_a unembed_b embed_c t_c nm args -> (match (args) with
| ((a, uu____297))::((b, uu____299))::((embedded_state, uu____301))::[] -> begin
((FStar_Tactics_Basic.log ps (fun uu____342 -> (

let uu____343 = (FStar_Ident.string_of_lid nm)
in (

let uu____344 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____343 uu____344)))));
(

let ps1 = (FStar_Tactics_Embedding.unembed_proofstate ps embedded_state)
in (

let res = (

let uu____349 = (

let uu____352 = (unembed_a a)
in (

let uu____353 = (unembed_b b)
in (t uu____352 uu____353)))
in (FStar_Tactics_Basic.run uu____349 ps1))
in (

let uu____354 = (FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c)
in FStar_Pervasives_Native.Some (uu____354))));
)
end
| uu____355 -> begin
(

let uu____356 = (

let uu____357 = (FStar_Ident.string_of_lid nm)
in (

let uu____358 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____357 uu____358)))
in (failwith uu____356))
end))


let mk_tactic_interpretation_3 : 'a 'b 'c 'd . FStar_Tactics_Basic.proofstate  ->  ('a  ->  'b  ->  'c  ->  'd FStar_Tactics_Basic.tac)  ->  (FStar_Syntax_Syntax.term  ->  'a)  ->  (FStar_Syntax_Syntax.term  ->  'b)  ->  (FStar_Syntax_Syntax.term  ->  'c)  ->  ('d  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ps t unembed_a unembed_b unembed_c embed_d t_d nm args -> (match (args) with
| ((a, uu____469))::((b, uu____471))::((c, uu____473))::((embedded_state, uu____475))::[] -> begin
((FStar_Tactics_Basic.log ps (fun uu____526 -> (

let uu____527 = (FStar_Ident.string_of_lid nm)
in (

let uu____528 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____527 uu____528)))));
(

let ps1 = (FStar_Tactics_Embedding.unembed_proofstate ps embedded_state)
in (

let res = (

let uu____533 = (

let uu____536 = (unembed_a a)
in (

let uu____537 = (unembed_b b)
in (

let uu____538 = (unembed_c c)
in (t uu____536 uu____537 uu____538))))
in (FStar_Tactics_Basic.run uu____533 ps1))
in (

let uu____539 = (FStar_Tactics_Embedding.embed_result ps1 res embed_d t_d)
in FStar_Pervasives_Native.Some (uu____539))));
)
end
| uu____540 -> begin
(

let uu____541 = (

let uu____542 = (FStar_Ident.string_of_lid nm)
in (

let uu____543 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____542 uu____543)))
in (failwith uu____541))
end))


let mk_tactic_interpretation_5 : 'a 'b 'c 'd 'e 'f . FStar_Tactics_Basic.proofstate  ->  ('a  ->  'b  ->  'c  ->  'd  ->  'e  ->  'f FStar_Tactics_Basic.tac)  ->  (FStar_Syntax_Syntax.term  ->  'a)  ->  (FStar_Syntax_Syntax.term  ->  'b)  ->  (FStar_Syntax_Syntax.term  ->  'c)  ->  (FStar_Syntax_Syntax.term  ->  'd)  ->  (FStar_Syntax_Syntax.term  ->  'e)  ->  ('f  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ps t unembed_a unembed_b unembed_c unembed_d unembed_e embed_f t_f nm args -> (match (args) with
| ((a, uu____692))::((b, uu____694))::((c, uu____696))::((d, uu____698))::((e, uu____700))::((embedded_state, uu____702))::[] -> begin
((FStar_Tactics_Basic.log ps (fun uu____773 -> (

let uu____774 = (FStar_Ident.string_of_lid nm)
in (

let uu____775 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____774 uu____775)))));
(

let ps1 = (FStar_Tactics_Embedding.unembed_proofstate ps embedded_state)
in (

let res = (

let uu____780 = (

let uu____783 = (unembed_a a)
in (

let uu____784 = (unembed_b b)
in (

let uu____785 = (unembed_c c)
in (

let uu____786 = (unembed_d d)
in (

let uu____787 = (unembed_e e)
in (t uu____783 uu____784 uu____785 uu____786 uu____787))))))
in (FStar_Tactics_Basic.run uu____780 ps1))
in (

let uu____788 = (FStar_Tactics_Embedding.embed_result ps1 res embed_f t_f)
in FStar_Pervasives_Native.Some (uu____788))));
)
end
| uu____789 -> begin
(

let uu____790 = (

let uu____791 = (FStar_Ident.string_of_lid nm)
in (

let uu____792 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____791 uu____792)))
in (failwith uu____790))
end))


let step_from_native_step : FStar_Tactics_Basic.proofstate  ->  FStar_Tactics_Native.native_primitive_step  ->  FStar_TypeChecker_Normalize.primitive_step = (fun ps s -> ((

let uu____804 = (FStar_Ident.string_of_lid s.FStar_Tactics_Native.name)
in (FStar_Util.print1 "Registered primitive step %s\n" uu____804));
{FStar_TypeChecker_Normalize.name = s.FStar_Tactics_Native.name; FStar_TypeChecker_Normalize.arity = s.FStar_Tactics_Native.arity; FStar_TypeChecker_Normalize.strong_reduction_ok = s.FStar_Tactics_Native.strong_reduction_ok; FStar_TypeChecker_Normalize.interpretation = (fun _rng args -> (s.FStar_Tactics_Native.tactic ps args))};
))


let rec primitive_steps : FStar_Tactics_Basic.proofstate  ->  FStar_TypeChecker_Normalize.primitive_step Prims.list = (fun ps -> (

let mk1 = (fun nm arity interpretation -> (

let nm1 = (FStar_Tactics_Embedding.fstar_tactics_lid' (("Builtins")::(nm)::[]))
in {FStar_TypeChecker_Normalize.name = nm1; FStar_TypeChecker_Normalize.arity = arity; FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.interpretation = (fun _rng args -> (interpretation nm1 args))}))
in (

let native_tactics = (FStar_Tactics_Native.list_all ())
in (

let native_tactics_steps = (FStar_List.map (step_from_native_step ps) native_tactics)
in (

let mk_refl = (fun nm arity interpretation -> (

let nm1 = (FStar_Reflection_Data.fstar_refl_lid nm)
in {FStar_TypeChecker_Normalize.name = nm1; FStar_TypeChecker_Normalize.arity = arity; FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.interpretation = (fun _rng args -> (interpretation nm1 args))}))
in (

let mktac0 = (fun name f e_a ta -> (mk1 name (Prims.parse_int "1") (mk_tactic_interpretation_0 ps f e_a ta)))
in (

let mktac1 = (fun name f u_a e_b tb -> (mk1 name (Prims.parse_int "2") (mk_tactic_interpretation_1 ps f u_a e_b tb)))
in (

let mktac2 = (fun name f u_a u_b e_c tc -> (mk1 name (Prims.parse_int "3") (mk_tactic_interpretation_2 ps f u_a u_b e_c tc)))
in (

let mktac3 = (fun name f u_a u_b u_c e_d tc -> (mk1 name (Prims.parse_int "4") (mk_tactic_interpretation_3 ps f u_a u_b u_c e_d tc)))
in (

let mktac5 = (fun name f u_a u_b u_c u_d u_e e_f tc -> (mk1 name (Prims.parse_int "6") (mk_tactic_interpretation_5 ps f u_a u_b u_c u_d u_e e_f tc)))
in (

let uu____1246 = (

let uu____1249 = (mktac0 "__trivial" FStar_Tactics_Basic.trivial FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1250 = (

let uu____1253 = (mktac2 "__trytac" (fun uu____1259 -> FStar_Tactics_Basic.trytac) (fun t -> t) (unembed_tactic_0 (fun t -> t)) (FStar_Syntax_Embeddings.embed_option (fun t -> t) FStar_Syntax_Syntax.t_unit) FStar_Syntax_Syntax.t_unit)
in (

let uu____1266 = (

let uu____1269 = (mktac0 "__intro" FStar_Tactics_Basic.intro FStar_Reflection_Basic.embed_binder FStar_Reflection_Data.fstar_refl_binder)
in (

let uu____1274 = (

let uu____1277 = (

let uu____1278 = (FStar_Tactics_Embedding.pair_typ FStar_Reflection_Data.fstar_refl_binder FStar_Reflection_Data.fstar_refl_binder)
in (mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec (FStar_Syntax_Embeddings.embed_pair FStar_Reflection_Basic.embed_binder FStar_Reflection_Data.fstar_refl_binder FStar_Reflection_Basic.embed_binder FStar_Reflection_Data.fstar_refl_binder) uu____1278))
in (

let uu____1287 = (

let uu____1290 = (mktac1 "__norm" FStar_Tactics_Basic.norm (FStar_Syntax_Embeddings.unembed_list FStar_Reflection_Basic.unembed_norm_step) FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1293 = (

let uu____1296 = (mktac0 "__revert" FStar_Tactics_Basic.revert FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1297 = (

let uu____1300 = (mktac0 "__clear" FStar_Tactics_Basic.clear FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1301 = (

let uu____1304 = (mktac1 "__rewrite" FStar_Tactics_Basic.rewrite FStar_Reflection_Basic.unembed_binder FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1305 = (

let uu____1308 = (mktac0 "__smt" FStar_Tactics_Basic.smt FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1309 = (

let uu____1312 = (mktac1 "__exact" FStar_Tactics_Basic.exact FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1313 = (

let uu____1316 = (mktac1 "__exact_lemma" FStar_Tactics_Basic.exact_lemma FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1317 = (

let uu____1320 = (mktac1 "__apply" FStar_Tactics_Basic.apply FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1321 = (

let uu____1324 = (mktac1 "__apply_lemma" FStar_Tactics_Basic.apply_lemma FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1325 = (

let uu____1328 = (mktac5 "__divide" (fun uu____1339 uu____1340 -> FStar_Tactics_Basic.divide) (fun t -> t) (fun t -> t) FStar_Syntax_Embeddings.unembed_int (unembed_tactic_0 (fun t -> t)) (unembed_tactic_0 (fun t -> t)) (FStar_Syntax_Embeddings.embed_pair (fun t -> t) FStar_Syntax_Syntax.t_unit (fun t -> t) FStar_Syntax_Syntax.t_unit) FStar_Syntax_Syntax.t_unit)
in (

let uu____1353 = (

let uu____1356 = (mktac1 "__set_options" FStar_Tactics_Basic.set_options FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1357 = (

let uu____1360 = (mktac2 "__seq" FStar_Tactics_Basic.seq (unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit) (unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit) FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1365 = (

let uu____1368 = (mktac1 "__prune" FStar_Tactics_Basic.prune FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1369 = (

let uu____1372 = (mktac1 "__addns" FStar_Tactics_Basic.addns FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1373 = (

let uu____1376 = (mktac1 "__print" (fun x -> ((FStar_Tactics_Basic.tacprint x);
(FStar_Tactics_Basic.ret ());
)) FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1381 = (

let uu____1384 = (mktac1 "__dump" FStar_Tactics_Basic.print_proof_state FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1385 = (

let uu____1388 = (mktac1 "__dump1" FStar_Tactics_Basic.print_proof_state1 FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1389 = (

let uu____1392 = (mktac1 "__pointwise" FStar_Tactics_Basic.pointwise (unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit) FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1395 = (

let uu____1398 = (mktac0 "__trefl" FStar_Tactics_Basic.trefl FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1399 = (

let uu____1402 = (mktac0 "__later" FStar_Tactics_Basic.later FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1403 = (

let uu____1406 = (mktac0 "__dup" FStar_Tactics_Basic.dup FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1407 = (

let uu____1410 = (mktac0 "__flip" FStar_Tactics_Basic.flip FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1411 = (

let uu____1414 = (mktac0 "__qed" FStar_Tactics_Basic.qed FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1415 = (

let uu____1418 = (

let uu____1419 = (FStar_Tactics_Embedding.pair_typ FStar_Reflection_Data.fstar_refl_term FStar_Reflection_Data.fstar_refl_term)
in (mktac1 "__cases" FStar_Tactics_Basic.cases FStar_Reflection_Basic.unembed_term (FStar_Syntax_Embeddings.embed_pair FStar_Reflection_Basic.embed_term FStar_Reflection_Data.fstar_refl_term FStar_Reflection_Basic.embed_term FStar_Reflection_Data.fstar_refl_term) uu____1419))
in (

let uu____1424 = (

let uu____1427 = (mktac0 "__cur_env" FStar_Tactics_Basic.cur_env FStar_Reflection_Basic.embed_env FStar_Reflection_Data.fstar_refl_env)
in (

let uu____1428 = (

let uu____1431 = (mktac0 "__cur_goal" FStar_Tactics_Basic.cur_goal' FStar_Reflection_Basic.embed_term FStar_Reflection_Data.fstar_refl_term)
in (

let uu____1432 = (

let uu____1435 = (mktac0 "__cur_witness" FStar_Tactics_Basic.cur_witness FStar_Reflection_Basic.embed_term FStar_Reflection_Data.fstar_refl_term)
in (uu____1435)::[])
in (uu____1431)::uu____1432))
in (uu____1427)::uu____1428))
in (uu____1418)::uu____1424))
in (uu____1414)::uu____1415))
in (uu____1410)::uu____1411))
in (uu____1406)::uu____1407))
in (uu____1402)::uu____1403))
in (uu____1398)::uu____1399))
in (uu____1392)::uu____1395))
in (uu____1388)::uu____1389))
in (uu____1384)::uu____1385))
in (uu____1376)::uu____1381))
in (uu____1372)::uu____1373))
in (uu____1368)::uu____1369))
in (uu____1360)::uu____1365))
in (uu____1356)::uu____1357))
in (uu____1328)::uu____1353))
in (uu____1324)::uu____1325))
in (uu____1320)::uu____1321))
in (uu____1316)::uu____1317))
in (uu____1312)::uu____1313))
in (uu____1308)::uu____1309))
in (uu____1304)::uu____1305))
in (uu____1300)::uu____1301))
in (uu____1296)::uu____1297))
in (uu____1290)::uu____1293))
in (uu____1277)::uu____1287))
in (uu____1269)::uu____1274))
in (uu____1253)::uu____1266))
in (uu____1249)::uu____1250))
in (FStar_List.append uu____1246 (FStar_List.append FStar_Reflection_Interpreter.reflection_primops native_tactics_steps)))))))))))))
and unembed_tactic_0 : 'Ab . (FStar_Syntax_Syntax.term  ->  'Ab)  ->  FStar_Syntax_Syntax.term  ->  'Ab FStar_Tactics_Basic.tac = (fun unembed_b embedded_tac_b -> (FStar_Tactics_Basic.bind FStar_Tactics_Basic.get (fun proof_state -> (

let tm = (

let uu____1448 = (

let uu____1449 = (

let uu____1450 = (

let uu____1451 = (FStar_Tactics_Embedding.embed_proofstate proof_state)
in (FStar_Syntax_Syntax.as_arg uu____1451))
in (uu____1450)::[])
in (FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1449))
in (uu____1448 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Primops)::[]
in (

let uu____1457 = (FStar_All.pipe_left FStar_Tactics_Basic.mlog (fun uu____1466 -> (

let uu____1467 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Starting normalizer with %s\n" uu____1467))))
in (FStar_Tactics_Basic.bind uu____1457 (fun uu____1471 -> (

let result = (

let uu____1473 = (primitive_steps proof_state)
in (FStar_TypeChecker_Normalize.normalize_with_primitive_steps uu____1473 steps proof_state.FStar_Tactics_Basic.main_context tm))
in (

let uu____1476 = (FStar_All.pipe_left FStar_Tactics_Basic.mlog (fun uu____1485 -> (

let uu____1486 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print1 "Reduced tactic: got %s\n" uu____1486))))
in (FStar_Tactics_Basic.bind uu____1476 (fun uu____1492 -> (

let uu____1493 = (FStar_Tactics_Embedding.unembed_result proof_state result unembed_b)
in (match (uu____1493) with
| FStar_Util.Inl (b, ps) -> begin
(

let uu____1518 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____1518 (fun uu____1522 -> (FStar_Tactics_Basic.ret b))))
end
| FStar_Util.Inr (msg, ps) -> begin
(

let uu____1533 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____1533 (fun uu____1537 -> (FStar_Tactics_Basic.fail msg))))
end))))))))))))))


let run_tactic_on_typ : 'a . 'a FStar_Tactics_Basic.tac  ->  FStar_Tactics_Basic.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Tactics_Basic.goal Prims.list * FStar_Syntax_Syntax.term) = (fun tau env typ -> (

let uu____1569 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1569) with
| (env1, uu____1583) -> begin
(

let env2 = (

let uu___114_1589 = env1
in {FStar_TypeChecker_Env.solver = uu___114_1589.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_1589.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_1589.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_1589.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___114_1589.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_1589.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_1589.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_1589.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_1589.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___114_1589.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_1589.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_1589.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___114_1589.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_1589.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_1589.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___114_1589.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___114_1589.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___114_1589.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___114_1589.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___114_1589.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_1589.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_1589.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___114_1589.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___114_1589.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___114_1589.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___114_1589.FStar_TypeChecker_Env.is_native_tactic})
in (

let uu____1590 = (FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ)
in (match (uu____1590) with
| (ps, w) -> begin
(

let r = try
(match (()) with
| () -> begin
(FStar_Tactics_Basic.run tau ps)
end)
with
| FStar_Tactics_Basic.TacFailure (s) -> begin
FStar_Tactics_Basic.Failed ((((Prims.strcat "EXCEPTION: " s)), (ps)))
end
in (match (r) with
| FStar_Tactics_Basic.Success (uu____1624, ps1) -> begin
((

let uu____1627 = (FStar_ST.read tacdbg)
in (match (uu____1627) with
| true -> begin
(

let uu____1628 = (FStar_Syntax_Print.term_to_string w)
in (FStar_Util.print1 "Tactic generated proofterm %s\n" uu____1628))
end
| uu____1629 -> begin
()
end));
(FStar_List.iter (fun g -> (

let uu____1635 = (FStar_Tactics_Basic.is_irrelevant g)
in (match (uu____1635) with
| true -> begin
(

let uu____1636 = (FStar_TypeChecker_Rel.teq_nosmt g.FStar_Tactics_Basic.context g.FStar_Tactics_Basic.witness FStar_Syntax_Util.exp_unit)
in (match (uu____1636) with
| true -> begin
()
end
| uu____1637 -> begin
(

let uu____1638 = (

let uu____1639 = (FStar_Syntax_Print.term_to_string g.FStar_Tactics_Basic.witness)
in (FStar_Util.format1 "Irrelevant tactic witness does not unify with (): %s" uu____1639))
in (failwith uu____1638))
end))
end
| uu____1640 -> begin
()
end))) (FStar_List.append ps1.FStar_Tactics_Basic.goals ps1.FStar_Tactics_Basic.smt_goals));
(

let g = (

let uu___117_1642 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___117_1642.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___117_1642.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___117_1642.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = ps1.FStar_Tactics_Basic.all_implicits})
in (

let g1 = (

let uu____1644 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____1644 FStar_TypeChecker_Rel.resolve_implicits_lax))
in ((FStar_TypeChecker_Rel.force_trivial_guard env2 g1);
(((FStar_List.append ps1.FStar_Tactics_Basic.goals ps1.FStar_Tactics_Basic.smt_goals)), (w));
)));
)
end
| FStar_Tactics_Basic.Failed (s, ps1) -> begin
((FStar_Tactics_Basic.dump_proofstate ps1 "at the time of failure");
(

let uu____1651 = (

let uu____1652 = (

let uu____1657 = (FStar_Util.format1 "user tactic failed: %s" s)
in ((uu____1657), (typ.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____1652))
in (FStar_Pervasives.raise uu____1651));
)
end))
end)))
end)))

type pol =
| Pos
| Neg


let uu___is_Pos : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pos -> begin
true
end
| uu____1668 -> begin
false
end))


let uu___is_Neg : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neg -> begin
true
end
| uu____1673 -> begin
false
end))


let flip : pol  ->  pol = (fun p -> (match (p) with
| Pos -> begin
Neg
end
| Neg -> begin
Pos
end))


let by_tactic_interp : pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Tactics_Basic.goal Prims.list) = (fun pol e t -> (

let uu____1702 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____1702) with
| (hd1, args) -> begin
(

let uu____1745 = (

let uu____1758 = (

let uu____1759 = (FStar_Syntax_Util.un_uinst hd1)
in uu____1759.FStar_Syntax_Syntax.n)
in ((uu____1758), (args)))
in (match (uu____1745) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((rett, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____1778))))::((tactic, FStar_Pervasives_Native.None))::((assertion, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid) -> begin
(match ((pol = Pos)) with
| true -> begin
(

let uu____1847 = (

let uu____1854 = (unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic)
in (run_tactic_on_typ uu____1854 e assertion))
in (match (uu____1847) with
| (gs, uu____1864) -> begin
((FStar_Syntax_Util.t_true), (gs))
end))
end
| uu____1871 -> begin
((assertion), ([]))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((assertion, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.spinoff_lid) -> begin
(match ((pol = Pos)) with
| true -> begin
(

let uu____1916 = (run_tactic_on_typ FStar_Tactics_Basic.idtac e assertion)
in (match (uu____1916) with
| (gs, uu____1930) -> begin
((FStar_Syntax_Util.t_true), (gs))
end))
end
| uu____1937 -> begin
((assertion), ([]))
end)
end
| uu____1942 -> begin
((t), ([]))
end))
end)))


let rec traverse : (pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Tactics_Basic.goal Prims.list))  ->  pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Tactics_Basic.goal Prims.list) = (fun f pol e t -> (

let uu____2012 = (

let uu____2019 = (

let uu____2020 = (FStar_Syntax_Subst.compress t)
in uu____2020.FStar_Syntax_Syntax.n)
in (match (uu____2019) with
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____2035 = (traverse f pol e t1)
in (match (uu____2035) with
| (t', gs) -> begin
((FStar_Syntax_Syntax.Tm_uinst (((t'), (us)))), (gs))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____2062 = (traverse f pol e t1)
in (match (uu____2062) with
| (t', gs) -> begin
((FStar_Syntax_Syntax.Tm_meta (((t'), (m)))), (gs))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____2084; FStar_Syntax_Syntax.vars = uu____2085}, ((p, uu____2087))::((q, uu____2089))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p)
in (

let uu____2129 = (traverse f (flip pol) e p)
in (match (uu____2129) with
| (p', gs1) -> begin
(

let uu____2148 = (

let uu____2155 = (FStar_TypeChecker_Env.push_bv e x)
in (traverse f pol uu____2155 q))
in (match (uu____2148) with
| (q', gs2) -> begin
(

let uu____2168 = (

let uu____2169 = (FStar_Syntax_Util.mk_imp p' q')
in uu____2169.FStar_Syntax_Syntax.n)
in ((uu____2168), ((FStar_List.append gs1 gs2))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____2196 = (traverse f pol e hd1)
in (match (uu____2196) with
| (hd', gs1) -> begin
(

let uu____2215 = (FStar_List.fold_right (fun uu____2253 uu____2254 -> (match (((uu____2253), (uu____2254))) with
| ((a, q), (as', gs)) -> begin
(

let uu____2335 = (traverse f pol e a)
in (match (uu____2335) with
| (a', gs') -> begin
(((((a'), (q)))::as'), ((FStar_List.append gs gs')))
end))
end)) args (([]), ([])))
in (match (uu____2215) with
| (as', gs2) -> begin
((FStar_Syntax_Syntax.Tm_app (((hd'), (as')))), ((FStar_List.append gs1 gs2)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____2439 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____2439) with
| (bs1, topen) -> begin
(

let e' = (FStar_TypeChecker_Env.push_binders e bs1)
in (

let uu____2453 = (

let uu____2468 = (FStar_List.map (fun uu____2501 -> (match (uu____2501) with
| (bv, aq) -> begin
(

let uu____2518 = (traverse f (flip pol) e bv.FStar_Syntax_Syntax.sort)
in (match (uu____2518) with
| (s', gs) -> begin
(((((

let uu___118_2548 = bv
in {FStar_Syntax_Syntax.ppname = uu___118_2548.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_2548.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s'})), (aq))), (gs))
end))
end)) bs1)
in (FStar_All.pipe_left FStar_List.unzip uu____2468))
in (match (uu____2453) with
| (bs2, gs1) -> begin
(

let gs11 = (FStar_List.flatten gs1)
in (

let uu____2612 = (traverse f pol e' topen)
in (match (uu____2612) with
| (topen', gs2) -> begin
(

let uu____2631 = (

let uu____2632 = (FStar_Syntax_Util.abs bs2 topen' k)
in uu____2632.FStar_Syntax_Syntax.n)
in ((uu____2631), ((FStar_List.append gs11 gs2))))
end)))
end)))
end))
end
| x -> begin
((x), ([]))
end))
in (match (uu____2012) with
| (tn', gs) -> begin
(

let t' = (

let uu___119_2655 = t
in {FStar_Syntax_Syntax.n = tn'; FStar_Syntax_Syntax.pos = uu___119_2655.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___119_2655.FStar_Syntax_Syntax.vars})
in (

let uu____2656 = (f pol e t')
in (match (uu____2656) with
| (t'1, gs') -> begin
((t'1), ((FStar_List.append gs gs')))
end)))
end)))


let getprop : FStar_Tactics_Basic.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun e t -> (

let tn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) e t)
in (FStar_Syntax_Util.un_squash tn)))


let preprocess : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term * FStar_Options.optionstate) Prims.list = (fun env goal -> ((

let uu____2715 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.write tacdbg uu____2715));
(

let uu____2717 = (FStar_ST.read tacdbg)
in (match (uu____2717) with
| true -> begin
(

let uu____2718 = (

let uu____2719 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____2719 (FStar_Syntax_Print.binders_to_string ",")))
in (

let uu____2720 = (FStar_Syntax_Print.term_to_string goal)
in (FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2718 uu____2720)))
end
| uu____2721 -> begin
()
end));
(

let initial = (((Prims.parse_int "1")), ([]))
in (

let uu____2749 = (traverse by_tactic_interp Pos env goal)
in (match (uu____2749) with
| (t', gs) -> begin
((

let uu____2771 = (FStar_ST.read tacdbg)
in (match (uu____2771) with
| true -> begin
(

let uu____2772 = (

let uu____2773 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____2773 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let uu____2774 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Main goal simplified to: %s |- %s\n" uu____2772 uu____2774)))
end
| uu____2775 -> begin
()
end));
(

let s = initial
in (

let s1 = (FStar_List.fold_left (fun uu____2821 g -> (match (uu____2821) with
| (n1, gs1) -> begin
(

let phi = (

let uu____2866 = (getprop g.FStar_Tactics_Basic.context g.FStar_Tactics_Basic.goal_ty)
in (match (uu____2866) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2869 = (

let uu____2870 = (FStar_Syntax_Print.term_to_string g.FStar_Tactics_Basic.goal_ty)
in (FStar_Util.format1 "Tactic returned proof-relevant goal: %s" uu____2870))
in (failwith uu____2869))
end
| FStar_Pervasives_Native.Some (phi) -> begin
phi
end))
in ((

let uu____2873 = (FStar_ST.read tacdbg)
in (match (uu____2873) with
| true -> begin
(

let uu____2874 = (FStar_Util.string_of_int n1)
in (

let uu____2875 = (FStar_Tactics_Basic.goal_to_string g)
in (FStar_Util.print2 "Got goal #%s: %s\n" uu____2874 uu____2875)))
end
| uu____2876 -> begin
()
end));
(

let gt' = (

let uu____2878 = (

let uu____2879 = (FStar_Util.string_of_int n1)
in (Prims.strcat "Could not prove goal #" uu____2879))
in (FStar_TypeChecker_Util.label uu____2878 goal.FStar_Syntax_Syntax.pos phi))
in (((n1 + (Prims.parse_int "1"))), ((((g.FStar_Tactics_Basic.context), (gt'), (g.FStar_Tactics_Basic.opts)))::gs1)));
))
end)) s gs)
in (

let uu____2894 = s1
in (match (uu____2894) with
| (uu____2915, gs1) -> begin
(

let uu____2933 = (

let uu____2940 = (FStar_Options.peek ())
in ((env), (t'), (uu____2940)))
in (uu____2933)::gs1)
end))));
)
end)));
))


let reify_tactic : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun a -> (

let r = (

let uu____2952 = (

let uu____2953 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2953))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2952 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____2954 = (

let uu____2955 = (

let uu____2956 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____2957 = (

let uu____2960 = (FStar_Syntax_Syntax.as_arg a)
in (uu____2960)::[])
in (uu____2956)::uu____2957))
in (FStar_Syntax_Syntax.mk_Tm_app r uu____2955))
in (uu____2954 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos))))


let synth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env typ tau -> ((

let uu____2976 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.write tacdbg uu____2976));
(

let uu____2977 = (

let uu____2984 = (

let uu____2987 = (reify_tactic tau)
in (unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit uu____2987))
in (run_tactic_on_typ uu____2984 env typ))
in (match (uu____2977) with
| (gs, w) -> begin
(match (gs) with
| [] -> begin
w
end
| (uu____2994)::uu____2995 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("synthesis left open goals"), (typ.FStar_Syntax_Syntax.pos)))))
end)
end));
))




