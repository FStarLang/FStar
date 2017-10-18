
open Prims
open FStar_Pervasives

let tacdbg : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let mk_tactic_interpretation_0 : 'a . 'a FStar_Tactics_Basic.tac  ->  ('a  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t embed_a t_a nm args -> (match (args) with
| ((embedded_state, uu____55))::[] -> begin
(

let uu____72 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____72 (fun ps -> ((FStar_Tactics_Basic.log ps (fun uu____84 -> (

let uu____85 = (FStar_Ident.string_of_lid nm)
in (

let uu____86 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "Reached %s, args are: %s\n" uu____85 uu____86)))));
(

let res = (FStar_Tactics_Basic.run t ps)
in (

let uu____90 = (FStar_Tactics_Embedding.embed_result ps res embed_a t_a)
in FStar_Pervasives_Native.Some (uu____90)));
))))
end
| uu____91 -> begin
(failwith "Unexpected application of tactic primitive")
end))


let mk_tactic_interpretation_1 : 'a 'r . ('a  ->  'r FStar_Tactics_Basic.tac)  ->  (FStar_Syntax_Syntax.term  ->  'a FStar_Pervasives_Native.option)  ->  ('r  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t unembed_a embed_r t_r nm args -> (match (args) with
| ((a, uu____162))::((embedded_state, uu____164))::[] -> begin
(

let uu____191 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____191 (fun ps -> ((FStar_Tactics_Basic.log ps (fun uu____202 -> (

let uu____203 = (FStar_Ident.string_of_lid nm)
in (

let uu____204 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____203 uu____204)))));
(

let uu____205 = (unembed_a a)
in (FStar_Util.bind_opt uu____205 (fun a1 -> (

let res = (

let uu____215 = (t a1)
in (FStar_Tactics_Basic.run uu____215 ps))
in (

let uu____218 = (FStar_Tactics_Embedding.embed_result ps res embed_r t_r)
in FStar_Pervasives_Native.Some (uu____218))))));
))))
end
| uu____219 -> begin
(

let uu____220 = (

let uu____221 = (FStar_Ident.string_of_lid nm)
in (

let uu____222 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____221 uu____222)))
in (failwith uu____220))
end))


let mk_tactic_interpretation_2 : 'a 'b 'r . ('a  ->  'b  ->  'r FStar_Tactics_Basic.tac)  ->  (FStar_Syntax_Syntax.term  ->  'a FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.term  ->  'b FStar_Pervasives_Native.option)  ->  ('r  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t unembed_a unembed_b embed_r t_r nm args -> (match (args) with
| ((a, uu____316))::((b, uu____318))::((embedded_state, uu____320))::[] -> begin
(

let uu____357 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____357 (fun ps -> ((FStar_Tactics_Basic.log ps (fun uu____368 -> (

let uu____369 = (FStar_Ident.string_of_lid nm)
in (

let uu____370 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____369 uu____370)))));
(

let uu____371 = (unembed_a a)
in (FStar_Util.bind_opt uu____371 (fun a1 -> (

let uu____377 = (unembed_b b)
in (FStar_Util.bind_opt uu____377 (fun b1 -> (

let res = (

let uu____387 = (t a1 b1)
in (FStar_Tactics_Basic.run uu____387 ps))
in (

let uu____390 = (FStar_Tactics_Embedding.embed_result ps res embed_r t_r)
in FStar_Pervasives_Native.Some (uu____390)))))))));
))))
end
| uu____391 -> begin
(

let uu____392 = (

let uu____393 = (FStar_Ident.string_of_lid nm)
in (

let uu____394 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____393 uu____394)))
in (failwith uu____392))
end))


let mk_tactic_interpretation_3 : 'a 'b 'c 'r . ('a  ->  'b  ->  'c  ->  'r FStar_Tactics_Basic.tac)  ->  (FStar_Syntax_Syntax.term  ->  'a FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.term  ->  'b FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.term  ->  'c FStar_Pervasives_Native.option)  ->  ('r  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t unembed_a unembed_b unembed_c embed_r t_r nm args -> (match (args) with
| ((a, uu____511))::((b, uu____513))::((c, uu____515))::((embedded_state, uu____517))::[] -> begin
(

let uu____564 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____564 (fun ps -> ((FStar_Tactics_Basic.log ps (fun uu____575 -> (

let uu____576 = (FStar_Ident.string_of_lid nm)
in (

let uu____577 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____576 uu____577)))));
(

let uu____578 = (unembed_a a)
in (FStar_Util.bind_opt uu____578 (fun a1 -> (

let uu____584 = (unembed_b b)
in (FStar_Util.bind_opt uu____584 (fun b1 -> (

let uu____590 = (unembed_c c)
in (FStar_Util.bind_opt uu____590 (fun c1 -> (

let res = (

let uu____600 = (t a1 b1 c1)
in (FStar_Tactics_Basic.run uu____600 ps))
in (

let uu____603 = (FStar_Tactics_Embedding.embed_result ps res embed_r t_r)
in FStar_Pervasives_Native.Some (uu____603))))))))))));
))))
end
| uu____604 -> begin
(

let uu____605 = (

let uu____606 = (FStar_Ident.string_of_lid nm)
in (

let uu____607 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____606 uu____607)))
in (failwith uu____605))
end))


let mk_tactic_interpretation_5 : 'a 'b 'c 'd 'e 'r . ('a  ->  'b  ->  'c  ->  'd  ->  'e  ->  'r FStar_Tactics_Basic.tac)  ->  (FStar_Syntax_Syntax.term  ->  'a FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.term  ->  'b FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.term  ->  'c FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.term  ->  'd FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.term  ->  'e FStar_Pervasives_Native.option)  ->  ('r  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t unembed_a unembed_b unembed_c unembed_d unembed_e embed_r t_r nm args -> (match (args) with
| ((a, uu____770))::((b, uu____772))::((c, uu____774))::((d, uu____776))::((e, uu____778))::((embedded_state, uu____780))::[] -> begin
(

let uu____847 = (FStar_Tactics_Embedding.unembed_proofstate embedded_state)
in (FStar_Util.bind_opt uu____847 (fun ps -> ((FStar_Tactics_Basic.log ps (fun uu____858 -> (

let uu____859 = (FStar_Ident.string_of_lid nm)
in (

let uu____860 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____859 uu____860)))));
(

let uu____861 = (unembed_a a)
in (FStar_Util.bind_opt uu____861 (fun a1 -> (

let uu____867 = (unembed_b b)
in (FStar_Util.bind_opt uu____867 (fun b1 -> (

let uu____873 = (unembed_c c)
in (FStar_Util.bind_opt uu____873 (fun c1 -> (

let uu____879 = (unembed_d d)
in (FStar_Util.bind_opt uu____879 (fun d1 -> (

let uu____885 = (unembed_e e)
in (FStar_Util.bind_opt uu____885 (fun e1 -> (

let res = (

let uu____895 = (t a1 b1 c1 d1 e1)
in (FStar_Tactics_Basic.run uu____895 ps))
in (

let uu____898 = (FStar_Tactics_Embedding.embed_result ps res embed_r t_r)
in FStar_Pervasives_Native.Some (uu____898))))))))))))))))));
))))
end
| uu____899 -> begin
(

let uu____900 = (

let uu____901 = (FStar_Ident.string_of_lid nm)
in (

let uu____902 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____901 uu____902)))
in (failwith uu____900))
end))


let step_from_native_step : FStar_Tactics_Native.native_primitive_step  ->  FStar_TypeChecker_Normalize.primitive_step = (fun s -> {FStar_TypeChecker_Normalize.name = s.FStar_Tactics_Native.name; FStar_TypeChecker_Normalize.arity = s.FStar_Tactics_Native.arity; FStar_TypeChecker_Normalize.strong_reduction_ok = s.FStar_Tactics_Native.strong_reduction_ok; FStar_TypeChecker_Normalize.interpretation = (fun _rng args -> (s.FStar_Tactics_Native.tactic args))})


let rec primitive_steps : Prims.unit  ->  FStar_TypeChecker_Normalize.primitive_step Prims.list = (fun uu____953 -> (

let mk1 = (fun nm arity interpretation -> (

let nm1 = (FStar_Tactics_Embedding.fstar_tactics_lid' (("Builtins")::(nm)::[]))
in {FStar_TypeChecker_Normalize.name = nm1; FStar_TypeChecker_Normalize.arity = arity; FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.interpretation = (fun _rng args -> (interpretation nm1 args))}))
in (

let native_tactics = (FStar_Tactics_Native.list_all ())
in (

let native_tactics_steps = (FStar_List.map step_from_native_step native_tactics)
in (

let mktac0 = (fun name f e_r tr -> (mk1 name (Prims.parse_int "1") (mk_tactic_interpretation_0 f e_r tr)))
in (

let mktac1 = (fun name f u_a e_r tr -> (mk1 name (Prims.parse_int "2") (mk_tactic_interpretation_1 f u_a e_r tr)))
in (

let mktac2 = (fun name f u_a u_b e_r tr -> (mk1 name (Prims.parse_int "3") (mk_tactic_interpretation_2 f u_a u_b e_r tr)))
in (

let mktac3 = (fun name f u_a u_b u_c e_r tr -> (mk1 name (Prims.parse_int "4") (mk_tactic_interpretation_3 f u_a u_b u_c e_r tr)))
in (

let mktac5 = (fun name f u_a u_b u_c u_d u_e e_r tr -> (mk1 name (Prims.parse_int "6") (mk_tactic_interpretation_5 f u_a u_b u_c u_d u_e e_r tr)))
in (

let decr_depth_interp = (fun rng args -> (match (args) with
| ((ps, uu____1394))::[] -> begin
(

let uu____1411 = (FStar_Tactics_Embedding.unembed_proofstate ps)
in (FStar_Util.bind_opt uu____1411 (fun ps1 -> (

let uu____1417 = (

let uu____1418 = (FStar_Tactics_Types.decr_depth ps1)
in (FStar_Tactics_Embedding.embed_proofstate uu____1418))
in FStar_Pervasives_Native.Some (uu____1417)))))
end
| uu____1419 -> begin
(failwith "Unexpected application of decr_depth")
end))
in (

let decr_depth_step = (

let uu____1423 = (FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth")
in {FStar_TypeChecker_Normalize.name = uu____1423; FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1"); FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.interpretation = decr_depth_interp})
in (

let incr_depth_interp = (fun rng args -> (match (args) with
| ((ps, uu____1436))::[] -> begin
(

let uu____1453 = (FStar_Tactics_Embedding.unembed_proofstate ps)
in (FStar_Util.bind_opt uu____1453 (fun ps1 -> (

let uu____1459 = (

let uu____1460 = (FStar_Tactics_Types.incr_depth ps1)
in (FStar_Tactics_Embedding.embed_proofstate uu____1460))
in FStar_Pervasives_Native.Some (uu____1459)))))
end
| uu____1461 -> begin
(failwith "Unexpected application of incr_depth")
end))
in (

let incr_depth_step = (

let uu____1465 = (FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth")
in {FStar_TypeChecker_Normalize.name = uu____1465; FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1"); FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.interpretation = incr_depth_interp})
in (

let tracepoint_interp = (fun rng args -> (match (args) with
| ((ps, uu____1482))::[] -> begin
(

let uu____1499 = (FStar_Tactics_Embedding.unembed_proofstate ps)
in (FStar_Util.bind_opt uu____1499 (fun ps1 -> ((FStar_Tactics_Types.tracepoint ps1);
FStar_Pervasives_Native.Some (FStar_Syntax_Util.exp_unit);
))))
end
| uu____1510 -> begin
(failwith "Unexpected application of tracepoint")
end))
in (

let tracepoint_step = (

let nm = (FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint")
in {FStar_TypeChecker_Normalize.name = nm; FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1"); FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.interpretation = tracepoint_interp})
in (

let uu____1517 = (

let uu____1520 = (mktac0 "__trivial" FStar_Tactics_Basic.trivial FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1521 = (

let uu____1524 = (mktac2 "__trytac" (fun uu____1530 -> FStar_Tactics_Basic.trytac) (fun _0_65 -> FStar_Pervasives_Native.Some (_0_65)) (unembed_tactic_0' (fun _0_66 -> FStar_Pervasives_Native.Some (_0_66))) (FStar_Syntax_Embeddings.embed_option (fun t -> t) FStar_Syntax_Syntax.t_unit) FStar_Syntax_Syntax.t_unit)
in (

let uu____1533 = (

let uu____1536 = (mktac0 "__intro" FStar_Tactics_Basic.intro FStar_Reflection_Basic.embed_binder FStar_Reflection_Data.fstar_refl_binder)
in (

let uu____1537 = (

let uu____1540 = (

let uu____1541 = (FStar_Tactics_Embedding.pair_typ FStar_Reflection_Data.fstar_refl_binder FStar_Reflection_Data.fstar_refl_binder)
in (mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec (FStar_Syntax_Embeddings.embed_pair FStar_Reflection_Basic.embed_binder FStar_Reflection_Data.fstar_refl_binder FStar_Reflection_Basic.embed_binder FStar_Reflection_Data.fstar_refl_binder) uu____1541))
in (

let uu____1546 = (

let uu____1549 = (mktac1 "__norm" FStar_Tactics_Basic.norm (FStar_Syntax_Embeddings.unembed_list FStar_Syntax_Embeddings.unembed_norm_step) FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1552 = (

let uu____1555 = (mktac3 "__norm_term_env" FStar_Tactics_Basic.norm_term_env FStar_Reflection_Basic.unembed_env (FStar_Syntax_Embeddings.unembed_list FStar_Syntax_Embeddings.unembed_norm_step) FStar_Reflection_Basic.unembed_term FStar_Reflection_Basic.embed_term FStar_Syntax_Syntax.t_term)
in (

let uu____1558 = (

let uu____1561 = (mktac2 "__norm_binder_type" FStar_Tactics_Basic.norm_binder_type (FStar_Syntax_Embeddings.unembed_list FStar_Syntax_Embeddings.unembed_norm_step) FStar_Reflection_Basic.unembed_binder FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1564 = (

let uu____1567 = (mktac2 "__rename_to" FStar_Tactics_Basic.rename_to FStar_Reflection_Basic.unembed_binder FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1568 = (

let uu____1571 = (mktac1 "__binder_retype" FStar_Tactics_Basic.binder_retype FStar_Reflection_Basic.unembed_binder FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1572 = (

let uu____1575 = (mktac0 "__revert" FStar_Tactics_Basic.revert FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1576 = (

let uu____1579 = (mktac0 "__clear_top" FStar_Tactics_Basic.clear_top FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1580 = (

let uu____1583 = (mktac1 "__clear" FStar_Tactics_Basic.clear FStar_Reflection_Basic.unembed_binder FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1584 = (

let uu____1587 = (mktac1 "__rewrite" FStar_Tactics_Basic.rewrite FStar_Reflection_Basic.unembed_binder FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1588 = (

let uu____1591 = (mktac0 "__smt" FStar_Tactics_Basic.smt FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1592 = (

let uu____1595 = (mktac1 "__exact" FStar_Tactics_Basic.exact FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1596 = (

let uu____1599 = (mktac1 "__apply" (FStar_Tactics_Basic.apply true) FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1600 = (

let uu____1603 = (mktac1 "__apply_raw" (FStar_Tactics_Basic.apply false) FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1604 = (

let uu____1607 = (mktac1 "__apply_lemma" FStar_Tactics_Basic.apply_lemma FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1608 = (

let uu____1611 = (mktac5 "__divide" (fun uu____1622 uu____1623 -> FStar_Tactics_Basic.divide) (fun _0_67 -> FStar_Pervasives_Native.Some (_0_67)) (fun _0_68 -> FStar_Pervasives_Native.Some (_0_68)) FStar_Syntax_Embeddings.unembed_int (unembed_tactic_0' (fun _0_69 -> FStar_Pervasives_Native.Some (_0_69))) (unembed_tactic_0' (fun _0_70 -> FStar_Pervasives_Native.Some (_0_70))) (FStar_Syntax_Embeddings.embed_pair (fun t -> t) FStar_Syntax_Syntax.t_unit (fun t -> t) FStar_Syntax_Syntax.t_unit) FStar_Syntax_Syntax.t_unit)
in (

let uu____1628 = (

let uu____1631 = (mktac1 "__set_options" FStar_Tactics_Basic.set_options FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1632 = (

let uu____1635 = (mktac2 "__seq" FStar_Tactics_Basic.seq (unembed_tactic_0' FStar_Syntax_Embeddings.unembed_unit) (unembed_tactic_0' FStar_Syntax_Embeddings.unembed_unit) FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1640 = (

let uu____1643 = (mktac1 "__tc" FStar_Tactics_Basic.tc FStar_Reflection_Basic.unembed_term FStar_Reflection_Basic.embed_term FStar_Syntax_Syntax.t_term)
in (

let uu____1644 = (

let uu____1647 = (mktac1 "__unshelve" FStar_Tactics_Basic.unshelve FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1648 = (

let uu____1651 = (mktac2 "__unquote" FStar_Tactics_Basic.unquote (fun _0_71 -> FStar_Pervasives_Native.Some (_0_71)) FStar_Reflection_Basic.unembed_term (fun t -> t) FStar_Syntax_Syntax.t_unit)
in (

let uu____1654 = (

let uu____1657 = (mktac1 "__prune" FStar_Tactics_Basic.prune FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1658 = (

let uu____1661 = (mktac1 "__addns" FStar_Tactics_Basic.addns FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1662 = (

let uu____1665 = (mktac1 "__print" (fun x -> ((FStar_Tactics_Basic.tacprint x);
(FStar_Tactics_Basic.ret ());
)) FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1670 = (

let uu____1673 = (mktac1 "__dump" FStar_Tactics_Basic.print_proof_state FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1674 = (

let uu____1677 = (mktac1 "__dump1" FStar_Tactics_Basic.print_proof_state1 FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1678 = (

let uu____1681 = (mktac2 "__pointwise" FStar_Tactics_Basic.pointwise FStar_Tactics_Embedding.unembed_direction (unembed_tactic_0' FStar_Syntax_Embeddings.unembed_unit) FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1684 = (

let uu____1687 = (mktac0 "__trefl" FStar_Tactics_Basic.trefl FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1688 = (

let uu____1691 = (mktac0 "__later" FStar_Tactics_Basic.later FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1692 = (

let uu____1695 = (mktac0 "__dup" FStar_Tactics_Basic.dup FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1696 = (

let uu____1699 = (mktac0 "__flip" FStar_Tactics_Basic.flip FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1700 = (

let uu____1703 = (mktac0 "__qed" FStar_Tactics_Basic.qed FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1704 = (

let uu____1707 = (

let uu____1708 = (FStar_Tactics_Embedding.pair_typ FStar_Syntax_Syntax.t_term FStar_Syntax_Syntax.t_term)
in (mktac1 "__cases" FStar_Tactics_Basic.cases FStar_Reflection_Basic.unembed_term (FStar_Syntax_Embeddings.embed_pair FStar_Reflection_Basic.embed_term FStar_Syntax_Syntax.t_term FStar_Reflection_Basic.embed_term FStar_Syntax_Syntax.t_term) uu____1708))
in (

let uu____1713 = (

let uu____1716 = (mktac0 "__top_env" FStar_Tactics_Basic.top_env FStar_Reflection_Basic.embed_env FStar_Reflection_Data.fstar_refl_env)
in (

let uu____1717 = (

let uu____1720 = (mktac0 "__cur_env" FStar_Tactics_Basic.cur_env FStar_Reflection_Basic.embed_env FStar_Reflection_Data.fstar_refl_env)
in (

let uu____1721 = (

let uu____1724 = (mktac0 "__cur_goal" FStar_Tactics_Basic.cur_goal' FStar_Reflection_Basic.embed_term FStar_Syntax_Syntax.t_term)
in (

let uu____1725 = (

let uu____1728 = (mktac0 "__cur_witness" FStar_Tactics_Basic.cur_witness FStar_Reflection_Basic.embed_term FStar_Syntax_Syntax.t_term)
in (

let uu____1729 = (

let uu____1732 = (mktac2 "__uvar_env" FStar_Tactics_Basic.uvar_env FStar_Reflection_Basic.unembed_env (FStar_Syntax_Embeddings.unembed_option FStar_Reflection_Basic.unembed_term) FStar_Reflection_Basic.embed_term FStar_Syntax_Syntax.t_term)
in (

let uu____1735 = (

let uu____1738 = (mktac2 "__unify" FStar_Tactics_Basic.unify FStar_Reflection_Basic.unembed_term FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_bool FStar_Syntax_Syntax.t_bool)
in (

let uu____1739 = (

let uu____1742 = (mktac3 "__launch_process" FStar_Tactics_Basic.launch_process FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_string FStar_Syntax_Syntax.t_string)
in (uu____1742)::(decr_depth_step)::(incr_depth_step)::(tracepoint_step)::[])
in (uu____1738)::uu____1739))
in (uu____1732)::uu____1735))
in (uu____1728)::uu____1729))
in (uu____1724)::uu____1725))
in (uu____1720)::uu____1721))
in (uu____1716)::uu____1717))
in (uu____1707)::uu____1713))
in (uu____1703)::uu____1704))
in (uu____1699)::uu____1700))
in (uu____1695)::uu____1696))
in (uu____1691)::uu____1692))
in (uu____1687)::uu____1688))
in (uu____1681)::uu____1684))
in (uu____1677)::uu____1678))
in (uu____1673)::uu____1674))
in (uu____1665)::uu____1670))
in (uu____1661)::uu____1662))
in (uu____1657)::uu____1658))
in (uu____1651)::uu____1654))
in (uu____1647)::uu____1648))
in (uu____1643)::uu____1644))
in (uu____1635)::uu____1640))
in (uu____1631)::uu____1632))
in (uu____1611)::uu____1628))
in (uu____1607)::uu____1608))
in (uu____1603)::uu____1604))
in (uu____1599)::uu____1600))
in (uu____1595)::uu____1596))
in (uu____1591)::uu____1592))
in (uu____1587)::uu____1588))
in (uu____1583)::uu____1584))
in (uu____1579)::uu____1580))
in (uu____1575)::uu____1576))
in (uu____1571)::uu____1572))
in (uu____1567)::uu____1568))
in (uu____1561)::uu____1564))
in (uu____1555)::uu____1558))
in (uu____1549)::uu____1552))
in (uu____1540)::uu____1546))
in (uu____1536)::uu____1537))
in (uu____1524)::uu____1533))
in (uu____1520)::uu____1521))
in (FStar_List.append uu____1517 (FStar_List.append FStar_Reflection_Interpreter.reflection_primops native_tactics_steps))))))))))))))))))
and unembed_tactic_0 : 'Ab . (FStar_Syntax_Syntax.term  ->  'Ab FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term  ->  'Ab FStar_Tactics_Basic.tac = (fun unembed_b embedded_tac_b -> (FStar_Tactics_Basic.bind FStar_Tactics_Basic.get (fun proof_state -> (

let tm = (

let uu____1763 = (

let uu____1764 = (

let uu____1765 = (

let uu____1766 = (FStar_Tactics_Embedding.embed_proofstate proof_state)
in (FStar_Syntax_Syntax.as_arg uu____1766))
in (uu____1765)::[])
in (FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1764))
in (uu____1763 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Primops)::[]
in ((

let uu____1773 = (FStar_ST.op_Bang tacdbg)
in (match (uu____1773) with
| true -> begin
(

let uu____1820 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Starting normalizer with %s\n" uu____1820))
end
| uu____1821 -> begin
()
end));
(

let result = (

let uu____1823 = (primitive_steps ())
in (FStar_TypeChecker_Normalize.normalize_with_primitive_steps uu____1823 steps proof_state.FStar_Tactics_Types.main_context tm))
in ((

let uu____1827 = (FStar_ST.op_Bang tacdbg)
in (match (uu____1827) with
| true -> begin
(

let uu____1874 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print1 "Reduced tactic: got %s\n" uu____1874))
end
| uu____1875 -> begin
()
end));
(

let uu____1876 = (FStar_Tactics_Embedding.unembed_result proof_state result unembed_b)
in (match (uu____1876) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (b, ps)) -> begin
(

let uu____1915 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____1915 (fun uu____1919 -> (FStar_Tactics_Basic.ret b))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (msg, ps)) -> begin
(

let uu____1942 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____1942 (fun uu____1946 -> (FStar_Tactics_Basic.fail msg))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1959 = (

let uu____1960 = (

let uu____1965 = (

let uu____1966 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.format1 "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s" uu____1966))
in ((uu____1965), (proof_state.FStar_Tactics_Types.main_context.FStar_TypeChecker_Env.range)))
in FStar_Errors.Error (uu____1960))
in (FStar_Exn.raise uu____1959))
end));
));
))))))
and unembed_tactic_0' : 'Ab . (FStar_Syntax_Syntax.term  ->  'Ab FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term  ->  'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option = (fun unembed_b embedded_tac_b -> (

let uu____1975 = (unembed_tactic_0 unembed_b embedded_tac_b)
in (FStar_All.pipe_left (fun _0_72 -> FStar_Pervasives_Native.Some (_0_72)) uu____1975)))


let report_implicits : FStar_Tactics_Types.proofstate  ->  FStar_TypeChecker_Env.implicits  ->  Prims.unit = (fun ps is -> (

let errs = (FStar_List.map (fun uu____2025 -> (match (uu____2025) with
| (r, uu____2043, uv, uu____2045, ty, rng) -> begin
(

let uu____2048 = (

let uu____2049 = (FStar_Syntax_Print.uvar_to_string uv)
in (

let uu____2050 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.format3 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")" uu____2049 uu____2050 r)))
in ((uu____2048), (rng)))
end)) is)
in (match (errs) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
((FStar_Tactics_Basic.dump_proofstate ps "failing due to uninstantiated implicits");
(FStar_Errors.add_errors tl1);
(FStar_Exn.raise (FStar_Errors.Error (hd1)));
)
end)))


let run_tactic_on_typ : FStar_Syntax_Syntax.term  ->  FStar_Tactics_Basic.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Tactics_Types.goal Prims.list * FStar_Syntax_Syntax.term) = (fun tactic env typ -> ((

let uu____2098 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2098) with
| true -> begin
(

let uu____2145 = (FStar_Syntax_Print.term_to_string tactic)
in (FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2145))
end
| uu____2146 -> begin
()
end));
(

let tactic1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic)
in ((

let uu____2149 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2149) with
| true -> begin
(

let uu____2196 = (FStar_Syntax_Print.term_to_string tactic1)
in (FStar_Util.print1 "About to check tactic term: %s\n" uu____2196))
end
| uu____2197 -> begin
()
end));
(

let uu____2198 = (FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1)
in (match (uu____2198) with
| (tactic2, uu____2212, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
(FStar_Errors.stop_if_err ());
(

let tau = (unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic2)
in (

let uu____2219 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____2219) with
| (env1, uu____2233) -> begin
(

let env2 = (

let uu___165_2239 = env1
in {FStar_TypeChecker_Env.solver = uu___165_2239.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___165_2239.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___165_2239.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___165_2239.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___165_2239.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___165_2239.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___165_2239.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___165_2239.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___165_2239.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___165_2239.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___165_2239.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___165_2239.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___165_2239.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___165_2239.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___165_2239.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___165_2239.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___165_2239.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___165_2239.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___165_2239.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___165_2239.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___165_2239.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___165_2239.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___165_2239.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___165_2239.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___165_2239.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___165_2239.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___165_2239.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___165_2239.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___165_2239.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___165_2239.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___165_2239.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___165_2239.FStar_TypeChecker_Env.dsenv})
in (

let uu____2240 = (FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ)
in (match (uu____2240) with
| (ps, w) -> begin
((

let uu____2254 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2254) with
| true -> begin
(FStar_Util.print_string "Running tactic.\n")
end
| uu____2301 -> begin
()
end));
(

let uu____2302 = (FStar_Tactics_Basic.run tau ps)
in (match (uu____2302) with
| FStar_Tactics_Result.Success (uu____2311, ps1) -> begin
((

let uu____2314 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2314) with
| true -> begin
(

let uu____2361 = (FStar_Syntax_Print.term_to_string w)
in (FStar_Util.print1 "Tactic generated proofterm %s\n" uu____2361))
end
| uu____2362 -> begin
()
end));
(FStar_List.iter (fun g1 -> (

let uu____2368 = (FStar_Tactics_Basic.is_irrelevant g1)
in (match (uu____2368) with
| true -> begin
(

let uu____2369 = (FStar_TypeChecker_Rel.teq_nosmt g1.FStar_Tactics_Types.context g1.FStar_Tactics_Types.witness FStar_Syntax_Util.exp_unit)
in (match (uu____2369) with
| true -> begin
()
end
| uu____2370 -> begin
(

let uu____2371 = (

let uu____2372 = (FStar_Syntax_Print.term_to_string g1.FStar_Tactics_Types.witness)
in (FStar_Util.format1 "Irrelevant tactic witness does not unify with (): %s" uu____2372))
in (failwith uu____2371))
end))
end
| uu____2373 -> begin
()
end))) (FStar_List.append ps1.FStar_Tactics_Types.goals ps1.FStar_Tactics_Types.smt_goals));
(

let g1 = (

let uu___166_2375 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___166_2375.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___166_2375.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___166_2375.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = ps1.FStar_Tactics_Types.all_implicits})
in (

let g2 = (

let uu____2377 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g1)
in (FStar_All.pipe_right uu____2377 FStar_TypeChecker_Rel.resolve_implicits_tac))
in ((report_implicits ps1 g2.FStar_TypeChecker_Env.implicits);
(((FStar_List.append ps1.FStar_Tactics_Types.goals ps1.FStar_Tactics_Types.smt_goals)), (w));
)));
)
end
| FStar_Tactics_Result.Failed (s, ps1) -> begin
((FStar_Tactics_Basic.dump_proofstate ps1 "at the time of failure");
(

let uu____2384 = (

let uu____2385 = (

let uu____2390 = (FStar_Util.format1 "user tactic failed: %s" s)
in ((uu____2390), (typ.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____2385))
in (FStar_Exn.raise uu____2384));
)
end));
)
end)))
end)));
)
end));
));
))

type pol =
| Pos
| Neg


let uu___is_Pos : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pos -> begin
true
end
| uu____2401 -> begin
false
end))


let uu___is_Neg : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neg -> begin
true
end
| uu____2406 -> begin
false
end))


let flip : pol  ->  pol = (fun p -> (match (p) with
| Pos -> begin
Neg
end
| Neg -> begin
Pos
end))


let by_tactic_interp : pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Tactics_Types.goal Prims.list) = (fun pol e t -> (

let uu____2435 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____2435) with
| (hd1, args) -> begin
(

let uu____2478 = (

let uu____2491 = (

let uu____2492 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2492.FStar_Syntax_Syntax.n)
in ((uu____2491), (args)))
in (match (uu____2478) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((rett, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____2511))))::((tactic, FStar_Pervasives_Native.None))::((assertion, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid) -> begin
(match ((Prims.op_Equality pol Pos)) with
| true -> begin
(

let uu____2580 = (run_tactic_on_typ tactic e assertion)
in (match (uu____2580) with
| (gs, uu____2594) -> begin
((FStar_Syntax_Util.t_true), (gs))
end))
end
| uu____2601 -> begin
((assertion), ([]))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((assertion, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.spinoff_lid) -> begin
(match ((Prims.op_Equality pol Pos)) with
| true -> begin
(

let uu____2646 = (

let uu____2649 = (

let uu____2650 = (FStar_Tactics_Basic.goal_of_goal_ty e assertion)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____2650))
in (uu____2649)::[])
in ((FStar_Syntax_Util.t_true), (uu____2646)))
end
| uu____2661 -> begin
((assertion), ([]))
end)
end
| uu____2666 -> begin
((t), ([]))
end))
end)))


let rec traverse : (pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Tactics_Types.goal Prims.list))  ->  pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Tactics_Types.goal Prims.list) = (fun f pol e t -> (

let uu____2736 = (

let uu____2743 = (

let uu____2744 = (FStar_Syntax_Subst.compress t)
in uu____2744.FStar_Syntax_Syntax.n)
in (match (uu____2743) with
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____2759 = (traverse f pol e t1)
in (match (uu____2759) with
| (t', gs) -> begin
((FStar_Syntax_Syntax.Tm_uinst (((t'), (us)))), (gs))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____2786 = (traverse f pol e t1)
in (match (uu____2786) with
| (t', gs) -> begin
((FStar_Syntax_Syntax.Tm_meta (((t'), (m)))), (gs))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____2808; FStar_Syntax_Syntax.vars = uu____2809}, ((p, uu____2811))::((q, uu____2813))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid) -> begin
(

let x = (

let uu____2853 = (FStar_Syntax_Util.mk_squash p)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____2853))
in (

let uu____2854 = (traverse f (flip pol) e p)
in (match (uu____2854) with
| (p', gs1) -> begin
(

let uu____2873 = (

let uu____2880 = (FStar_TypeChecker_Env.push_bv e x)
in (traverse f pol uu____2880 q))
in (match (uu____2873) with
| (q', gs2) -> begin
(

let uu____2893 = (

let uu____2894 = (FStar_Syntax_Util.mk_imp p' q')
in uu____2894.FStar_Syntax_Syntax.n)
in ((uu____2893), ((FStar_List.append gs1 gs2))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____2921 = (traverse f pol e hd1)
in (match (uu____2921) with
| (hd', gs1) -> begin
(

let uu____2940 = (FStar_List.fold_right (fun uu____2978 uu____2979 -> (match (((uu____2978), (uu____2979))) with
| ((a, q), (as', gs)) -> begin
(

let uu____3060 = (traverse f pol e a)
in (match (uu____3060) with
| (a', gs') -> begin
(((((a'), (q)))::as'), ((FStar_List.append gs gs')))
end))
end)) args (([]), ([])))
in (match (uu____2940) with
| (as', gs2) -> begin
((FStar_Syntax_Syntax.Tm_app (((hd'), (as')))), ((FStar_List.append gs1 gs2)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____3164 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____3164) with
| (bs1, topen) -> begin
(

let e' = (FStar_TypeChecker_Env.push_binders e bs1)
in (

let uu____3178 = (

let uu____3193 = (FStar_List.map (fun uu____3226 -> (match (uu____3226) with
| (bv, aq) -> begin
(

let uu____3243 = (traverse f (flip pol) e bv.FStar_Syntax_Syntax.sort)
in (match (uu____3243) with
| (s', gs) -> begin
(((((

let uu___167_3273 = bv
in {FStar_Syntax_Syntax.ppname = uu___167_3273.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___167_3273.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s'})), (aq))), (gs))
end))
end)) bs1)
in (FStar_All.pipe_left FStar_List.unzip uu____3193))
in (match (uu____3178) with
| (bs2, gs1) -> begin
(

let gs11 = (FStar_List.flatten gs1)
in (

let uu____3337 = (traverse f pol e' topen)
in (match (uu____3337) with
| (topen', gs2) -> begin
(

let uu____3356 = (

let uu____3357 = (FStar_Syntax_Util.abs bs2 topen' k)
in uu____3357.FStar_Syntax_Syntax.n)
in ((uu____3356), ((FStar_List.append gs11 gs2))))
end)))
end)))
end))
end
| x -> begin
((x), ([]))
end))
in (match (uu____2736) with
| (tn', gs) -> begin
(

let t' = (

let uu___168_3380 = t
in {FStar_Syntax_Syntax.n = tn'; FStar_Syntax_Syntax.pos = uu___168_3380.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___168_3380.FStar_Syntax_Syntax.vars})
in (

let uu____3381 = (f pol e t')
in (match (uu____3381) with
| (t'1, gs') -> begin
((t'1), ((FStar_List.append gs gs')))
end)))
end)))


let getprop : FStar_Tactics_Basic.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun e t -> (

let tn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) e t)
in (FStar_Syntax_Util.un_squash tn)))


let preprocess : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term * FStar_Options.optionstate) Prims.list = (fun env goal -> ((

let uu____3440 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____3440));
(

let uu____3488 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3488) with
| true -> begin
(

let uu____3535 = (

let uu____3536 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____3536 (FStar_Syntax_Print.binders_to_string ",")))
in (

let uu____3537 = (FStar_Syntax_Print.term_to_string goal)
in (FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3535 uu____3537)))
end
| uu____3538 -> begin
()
end));
(

let initial = (((Prims.parse_int "1")), ([]))
in (

let uu____3566 = (traverse by_tactic_interp Pos env goal)
in (match (uu____3566) with
| (t', gs) -> begin
((

let uu____3588 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3588) with
| true -> begin
(

let uu____3635 = (

let uu____3636 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____3636 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let uu____3637 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Main goal simplified to: %s |- %s\n" uu____3635 uu____3637)))
end
| uu____3638 -> begin
()
end));
(

let s = initial
in (

let s1 = (FStar_List.fold_left (fun uu____3684 g -> (match (uu____3684) with
| (n1, gs1) -> begin
(

let phi = (

let uu____3729 = (getprop g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (match (uu____3729) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3732 = (

let uu____3733 = (FStar_Syntax_Print.term_to_string g.FStar_Tactics_Types.goal_ty)
in (FStar_Util.format1 "Tactic returned proof-relevant goal: %s" uu____3733))
in (failwith uu____3732))
end
| FStar_Pervasives_Native.Some (phi) -> begin
phi
end))
in ((

let uu____3736 = (FStar_ST.op_Bang tacdbg)
in (match (uu____3736) with
| true -> begin
(

let uu____3783 = (FStar_Util.string_of_int n1)
in (

let uu____3784 = (FStar_Tactics_Basic.goal_to_string g)
in (FStar_Util.print2 "Got goal #%s: %s\n" uu____3783 uu____3784)))
end
| uu____3785 -> begin
()
end));
(

let gt' = (

let uu____3787 = (

let uu____3788 = (FStar_Util.string_of_int n1)
in (Prims.strcat "Could not prove goal #" uu____3788))
in (FStar_TypeChecker_Util.label uu____3787 goal.FStar_Syntax_Syntax.pos phi))
in (((n1 + (Prims.parse_int "1"))), ((((g.FStar_Tactics_Types.context), (gt'), (g.FStar_Tactics_Types.opts)))::gs1)));
))
end)) s gs)
in (

let uu____3803 = s1
in (match (uu____3803) with
| (uu____3824, gs1) -> begin
(

let uu____3842 = (

let uu____3849 = (FStar_Options.peek ())
in ((env), (t'), (uu____3849)))
in (uu____3842)::gs1)
end))));
)
end)));
))


let reify_tactic : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun a -> (

let r = (

let uu____3861 = (

let uu____3862 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____3862))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3861 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____3863 = (

let uu____3864 = (

let uu____3865 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____3866 = (

let uu____3869 = (FStar_Syntax_Syntax.as_arg a)
in (uu____3869)::[])
in (uu____3865)::uu____3866))
in (FStar_Syntax_Syntax.mk_Tm_app r uu____3864))
in (uu____3863 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos))))


let synth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env typ tau -> ((

let uu____3885 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____3885));
(

let uu____3932 = (

let uu____3939 = (reify_tactic tau)
in (run_tactic_on_typ uu____3939 env typ))
in (match (uu____3932) with
| (gs, w) -> begin
(

let uu____3946 = (FStar_List.existsML (fun g -> (

let uu____3950 = (

let uu____3951 = (getprop g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Option.isSome uu____3951))
in (not (uu____3950)))) gs)
in (match (uu____3946) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("synthesis left open goals"), (typ.FStar_Syntax_Syntax.pos)))))
end
| uu____3954 -> begin
w
end))
end));
))




