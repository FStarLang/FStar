
open Prims
open FStar_Pervasives

let tacdbg : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let mktot1' : 'Auu____42 'Auu____43 'Auu____44 'Auu____45 . Prims.int  ->  Prims.string  ->  ('Auu____42  ->  'Auu____43)  ->  'Auu____42 FStar_Syntax_Embeddings.embedding  ->  'Auu____43 FStar_Syntax_Embeddings.embedding  ->  ('Auu____44  ->  'Auu____45)  ->  'Auu____44 FStar_TypeChecker_NBETerm.embedding  ->  'Auu____45 FStar_TypeChecker_NBETerm.embedding  ->  FStar_TypeChecker_Cfg.primitive_step = (fun uarity nm f ea er nf ena enr -> (

let uu___365_116 = (FStar_Tactics_InterpFuns.mktot1 uarity nm f ea er nf ena enr)
in (

let uu____117 = (FStar_Ident.lid_of_str (Prims.strcat "FStar.Tactics.Types." nm))
in {FStar_TypeChecker_Cfg.name = uu____117; FStar_TypeChecker_Cfg.arity = uu___365_116.FStar_TypeChecker_Cfg.arity; FStar_TypeChecker_Cfg.univ_arity = uu___365_116.FStar_TypeChecker_Cfg.univ_arity; FStar_TypeChecker_Cfg.auto_reflect = uu___365_116.FStar_TypeChecker_Cfg.auto_reflect; FStar_TypeChecker_Cfg.strong_reduction_ok = uu___365_116.FStar_TypeChecker_Cfg.strong_reduction_ok; FStar_TypeChecker_Cfg.requires_binder_substitution = uu___365_116.FStar_TypeChecker_Cfg.requires_binder_substitution; FStar_TypeChecker_Cfg.interpretation = uu___365_116.FStar_TypeChecker_Cfg.interpretation; FStar_TypeChecker_Cfg.interpretation_nbe = uu___365_116.FStar_TypeChecker_Cfg.interpretation_nbe})))


let mktot2' : 'Auu____152 'Auu____153 'Auu____154 'Auu____155 'Auu____156 'Auu____157 . Prims.int  ->  Prims.string  ->  ('Auu____152  ->  'Auu____153  ->  'Auu____154)  ->  'Auu____152 FStar_Syntax_Embeddings.embedding  ->  'Auu____153 FStar_Syntax_Embeddings.embedding  ->  'Auu____154 FStar_Syntax_Embeddings.embedding  ->  ('Auu____155  ->  'Auu____156  ->  'Auu____157)  ->  'Auu____155 FStar_TypeChecker_NBETerm.embedding  ->  'Auu____156 FStar_TypeChecker_NBETerm.embedding  ->  'Auu____157 FStar_TypeChecker_NBETerm.embedding  ->  FStar_TypeChecker_Cfg.primitive_step = (fun uarity nm f ea eb er nf ena enb enr -> (

let uu___366_256 = (FStar_Tactics_InterpFuns.mktot2 uarity nm f ea eb er nf ena enb enr)
in (

let uu____257 = (FStar_Ident.lid_of_str (Prims.strcat "FStar.Tactics.Types." nm))
in {FStar_TypeChecker_Cfg.name = uu____257; FStar_TypeChecker_Cfg.arity = uu___366_256.FStar_TypeChecker_Cfg.arity; FStar_TypeChecker_Cfg.univ_arity = uu___366_256.FStar_TypeChecker_Cfg.univ_arity; FStar_TypeChecker_Cfg.auto_reflect = uu___366_256.FStar_TypeChecker_Cfg.auto_reflect; FStar_TypeChecker_Cfg.strong_reduction_ok = uu___366_256.FStar_TypeChecker_Cfg.strong_reduction_ok; FStar_TypeChecker_Cfg.requires_binder_substitution = uu___366_256.FStar_TypeChecker_Cfg.requires_binder_substitution; FStar_TypeChecker_Cfg.interpretation = uu___366_256.FStar_TypeChecker_Cfg.interpretation; FStar_TypeChecker_Cfg.interpretation_nbe = uu___366_256.FStar_TypeChecker_Cfg.interpretation_nbe})))


let rec e_tactic_thunk : 'Ar . 'Ar FStar_Syntax_Embeddings.embedding  ->  'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding = (fun er -> (

let uu____566 = (FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Embeddings.mk_emb (fun uu____573 uu____574 uu____575 uu____576 -> (failwith "Impossible: embedding tactic (thunk)?")) (fun t w cb -> (

let uu____611 = (

let uu____614 = (unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb)
in (uu____614 ()))
in FStar_Pervasives_Native.Some (uu____611))) uu____566)))
and e_tactic_nbe_thunk : 'Ar . 'Ar FStar_TypeChecker_NBETerm.embedding  ->  'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding = (fun er -> (

let uu____628 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit)
in (FStar_TypeChecker_NBETerm.mk_emb (fun cb uu____634 -> (failwith "Impossible: NBE embedding tactic (thunk)?")) (fun cb t -> (

let uu____643 = (

let uu____646 = (unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t)
in (uu____646 ()))
in FStar_Pervasives_Native.Some (uu____643))) (FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit)) uu____628)))
and e_tactic_1 : 'Aa 'Ar . 'Aa FStar_Syntax_Embeddings.embedding  ->  'Ar FStar_Syntax_Embeddings.embedding  ->  ('Aa  ->  'Ar FStar_Tactics_Basic.tac) FStar_Syntax_Embeddings.embedding = (fun ea er -> (

let uu____661 = (FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Embeddings.mk_emb (fun uu____671 uu____672 uu____673 uu____674 -> (failwith "Impossible: embedding tactic (1)?")) (fun t w cb -> (

let uu____711 = (unembed_tactic_1 ea er t cb)
in FStar_Pervasives_Native.Some (uu____711))) uu____661)))
and e_tactic_nbe_1 : 'Aa 'Ar . 'Aa FStar_TypeChecker_NBETerm.embedding  ->  'Ar FStar_TypeChecker_NBETerm.embedding  ->  ('Aa  ->  'Ar FStar_Tactics_Basic.tac) FStar_TypeChecker_NBETerm.embedding = (fun ea er -> (

let uu____731 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit)
in (FStar_TypeChecker_NBETerm.mk_emb (fun cb uu____740 -> (failwith "Impossible: NBE embedding tactic (1)?")) (fun cb t -> (

let uu____751 = (unembed_tactic_nbe_1 ea er cb t)
in FStar_Pervasives_Native.Some (uu____751))) (FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit)) uu____731)))
and primitive_steps : unit  ->  FStar_TypeChecker_Cfg.primitive_step Prims.list = (fun uu____763 -> (

let uu____766 = (

let uu____769 = (mktot1' (Prims.parse_int "0") "tracepoint" FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate_nbe FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____772 = (

let uu____775 = (mktot2' (Prims.parse_int "0") "set_proofstate_range" FStar_Tactics_Types.set_proofstate_range FStar_Tactics_Embedding.e_proofstate FStar_Syntax_Embeddings.e_range FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.set_proofstate_range FStar_Tactics_Embedding.e_proofstate_nbe FStar_TypeChecker_NBETerm.e_range FStar_Tactics_Embedding.e_proofstate_nbe)
in (

let uu____778 = (

let uu____781 = (mktot1' (Prims.parse_int "0") "incr_depth" FStar_Tactics_Types.incr_depth FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.incr_depth FStar_Tactics_Embedding.e_proofstate_nbe FStar_Tactics_Embedding.e_proofstate_nbe)
in (

let uu____784 = (

let uu____787 = (mktot1' (Prims.parse_int "0") "decr_depth" FStar_Tactics_Types.decr_depth FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.decr_depth FStar_Tactics_Embedding.e_proofstate_nbe FStar_Tactics_Embedding.e_proofstate_nbe)
in (

let uu____790 = (

let uu____793 = (

let uu____794 = (FStar_Syntax_Embeddings.e_list FStar_Tactics_Embedding.e_goal)
in (

let uu____799 = (FStar_TypeChecker_NBETerm.e_list FStar_Tactics_Embedding.e_goal_nbe)
in (mktot1' (Prims.parse_int "0") "goals_of" FStar_Tactics_Types.goals_of FStar_Tactics_Embedding.e_proofstate uu____794 FStar_Tactics_Types.goals_of FStar_Tactics_Embedding.e_proofstate_nbe uu____799)))
in (

let uu____810 = (

let uu____813 = (

let uu____814 = (FStar_Syntax_Embeddings.e_list FStar_Tactics_Embedding.e_goal)
in (

let uu____819 = (FStar_TypeChecker_NBETerm.e_list FStar_Tactics_Embedding.e_goal_nbe)
in (mktot1' (Prims.parse_int "0") "smt_goals_of" FStar_Tactics_Types.smt_goals_of FStar_Tactics_Embedding.e_proofstate uu____814 FStar_Tactics_Types.smt_goals_of FStar_Tactics_Embedding.e_proofstate_nbe uu____819)))
in (

let uu____830 = (

let uu____833 = (mktot1' (Prims.parse_int "0") "goal_env" FStar_Tactics_Types.goal_env FStar_Tactics_Embedding.e_goal FStar_Reflection_Embeddings.e_env FStar_Tactics_Types.goal_env FStar_Tactics_Embedding.e_goal_nbe FStar_Reflection_NBEEmbeddings.e_env)
in (

let uu____836 = (

let uu____839 = (mktot1' (Prims.parse_int "0") "goal_type" FStar_Tactics_Types.goal_type FStar_Tactics_Embedding.e_goal FStar_Reflection_Embeddings.e_term FStar_Tactics_Types.goal_type FStar_Tactics_Embedding.e_goal_nbe FStar_Reflection_NBEEmbeddings.e_term)
in (

let uu____842 = (

let uu____845 = (mktot1' (Prims.parse_int "0") "goal_witness" FStar_Tactics_Types.goal_witness FStar_Tactics_Embedding.e_goal FStar_Reflection_Embeddings.e_term FStar_Tactics_Types.goal_witness FStar_Tactics_Embedding.e_goal_nbe FStar_Reflection_NBEEmbeddings.e_term)
in (

let uu____848 = (

let uu____851 = (mktot1' (Prims.parse_int "0") "is_guard" FStar_Tactics_Types.is_guard FStar_Tactics_Embedding.e_goal FStar_Syntax_Embeddings.e_bool FStar_Tactics_Types.is_guard FStar_Tactics_Embedding.e_goal_nbe FStar_TypeChecker_NBETerm.e_bool)
in (

let uu____856 = (

let uu____859 = (mktot1' (Prims.parse_int "0") "get_label" FStar_Tactics_Types.get_label FStar_Tactics_Embedding.e_goal FStar_Syntax_Embeddings.e_string FStar_Tactics_Types.get_label FStar_Tactics_Embedding.e_goal_nbe FStar_TypeChecker_NBETerm.e_string)
in (

let uu____864 = (

let uu____867 = (mktot2' (Prims.parse_int "0") "set_label" FStar_Tactics_Types.set_label FStar_Syntax_Embeddings.e_string FStar_Tactics_Embedding.e_goal FStar_Tactics_Embedding.e_goal FStar_Tactics_Types.set_label FStar_TypeChecker_NBETerm.e_string FStar_Tactics_Embedding.e_goal_nbe FStar_Tactics_Embedding.e_goal_nbe)
in (

let uu____872 = (

let uu____875 = (FStar_Tactics_InterpFuns.mktot2 (Prims.parse_int "0") "push_binder" (fun env b -> (FStar_TypeChecker_Env.push_binders env ((b)::[]))) FStar_Reflection_Embeddings.e_env FStar_Reflection_Embeddings.e_binder FStar_Reflection_Embeddings.e_env (fun env b -> (FStar_TypeChecker_Env.push_binders env ((b)::[]))) FStar_Reflection_NBEEmbeddings.e_env FStar_Reflection_NBEEmbeddings.e_binder FStar_Reflection_NBEEmbeddings.e_env)
in (

let uu____934 = (

let uu____937 = (

let uu____938 = (FStar_Syntax_Embeddings.e_list FStar_Tactics_Embedding.e_goal)
in (

let uu____943 = (FStar_TypeChecker_NBETerm.e_list FStar_Tactics_Embedding.e_goal_nbe)
in (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "set_goals" FStar_Tactics_Basic.set_goals uu____938 FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.set_goals uu____943 FStar_TypeChecker_NBETerm.e_unit)))
in (

let uu____954 = (

let uu____957 = (

let uu____958 = (FStar_Syntax_Embeddings.e_list FStar_Tactics_Embedding.e_goal)
in (

let uu____963 = (FStar_TypeChecker_NBETerm.e_list FStar_Tactics_Embedding.e_goal_nbe)
in (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "set_smt_goals" FStar_Tactics_Basic.set_smt_goals uu____958 FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.set_smt_goals uu____963 FStar_TypeChecker_NBETerm.e_unit)))
in (

let uu____974 = (

let uu____977 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "trivial" FStar_Tactics_Basic.trivial FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.trivial FStar_TypeChecker_NBETerm.e_unit FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____980 = (

let uu____983 = (

let uu____984 = (e_tactic_thunk FStar_Syntax_Embeddings.e_any)
in (

let uu____989 = (FStar_Syntax_Embeddings.e_either FStar_Tactics_Embedding.e_exn FStar_Syntax_Embeddings.e_any)
in (

let uu____996 = (e_tactic_nbe_thunk FStar_TypeChecker_NBETerm.e_any)
in (

let uu____1001 = (FStar_TypeChecker_NBETerm.e_either FStar_Tactics_Embedding.e_exn_nbe FStar_TypeChecker_NBETerm.e_any)
in (FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1") "catch" (fun uu____1023 -> FStar_Tactics_Basic.catch) FStar_Syntax_Embeddings.e_any uu____984 uu____989 (fun uu____1025 -> FStar_Tactics_Basic.catch) FStar_TypeChecker_NBETerm.e_any uu____996 uu____1001)))))
in (

let uu____1026 = (

let uu____1029 = (

let uu____1030 = (e_tactic_thunk FStar_Syntax_Embeddings.e_any)
in (

let uu____1035 = (FStar_Syntax_Embeddings.e_either FStar_Tactics_Embedding.e_exn FStar_Syntax_Embeddings.e_any)
in (

let uu____1042 = (e_tactic_nbe_thunk FStar_TypeChecker_NBETerm.e_any)
in (

let uu____1047 = (FStar_TypeChecker_NBETerm.e_either FStar_Tactics_Embedding.e_exn_nbe FStar_TypeChecker_NBETerm.e_any)
in (FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1") "recover" (fun uu____1069 -> FStar_Tactics_Basic.recover) FStar_Syntax_Embeddings.e_any uu____1030 uu____1035 (fun uu____1071 -> FStar_Tactics_Basic.recover) FStar_TypeChecker_NBETerm.e_any uu____1042 uu____1047)))))
in (

let uu____1072 = (

let uu____1075 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "intro" FStar_Tactics_Basic.intro FStar_Syntax_Embeddings.e_unit FStar_Reflection_Embeddings.e_binder FStar_Tactics_Basic.intro FStar_TypeChecker_NBETerm.e_unit FStar_Reflection_NBEEmbeddings.e_binder)
in (

let uu____1078 = (

let uu____1081 = (

let uu____1082 = (FStar_Syntax_Embeddings.e_tuple2 FStar_Reflection_Embeddings.e_binder FStar_Reflection_Embeddings.e_binder)
in (

let uu____1089 = (FStar_TypeChecker_NBETerm.e_tuple2 FStar_Reflection_NBEEmbeddings.e_binder FStar_Reflection_NBEEmbeddings.e_binder)
in (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "intro_rec" FStar_Tactics_Basic.intro_rec FStar_Syntax_Embeddings.e_unit uu____1082 FStar_Tactics_Basic.intro_rec FStar_TypeChecker_NBETerm.e_unit uu____1089)))
in (

let uu____1106 = (

let uu____1109 = (

let uu____1110 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_norm_step)
in (

let uu____1115 = (FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_norm_step)
in (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "norm" FStar_Tactics_Basic.norm uu____1110 FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.norm uu____1115 FStar_TypeChecker_NBETerm.e_unit)))
in (

let uu____1126 = (

let uu____1129 = (

let uu____1130 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_norm_step)
in (

let uu____1135 = (FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_norm_step)
in (FStar_Tactics_InterpFuns.mktac3 (Prims.parse_int "0") "norm_term_env" FStar_Tactics_Basic.norm_term_env FStar_Reflection_Embeddings.e_env uu____1130 FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_term FStar_Tactics_Basic.norm_term_env FStar_Reflection_NBEEmbeddings.e_env uu____1135 FStar_Reflection_NBEEmbeddings.e_term FStar_Reflection_NBEEmbeddings.e_term)))
in (

let uu____1146 = (

let uu____1149 = (

let uu____1150 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_norm_step)
in (

let uu____1155 = (FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_norm_step)
in (FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "0") "norm_binder_type" FStar_Tactics_Basic.norm_binder_type uu____1150 FStar_Reflection_Embeddings.e_binder FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.norm_binder_type uu____1155 FStar_Reflection_NBEEmbeddings.e_binder FStar_TypeChecker_NBETerm.e_unit)))
in (

let uu____1166 = (

let uu____1169 = (FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "0") "rename_to" FStar_Tactics_Basic.rename_to FStar_Reflection_Embeddings.e_binder FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.rename_to FStar_Reflection_NBEEmbeddings.e_binder FStar_TypeChecker_NBETerm.e_string FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1174 = (

let uu____1177 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "binder_retype" FStar_Tactics_Basic.binder_retype FStar_Reflection_Embeddings.e_binder FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.binder_retype FStar_Reflection_NBEEmbeddings.e_binder FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1180 = (

let uu____1183 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "revert" FStar_Tactics_Basic.revert FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.revert FStar_TypeChecker_NBETerm.e_unit FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1186 = (

let uu____1189 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "clear_top" FStar_Tactics_Basic.clear_top FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.clear_top FStar_TypeChecker_NBETerm.e_unit FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1192 = (

let uu____1195 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "clear" FStar_Tactics_Basic.clear FStar_Reflection_Embeddings.e_binder FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.clear FStar_Reflection_NBEEmbeddings.e_binder FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1198 = (

let uu____1201 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "rewrite" FStar_Tactics_Basic.rewrite FStar_Reflection_Embeddings.e_binder FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.rewrite FStar_Reflection_NBEEmbeddings.e_binder FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1204 = (

let uu____1207 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "refine_intro" FStar_Tactics_Basic.refine_intro FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.refine_intro FStar_TypeChecker_NBETerm.e_unit FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1210 = (

let uu____1213 = (FStar_Tactics_InterpFuns.mktac3 (Prims.parse_int "0") "t_exact" FStar_Tactics_Basic.t_exact FStar_Syntax_Embeddings.e_bool FStar_Syntax_Embeddings.e_bool FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.t_exact FStar_TypeChecker_NBETerm.e_bool FStar_TypeChecker_NBETerm.e_bool FStar_Reflection_NBEEmbeddings.e_term FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1220 = (

let uu____1223 = (FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1") "t_apply" FStar_Tactics_Basic.t_apply FStar_Syntax_Embeddings.e_bool FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.t_apply FStar_TypeChecker_NBETerm.e_bool FStar_Reflection_NBEEmbeddings.e_term FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1228 = (

let uu____1231 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "apply_lemma" FStar_Tactics_Basic.apply_lemma FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.apply_lemma FStar_Reflection_NBEEmbeddings.e_term FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1234 = (

let uu____1237 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "set_options" FStar_Tactics_Basic.set_options FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.set_options FStar_TypeChecker_NBETerm.e_string FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1242 = (

let uu____1245 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "tc" FStar_Tactics_Basic.tc FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_term FStar_Tactics_Basic.tc FStar_Reflection_NBEEmbeddings.e_term FStar_Reflection_NBEEmbeddings.e_term)
in (

let uu____1248 = (

let uu____1251 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "unshelve" FStar_Tactics_Basic.unshelve FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.unshelve FStar_Reflection_NBEEmbeddings.e_term FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1254 = (

let uu____1257 = (FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1") "unquote" FStar_Tactics_Basic.unquote FStar_Syntax_Embeddings.e_any FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_any (fun uu____1262 uu____1263 -> (failwith "NBE unquote")) FStar_TypeChecker_NBETerm.e_any FStar_Reflection_NBEEmbeddings.e_term FStar_TypeChecker_NBETerm.e_any)
in (

let uu____1267 = (

let uu____1270 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "prune" FStar_Tactics_Basic.prune FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.prune FStar_TypeChecker_NBETerm.e_string FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1275 = (

let uu____1278 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "addns" FStar_Tactics_Basic.addns FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.addns FStar_TypeChecker_NBETerm.e_string FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1283 = (

let uu____1286 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "print" FStar_Tactics_Basic.print FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.print FStar_TypeChecker_NBETerm.e_string FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1291 = (

let uu____1294 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "debugging" FStar_Tactics_Basic.debugging FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_bool FStar_Tactics_Basic.debugging FStar_TypeChecker_NBETerm.e_unit FStar_TypeChecker_NBETerm.e_bool)
in (

let uu____1299 = (

let uu____1302 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "dump" FStar_Tactics_Basic.print_proof_state FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.print_proof_state FStar_TypeChecker_NBETerm.e_string FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1307 = (

let uu____1310 = (

let uu____1311 = (e_tactic_thunk FStar_Syntax_Embeddings.e_unit)
in (

let uu____1316 = (e_tactic_nbe_thunk FStar_TypeChecker_NBETerm.e_unit)
in (FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "0") "t_pointwise" FStar_Tactics_Basic.pointwise FStar_Tactics_Embedding.e_direction uu____1311 FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.pointwise FStar_Tactics_Embedding.e_direction_nbe uu____1316 FStar_TypeChecker_NBETerm.e_unit)))
in (

let uu____1327 = (

let uu____1330 = (

let uu____1331 = (

let uu____1344 = (FStar_Syntax_Embeddings.e_tuple2 FStar_Syntax_Embeddings.e_bool FStar_Syntax_Embeddings.e_int)
in (e_tactic_1 FStar_Reflection_Embeddings.e_term uu____1344))
in (

let uu____1358 = (e_tactic_thunk FStar_Syntax_Embeddings.e_unit)
in (

let uu____1363 = (

let uu____1376 = (FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_bool FStar_TypeChecker_NBETerm.e_int)
in (e_tactic_nbe_1 FStar_Reflection_NBEEmbeddings.e_term uu____1376))
in (

let uu____1390 = (e_tactic_nbe_thunk FStar_TypeChecker_NBETerm.e_unit)
in (FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "0") "topdown_rewrite" FStar_Tactics_Basic.topdown_rewrite uu____1331 uu____1358 FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.topdown_rewrite uu____1363 uu____1390 FStar_TypeChecker_NBETerm.e_unit)))))
in (

let uu____1421 = (

let uu____1424 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "trefl" FStar_Tactics_Basic.trefl FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.trefl FStar_TypeChecker_NBETerm.e_unit FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1427 = (

let uu____1430 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "dup" FStar_Tactics_Basic.dup FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.dup FStar_TypeChecker_NBETerm.e_unit FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1433 = (

let uu____1436 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "tadmit_t" FStar_Tactics_Basic.tadmit_t FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.tadmit_t FStar_Reflection_NBEEmbeddings.e_term FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1439 = (

let uu____1442 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "join" FStar_Tactics_Basic.join FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.join FStar_TypeChecker_NBETerm.e_unit FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1445 = (

let uu____1448 = (

let uu____1449 = (FStar_Syntax_Embeddings.e_tuple2 FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_term)
in (

let uu____1456 = (FStar_TypeChecker_NBETerm.e_tuple2 FStar_Reflection_NBEEmbeddings.e_term FStar_Reflection_NBEEmbeddings.e_term)
in (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "cases" FStar_Tactics_Basic.cases FStar_Reflection_Embeddings.e_term uu____1449 FStar_Tactics_Basic.cases FStar_Reflection_NBEEmbeddings.e_term uu____1456)))
in (

let uu____1473 = (

let uu____1476 = (

let uu____1477 = (

let uu____1486 = (FStar_Syntax_Embeddings.e_tuple2 FStar_Reflection_Embeddings.e_fv FStar_Syntax_Embeddings.e_int)
in (FStar_Syntax_Embeddings.e_list uu____1486))
in (

let uu____1497 = (

let uu____1506 = (FStar_TypeChecker_NBETerm.e_tuple2 FStar_Reflection_NBEEmbeddings.e_fv FStar_TypeChecker_NBETerm.e_int)
in (FStar_TypeChecker_NBETerm.e_list uu____1506))
in (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "t_destruct" FStar_Tactics_Basic.t_destruct FStar_Reflection_Embeddings.e_term uu____1477 FStar_Tactics_Basic.t_destruct FStar_Reflection_NBEEmbeddings.e_term uu____1497)))
in (

let uu____1531 = (

let uu____1534 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "top_env" FStar_Tactics_Basic.top_env FStar_Syntax_Embeddings.e_unit FStar_Reflection_Embeddings.e_env FStar_Tactics_Basic.top_env FStar_TypeChecker_NBETerm.e_unit FStar_Reflection_NBEEmbeddings.e_env)
in (

let uu____1537 = (

let uu____1540 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "inspect" FStar_Tactics_Basic.inspect FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_term_view FStar_Tactics_Basic.inspect FStar_Reflection_NBEEmbeddings.e_term FStar_Reflection_NBEEmbeddings.e_term_view)
in (

let uu____1543 = (

let uu____1546 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "pack" FStar_Tactics_Basic.pack FStar_Reflection_Embeddings.e_term_view FStar_Reflection_Embeddings.e_term FStar_Tactics_Basic.pack FStar_Reflection_NBEEmbeddings.e_term_view FStar_Reflection_NBEEmbeddings.e_term)
in (

let uu____1549 = (

let uu____1552 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "fresh" FStar_Tactics_Basic.fresh FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_int FStar_Tactics_Basic.fresh FStar_TypeChecker_NBETerm.e_unit FStar_TypeChecker_NBETerm.e_int)
in (

let uu____1555 = (

let uu____1558 = (

let uu____1559 = (FStar_Syntax_Embeddings.e_option FStar_Reflection_Embeddings.e_term)
in (

let uu____1564 = (FStar_TypeChecker_NBETerm.e_option FStar_Reflection_NBEEmbeddings.e_term)
in (FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "0") "uvar_env" FStar_Tactics_Basic.uvar_env FStar_Reflection_Embeddings.e_env uu____1559 FStar_Reflection_Embeddings.e_term FStar_Tactics_Basic.uvar_env FStar_Reflection_NBEEmbeddings.e_env uu____1564 FStar_Reflection_NBEEmbeddings.e_term)))
in (

let uu____1575 = (

let uu____1578 = (FStar_Tactics_InterpFuns.mktac3 (Prims.parse_int "0") "unify_env" FStar_Tactics_Basic.unify_env FStar_Reflection_Embeddings.e_env FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_bool FStar_Tactics_Basic.unify_env FStar_Reflection_NBEEmbeddings.e_env FStar_Reflection_NBEEmbeddings.e_term FStar_Reflection_NBEEmbeddings.e_term FStar_TypeChecker_NBETerm.e_bool)
in (

let uu____1583 = (

let uu____1586 = (

let uu____1587 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string)
in (

let uu____1594 = (FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_string)
in (FStar_Tactics_InterpFuns.mktac3 (Prims.parse_int "0") "launch_process" FStar_Tactics_Basic.launch_process FStar_Syntax_Embeddings.e_string uu____1587 FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_string FStar_Tactics_Basic.launch_process FStar_TypeChecker_NBETerm.e_string uu____1594 FStar_TypeChecker_NBETerm.e_string FStar_TypeChecker_NBETerm.e_string)))
in (

let uu____1615 = (

let uu____1618 = (FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "0") "fresh_bv_named" FStar_Tactics_Basic.fresh_bv_named FStar_Syntax_Embeddings.e_string FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_bv FStar_Tactics_Basic.fresh_bv_named FStar_TypeChecker_NBETerm.e_string FStar_Reflection_NBEEmbeddings.e_term FStar_Reflection_NBEEmbeddings.e_bv)
in (

let uu____1623 = (

let uu____1626 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "change" FStar_Tactics_Basic.change FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.change FStar_Reflection_NBEEmbeddings.e_term FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1629 = (

let uu____1632 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "get_guard_policy" FStar_Tactics_Basic.get_guard_policy FStar_Syntax_Embeddings.e_unit FStar_Tactics_Embedding.e_guard_policy FStar_Tactics_Basic.get_guard_policy FStar_TypeChecker_NBETerm.e_unit FStar_Tactics_Embedding.e_guard_policy_nbe)
in (

let uu____1635 = (

let uu____1638 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "set_guard_policy" FStar_Tactics_Basic.set_guard_policy FStar_Tactics_Embedding.e_guard_policy FStar_Syntax_Embeddings.e_unit FStar_Tactics_Basic.set_guard_policy FStar_Tactics_Embedding.e_guard_policy_nbe FStar_TypeChecker_NBETerm.e_unit)
in (

let uu____1641 = (

let uu____1644 = (FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0") "lax_on" FStar_Tactics_Basic.lax_on FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_bool FStar_Tactics_Basic.lax_on FStar_TypeChecker_NBETerm.e_unit FStar_TypeChecker_NBETerm.e_bool)
in (

let uu____1649 = (

let uu____1652 = (FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1") "lget" FStar_Tactics_Basic.lget FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_any (fun uu____1659 uu____1660 -> (FStar_Tactics_Basic.fail "sorry, `lget` does not work in NBE")) FStar_TypeChecker_NBETerm.e_any FStar_TypeChecker_NBETerm.e_string FStar_TypeChecker_NBETerm.e_any)
in (

let uu____1663 = (

let uu____1666 = (FStar_Tactics_InterpFuns.mktac3 (Prims.parse_int "1") "lset" FStar_Tactics_Basic.lset FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_unit (fun uu____1674 uu____1675 uu____1676 -> (FStar_Tactics_Basic.fail "sorry, `lset` does not work in NBE")) FStar_TypeChecker_NBETerm.e_any FStar_TypeChecker_NBETerm.e_string FStar_TypeChecker_NBETerm.e_any FStar_TypeChecker_NBETerm.e_unit)
in (uu____1666)::[])
in (uu____1652)::uu____1663))
in (uu____1644)::uu____1649))
in (uu____1638)::uu____1641))
in (uu____1632)::uu____1635))
in (uu____1626)::uu____1629))
in (uu____1618)::uu____1623))
in (uu____1586)::uu____1615))
in (uu____1578)::uu____1583))
in (uu____1558)::uu____1575))
in (uu____1552)::uu____1555))
in (uu____1546)::uu____1549))
in (uu____1540)::uu____1543))
in (uu____1534)::uu____1537))
in (uu____1476)::uu____1531))
in (uu____1448)::uu____1473))
in (uu____1442)::uu____1445))
in (uu____1436)::uu____1439))
in (uu____1430)::uu____1433))
in (uu____1424)::uu____1427))
in (uu____1330)::uu____1421))
in (uu____1310)::uu____1327))
in (uu____1302)::uu____1307))
in (uu____1294)::uu____1299))
in (uu____1286)::uu____1291))
in (uu____1278)::uu____1283))
in (uu____1270)::uu____1275))
in (uu____1257)::uu____1267))
in (uu____1251)::uu____1254))
in (uu____1245)::uu____1248))
in (uu____1237)::uu____1242))
in (uu____1231)::uu____1234))
in (uu____1223)::uu____1228))
in (uu____1213)::uu____1220))
in (uu____1207)::uu____1210))
in (uu____1201)::uu____1204))
in (uu____1195)::uu____1198))
in (uu____1189)::uu____1192))
in (uu____1183)::uu____1186))
in (uu____1177)::uu____1180))
in (uu____1169)::uu____1174))
in (uu____1149)::uu____1166))
in (uu____1129)::uu____1146))
in (uu____1109)::uu____1126))
in (uu____1081)::uu____1106))
in (uu____1075)::uu____1078))
in (uu____1029)::uu____1072))
in (uu____983)::uu____1026))
in (uu____977)::uu____980))
in (uu____957)::uu____974))
in (uu____937)::uu____954))
in (uu____875)::uu____934))
in (uu____867)::uu____872))
in (uu____859)::uu____864))
in (uu____851)::uu____856))
in (uu____845)::uu____848))
in (uu____839)::uu____842))
in (uu____833)::uu____836))
in (uu____813)::uu____830))
in (uu____793)::uu____810))
in (uu____787)::uu____790))
in (uu____781)::uu____784))
in (uu____775)::uu____778))
in (uu____769)::uu____772))
in (

let uu____1679 = (

let uu____1682 = (FStar_Tactics_InterpFuns.native_tactics_steps ())
in (FStar_List.append FStar_Reflection_Interpreter.reflection_primops uu____1682))
in (FStar_List.append uu____766 uu____1679))))
and unembed_tactic_1 : 'Aa 'Ar . 'Aa FStar_Syntax_Embeddings.embedding  ->  'Ar FStar_Syntax_Embeddings.embedding  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Embeddings.norm_cb  ->  'Aa  ->  'Ar FStar_Tactics_Basic.tac = (fun ea er f ncb x -> (

let rng = FStar_Range.dummyRange
in (

let x_tm = (FStar_Tactics_InterpFuns.embed ea rng x ncb)
in (

let app = (

let uu____1703 = (

let uu____1708 = (

let uu____1709 = (FStar_Syntax_Syntax.as_arg x_tm)
in (uu____1709)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f uu____1708))
in (uu____1703 FStar_Pervasives_Native.None rng))
in (unembed_tactic_0 er app ncb)))))
and unembed_tactic_0 : 'Ab . 'Ab FStar_Syntax_Embeddings.embedding  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Embeddings.norm_cb  ->  'Ab FStar_Tactics_Basic.tac = (fun eb embedded_tac_b ncb -> (FStar_Tactics_Basic.bind FStar_Tactics_Basic.get (fun proof_state -> (

let rng = embedded_tac_b.FStar_Syntax_Syntax.pos
in (

let embedded_tac_b1 = (FStar_Syntax_Util.mk_reify embedded_tac_b)
in (

let tm = (

let uu____1766 = (

let uu____1771 = (

let uu____1772 = (

let uu____1781 = (FStar_Tactics_InterpFuns.embed FStar_Tactics_Embedding.e_proofstate rng proof_state ncb)
in (FStar_Syntax_Syntax.as_arg uu____1781))
in (uu____1772)::[])
in (FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____1771))
in (uu____1766 FStar_Pervasives_Native.None rng))
in (

let steps = (FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.UnfoldTac)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Unascribe)::[]
in (

let norm_f = (

let uu____1826 = (FStar_Options.tactics_nbe ())
in (match (uu____1826) with
| true -> begin
FStar_TypeChecker_NBE.normalize
end
| uu____1845 -> begin
FStar_TypeChecker_Normalize.normalize_with_primitive_steps
end))
in ((match (proof_state.FStar_Tactics_Types.tac_verb_dbg) with
| true -> begin
(

let uu____1849 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Starting normalizer with %s\n" uu____1849))
end
| uu____1852 -> begin
()
end);
(

let result = (

let uu____1855 = (primitive_steps ())
in (norm_f uu____1855 steps proof_state.FStar_Tactics_Types.main_context tm))
in ((match (proof_state.FStar_Tactics_Types.tac_verb_dbg) with
| true -> begin
(

let uu____1860 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print1 "Reduced tactic: got %s\n" uu____1860))
end
| uu____1863 -> begin
()
end);
(

let res = (

let uu____1870 = (FStar_Tactics_Embedding.e_result eb)
in (FStar_Tactics_InterpFuns.unembed uu____1870 result ncb))
in (match (res) with
| FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success (b, ps)) -> begin
(

let uu____1885 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____1885 (fun uu____1889 -> (FStar_Tactics_Basic.ret b))))
end
| FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed (e, ps)) -> begin
(

let uu____1894 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____1894 (fun uu____1898 -> (FStar_Tactics_Basic.traise e))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1901 = (

let uu____1907 = (

let uu____1909 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.format1 "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s" uu____1909))
in ((FStar_Errors.Fatal_TacticGotStuck), (uu____1907)))
in (FStar_Errors.raise_error uu____1901 proof_state.FStar_Tactics_Types.main_context.FStar_TypeChecker_Env.range))
end));
));
)))))))))
and unembed_tactic_nbe_1 : 'Aa 'Ar . 'Aa FStar_TypeChecker_NBETerm.embedding  ->  'Ar FStar_TypeChecker_NBETerm.embedding  ->  FStar_TypeChecker_NBETerm.nbe_cbs  ->  FStar_TypeChecker_NBETerm.t  ->  'Aa  ->  'Ar FStar_Tactics_Basic.tac = (fun ea er cb f x -> (

let x_tm = (FStar_TypeChecker_NBETerm.embed ea cb x)
in (

let app = (

let uu____1926 = (

let uu____1927 = (FStar_TypeChecker_NBETerm.as_arg x_tm)
in (uu____1927)::[])
in (FStar_TypeChecker_NBETerm.iapp_cb cb f uu____1926))
in (unembed_tactic_nbe_0 er cb app))))
and unembed_tactic_nbe_0 : 'Ab . 'Ab FStar_TypeChecker_NBETerm.embedding  ->  FStar_TypeChecker_NBETerm.nbe_cbs  ->  FStar_TypeChecker_NBETerm.t  ->  'Ab FStar_Tactics_Basic.tac = (fun eb cb embedded_tac_b -> (FStar_Tactics_Basic.bind FStar_Tactics_Basic.get (fun proof_state -> (

let result = (

let uu____1953 = (

let uu____1954 = (

let uu____1959 = (FStar_TypeChecker_NBETerm.embed FStar_Tactics_Embedding.e_proofstate_nbe cb proof_state)
in (FStar_TypeChecker_NBETerm.as_arg uu____1959))
in (uu____1954)::[])
in (FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____1953))
in (

let res = (

let uu____1973 = (FStar_Tactics_Embedding.e_result_nbe eb)
in (FStar_TypeChecker_NBETerm.unembed uu____1973 cb result))
in (match (res) with
| FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success (b, ps)) -> begin
(

let uu____1986 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____1986 (fun uu____1990 -> (FStar_Tactics_Basic.ret b))))
end
| FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed (e, ps)) -> begin
(

let uu____1995 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____1995 (fun uu____1999 -> (FStar_Tactics_Basic.traise e))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2002 = (

let uu____2008 = (

let uu____2010 = (FStar_TypeChecker_NBETerm.t_to_string result)
in (FStar_Util.format1 "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s" uu____2010))
in ((FStar_Errors.Fatal_TacticGotStuck), (uu____2008)))
in (FStar_Errors.raise_error uu____2002 proof_state.FStar_Tactics_Types.main_context.FStar_TypeChecker_Env.range))
end))))))
and unembed_tactic_1_alt : 'Aa 'Ar . 'Aa FStar_Syntax_Embeddings.embedding  ->  'Ar FStar_Syntax_Embeddings.embedding  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Embeddings.norm_cb  ->  ('Aa  ->  'Ar FStar_Tactics_Basic.tac) FStar_Pervasives_Native.option = (fun ea er f ncb -> FStar_Pervasives_Native.Some ((fun x -> (

let rng = FStar_Range.dummyRange
in (

let x_tm = (FStar_Tactics_InterpFuns.embed ea rng x ncb)
in (

let app = (

let uu____2043 = (

let uu____2048 = (

let uu____2049 = (FStar_Syntax_Syntax.as_arg x_tm)
in (uu____2049)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f uu____2048))
in (uu____2043 FStar_Pervasives_Native.None rng))
in (unembed_tactic_0 er app ncb)))))))
and e_tactic_1_alt : 'Aa 'Ar . 'Aa FStar_Syntax_Embeddings.embedding  ->  'Ar FStar_Syntax_Embeddings.embedding  ->  ('Aa  ->  FStar_Tactics_Types.proofstate  ->  'Ar FStar_Tactics_Result.__result) FStar_Syntax_Embeddings.embedding = (fun ea er -> (

let em = (fun uu____2130 uu____2131 uu____2132 uu____2133 -> (failwith "Impossible: embedding tactic (1)?"))
in (

let un = (fun t0 w n1 -> (

let uu____2204 = (unembed_tactic_1_alt ea er t0 n1)
in (match (uu____2204) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some ((fun x -> (

let uu____2246 = (f x)
in (FStar_Tactics_Basic.run uu____2246))))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____2262 = (FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Embeddings.mk_emb em un uu____2262)))))


let report_implicits : FStar_Range.range  ->  FStar_TypeChecker_Env.implicits  ->  unit = (fun rng is -> (

let errs = (FStar_List.map (fun imp -> (

let uu____2302 = (

let uu____2304 = (FStar_Syntax_Print.uvar_to_string imp.FStar_TypeChecker_Env.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____2306 = (FStar_Syntax_Print.term_to_string imp.FStar_TypeChecker_Env.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format3 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")" uu____2304 uu____2306 imp.FStar_TypeChecker_Env.imp_reason)))
in ((FStar_Errors.Error_UninstantiatedUnificationVarInTactic), (uu____2302), (rng)))) is)
in ((FStar_Errors.add_errors errs);
(FStar_Errors.stop_if_err ());
)))


let run_tactic_on_typ : FStar_Range.range  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Tactics_Types.goal Prims.list * FStar_Syntax_Syntax.term) = (fun rng_tac rng_goal tactic env typ -> ((

let uu____2350 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2350) with
| true -> begin
(

let uu____2374 = (FStar_Syntax_Print.term_to_string tactic)
in (FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____2374))
end
| uu____2377 -> begin
()
end));
(

let uu____2379 = (FStar_TypeChecker_TcTerm.tc_tactic env tactic)
in (match (uu____2379) with
| (uu____2392, uu____2393, g) -> begin
((

let uu____2396 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2396) with
| true -> begin
(FStar_Util.print_string "}\n")
end
| uu____2421 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g);
(FStar_Errors.stop_if_err ());
(

let tau = (unembed_tactic_1 FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit tactic FStar_Syntax_Embeddings.id_norm_cb)
in (

let uu____2432 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____2432) with
| (env1, uu____2446) -> begin
(

let env2 = (

let uu___367_2452 = env1
in {FStar_TypeChecker_Env.solver = uu___367_2452.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___367_2452.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___367_2452.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___367_2452.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___367_2452.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___367_2452.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___367_2452.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___367_2452.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___367_2452.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___367_2452.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___367_2452.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___367_2452.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___367_2452.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___367_2452.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___367_2452.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___367_2452.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___367_2452.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___367_2452.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___367_2452.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___367_2452.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___367_2452.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___367_2452.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___367_2452.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___367_2452.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___367_2452.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___367_2452.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___367_2452.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___367_2452.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___367_2452.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___367_2452.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___367_2452.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___367_2452.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___367_2452.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___367_2452.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___367_2452.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___367_2452.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___367_2452.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___367_2452.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___367_2452.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___367_2452.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___367_2452.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___367_2452.FStar_TypeChecker_Env.nbe})
in (

let env3 = (

let uu___368_2455 = env2
in {FStar_TypeChecker_Env.solver = uu___368_2455.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___368_2455.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___368_2455.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___368_2455.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___368_2455.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___368_2455.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___368_2455.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___368_2455.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___368_2455.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___368_2455.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___368_2455.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___368_2455.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___368_2455.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___368_2455.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___368_2455.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___368_2455.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___368_2455.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___368_2455.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___368_2455.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___368_2455.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___368_2455.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.phase1 = uu___368_2455.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___368_2455.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___368_2455.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___368_2455.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___368_2455.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___368_2455.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___368_2455.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___368_2455.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___368_2455.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___368_2455.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___368_2455.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___368_2455.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___368_2455.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___368_2455.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___368_2455.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___368_2455.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___368_2455.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___368_2455.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___368_2455.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___368_2455.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___368_2455.FStar_TypeChecker_Env.nbe})
in (

let env4 = (

let uu___369_2458 = env3
in {FStar_TypeChecker_Env.solver = uu___369_2458.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___369_2458.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___369_2458.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___369_2458.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___369_2458.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___369_2458.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___369_2458.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___369_2458.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___369_2458.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___369_2458.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___369_2458.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___369_2458.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___369_2458.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___369_2458.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___369_2458.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___369_2458.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___369_2458.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___369_2458.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___369_2458.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___369_2458.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___369_2458.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___369_2458.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___369_2458.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___369_2458.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___369_2458.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___369_2458.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___369_2458.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___369_2458.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___369_2458.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___369_2458.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___369_2458.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___369_2458.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___369_2458.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___369_2458.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___369_2458.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___369_2458.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___369_2458.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___369_2458.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___369_2458.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___369_2458.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___369_2458.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___369_2458.FStar_TypeChecker_Env.nbe})
in (

let rng = (

let uu____2461 = (FStar_Range.use_range rng_goal)
in (

let uu____2462 = (FStar_Range.use_range rng_tac)
in (FStar_Range.range_of_rng uu____2461 uu____2462)))
in (

let uu____2463 = (FStar_Tactics_Basic.proofstate_of_goal_ty rng env4 typ)
in (match (uu____2463) with
| (ps, w) -> begin
((FStar_ST.op_Colon_Equals FStar_Reflection_Basic.env_hook (FStar_Pervasives_Native.Some (env4)));
(

let uu____2501 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2501) with
| true -> begin
(

let uu____2525 = (FStar_Syntax_Print.term_to_string typ)
in (FStar_Util.print1 "Running tactic with goal = (%s) {\n" uu____2525))
end
| uu____2528 -> begin
()
end));
(

let uu____2530 = (FStar_Util.record_time (fun uu____2542 -> (

let uu____2543 = (tau ())
in (FStar_Tactics_Basic.run_safe uu____2543 ps))))
in (match (uu____2530) with
| (res, ms) -> begin
((

let uu____2561 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2561) with
| true -> begin
(FStar_Util.print_string "}\n")
end
| uu____2586 -> begin
()
end));
(

let uu____2589 = ((FStar_ST.op_Bang tacdbg) || (FStar_Options.tactics_info ()))
in (match (uu____2589) with
| true -> begin
(

let uu____2613 = (FStar_Syntax_Print.term_to_string tactic)
in (

let uu____2615 = (FStar_Util.string_of_int ms)
in (

let uu____2617 = (FStar_Syntax_Print.lid_to_string env4.FStar_TypeChecker_Env.curmodule)
in (FStar_Util.print3 "Tactic %s ran in %s ms (%s)\n" uu____2613 uu____2615 uu____2617))))
end
| uu____2620 -> begin
()
end));
(match (res) with
| FStar_Tactics_Result.Success (uu____2628, ps1) -> begin
((

let uu____2631 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2631) with
| true -> begin
(

let uu____2655 = (FStar_Syntax_Print.term_to_string w)
in (FStar_Util.print1 "Tactic generated proofterm %s\n" uu____2655))
end
| uu____2658 -> begin
()
end));
(FStar_List.iter (fun g1 -> (

let uu____2665 = (FStar_Tactics_Basic.is_irrelevant g1)
in (match (uu____2665) with
| true -> begin
(

let uu____2668 = (

let uu____2670 = (FStar_Tactics_Types.goal_env g1)
in (

let uu____2671 = (FStar_Tactics_Types.goal_witness g1)
in (FStar_TypeChecker_Rel.teq_nosmt_force uu____2670 uu____2671 FStar_Syntax_Util.exp_unit)))
in (match (uu____2668) with
| true -> begin
()
end
| uu____2673 -> begin
(

let uu____2675 = (

let uu____2677 = (

let uu____2679 = (FStar_Tactics_Types.goal_witness g1)
in (FStar_Syntax_Print.term_to_string uu____2679))
in (FStar_Util.format1 "Irrelevant tactic witness does not unify with (): %s" uu____2677))
in (failwith uu____2675))
end))
end
| uu____2681 -> begin
()
end))) (FStar_List.append ps1.FStar_Tactics_Types.goals ps1.FStar_Tactics_Types.smt_goals));
(

let uu____2684 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2684) with
| true -> begin
(

let uu____2708 = (FStar_Common.string_of_list (fun imp -> (FStar_Syntax_Print.ctx_uvar_to_string imp.FStar_TypeChecker_Env.imp_uvar)) ps1.FStar_Tactics_Types.all_implicits)
in (FStar_Util.print1 "About to check tactic implicits: %s\n" uu____2708))
end
| uu____2713 -> begin
()
end));
(

let g1 = (

let uu___370_2716 = FStar_TypeChecker_Env.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___370_2716.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___370_2716.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___370_2716.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = ps1.FStar_Tactics_Types.all_implicits})
in (

let g2 = (FStar_TypeChecker_Rel.solve_deferred_constraints env4 g1)
in ((

let uu____2719 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2719) with
| true -> begin
(

let uu____2743 = (FStar_Util.string_of_int (FStar_List.length ps1.FStar_Tactics_Types.all_implicits))
in (

let uu____2745 = (FStar_Common.string_of_list (fun imp -> (FStar_Syntax_Print.ctx_uvar_to_string imp.FStar_TypeChecker_Env.imp_uvar)) ps1.FStar_Tactics_Types.all_implicits)
in (FStar_Util.print2 "Checked %s implicits (1): %s\n" uu____2743 uu____2745)))
end
| uu____2750 -> begin
()
end));
(

let g3 = (FStar_TypeChecker_Rel.resolve_implicits_tac env4 g2)
in ((

let uu____2754 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2754) with
| true -> begin
(

let uu____2778 = (FStar_Util.string_of_int (FStar_List.length ps1.FStar_Tactics_Types.all_implicits))
in (

let uu____2780 = (FStar_Common.string_of_list (fun imp -> (FStar_Syntax_Print.ctx_uvar_to_string imp.FStar_TypeChecker_Env.imp_uvar)) ps1.FStar_Tactics_Types.all_implicits)
in (FStar_Util.print2 "Checked %s implicits (2): %s\n" uu____2778 uu____2780)))
end
| uu____2785 -> begin
()
end));
(report_implicits rng_goal g3.FStar_TypeChecker_Env.implicits);
(

let uu____2789 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2789) with
| true -> begin
(

let uu____2813 = (

let uu____2814 = (FStar_TypeChecker_Cfg.psc_subst ps1.FStar_Tactics_Types.psc)
in (FStar_Tactics_Types.subst_proof_state uu____2814 ps1))
in (FStar_Tactics_Basic.dump_proofstate uu____2813 "at the finish line"))
end
| uu____2816 -> begin
()
end));
(((FStar_List.append ps1.FStar_Tactics_Types.goals ps1.FStar_Tactics_Types.smt_goals)), (w));
));
)));
)
end
| FStar_Tactics_Result.Failed (e, ps1) -> begin
((

let uu____2823 = (

let uu____2824 = (FStar_TypeChecker_Cfg.psc_subst ps1.FStar_Tactics_Types.psc)
in (FStar_Tactics_Types.subst_proof_state uu____2824 ps1))
in (FStar_Tactics_Basic.dump_proofstate uu____2823 "at the time of failure"));
(

let texn_to_string = (fun e1 -> (match (e1) with
| FStar_Tactics_Types.TacticFailure (s) -> begin
s
end
| FStar_Tactics_Types.EExn (t) -> begin
(

let uu____2837 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "uncaught exception: " uu____2837))
end
| e2 -> begin
(FStar_Exn.raise e2)
end))
in (

let uu____2842 = (

let uu____2848 = (

let uu____2850 = (texn_to_string e)
in (FStar_Util.format1 "user tactic failed: %s" uu____2850))
in ((FStar_Errors.Fatal_UserTacticFailure), (uu____2848)))
in (FStar_Errors.raise_error uu____2842 ps1.FStar_Tactics_Types.entry_range)));
)
end);
)
end));
)
end))))))
end)));
)
end));
))

type pol =
| Pos
| Neg
| Both


let uu___is_Pos : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pos -> begin
true
end
| uu____2869 -> begin
false
end))


let uu___is_Neg : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neg -> begin
true
end
| uu____2880 -> begin
false
end))


let uu___is_Both : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Both -> begin
true
end
| uu____2891 -> begin
false
end))

type 'a tres_m =
| Unchanged of 'a
| Simplified of ('a * FStar_Tactics_Types.goal Prims.list)
| Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list)


let uu___is_Unchanged : 'a . 'a tres_m  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unchanged (_0) -> begin
true
end
| uu____2950 -> begin
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
| uu____2995 -> begin
false
end))


let __proj__Simplified__item___0 : 'a . 'a tres_m  ->  ('a * FStar_Tactics_Types.goal Prims.list) = (fun projectee -> (match (projectee) with
| Simplified (_0) -> begin
_0
end))


let uu___is_Dual : 'a . 'a tres_m  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Dual (_0) -> begin
true
end
| uu____3054 -> begin
false
end))


let __proj__Dual__item___0 : 'a . 'a tres_m  ->  ('a * 'a * FStar_Tactics_Types.goal Prims.list) = (fun projectee -> (match (projectee) with
| Dual (_0) -> begin
_0
end))


type tres =
FStar_Syntax_Syntax.term tres_m


let tpure : 'Auu____3098 . 'Auu____3098  ->  'Auu____3098 tres_m = (fun x -> Unchanged (x))


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

let uu____3128 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____3128) with
| (hd1, args) -> begin
(

let uu____3171 = (

let uu____3186 = (

let uu____3187 = (FStar_Syntax_Util.un_uinst hd1)
in uu____3187.FStar_Syntax_Syntax.n)
in ((uu____3186), (args)))
in (match (uu____3171) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((rett, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____3202))))::((tactic, FStar_Pervasives_Native.None))::((assertion, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid) -> begin
(match (pol) with
| Pos -> begin
(

let uu____3266 = (run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos assertion.FStar_Syntax_Syntax.pos tactic e assertion)
in (match (uu____3266) with
| (gs, uu____3274) -> begin
Simplified (((FStar_Syntax_Util.t_true), (gs)))
end))
end
| Both -> begin
(

let uu____3281 = (run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos assertion.FStar_Syntax_Syntax.pos tactic e assertion)
in (match (uu____3281) with
| (gs, uu____3289) -> begin
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

let uu____3332 = (

let uu____3339 = (

let uu____3342 = (

let uu____3343 = (FStar_Tactics_Basic.goal_of_goal_ty e assertion)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3343))
in (uu____3342)::[])
in ((FStar_Syntax_Util.t_true), (uu____3339)))
in Simplified (uu____3332))
end
| Both -> begin
(

let uu____3354 = (

let uu____3363 = (

let uu____3366 = (

let uu____3367 = (FStar_Tactics_Basic.goal_of_goal_ty e assertion)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3367))
in (uu____3366)::[])
in ((assertion), (FStar_Syntax_Util.t_true), (uu____3363)))
in Dual (uu____3354))
end
| Neg -> begin
Simplified (((assertion), ([])))
end)
end
| uu____3380 -> begin
Unchanged (t)
end))
end)))


let explode : 'a . 'a tres_m  ->  ('a * 'a * FStar_Tactics_Types.goal Prims.list) = (fun t -> (match (t) with
| Unchanged (t1) -> begin
((t1), (t1), ([]))
end
| Simplified (t1, gs) -> begin
((t1), (t1), (gs))
end
| Dual (tn, tp, gs) -> begin
((tn), (tp), (gs))
end))


let comb1 : 'a 'b . ('a  ->  'b)  ->  'a tres_m  ->  'b tres_m = (fun f uu___364_3472 -> (match (uu___364_3472) with
| Unchanged (t) -> begin
(

let uu____3478 = (f t)
in Unchanged (uu____3478))
end
| Simplified (t, gs) -> begin
(

let uu____3485 = (

let uu____3492 = (f t)
in ((uu____3492), (gs)))
in Simplified (uu____3485))
end
| Dual (tn, tp, gs) -> begin
(

let uu____3502 = (

let uu____3511 = (f tn)
in (

let uu____3512 = (f tp)
in ((uu____3511), (uu____3512), (gs))))
in Dual (uu____3502))
end))


let comb2 : 'a 'b 'c . ('a  ->  'b  ->  'c)  ->  'a tres_m  ->  'b tres_m  ->  'c tres_m = (fun f x y -> (match (((x), (y))) with
| (Unchanged (t1), Unchanged (t2)) -> begin
(

let uu____3576 = (f t1 t2)
in Unchanged (uu____3576))
end
| (Unchanged (t1), Simplified (t2, gs)) -> begin
(

let uu____3588 = (

let uu____3595 = (f t1 t2)
in ((uu____3595), (gs)))
in Simplified (uu____3588))
end
| (Simplified (t1, gs), Unchanged (t2)) -> begin
(

let uu____3609 = (

let uu____3616 = (f t1 t2)
in ((uu____3616), (gs)))
in Simplified (uu____3609))
end
| (Simplified (t1, gs1), Simplified (t2, gs2)) -> begin
(

let uu____3635 = (

let uu____3642 = (f t1 t2)
in ((uu____3642), ((FStar_List.append gs1 gs2))))
in Simplified (uu____3635))
end
| uu____3645 -> begin
(

let uu____3654 = (explode x)
in (match (uu____3654) with
| (n1, p1, gs1) -> begin
(

let uu____3672 = (explode y)
in (match (uu____3672) with
| (n2, p2, gs2) -> begin
(

let uu____3690 = (

let uu____3699 = (f n1 n2)
in (

let uu____3700 = (f p1 p2)
in ((uu____3699), (uu____3700), ((FStar_List.append gs1 gs2)))))
in Dual (uu____3690))
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

let uu____3773 = (comb2 (fun l r -> (l)::r) hd1 acc)
in (aux tl1 uu____3773))
end))
in (aux (FStar_List.rev rs) (tpure []))))


let emit : 'a . FStar_Tactics_Types.goal Prims.list  ->  'a tres_m  ->  'a tres_m = (fun gs m -> (comb2 (fun uu____3822 x -> x) (Simplified (((()), (gs)))) m))


let rec traverse : (pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  tres)  ->  pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  tres = (fun f pol e t -> (

let r = (

let uu____3865 = (

let uu____3866 = (FStar_Syntax_Subst.compress t)
in uu____3866.FStar_Syntax_Syntax.n)
in (match (uu____3865) with
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let tr = (traverse f pol e t1)
in (

let uu____3878 = (comb1 (fun t' -> FStar_Syntax_Syntax.Tm_uinst (((t'), (us)))))
in (uu____3878 tr)))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let tr = (traverse f pol e t1)
in (

let uu____3904 = (comb1 (fun t' -> FStar_Syntax_Syntax.Tm_meta (((t'), (m)))))
in (uu____3904 tr)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____3924; FStar_Syntax_Syntax.vars = uu____3925}, ((p, uu____3927))::((q, uu____3929))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p)
in (

let r1 = (traverse f (flip pol) e p)
in (

let r2 = (

let uu____3987 = (FStar_TypeChecker_Env.push_bv e x)
in (traverse f pol uu____3987 q))
in (comb2 (fun l r -> (

let uu____4001 = (FStar_Syntax_Util.mk_imp l r)
in uu____4001.FStar_Syntax_Syntax.n)) r1 r2))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____4005; FStar_Syntax_Syntax.vars = uu____4006}, ((p, uu____4008))::((q, uu____4010))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid) -> begin
(

let xp = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p)
in (

let xq = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q)
in (

let r1 = (

let uu____4068 = (FStar_TypeChecker_Env.push_bv e xq)
in (traverse f Both uu____4068 p))
in (

let r2 = (

let uu____4070 = (FStar_TypeChecker_Env.push_bv e xp)
in (traverse f Both uu____4070 q))
in (match (((r1), (r2))) with
| (Unchanged (uu____4077), Unchanged (uu____4078)) -> begin
(comb2 (fun l r -> (

let uu____4096 = (FStar_Syntax_Util.mk_iff l r)
in uu____4096.FStar_Syntax_Syntax.n)) r1 r2)
end
| uu____4099 -> begin
(

let uu____4108 = (explode r1)
in (match (uu____4108) with
| (pn, pp, gs1) -> begin
(

let uu____4126 = (explode r2)
in (match (uu____4126) with
| (qn, qp, gs2) -> begin
(

let t1 = (

let uu____4147 = (FStar_Syntax_Util.mk_imp pn qp)
in (

let uu____4150 = (FStar_Syntax_Util.mk_imp qn pp)
in (FStar_Syntax_Util.mk_conj uu____4147 uu____4150)))
in Simplified (((t1.FStar_Syntax_Syntax.n), ((FStar_List.append gs1 gs2)))))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let r0 = (traverse f pol e hd1)
in (

let r1 = (FStar_List.fold_right (fun uu____4214 r -> (match (uu____4214) with
| (a, q) -> begin
(

let r' = (traverse f pol e a)
in (comb2 (fun a1 args1 -> (((a1), (q)))::args1) r' r))
end)) args (tpure []))
in (comb2 (fun hd2 args1 -> FStar_Syntax_Syntax.Tm_app (((hd2), (args1)))) r0 r1)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____4366 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____4366) with
| (bs1, topen) -> begin
(

let e' = (FStar_TypeChecker_Env.push_binders e bs1)
in (

let r0 = (FStar_List.map (fun uu____4406 -> (match (uu____4406) with
| (bv, aq) -> begin
(

let r = (traverse f (flip pol) e bv.FStar_Syntax_Syntax.sort)
in (

let uu____4428 = (comb1 (fun s' -> (((

let uu___371_4460 = bv
in {FStar_Syntax_Syntax.ppname = uu___371_4460.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___371_4460.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s'})), (aq))))
in (uu____4428 r)))
end)) bs1)
in (

let rbs = (comb_list r0)
in (

let rt = (traverse f pol e' topen)
in (comb2 (fun bs2 t2 -> (

let uu____4488 = (FStar_Syntax_Util.abs bs2 t2 k)
in uu____4488.FStar_Syntax_Syntax.n)) rbs rt)))))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, ef) -> begin
(

let uu____4534 = (traverse f pol e t1)
in (

let uu____4539 = (comb1 (fun t2 -> FStar_Syntax_Syntax.Tm_ascribed (((t2), (asc), (ef)))))
in (uu____4539 uu____4534)))
end
| FStar_Syntax_Syntax.Tm_match (sc, brs) -> begin
(

let uu____4614 = (traverse f pol e sc)
in (

let uu____4619 = (

let uu____4638 = (FStar_List.map (fun br -> (

let uu____4655 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____4655) with
| (pat, w, exp) -> begin
(

let bvs = (FStar_Syntax_Syntax.pat_bvs pat)
in (

let e1 = (FStar_TypeChecker_Env.push_bvs e bvs)
in (

let r = (traverse f pol e1 exp)
in (

let uu____4682 = (comb1 (fun exp1 -> (FStar_Syntax_Subst.close_branch ((pat), (w), (exp1)))))
in (uu____4682 r)))))
end))) brs)
in (comb_list uu____4638))
in (comb2 (fun sc1 brs1 -> FStar_Syntax_Syntax.Tm_match (((sc1), (brs1)))) uu____4614 uu____4619)))
end
| x -> begin
(tpure x)
end))
in (match (r) with
| Unchanged (tn') -> begin
(f pol e (

let uu___372_4768 = t
in {FStar_Syntax_Syntax.n = tn'; FStar_Syntax_Syntax.pos = uu___372_4768.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___372_4768.FStar_Syntax_Syntax.vars}))
end
| Simplified (tn', gs) -> begin
(

let uu____4775 = (f pol e (

let uu___373_4779 = t
in {FStar_Syntax_Syntax.n = tn'; FStar_Syntax_Syntax.pos = uu___373_4779.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___373_4779.FStar_Syntax_Syntax.vars}))
in (emit gs uu____4775))
end
| Dual (tn, tp, gs) -> begin
(

let rp = (f pol e (

let uu___374_4789 = t
in {FStar_Syntax_Syntax.n = tp; FStar_Syntax_Syntax.pos = uu___374_4789.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___374_4789.FStar_Syntax_Syntax.vars}))
in (

let uu____4790 = (explode rp)
in (match (uu____4790) with
| (uu____4799, p', gs') -> begin
Dual ((((

let uu___375_4809 = t
in {FStar_Syntax_Syntax.n = tn; FStar_Syntax_Syntax.pos = uu___375_4809.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___375_4809.FStar_Syntax_Syntax.vars})), (p'), ((FStar_List.append gs gs'))))
end)))
end)))


let getprop : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun e t -> (

let tn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) e t)
in (FStar_Syntax_Util.un_squash tn)))


let preprocess : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term * FStar_Options.optionstate) Prims.list = (fun env goal -> ((

let uu____4854 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____4854));
(

let uu____4879 = (FStar_ST.op_Bang tacdbg)
in (match (uu____4879) with
| true -> begin
(

let uu____4903 = (

let uu____4905 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____4905 (FStar_Syntax_Print.binders_to_string ",")))
in (

let uu____4908 = (FStar_Syntax_Print.term_to_string goal)
in (FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4903 uu____4908)))
end
| uu____4911 -> begin
()
end));
(

let initial = (((Prims.parse_int "1")), ([]))
in (

let uu____4943 = (

let uu____4952 = (traverse by_tactic_interp Pos env goal)
in (match (uu____4952) with
| Unchanged (t') -> begin
((t'), ([]))
end
| Simplified (t', gs) -> begin
((t'), (gs))
end
| uu____4976 -> begin
(failwith "no")
end))
in (match (uu____4943) with
| (t', gs) -> begin
((

let uu____5005 = (FStar_ST.op_Bang tacdbg)
in (match (uu____5005) with
| true -> begin
(

let uu____5029 = (

let uu____5031 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____5031 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let uu____5034 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Main goal simplified to: %s |- %s\n" uu____5029 uu____5034)))
end
| uu____5037 -> begin
()
end));
(

let s = initial
in (

let s1 = (FStar_List.fold_left (fun uu____5089 g -> (match (uu____5089) with
| (n1, gs1) -> begin
(

let phi = (

let uu____5138 = (

let uu____5141 = (FStar_Tactics_Types.goal_env g)
in (

let uu____5142 = (FStar_Tactics_Types.goal_type g)
in (getprop uu____5141 uu____5142)))
in (match (uu____5138) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5143 = (

let uu____5149 = (

let uu____5151 = (

let uu____5153 = (FStar_Tactics_Types.goal_type g)
in (FStar_Syntax_Print.term_to_string uu____5153))
in (FStar_Util.format1 "Tactic returned proof-relevant goal: %s" uu____5151))
in ((FStar_Errors.Fatal_TacticProofRelevantGoal), (uu____5149)))
in (FStar_Errors.raise_error uu____5143 env.FStar_TypeChecker_Env.range))
end
| FStar_Pervasives_Native.Some (phi) -> begin
phi
end))
in ((

let uu____5158 = (FStar_ST.op_Bang tacdbg)
in (match (uu____5158) with
| true -> begin
(

let uu____5182 = (FStar_Util.string_of_int n1)
in (

let uu____5184 = (

let uu____5186 = (FStar_Tactics_Types.goal_type g)
in (FStar_Syntax_Print.term_to_string uu____5186))
in (FStar_Util.print2 "Got goal #%s: %s\n" uu____5182 uu____5184)))
end
| uu____5188 -> begin
()
end));
(

let label1 = (

let uu____5192 = (

let uu____5194 = (FStar_Tactics_Types.get_label g)
in (Prims.op_Equality uu____5194 ""))
in (match (uu____5192) with
| true -> begin
(

let uu____5200 = (FStar_Util.string_of_int n1)
in (Prims.strcat "Could not prove goal #" uu____5200))
end
| uu____5203 -> begin
(

let uu____5205 = (

let uu____5207 = (FStar_Util.string_of_int n1)
in (

let uu____5209 = (

let uu____5211 = (

let uu____5213 = (FStar_Tactics_Types.get_label g)
in (Prims.strcat uu____5213 ")"))
in (Prims.strcat " (" uu____5211))
in (Prims.strcat uu____5207 uu____5209)))
in (Prims.strcat "Could not prove goal #" uu____5205))
end))
in (

let gt' = (FStar_TypeChecker_Util.label label1 goal.FStar_Syntax_Syntax.pos phi)
in (

let uu____5219 = (

let uu____5228 = (

let uu____5235 = (FStar_Tactics_Types.goal_env g)
in ((uu____5235), (gt'), (g.FStar_Tactics_Types.opts)))
in (uu____5228)::gs1)
in (((n1 + (Prims.parse_int "1"))), (uu____5219)))));
))
end)) s gs)
in (

let uu____5252 = s1
in (match (uu____5252) with
| (uu____5274, gs1) -> begin
(

let uu____5294 = (

let uu____5301 = (FStar_Options.peek ())
in ((env), (t'), (uu____5301)))
in (uu____5294)::gs1)
end))));
)
end)));
))


let synthesize : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env typ tau -> (match (env.FStar_TypeChecker_Env.nosynth) with
| true -> begin
(

let uu____5325 = (

let uu____5330 = (FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.magic_lid)
in (

let uu____5331 = (

let uu____5332 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____5332)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____5330 uu____5331)))
in (uu____5325 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos))
end
| uu____5359 -> begin
((

let uu____5362 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____5362));
(

let uu____5386 = (run_tactic_on_typ tau.FStar_Syntax_Syntax.pos typ.FStar_Syntax_Syntax.pos tau env typ)
in (match (uu____5386) with
| (gs, w) -> begin
((FStar_List.iter (fun g -> (

let uu____5407 = (

let uu____5410 = (FStar_Tactics_Types.goal_env g)
in (

let uu____5411 = (FStar_Tactics_Types.goal_type g)
in (getprop uu____5410 uu____5411)))
in (match (uu____5407) with
| FStar_Pervasives_Native.Some (vc) -> begin
((

let uu____5414 = (FStar_ST.op_Bang tacdbg)
in (match (uu____5414) with
| true -> begin
(

let uu____5438 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "Synthesis left a goal: %s\n" uu____5438))
end
| uu____5441 -> begin
()
end));
(

let guard = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (vc); FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []}
in (

let uu____5453 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Rel.force_trivial_guard uu____5453 guard)));
)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_OpenGoalsInSynthesis), ("synthesis left open goals")) typ.FStar_Syntax_Syntax.pos)
end))) gs);
w;
)
end));
)
end))


let splice : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env tau -> (match (env.FStar_TypeChecker_Env.nosynth) with
| true -> begin
[]
end
| uu____5472 -> begin
((

let uu____5475 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____5475));
(

let typ = FStar_Syntax_Syntax.t_decls
in (

let uu____5500 = (run_tactic_on_typ tau.FStar_Syntax_Syntax.pos tau.FStar_Syntax_Syntax.pos tau env typ)
in (match (uu____5500) with
| (gs, w) -> begin
((

let uu____5516 = (FStar_List.existsML (fun g -> (

let uu____5521 = (

let uu____5523 = (

let uu____5526 = (FStar_Tactics_Types.goal_env g)
in (

let uu____5527 = (FStar_Tactics_Types.goal_type g)
in (getprop uu____5526 uu____5527)))
in (FStar_Option.isSome uu____5523))
in (not (uu____5521)))) gs)
in (match (uu____5516) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_OpenGoalsInSynthesis), ("splice left open goals")) typ.FStar_Syntax_Syntax.pos)
end
| uu____5531 -> begin
()
end));
(

let w1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Unascribe)::(FStar_TypeChecker_Env.Unmeta)::[]) env w)
in ((

let uu____5535 = (FStar_ST.op_Bang tacdbg)
in (match (uu____5535) with
| true -> begin
(

let uu____5559 = (FStar_Syntax_Print.term_to_string w1)
in (FStar_Util.print1 "splice: got witness = %s\n" uu____5559))
end
| uu____5562 -> begin
()
end));
(

let uu____5564 = (

let uu____5569 = (FStar_Syntax_Embeddings.e_list FStar_Reflection_Embeddings.e_sigelt)
in (FStar_Tactics_InterpFuns.unembed uu____5569 w1 FStar_Syntax_Embeddings.id_norm_cb))
in (match (uu____5564) with
| FStar_Pervasives_Native.Some (sigelts) -> begin
sigelts
end
| FStar_Pervasives_Native.None -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_SpliceUnembedFail), ("splice: failed to unembed sigelts")) typ.FStar_Syntax_Syntax.pos)
end));
));
)
end)));
)
end))


let postprocess : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env tau typ tm -> (match (env.FStar_TypeChecker_Env.nosynth) with
| true -> begin
tm
end
| uu____5611 -> begin
((

let uu____5614 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____5614));
(

let uu____5638 = (FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS" tm.FStar_Syntax_Syntax.pos env typ FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None)
in (match (uu____5638) with
| (uvtm, uu____5657, g_imp) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env typ)
in (

let goal = (

let uu____5675 = (FStar_Syntax_Util.mk_eq2 u typ tm uvtm)
in (FStar_Syntax_Util.mk_squash u uu____5675))
in (

let uu____5676 = (run_tactic_on_typ tau.FStar_Syntax_Syntax.pos tm.FStar_Syntax_Syntax.pos tau env goal)
in (match (uu____5676) with
| (gs, w) -> begin
((FStar_List.iter (fun g -> (

let uu____5697 = (

let uu____5700 = (FStar_Tactics_Types.goal_env g)
in (

let uu____5701 = (FStar_Tactics_Types.goal_type g)
in (getprop uu____5700 uu____5701)))
in (match (uu____5697) with
| FStar_Pervasives_Native.Some (vc) -> begin
((

let uu____5704 = (FStar_ST.op_Bang tacdbg)
in (match (uu____5704) with
| true -> begin
(

let uu____5728 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "Postprocessing left a goal: %s\n" uu____5728))
end
| uu____5731 -> begin
()
end));
(

let guard = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.NonTrivial (vc); FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = (([]), ([])); FStar_TypeChecker_Env.implicits = []}
in (

let uu____5743 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Rel.force_trivial_guard uu____5743 guard)));
)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_OpenGoalsInSynthesis), ("postprocessing left open goals")) typ.FStar_Syntax_Syntax.pos)
end))) gs);
(

let g_imp1 = (FStar_TypeChecker_Rel.resolve_implicits_tac env g_imp)
in ((report_implicits tm.FStar_Syntax_Syntax.pos g_imp1.FStar_TypeChecker_Env.implicits);
uvtm;
));
)
end))))
end));
)
end))




