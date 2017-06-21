open Prims
let set_hint_correlator:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____9 = FStar_Options.reuse_hint_for () in
      match uu____9 with
      | Some l ->
          let lid =
            let uu____13 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____13 l in
          let uu___91_14 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___91_14.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___91_14.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___91_14.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___91_14.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___91_14.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___91_14.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___91_14.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___91_14.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___91_14.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___91_14.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___91_14.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___91_14.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___91_14.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___91_14.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___91_14.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___91_14.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___91_14.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___91_14.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___91_14.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___91_14.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___91_14.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___91_14.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___91_14.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___91_14.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___91_14.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___91_14.FStar_TypeChecker_Env.is_native_tactic)
          }
      | None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____20 = FStar_TypeChecker_Env.current_module env in
                let uu____21 =
                  let uu____22 = FStar_Syntax_Syntax.next_id () in
                  FStar_All.pipe_right uu____22 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____20 uu____21
            | l::uu____24 -> l in
          let uu___92_26 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___92_26.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___92_26.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___92_26.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___92_26.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___92_26.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___92_26.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___92_26.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___92_26.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___92_26.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___92_26.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___92_26.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___92_26.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___92_26.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___92_26.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___92_26.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___92_26.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___92_26.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___92_26.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___92_26.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___92_26.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___92_26.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___92_26.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___92_26.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___92_26.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___92_26.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___92_26.FStar_TypeChecker_Env.is_native_tactic)
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
<<<<<<< HEAD
      (let uu____31 =
         let uu____32 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____32 in
       Prims.op_Negation uu____31)
=======
      (let uu____33 =
         let uu____34 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____34 in
       Prims.op_Negation uu____33)
let is_native_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool
  =
  fun env  ->
    fun tac_lid  ->
      fun h  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____48) ->
            let uu____53 =
              let uu____54 = FStar_Syntax_Subst.compress h' in
              uu____54.FStar_Syntax_Syntax.n in
            (match uu____53 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.tactic_lid
                 -> env.FStar_TypeChecker_Env.is_native_tactic tac_lid
             | uu____58 -> false)
        | uu____59 -> false
>>>>>>> origin/guido_tactics
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
<<<<<<< HEAD
        let uu____42 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____42 with
=======
        let uu____72 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____72 with
>>>>>>> origin/guido_tactics
        | (t1,c,g) ->
            (FStar_ST.write t1.FStar_Syntax_Syntax.tk
               (Some ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n));
             FStar_TypeChecker_Rel.force_trivial_guard env g;
             t1)
let recheck_debug:
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
<<<<<<< HEAD
        (let uu____64 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____64
         then
           let uu____65 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____65
         else ());
        (let uu____67 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____67 with
         | (t',uu____72,uu____73) ->
             ((let uu____75 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____75
               then
                 let uu____76 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____76
=======
        (let uu____97 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____97
         then
           let uu____98 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____98
         else ());
        (let uu____100 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____100 with
         | (t',uu____105,uu____106) ->
             ((let uu____108 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____108
               then
                 let uu____109 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____109
>>>>>>> origin/guido_tactics
               else ());
              t))
let check_and_gen:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme
  =
  fun env  ->
    fun t  ->
      fun k  ->
<<<<<<< HEAD
        let uu____87 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____87
let check_nogen env t k =
  let t1 = tc_check_trivial_guard env t k in
  let uu____109 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t1 in
  ([], uu____109)
=======
        let uu____123 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____123
let check_nogen env t k =
  let t1 = tc_check_trivial_guard env t k in
  let uu____149 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t1 in
  ([], uu____149)
>>>>>>> origin/guido_tactics
let monad_signature:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv*
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun m  ->
      fun s  ->
<<<<<<< HEAD
        let fail uu____131 =
          let uu____132 =
            let uu____133 =
              let uu____136 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____136, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____133 in
          raise uu____132 in
=======
        let fail uu____174 =
          let uu____175 =
            let uu____176 =
              let uu____179 =
                FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
              (uu____179, (FStar_Ident.range_of_lid m)) in
            FStar_Errors.Error uu____176 in
          raise uu____175 in
>>>>>>> origin/guido_tactics
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
<<<<<<< HEAD
             | (a,uu____164)::(wp,uu____166)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____175 -> fail ())
        | uu____176 -> fail ()
let tc_eff_decl:
=======
             | (a,uu____207)::(wp,uu____209)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____218 -> fail ())
        | uu____219 -> fail ()
let rec tc_eff_decl:
>>>>>>> origin/guido_tactics
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
<<<<<<< HEAD
      let uu____185 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____185 with
      | (effect_params_un,signature_un,opening) ->
          let uu____192 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____192 with
           | (effect_params,env,uu____198) ->
               let uu____199 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____199 with
                | (signature,uu____203) ->
                    let ed1 =
                      let uu___91_205 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___91_205.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___91_205.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___91_205.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___91_205.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___91_205.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___91_205.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___91_205.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___91_205.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___91_205.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___91_205.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___91_205.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___91_205.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___91_205.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___91_205.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___91_205.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___91_205.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___91_205.FStar_Syntax_Syntax.actions)
=======
      let uu____281 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____281 with
      | (effect_params_un,signature_un,opening) ->
          let uu____288 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____288 with
           | (effect_params,env,uu____294) ->
               let uu____295 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____295 with
                | (signature,uu____299) ->
                    let ed1 =
                      let uu___93_301 = ed in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___93_301.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___93_301.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___93_301.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___93_301.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___93_301.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___93_301.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___93_301.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___93_301.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___93_301.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___93_301.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___93_301.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___93_301.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___93_301.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___93_301.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___93_301.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___93_301.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___93_301.FStar_Syntax_Syntax.actions)
>>>>>>> origin/guido_tactics
                      } in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
<<<<<<< HEAD
                      | uu____209 ->
=======
                      | uu____305 ->
>>>>>>> origin/guido_tactics
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (snd ts) in
                            ([], t1) in
<<<<<<< HEAD
                          let uu___92_228 = ed1 in
                          let uu____229 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____230 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____231 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____232 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____233 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____234 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____235 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____236 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____237 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____238 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____239 =
                            let uu____240 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            snd uu____240 in
                          let uu____246 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____247 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____248 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___93_255 = a in
                                 let uu____256 =
                                   let uu____257 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   snd uu____257 in
                                 let uu____263 =
                                   let uu____264 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   snd uu____264 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___93_255.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___93_255.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___93_255.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___93_255.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____256;
                                   FStar_Syntax_Syntax.action_typ = uu____263
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___92_228.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___92_228.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___92_228.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___92_228.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___92_228.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____229;
                            FStar_Syntax_Syntax.bind_wp = uu____230;
                            FStar_Syntax_Syntax.if_then_else = uu____231;
                            FStar_Syntax_Syntax.ite_wp = uu____232;
                            FStar_Syntax_Syntax.stronger = uu____233;
                            FStar_Syntax_Syntax.close_wp = uu____234;
                            FStar_Syntax_Syntax.assert_p = uu____235;
                            FStar_Syntax_Syntax.assume_p = uu____236;
                            FStar_Syntax_Syntax.null_wp = uu____237;
                            FStar_Syntax_Syntax.trivial = uu____238;
                            FStar_Syntax_Syntax.repr = uu____239;
                            FStar_Syntax_Syntax.return_repr = uu____246;
                            FStar_Syntax_Syntax.bind_repr = uu____247;
                            FStar_Syntax_Syntax.actions = uu____248
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____292 =
                          let uu____293 =
                            let uu____296 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____296, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____293 in
                        raise uu____292 in
                      let uu____301 =
                        let uu____302 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____302.FStar_Syntax_Syntax.n in
                      match uu____301 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____327)::(wp,uu____329)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____338 -> fail signature1)
                      | uu____339 -> fail signature1 in
                    let uu____340 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____340 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____358 =
                           let uu____359 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____359 with
                           | (signature1,uu____367) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____369 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____369 in
                         ((let uu____371 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____371
                           then
                             let uu____372 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____373 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____374 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____375 =
                               let uu____376 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____376 in
                             let uu____377 =
=======
                          let uu___94_323 = ed1 in
                          let uu____324 = op ed1.FStar_Syntax_Syntax.ret_wp in
                          let uu____325 = op ed1.FStar_Syntax_Syntax.bind_wp in
                          let uu____326 =
                            op ed1.FStar_Syntax_Syntax.if_then_else in
                          let uu____327 = op ed1.FStar_Syntax_Syntax.ite_wp in
                          let uu____328 = op ed1.FStar_Syntax_Syntax.stronger in
                          let uu____329 = op ed1.FStar_Syntax_Syntax.close_wp in
                          let uu____330 = op ed1.FStar_Syntax_Syntax.assert_p in
                          let uu____331 = op ed1.FStar_Syntax_Syntax.assume_p in
                          let uu____332 = op ed1.FStar_Syntax_Syntax.null_wp in
                          let uu____333 = op ed1.FStar_Syntax_Syntax.trivial in
                          let uu____334 =
                            let uu____335 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                            snd uu____335 in
                          let uu____341 =
                            op ed1.FStar_Syntax_Syntax.return_repr in
                          let uu____342 =
                            op ed1.FStar_Syntax_Syntax.bind_repr in
                          let uu____343 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___95_346 = a in
                                 let uu____347 =
                                   let uu____348 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn)) in
                                   snd uu____348 in
                                 let uu____354 =
                                   let uu____355 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ)) in
                                   snd uu____355 in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___95_346.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___95_346.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___95_346.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_params =
                                     (uu___95_346.FStar_Syntax_Syntax.action_params);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____347;
                                   FStar_Syntax_Syntax.action_typ = uu____354
                                 }) ed1.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.cattributes =
                              (uu___94_323.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___94_323.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___94_323.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___94_323.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___94_323.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____324;
                            FStar_Syntax_Syntax.bind_wp = uu____325;
                            FStar_Syntax_Syntax.if_then_else = uu____326;
                            FStar_Syntax_Syntax.ite_wp = uu____327;
                            FStar_Syntax_Syntax.stronger = uu____328;
                            FStar_Syntax_Syntax.close_wp = uu____329;
                            FStar_Syntax_Syntax.assert_p = uu____330;
                            FStar_Syntax_Syntax.assume_p = uu____331;
                            FStar_Syntax_Syntax.null_wp = uu____332;
                            FStar_Syntax_Syntax.trivial = uu____333;
                            FStar_Syntax_Syntax.repr = uu____334;
                            FStar_Syntax_Syntax.return_repr = uu____341;
                            FStar_Syntax_Syntax.bind_repr = uu____342;
                            FStar_Syntax_Syntax.actions = uu____343
                          } in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____383 =
                          let uu____384 =
                            let uu____387 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t in
                            (uu____387, (FStar_Ident.range_of_lid mname)) in
                          FStar_Errors.Error uu____384 in
                        raise uu____383 in
                      let uu____392 =
                        let uu____393 =
                          FStar_Syntax_Subst.compress signature1 in
                        uu____393.FStar_Syntax_Syntax.n in
                      match uu____392 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs in
                          (match bs1 with
                           | (a,uu____418)::(wp,uu____420)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____429 -> fail signature1)
                      | uu____430 -> fail signature1 in
                    let uu____431 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature in
                    (match uu____431 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____449 =
                           let uu____450 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____450 with
                           | (signature1,uu____458) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1 in
                         let env1 =
                           let uu____460 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env uu____460 in
                         ((let uu____462 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____462
                           then
                             let uu____463 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname in
                             let uu____464 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders in
                             let uu____465 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature in
                             let uu____466 =
                               let uu____467 =
                                 FStar_Syntax_Syntax.bv_to_name a in
                               FStar_Syntax_Print.term_to_string uu____467 in
                             let uu____468 =
>>>>>>> origin/guido_tactics
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
<<<<<<< HEAD
                               uu____372 uu____373 uu____374 uu____375
                               uu____377
                           else ());
                          (let check_and_gen' env2 uu____390 k =
                             match uu____390 with
                             | (uu____395,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____403 =
                                 let uu____407 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____408 =
                                   let uu____410 =
                                     let uu____411 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____411 in
                                   [uu____410] in
                                 uu____407 :: uu____408 in
                               let uu____412 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____403 uu____412 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____416 = fresh_effect_signature () in
                             match uu____416 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____430 =
                                     let uu____434 =
                                       let uu____435 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____435 in
                                     [uu____434] in
                                   let uu____436 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____430
                                     uu____436 in
                                 let expected_k =
                                   let uu____442 =
                                     let uu____446 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____447 =
                                       let uu____449 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____450 =
                                         let uu____452 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____453 =
                                           let uu____455 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____456 =
                                             let uu____458 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____458] in
                                           uu____455 :: uu____456 in
                                         uu____452 :: uu____453 in
                                       uu____449 :: uu____450 in
                                     uu____446 :: uu____447 in
                                   let uu____459 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____442
                                     uu____459 in
=======
                               uu____463 uu____464 uu____465 uu____466
                               uu____468
                           else ());
                          (let check_and_gen' env2 uu____481 k =
                             match uu____481 with
                             | (uu____486,t) -> check_and_gen env2 t k in
                           let return_wp =
                             let expected_k =
                               let uu____494 =
                                 let uu____498 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____499 =
                                   let uu____501 =
                                     let uu____502 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____502 in
                                   [uu____501] in
                                 uu____498 :: uu____499 in
                               let uu____503 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow uu____494 uu____503 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                           let bind_wp =
                             let uu____507 = fresh_effect_signature () in
                             match uu____507 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____521 =
                                     let uu____525 =
                                       let uu____526 =
                                         FStar_Syntax_Syntax.bv_to_name a in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____526 in
                                     [uu____525] in
                                   let uu____527 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____521
                                     uu____527 in
                                 let expected_k =
                                   let uu____533 =
                                     let uu____537 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let uu____538 =
                                       let uu____540 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____541 =
                                         let uu____543 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let uu____544 =
                                           let uu____546 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let uu____547 =
                                             let uu____549 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [uu____549] in
                                           uu____546 :: uu____547 in
                                         uu____543 :: uu____544 in
                                       uu____540 :: uu____541 in
                                     uu____537 :: uu____538 in
                                   let uu____550 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow uu____533
                                     uu____550 in
>>>>>>> origin/guido_tactics
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else1 =
                             let p =
<<<<<<< HEAD
                               let uu____464 =
                                 let uu____465 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____465
=======
                               let uu____555 =
                                 let uu____556 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____556
>>>>>>> origin/guido_tactics
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
<<<<<<< HEAD
                                 uu____464 in
                             let expected_k =
                               let uu____473 =
                                 let uu____477 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____478 =
                                   let uu____480 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____481 =
                                     let uu____483 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____484 =
                                       let uu____486 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____486] in
                                     uu____483 :: uu____484 in
                                   uu____480 :: uu____481 in
                                 uu____477 :: uu____478 in
                               let uu____487 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____473 uu____487 in
=======
                                 uu____555 in
                             let expected_k =
                               let uu____564 =
                                 let uu____568 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____569 =
                                   let uu____571 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let uu____572 =
                                     let uu____574 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let uu____575 =
                                       let uu____577 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____577] in
                                     uu____574 :: uu____575 in
                                   uu____571 :: uu____572 in
                                 uu____568 :: uu____569 in
                               let uu____578 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____564 uu____578 in
>>>>>>> origin/guido_tactics
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k in
                           let ite_wp =
                             let expected_k =
<<<<<<< HEAD
                               let uu____494 =
                                 let uu____498 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____499 =
                                   let uu____501 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____501] in
                                 uu____498 :: uu____499 in
                               let uu____502 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____494 uu____502 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____506 = FStar_Syntax_Util.type_u () in
                             match uu____506 with
                             | (t,uu____510) ->
                                 let expected_k =
                                   let uu____514 =
                                     let uu____518 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____519 =
                                       let uu____521 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____522 =
                                         let uu____524 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____524] in
                                       uu____521 :: uu____522 in
                                     uu____518 :: uu____519 in
                                   let uu____525 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____514
                                     uu____525 in
=======
                               let uu____585 =
                                 let uu____589 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____590 =
                                   let uu____592 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [uu____592] in
                                 uu____589 :: uu____590 in
                               let uu____593 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____585 uu____593 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                           let stronger =
                             let uu____597 = FStar_Syntax_Util.type_u () in
                             match uu____597 with
                             | (t,uu____601) ->
                                 let expected_k =
                                   let uu____605 =
                                     let uu____609 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____610 =
                                       let uu____612 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let uu____613 =
                                         let uu____615 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [uu____615] in
                                       uu____612 :: uu____613 in
                                     uu____609 :: uu____610 in
                                   let uu____616 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow uu____605
                                     uu____616 in
>>>>>>> origin/guido_tactics
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k in
                           let close_wp =
                             let b =
<<<<<<< HEAD
                               let uu____530 =
                                 let uu____531 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____531
=======
                               let uu____621 =
                                 let uu____622 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right uu____622
>>>>>>> origin/guido_tactics
                                   FStar_Pervasives.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
<<<<<<< HEAD
                                 uu____530 in
                             let b_wp_a =
                               let uu____539 =
                                 let uu____543 =
                                   let uu____544 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____544 in
                                 [uu____543] in
                               let uu____545 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____539 uu____545 in
                             let expected_k =
                               let uu____551 =
                                 let uu____555 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____556 =
                                   let uu____558 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____559 =
                                     let uu____561 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____561] in
                                   uu____558 :: uu____559 in
                                 uu____555 :: uu____556 in
                               let uu____562 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____551 uu____562 in
=======
                                 uu____621 in
                             let b_wp_a =
                               let uu____630 =
                                 let uu____634 =
                                   let uu____635 =
                                     FStar_Syntax_Syntax.bv_to_name b in
                                   FStar_Syntax_Syntax.null_binder uu____635 in
                                 [uu____634] in
                               let uu____636 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____630 uu____636 in
                             let expected_k =
                               let uu____642 =
                                 let uu____646 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____647 =
                                   let uu____649 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let uu____650 =
                                     let uu____652 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [uu____652] in
                                   uu____649 :: uu____650 in
                                 uu____646 :: uu____647 in
                               let uu____653 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____642 uu____653 in
>>>>>>> origin/guido_tactics
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
<<<<<<< HEAD
                               let uu____569 =
                                 let uu____573 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____574 =
                                   let uu____576 =
                                     let uu____577 =
                                       let uu____578 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____578
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____577 in
                                   let uu____583 =
                                     let uu____585 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____585] in
                                   uu____576 :: uu____583 in
                                 uu____573 :: uu____574 in
                               let uu____586 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____569 uu____586 in
=======
                               let uu____660 =
                                 let uu____664 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____665 =
                                   let uu____667 =
                                     let uu____668 =
                                       let uu____669 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____669
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____668 in
                                   let uu____674 =
                                     let uu____676 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____676] in
                                   uu____667 :: uu____674 in
                                 uu____664 :: uu____665 in
                               let uu____677 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____660 uu____677 in
>>>>>>> origin/guido_tactics
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
<<<<<<< HEAD
                               let uu____593 =
                                 let uu____597 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____598 =
                                   let uu____600 =
                                     let uu____601 =
                                       let uu____602 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____602
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____601 in
                                   let uu____607 =
                                     let uu____609 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____609] in
                                   uu____600 :: uu____607 in
                                 uu____597 :: uu____598 in
                               let uu____610 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____593 uu____610 in
=======
                               let uu____684 =
                                 let uu____688 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 let uu____689 =
                                   let uu____691 =
                                     let uu____692 =
                                       let uu____693 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____693
                                         FStar_Pervasives.fst in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____692 in
                                   let uu____698 =
                                     let uu____700 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [uu____700] in
                                   uu____691 :: uu____698 in
                                 uu____688 :: uu____689 in
                               let uu____701 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____684 uu____701 in
>>>>>>> origin/guido_tactics
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
<<<<<<< HEAD
                               let uu____617 =
                                 let uu____621 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____621] in
                               let uu____622 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____617 uu____622 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____626 = FStar_Syntax_Util.type_u () in
                             match uu____626 with
                             | (t,uu____630) ->
                                 let expected_k =
                                   let uu____634 =
                                     let uu____638 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____639 =
                                       let uu____641 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____641] in
                                     uu____638 :: uu____639 in
                                   let uu____642 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____634
                                     uu____642 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____645 =
                             let uu____651 =
                               let uu____652 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____652.FStar_Syntax_Syntax.n in
                             match uu____651 with
=======
                               let uu____708 =
                                 let uu____712 =
                                   FStar_Syntax_Syntax.mk_binder a in
                                 [uu____712] in
                               let uu____713 =
                                 FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow uu____708 uu____713 in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____717 = FStar_Syntax_Util.type_u () in
                             match uu____717 with
                             | (t,uu____721) ->
                                 let expected_k =
                                   let uu____725 =
                                     let uu____729 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let uu____730 =
                                       let uu____732 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [uu____732] in
                                     uu____729 :: uu____730 in
                                   let uu____733 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow uu____725
                                     uu____733 in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____736 =
                             let uu____742 =
                               let uu____743 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr in
                               uu____743.FStar_Syntax_Syntax.n in
                             match uu____742 with
>>>>>>> origin/guido_tactics
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
<<<<<<< HEAD
                             | uu____661 ->
                                 let repr =
                                   let uu____663 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____663 with
                                   | (t,uu____667) ->
                                       let expected_k =
                                         let uu____671 =
                                           let uu____675 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____676 =
                                             let uu____678 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____678] in
                                           uu____675 :: uu____676 in
                                         let uu____679 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____671
                                           uu____679 in
=======
                             | uu____752 ->
                                 let repr =
                                   let uu____754 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____754 with
                                   | (t,uu____758) ->
                                       let expected_k =
                                         let uu____762 =
                                           let uu____766 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____767 =
                                             let uu____769 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [uu____769] in
                                           uu____766 :: uu____767 in
                                         let uu____770 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow uu____762
                                           uu____770 in
>>>>>>> origin/guido_tactics
                                       tc_check_trivial_guard env1
                                         ed2.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env1 repr in
<<<<<<< HEAD
                                   let uu____692 =
                                     let uu____695 =
                                       let uu____696 =
                                         let uu____706 =
                                           let uu____708 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____709 =
                                             let uu____711 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____711] in
                                           uu____708 :: uu____709 in
                                         (repr1, uu____706) in
                                       FStar_Syntax_Syntax.Tm_app uu____696 in
                                     FStar_Syntax_Syntax.mk uu____695 in
                                   uu____692 None FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____730 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____730 wp in
                                 let destruct_repr t =
                                   let uu____741 =
                                     let uu____742 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____742.FStar_Syntax_Syntax.n in
                                   match uu____741 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____751,(t1,uu____753)::(wp,uu____755)::[])
                                       -> (t1, wp)
                                   | uu____789 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____798 =
=======
                                   let uu____783 =
                                     let uu____786 =
                                       let uu____787 =
                                         let uu____797 =
                                           let uu____799 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu____800 =
                                             let uu____802 =
                                               FStar_Syntax_Syntax.as_arg wp in
                                             [uu____802] in
                                           uu____799 :: uu____800 in
                                         (repr1, uu____797) in
                                       FStar_Syntax_Syntax.Tm_app uu____787 in
                                     FStar_Syntax_Syntax.mk uu____786 in
                                   uu____783 None FStar_Range.dummyRange in
                                 let mk_repr a1 wp =
                                   let uu____821 =
                                     FStar_Syntax_Syntax.bv_to_name a1 in
                                   mk_repr' uu____821 wp in
                                 let destruct_repr t =
                                   let uu____832 =
                                     let uu____833 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____833.FStar_Syntax_Syntax.n in
                                   match uu____832 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____842,(t1,uu____844)::(wp,uu____846)::[])
                                       -> (t1, wp)
                                   | uu____880 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let uu____889 =
>>>>>>> origin/guido_tactics
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
<<<<<<< HEAD
                                     FStar_All.pipe_right uu____798
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____799 = fresh_effect_signature () in
                                   match uu____799 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____813 =
                                           let uu____817 =
                                             let uu____818 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____818 in
                                           [uu____817] in
                                         let uu____819 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____813
                                           uu____819 in
=======
                                     FStar_All.pipe_right uu____889
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____890 = fresh_effect_signature () in
                                   match uu____890 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____904 =
                                           let uu____908 =
                                             let uu____909 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____909 in
                                           [uu____908] in
                                         let uu____910 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow uu____904
                                           uu____910 in
>>>>>>> origin/guido_tactics
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b in
                                       let x_a =
<<<<<<< HEAD
                                         let uu____825 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____825 in
                                       let wp_g_x =
                                         let uu____829 =
                                           let uu____830 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____831 =
                                             let uu____832 =
                                               let uu____833 =
=======
                                         let uu____916 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____916 in
                                       let wp_g_x =
                                         let uu____920 =
                                           let uu____921 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g in
                                           let uu____922 =
                                             let uu____923 =
                                               let uu____924 =
>>>>>>> origin/guido_tactics
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
<<<<<<< HEAD
                                                 uu____833 in
                                             [uu____832] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____830 uu____831 in
                                         uu____829 None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____844 =
                                             let uu____845 =
                                               let uu____846 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right uu____846
                                                 FStar_Pervasives.snd in
                                             let uu____851 =
                                               let uu____852 =
                                                 let uu____854 =
                                                   let uu____856 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____857 =
                                                     let uu____859 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____860 =
                                                       let uu____862 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____863 =
                                                         let uu____865 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____865] in
                                                       uu____862 :: uu____863 in
                                                     uu____859 :: uu____860 in
                                                   uu____856 :: uu____857 in
                                                 r :: uu____854 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____852 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____845 uu____851 in
                                           uu____844 None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____873 =
                                           let uu____877 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____878 =
                                             let uu____880 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____881 =
                                               let uu____883 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____884 =
                                                 let uu____886 =
                                                   let uu____887 =
                                                     let uu____888 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____888 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____887 in
                                                 let uu____889 =
                                                   let uu____891 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____892 =
                                                     let uu____894 =
                                                       let uu____895 =
                                                         let uu____896 =
                                                           let uu____900 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____900] in
                                                         let uu____901 =
                                                           let uu____904 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____904 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____896
                                                           uu____901 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____895 in
                                                     [uu____894] in
                                                   uu____891 :: uu____892 in
                                                 uu____886 :: uu____889 in
                                               uu____883 :: uu____884 in
                                             uu____880 :: uu____881 in
                                           uu____877 :: uu____878 in
                                         let uu____905 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____873
                                           uu____905 in
                                       let uu____908 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____908 with
                                        | (expected_k1,uu____913,uu____914)
=======
                                                 uu____924 in
                                             [uu____923] in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____921 uu____922 in
                                         uu____920 None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           let uu____935 =
                                             let uu____936 =
                                               let uu____937 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp in
                                               FStar_All.pipe_right uu____937
                                                 FStar_Pervasives.snd in
                                             let uu____942 =
                                               let uu____943 =
                                                 let uu____945 =
                                                   let uu____947 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a in
                                                   let uu____948 =
                                                     let uu____950 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     let uu____951 =
                                                       let uu____953 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f in
                                                       let uu____954 =
                                                         let uu____956 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g in
                                                         [uu____956] in
                                                       uu____953 :: uu____954 in
                                                     uu____950 :: uu____951 in
                                                   uu____947 :: uu____948 in
                                                 r :: uu____945 in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____943 in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____936 uu____942 in
                                           uu____935 None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let uu____964 =
                                           let uu____968 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____969 =
                                             let uu____971 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____972 =
                                               let uu____974 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let uu____975 =
                                                 let uu____977 =
                                                   let uu____978 =
                                                     let uu____979 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f in
                                                     mk_repr a uu____979 in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____978 in
                                                 let uu____980 =
                                                   let uu____982 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let uu____983 =
                                                     let uu____985 =
                                                       let uu____986 =
                                                         let uu____987 =
                                                           let uu____991 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a in
                                                           [uu____991] in
                                                         let uu____992 =
                                                           let uu____995 =
                                                             mk_repr b wp_g_x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____995 in
                                                         FStar_Syntax_Util.arrow
                                                           uu____987
                                                           uu____992 in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____986 in
                                                     [uu____985] in
                                                   uu____982 :: uu____983 in
                                                 uu____977 :: uu____980 in
                                               uu____974 :: uu____975 in
                                             uu____971 :: uu____972 in
                                           uu____968 :: uu____969 in
                                         let uu____996 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow uu____964
                                           uu____996 in
                                       let uu____999 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k in
                                       (match uu____999 with
                                        | (expected_k1,uu____1004,uu____1005)
>>>>>>> origin/guido_tactics
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env3 =
<<<<<<< HEAD
                                              let uu___94_918 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___94_918.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___94_918.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___94_918.FStar_TypeChecker_Env.admit);
=======
                                              let uu___96_1009 = env2 in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___96_1009.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___96_1009.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___96_1009.FStar_TypeChecker_Env.admit);
>>>>>>> origin/guido_tactics
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
<<<<<<< HEAD
                                                  (uu___94_918.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___94_918.FStar_TypeChecker_Env.qname_and_index)
=======
                                                  (uu___96_1009.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.qname_and_index);
                                                FStar_TypeChecker_Env.proof_ns
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.proof_ns);
                                                FStar_TypeChecker_Env.synth =
                                                  (uu___96_1009.FStar_TypeChecker_Env.synth);
                                                FStar_TypeChecker_Env.is_native_tactic
                                                  =
                                                  (uu___96_1009.FStar_TypeChecker_Env.is_native_tactic)
>>>>>>> origin/guido_tactics
                                              } in
                                            let br =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_k1 in
                                            br) in
                                 let return_repr =
                                   let x_a =
<<<<<<< HEAD
                                     let uu____925 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____925 in
                                   let res =
                                     let wp =
                                       let uu____932 =
                                         let uu____933 =
                                           let uu____934 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____934
                                             FStar_Pervasives.snd in
                                         let uu____939 =
                                           let uu____940 =
                                             let uu____942 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____943 =
                                               let uu____945 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____945] in
                                             uu____942 :: uu____943 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____940 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____933 uu____939 in
                                       uu____932 None FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____953 =
                                       let uu____957 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____958 =
                                         let uu____960 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____960] in
                                       uu____957 :: uu____958 in
                                     let uu____961 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____953
                                       uu____961 in
                                   let uu____964 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____964 with
                                   | (expected_k1,uu____972,uu____973) ->
=======
                                     let uu____1016 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____1016 in
                                   let res =
                                     let wp =
                                       let uu____1023 =
                                         let uu____1024 =
                                           let uu____1025 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp in
                                           FStar_All.pipe_right uu____1025
                                             FStar_Pervasives.snd in
                                         let uu____1030 =
                                           let uu____1031 =
                                             let uu____1033 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a in
                                             let uu____1034 =
                                               let uu____1036 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a in
                                               [uu____1036] in
                                             uu____1033 :: uu____1034 in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1031 in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____1024 uu____1030 in
                                       uu____1023 None FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let uu____1044 =
                                       let uu____1048 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____1049 =
                                         let uu____1051 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [uu____1051] in
                                       uu____1048 :: uu____1049 in
                                     let uu____1052 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow uu____1044
                                       uu____1052 in
                                   let uu____1055 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k in
                                   match uu____1055 with
                                   | (expected_k1,uu____1063,uu____1064) ->
>>>>>>> origin/guido_tactics
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
<<<<<<< HEAD
                                       let uu____976 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____976 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____988 ->
=======
                                       let uu____1067 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1 in
                                       (match uu____1067 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1079 ->
>>>>>>> origin/guido_tactics
                                                 raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
<<<<<<< HEAD
                                     let uu____1002 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1002 with
                                     | (act_typ,uu____1007,g_t) ->
                                         let env' =
                                           let uu___95_1010 =
=======
                                     let uu____1099 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____1099 with
                                     | (act_typ,uu____1104,g_t) ->
                                         let env' =
                                           let uu___97_1107 =
>>>>>>> origin/guido_tactics
                                             FStar_TypeChecker_Env.set_expected_typ
                                               env1 act_typ in
                                           {
                                             FStar_TypeChecker_Env.solver =
<<<<<<< HEAD
                                               (uu___95_1010.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___95_1010.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___95_1010.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___95_1010.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___95_1010.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___95_1010.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___95_1010.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___95_1010.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___95_1010.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___95_1010.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___95_1010.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___95_1010.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___95_1010.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___95_1010.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___95_1010.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___95_1010.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___95_1010.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___95_1010.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___95_1010.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___95_1010.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___95_1010.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___95_1010.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___95_1010.FStar_TypeChecker_Env.qname_and_index)
                                           } in
                                         ((let uu____1012 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1012
                                           then
                                             let uu____1013 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1014 =
=======
                                               (uu___97_1107.FStar_TypeChecker_Env.solver);
                                             FStar_TypeChecker_Env.range =
                                               (uu___97_1107.FStar_TypeChecker_Env.range);
                                             FStar_TypeChecker_Env.curmodule
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.curmodule);
                                             FStar_TypeChecker_Env.gamma =
                                               (uu___97_1107.FStar_TypeChecker_Env.gamma);
                                             FStar_TypeChecker_Env.gamma_cache
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.gamma_cache);
                                             FStar_TypeChecker_Env.modules =
                                               (uu___97_1107.FStar_TypeChecker_Env.modules);
                                             FStar_TypeChecker_Env.expected_typ
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.expected_typ);
                                             FStar_TypeChecker_Env.sigtab =
                                               (uu___97_1107.FStar_TypeChecker_Env.sigtab);
                                             FStar_TypeChecker_Env.is_pattern
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.is_pattern);
                                             FStar_TypeChecker_Env.instantiate_imp
                                               = false;
                                             FStar_TypeChecker_Env.effects =
                                               (uu___97_1107.FStar_TypeChecker_Env.effects);
                                             FStar_TypeChecker_Env.generalize
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.generalize);
                                             FStar_TypeChecker_Env.letrecs =
                                               (uu___97_1107.FStar_TypeChecker_Env.letrecs);
                                             FStar_TypeChecker_Env.top_level
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.top_level);
                                             FStar_TypeChecker_Env.check_uvars
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.check_uvars);
                                             FStar_TypeChecker_Env.use_eq =
                                               (uu___97_1107.FStar_TypeChecker_Env.use_eq);
                                             FStar_TypeChecker_Env.is_iface =
                                               (uu___97_1107.FStar_TypeChecker_Env.is_iface);
                                             FStar_TypeChecker_Env.admit =
                                               (uu___97_1107.FStar_TypeChecker_Env.admit);
                                             FStar_TypeChecker_Env.lax =
                                               (uu___97_1107.FStar_TypeChecker_Env.lax);
                                             FStar_TypeChecker_Env.lax_universes
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.lax_universes);
                                             FStar_TypeChecker_Env.type_of =
                                               (uu___97_1107.FStar_TypeChecker_Env.type_of);
                                             FStar_TypeChecker_Env.universe_of
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.universe_of);
                                             FStar_TypeChecker_Env.use_bv_sorts
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.use_bv_sorts);
                                             FStar_TypeChecker_Env.qname_and_index
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.qname_and_index);
                                             FStar_TypeChecker_Env.proof_ns =
                                               (uu___97_1107.FStar_TypeChecker_Env.proof_ns);
                                             FStar_TypeChecker_Env.synth =
                                               (uu___97_1107.FStar_TypeChecker_Env.synth);
                                             FStar_TypeChecker_Env.is_native_tactic
                                               =
                                               (uu___97_1107.FStar_TypeChecker_Env.is_native_tactic)
                                           } in
                                         ((let uu____1109 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED") in
                                           if uu____1109
                                           then
                                             let uu____1110 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let uu____1111 =
>>>>>>> origin/guido_tactics
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
<<<<<<< HEAD
                                               uu____1013 uu____1014
                                           else ());
                                          (let uu____1016 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1016 with
                                           | (act_defn,uu____1021,g_a) ->
=======
                                               uu____1110 uu____1111
                                           else ());
                                          (let uu____1113 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____1113 with
                                           | (act_defn,uu____1118,g_a) ->
>>>>>>> origin/guido_tactics
                                               let act_defn1 =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant]
                                                   env1 act_defn in
                                               let act_typ1 =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant;
                                                   FStar_TypeChecker_Normalize.Eager_unfolding;
                                                   FStar_TypeChecker_Normalize.Beta]
                                                   env1 act_typ in
<<<<<<< HEAD
                                               let uu____1025 =
=======
                                               let uu____1122 =
>>>>>>> origin/guido_tactics
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1 in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
<<<<<<< HEAD
                                                     let uu____1043 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1043 with
                                                      | (bs1,uu____1049) ->
=======
                                                     let uu____1140 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____1140 with
                                                      | (bs1,uu____1146) ->
>>>>>>> origin/guido_tactics
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
<<<<<<< HEAD
                                                            let uu____1056 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1056 in
                                                          let uu____1059 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1059
                                                           with
                                                           | (k1,uu____1066,g)
                                                               -> (k1, g)))
                                                 | uu____1068 ->
                                                     let uu____1069 =
                                                       let uu____1070 =
                                                         let uu____1073 =
                                                           let uu____1074 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1075 =
=======
                                                            let uu____1153 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1153 in
                                                          let uu____1156 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k in
                                                          (match uu____1156
                                                           with
                                                           | (k1,uu____1163,g)
                                                               -> (k1, g)))
                                                 | uu____1165 ->
                                                     let uu____1166 =
                                                       let uu____1167 =
                                                         let uu____1170 =
                                                           let uu____1171 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2 in
                                                           let uu____1172 =
>>>>>>> origin/guido_tactics
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2 in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
<<<<<<< HEAD
                                                             uu____1074
                                                             uu____1075 in
                                                         (uu____1073,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1070 in
                                                     raise uu____1069 in
                                               (match uu____1025 with
=======
                                                             uu____1171
                                                             uu____1172 in
                                                         (uu____1170,
                                                           (act_defn1.FStar_Syntax_Syntax.pos)) in
                                                       FStar_Errors.Error
                                                         uu____1167 in
                                                     raise uu____1166 in
                                               (match uu____1122 with
>>>>>>> origin/guido_tactics
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k in
<<<<<<< HEAD
                                                    ((let uu____1082 =
                                                        let uu____1083 =
                                                          let uu____1084 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1084 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1083 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1082);
                                                     (let act_typ2 =
                                                        let uu____1088 =
                                                          let uu____1089 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1089.FStar_Syntax_Syntax.n in
                                                        match uu____1088 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1106 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1106
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1113
=======
                                                    ((let uu____1179 =
                                                        let uu____1180 =
                                                          let uu____1181 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1181 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1180 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1179);
                                                     (let act_typ2 =
                                                        let uu____1185 =
                                                          let uu____1186 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k in
                                                          uu____1186.FStar_Syntax_Syntax.n in
                                                        match uu____1185 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1203 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____1203
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1210
>>>>>>> origin/guido_tactics
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
<<<<<<< HEAD
                                                                 (match uu____1113
=======
                                                                 (match uu____1210
>>>>>>> origin/guido_tactics
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
<<<<<<< HEAD
                                                                    let uu____1133
                                                                    =
                                                                    let uu____1134
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1134] in
                                                                    let uu____1135
                                                                    =
                                                                    let uu____1141
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1141] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1133;
=======
                                                                    let uu____1230
                                                                    =
                                                                    let uu____1231
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1231] in
                                                                    let uu____1232
                                                                    =
                                                                    let uu____1238
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1238] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1230;
>>>>>>> origin/guido_tactics
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
<<<<<<< HEAD
                                                                    uu____1135;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1142
=======
                                                                    uu____1232;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1239
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
<<<<<<< HEAD
                                                                    uu____1142))
                                                        | uu____1145 ->
                                                            failwith "" in
                                                      let uu____1148 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1148 with
=======
                                                                    uu____1239))
                                                        | uu____1242 ->
                                                            failwith "" in
                                                      let uu____1245 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1 in
                                                      match uu____1245 with
>>>>>>> origin/guido_tactics
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2 in
<<<<<<< HEAD
                                                          let uu___96_1154 =
=======
                                                          let uu___98_1251 =
>>>>>>> origin/guido_tactics
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
<<<<<<< HEAD
                                                              (uu___96_1154.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___96_1154.FStar_Syntax_Syntax.action_unqualified_name);
=======
                                                              (uu___98_1251.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___98_1251.FStar_Syntax_Syntax.action_unqualified_name);
>>>>>>> origin/guido_tactics
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs1;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
<<<<<<< HEAD
                                                              (uu___96_1154.FStar_Syntax_Syntax.action_params);
=======
                                                              (uu___98_1251.FStar_Syntax_Syntax.action_params);
>>>>>>> origin/guido_tactics
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn2;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ3
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed2.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
<<<<<<< HEAD
                           match uu____645 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1170 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1170 in
                               let uu____1173 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1173 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1179 =
                                        let uu____1182 =
                                          let uu____1183 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1183.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1182) in
                                      match uu____1179 with
                                      | ([],uu____1186) -> t1
                                      | (uu____1192,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1193,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1205 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1216 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1216 in
                                      let m = FStar_List.length (fst ts1) in
                                      (let uu____1221 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1223 =
                                               FStar_Syntax_Util.is_unknown
                                                 (snd ts1) in
                                             Prims.op_Negation uu____1223))
                                           && (m <> n1) in
                                       if uu____1221
=======
                           match uu____736 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let uu____1267 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed2.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed2.FStar_Syntax_Syntax.binders uu____1267 in
                               let uu____1270 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____1270 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1276 =
                                        let uu____1279 =
                                          let uu____1280 =
                                            FStar_Syntax_Subst.compress t1 in
                                          uu____1280.FStar_Syntax_Syntax.n in
                                        (effect_params, uu____1279) in
                                      match uu____1276 with
                                      | ([],uu____1283) -> t1
                                      | (uu____1289,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1290,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____1302 -> failwith "Impossible" in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1313 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1313 in
                                      let m = FStar_List.length (fst ts1) in
                                      (let uu____1319 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1320 =
                                               FStar_Syntax_Util.is_unknown
                                                 (snd ts1) in
                                             Prims.op_Negation uu____1320))
                                           && (m <> n1) in
                                       if uu____1319
>>>>>>> origin/guido_tactics
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
<<<<<<< HEAD
                                         let uu____1232 =
                                           let uu____1233 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1234 =
=======
                                         let uu____1334 =
                                           let uu____1335 =
                                             FStar_Util.string_of_int n1 in
                                           let uu____1336 =
>>>>>>> origin/guido_tactics
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1 in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
<<<<<<< HEAD
                                             error uu____1233 uu____1234 in
                                         failwith uu____1232
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1240 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1240 with
                                      | (univs2,defn) ->
                                          let uu____1245 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1245 with
                                           | (univs',typ) ->
                                               let uu___97_1252 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___97_1252.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___97_1252.FStar_Syntax_Syntax.action_unqualified_name);
=======
                                             error uu____1335 uu____1336 in
                                         failwith uu____1334
                                       else ());
                                      ts1 in
                                    let close_action act =
                                      let uu____1342 =
                                        close1 (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____1342 with
                                      | (univs2,defn) ->
                                          let uu____1347 =
                                            close1 (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____1347 with
                                           | (univs',typ) ->
                                               let uu___99_1353 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___99_1353.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___99_1353.FStar_Syntax_Syntax.action_unqualified_name);
>>>>>>> origin/guido_tactics
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs2;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
<<<<<<< HEAD
                                                   (uu___97_1252.FStar_Syntax_Syntax.action_params);
=======
                                                   (uu___99_1353.FStar_Syntax_Syntax.action_params);
>>>>>>> origin/guido_tactics
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let ed3 =
<<<<<<< HEAD
                                      let uu___98_1256 = ed2 in
                                      let uu____1257 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1258 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1259 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1260 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1261 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1262 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1263 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1264 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1265 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1266 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1267 =
                                        let uu____1268 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        snd uu____1268 in
                                      let uu____1274 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1275 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1276 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___98_1256.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___98_1256.FStar_Syntax_Syntax.mname);
=======
                                      let uu___100_1356 = ed2 in
                                      let uu____1357 =
                                        close1 (Prims.parse_int "0")
                                          return_wp in
                                      let uu____1358 =
                                        close1 (Prims.parse_int "1") bind_wp in
                                      let uu____1359 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1 in
                                      let uu____1360 =
                                        close1 (Prims.parse_int "0") ite_wp in
                                      let uu____1361 =
                                        close1 (Prims.parse_int "0") stronger in
                                      let uu____1362 =
                                        close1 (Prims.parse_int "1") close_wp in
                                      let uu____1363 =
                                        close1 (Prims.parse_int "0") assert_p in
                                      let uu____1364 =
                                        close1 (Prims.parse_int "0") assume_p in
                                      let uu____1365 =
                                        close1 (Prims.parse_int "0") null_wp in
                                      let uu____1366 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp in
                                      let uu____1367 =
                                        let uu____1368 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr) in
                                        snd uu____1368 in
                                      let uu____1374 =
                                        close1 (Prims.parse_int "0")
                                          return_repr in
                                      let uu____1375 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr in
                                      let uu____1376 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___100_1356.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___100_1356.FStar_Syntax_Syntax.mname);
>>>>>>> origin/guido_tactics
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
<<<<<<< HEAD
                                          uu____1257;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1258;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1259;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1260;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1261;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1262;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1263;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1264;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1265;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1266;
                                        FStar_Syntax_Syntax.repr = uu____1267;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1274;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1275;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1276
                                      } in
                                    ((let uu____1279 =
=======
                                          uu____1357;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1358;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1359;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1360;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1361;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1362;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1363;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1364;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1365;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1366;
                                        FStar_Syntax_Syntax.repr = uu____1367;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1374;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1375;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1376
                                      } in
                                    ((let uu____1379 =
>>>>>>> origin/guido_tactics
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED")) in
<<<<<<< HEAD
                                      if uu____1279
                                      then
                                        let uu____1280 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1280
=======
                                      if uu____1379
                                      then
                                        let uu____1380 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print_string uu____1380
>>>>>>> origin/guido_tactics
                                      else ());
                                     ed3)))))))
let cps_and_elaborate:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.eff_decl*
        FStar_Syntax_Syntax.sigelt option)
  =
  fun env  ->
    fun ed  ->
<<<<<<< HEAD
      let uu____1293 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1293 with
      | (effect_binders_un,signature_un) ->
          let uu____1303 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1303 with
           | (effect_binders,env1,uu____1314) ->
               let uu____1315 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1315 with
                | (signature,uu____1324) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1337  ->
                           match uu____1337 with
                           | (bv,qual) ->
                               let uu____1344 =
                                 let uu___99_1345 = bv in
                                 let uu____1346 =
=======
      let uu____1384 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1384 with
      | (effect_binders_un,signature_un) ->
          let uu____1394 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1394 with
           | (effect_binders,env1,uu____1405) ->
               let uu____1406 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____1406 with
                | (signature,uu____1415) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1424  ->
                           match uu____1424 with
                           | (bv,qual) ->
                               let uu____1431 =
                                 let uu___101_1432 = bv in
                                 let uu____1433 =
>>>>>>> origin/guido_tactics
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                                     (uu___99_1345.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___99_1345.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1346
                                 } in
                               (uu____1344, qual)) effect_binders in
                    let uu____1349 =
                      let uu____1354 =
                        let uu____1355 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1355.FStar_Syntax_Syntax.n in
                      match uu____1354 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1363)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1378 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1349 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1395 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1395
                           then
                             let uu____1396 =
                               let uu____1398 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1398 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1396
=======
                                     (uu___101_1432.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___101_1432.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1433
                                 } in
                               (uu____1431, qual)) effect_binders in
                    let uu____1436 =
                      let uu____1441 =
                        let uu____1442 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____1442.FStar_Syntax_Syntax.n in
                      match uu____1441 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1450)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1465 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____1436 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1482 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____1482
                           then
                             let uu____1483 =
                               let uu____1485 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               Some uu____1485 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1483
>>>>>>> origin/guido_tactics
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
<<<<<<< HEAD
                           let uu____1422 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1422 with
                           | (t2,comp,uu____1430) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1441 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1441 with
                          | (repr,_comp) ->
                              ((let uu____1454 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1454
                                then
                                  let uu____1455 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1455
=======
                           let uu____1509 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____1509 with
                           | (t2,comp,uu____1517) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1528 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____1528 with
                          | (repr,_comp) ->
                              ((let uu____1541 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____1541
                                then
                                  let uu____1542 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1542
>>>>>>> origin/guido_tactics
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       FStar_Range.dummyRange) in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr in
                                let wp_type1 = recheck_debug "*" env1 wp_type in
                                let wp_a =
<<<<<<< HEAD
                                  let uu____1461 =
                                    let uu____1462 =
                                      let uu____1463 =
                                        let uu____1473 =
                                          let uu____1477 =
                                            let uu____1480 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1481 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1480, uu____1481) in
                                          [uu____1477] in
                                        (wp_type1, uu____1473) in
                                      FStar_Syntax_Syntax.Tm_app uu____1463 in
                                    mk1 uu____1462 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1461 in
                                let effect_signature =
                                  let binders =
                                    let uu____1496 =
                                      let uu____1499 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1499) in
                                    let uu____1500 =
                                      let uu____1504 =
                                        let uu____1505 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1505
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1504] in
                                    uu____1496 :: uu____1500 in
=======
                                  let uu____1548 =
                                    let uu____1549 =
                                      let uu____1550 =
                                        let uu____1560 =
                                          let uu____1564 =
                                            let uu____1567 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____1568 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____1567, uu____1568) in
                                          [uu____1564] in
                                        (wp_type1, uu____1560) in
                                      FStar_Syntax_Syntax.Tm_app uu____1550 in
                                    mk1 uu____1549 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1548 in
                                let effect_signature =
                                  let binders =
                                    let uu____1583 =
                                      let uu____1586 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____1586) in
                                    let uu____1587 =
                                      let uu____1591 =
                                        let uu____1592 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right uu____1592
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____1591] in
                                    uu____1583 :: uu____1587 in
>>>>>>> origin/guido_tactics
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker)) in
                                let effect_signature1 =
                                  recheck_debug
                                    "turned into the effect signature" env1
                                    effect_signature in
                                let sigelts = FStar_Util.mk_ref [] in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name in
                                let elaborate_and_star dmff_env1
                                  other_binders item =
                                  let env2 =
                                    FStar_TypeChecker_DMFF.get_env dmff_env1 in
<<<<<<< HEAD
                                  let uu____1548 = item in
                                  match uu____1548 with
                                  | (u_item,item1) ->
                                      let uu____1560 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____1560 with
                                       | (item2,item_comp) ->
                                           ((let uu____1570 =
                                               let uu____1571 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1571 in
                                             if uu____1570
                                             then
                                               let uu____1572 =
                                                 let uu____1573 =
                                                   let uu____1574 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1575 =
=======
                                  let uu____1635 = item in
                                  match uu____1635 with
                                  | (u_item,item1) ->
                                      let uu____1647 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____1647 with
                                       | (item2,item_comp) ->
                                           ((let uu____1657 =
                                               let uu____1658 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____1658 in
                                             if uu____1657
                                             then
                                               let uu____1659 =
                                                 let uu____1660 =
                                                   let uu____1661 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____1662 =
>>>>>>> origin/guido_tactics
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
<<<<<<< HEAD
                                                     uu____1574 uu____1575 in
                                                 FStar_Errors.Err uu____1573 in
                                               raise uu____1572
                                             else ());
                                            (let uu____1577 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1577 with
=======
                                                     uu____1661 uu____1662 in
                                                 FStar_Errors.Err uu____1660 in
                                               raise uu____1659
                                             else ());
                                            (let uu____1664 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____1664 with
>>>>>>> origin/guido_tactics
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
<<<<<<< HEAD
                                let uu____1590 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1590 with
                                | (dmff_env1,uu____1603,bind_wp,bind_elab) ->
                                    let uu____1606 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1606 with
                                     | (dmff_env2,uu____1619,return_wp,return_elab)
=======
                                let uu____1677 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1677 with
                                | (dmff_env1,uu____1690,bind_wp,bind_elab) ->
                                    let uu____1693 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1693 with
                                     | (dmff_env2,uu____1706,return_wp,return_elab)
>>>>>>> origin/guido_tactics
                                         ->
                                         let rc_gtot =
                                           {
                                             FStar_Syntax_Syntax.residual_effect
                                               =
                                               FStar_Syntax_Const.effect_GTot_lid;
                                             FStar_Syntax_Syntax.residual_typ
                                               = None;
                                             FStar_Syntax_Syntax.residual_flags
                                               = []
                                           } in
                                         let lift_from_pure_wp =
<<<<<<< HEAD
                                           let uu____1623 =
                                             let uu____1624 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1624.FStar_Syntax_Syntax.n in
                                           match uu____1623 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1662 =
                                                 let uu____1670 =
                                                   let uu____1673 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1673 in
                                                 match uu____1670 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1712 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1662 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1734 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1734 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1745 =
                                                          let uu____1746 =
                                                            let uu____1756 =
                                                              let uu____1760
                                                                =
                                                                let uu____1763
=======
                                           let uu____1713 =
                                             let uu____1714 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1714.FStar_Syntax_Syntax.n in
                                           match uu____1713 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1742 =
                                                 let uu____1750 =
                                                   let uu____1753 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____1753 in
                                                 match uu____1750 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____1787 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1742 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____1809 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____1809 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____1820 =
                                                          let uu____1821 =
                                                            let uu____1831 =
                                                              let uu____1835
                                                                =
                                                                let uu____1838
>>>>>>> origin/guido_tactics
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    fst b11) in
<<<<<<< HEAD
                                                                let uu____1764
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1763,
                                                                  uu____1764) in
                                                              [uu____1760] in
                                                            (wp_type1,
                                                              uu____1756) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1746 in
                                                        mk1 uu____1745 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1772 =
                                                      let uu____1782 =
                                                        let uu____1783 =
=======
                                                                let uu____1839
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____1838,
                                                                  uu____1839) in
                                                              [uu____1835] in
                                                            (wp_type1,
                                                              uu____1831) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____1821 in
                                                        mk1 uu____1820 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____1847 =
                                                      let uu____1852 =
                                                        let uu____1853 =
>>>>>>> origin/guido_tactics
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
<<<<<<< HEAD
                                                          uu____1783 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1782 in
                                                    (match uu____1772 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____1811
                                                           =
                                                           let error_msg =
                                                             let uu____1813 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____1814 =
                                                               match what'
                                                               with
                                                               | None  ->
                                                                   "None"
                                                               | Some
                                                                   (FStar_Util.Inl
                                                                   lc) ->
                                                                   FStar_Syntax_Print.lcomp_to_string
                                                                    lc
                                                               | Some
                                                                   (FStar_Util.Inr
                                                                   (lid,uu____1830))
                                                                   ->
                                                                   FStar_Ident.text_of_lid
                                                                    lid in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1813
                                                               uu____1814 in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  -> fail ()
                                                           | Some
                                                               (FStar_Util.Inl
                                                               lc) ->
                                                               let uu____1856
                                                                 =
                                                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                                   lc in
                                                               if uu____1856
                                                               then
                                                                 let g_opt =
                                                                   FStar_TypeChecker_Rel.try_teq
=======
                                                          uu____1853 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____1852 in
                                                    (match uu____1847 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____1866
                                                           =
                                                           let error_msg =
                                                             let uu____1868 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____1868
                                                               (match what'
                                                                with
                                                                | None  ->
                                                                    "None"
                                                                | Some rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect) in
                                                           failwith error_msg in
                                                         ((match what' with
                                                           | None  -> fail ()
                                                           | Some rc ->
                                                               (if
                                                                  Prims.op_Negation
                                                                    (
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect)
                                                                then fail ()
                                                                else ();
                                                                (let uu____1874
                                                                   =
                                                                   FStar_Util.map_opt
                                                                    rc.FStar_Syntax_Syntax.residual_typ
                                                                    (fun rt 
                                                                    ->
                                                                    let g_opt
                                                                    =
                                                                    FStar_TypeChecker_Rel.try_teq
>>>>>>> origin/guido_tactics
                                                                    true env1
                                                                    rt
                                                                    FStar_Syntax_Util.ktype0 in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    Some g'
                                                                    ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
<<<<<<< HEAD
                                                                  | None  ->
                                                                    fail ())
                                                               else fail ()
                                                           | Some
                                                               (FStar_Util.Inr
                                                               (lid,uu____1862))
                                                               ->
                                                               if
                                                                 Prims.op_Negation
                                                                   (FStar_Syntax_Util.is_pure_effect
                                                                    lid)
                                                               then fail ()
                                                               else ());
=======
                                                                    | 
                                                                    None  ->
                                                                    fail ()) in
                                                                 FStar_All.pipe_right
                                                                   uu____1874
                                                                   FStar_Pervasives.ignore)));
>>>>>>> origin/guido_tactics
                                                          (let wp =
                                                             let t2 =
                                                               (fst b21).FStar_Syntax_Syntax.sort in
                                                             let pure_wp_type
                                                               =
                                                               FStar_TypeChecker_DMFF.double_star
                                                                 t2 in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp" None
                                                               pure_wp_type in
                                                           let body3 =
<<<<<<< HEAD
                                                             let uu____1882 =
                                                               let uu____1883
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1884
                                                                 =
                                                                 let uu____1885
                                                                   =
                                                                   let uu____1889
=======
                                                             let uu____1894 =
                                                               let uu____1895
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____1896
                                                                 =
                                                                 let uu____1897
                                                                   =
                                                                   let uu____1901
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
<<<<<<< HEAD
                                                                   (uu____1889,
                                                                    None) in
                                                                 [uu____1885] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1883
                                                                 uu____1884 in
                                                             uu____1882 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1905 =
                                                             let uu____1906 =
                                                               let uu____1910
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1910] in
                                                             b11 ::
                                                               uu____1906 in
                                                           let uu____1913 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1905
                                                             uu____1913
                                                             (Some
                                                                (FStar_Util.Inr
                                                                   (FStar_Syntax_Const.effect_GTot_lid,
                                                                    [])))))))
                                           | uu____1923 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____1925 =
                                             let uu____1926 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1926.FStar_Syntax_Syntax.n in
                                           match uu____1925 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1964 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____1964
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____1980 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____1982 =
                                             let uu____1983 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____1983.FStar_Syntax_Syntax.n in
                                           match uu____1982 with
=======
                                                                   (uu____1901,
                                                                    None) in
                                                                 [uu____1897] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____1895
                                                                 uu____1896 in
                                                             uu____1894 None
                                                               FStar_Range.dummyRange in
                                                           let uu____1917 =
                                                             let uu____1918 =
                                                               let uu____1922
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____1922] in
                                                             b11 ::
                                                               uu____1918 in
                                                           let uu____1925 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____1917
                                                             uu____1925
                                                             (Some rc_gtot)))))
                                           | uu____1926 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu____1928 =
                                             let uu____1929 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____1929.FStar_Syntax_Syntax.n in
                                           match uu____1928 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1957 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____1957
                                                 (Some rc_gtot)
                                           | uu____1964 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu____1966 =
                                             let uu____1967 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____1967.FStar_Syntax_Syntax.n in
                                           match uu____1966 with
>>>>>>> origin/guido_tactics
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
<<<<<<< HEAD
                                               let uu____2012 =
                                                 let uu____2013 =
                                                   let uu____2015 =
                                                     let uu____2016 =
=======
                                               let uu____1986 =
                                                 let uu____1987 =
                                                   let uu____1989 =
                                                     let uu____1990 =
>>>>>>> origin/guido_tactics
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
<<<<<<< HEAD
                                                       uu____2016 in
                                                   [uu____2015] in
                                                 FStar_List.append uu____2013
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____2012 body what
                                           | uu____2017 ->
=======
                                                       uu____1990 in
                                                   [uu____1989] in
                                                 FStar_List.append uu____1987
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____1986 body what
                                           | uu____1991 ->
>>>>>>> origin/guido_tactics
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
<<<<<<< HEAD
                                             (let uu____2035 =
                                                let uu____2036 =
                                                  let uu____2037 =
                                                    let uu____2047 =
                                                      let uu____2048 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      snd uu____2048 in
                                                    (t, uu____2047) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2037 in
                                                mk1 uu____2036 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2035) in
=======
                                             (let uu____2011 =
                                                let uu____2012 =
                                                  let uu____2013 =
                                                    let uu____2023 =
                                                      let uu____2024 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      snd uu____2024 in
                                                    (t, uu____2023) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2013 in
                                                mk1 uu____2012 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2011) in
>>>>>>> origin/guido_tactics
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
<<<<<<< HEAD
                                               let uu____2071 = f a2 in
                                               [uu____2071]
                                           | x::xs ->
                                               let uu____2075 =
                                                 apply_last1 f xs in
                                               x :: uu____2075 in
=======
                                               let uu____2047 = f a2 in
                                               [uu____2047]
                                           | x::xs ->
                                               let uu____2051 =
                                                 apply_last1 f xs in
                                               x :: uu____2051 in
>>>>>>> origin/guido_tactics
                                         let register name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname in
                                           let p' =
                                             apply_last1
                                               (fun s  ->
                                                  Prims.strcat "__"
                                                    (Prims.strcat s
                                                       (Prims.strcat
                                                          "_eff_override_"
                                                          name))) p in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               FStar_Range.dummyRange in
<<<<<<< HEAD
                                           let uu____2092 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2092 with
                                           | Some (_us,_t) ->
                                               ((let uu____2109 =
                                                   FStar_Ident.string_of_lid
                                                     l' in
                                                 FStar_Util.print1
                                                   "DM4F: Applying override %s\n"
                                                   uu____2109);
                                                (let uu____2110 =
=======
                                           let uu____2066 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____2066 with
                                           | Some (_us,_t) ->
                                               ((let uu____2083 =
                                                   FStar_Options.debug_any () in
                                                 if uu____2083
                                                 then
                                                   let uu____2084 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____2084
                                                 else ());
                                                (let uu____2086 =
>>>>>>> origin/guido_tactics
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     None in
                                                 FStar_Syntax_Syntax.fv_to_tm
<<<<<<< HEAD
                                                   uu____2110))
                                           | None  ->
                                               let uu____2115 =
                                                 let uu____2118 = mk_lid name in
                                                 let uu____2119 =
=======
                                                   uu____2086))
                                           | None  ->
                                               let uu____2091 =
                                                 let uu____2094 = mk_lid name in
                                                 let uu____2095 =
>>>>>>> origin/guido_tactics
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
<<<<<<< HEAD
                                                   env1 uu____2118 uu____2119 in
                                               (match uu____2115 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2128 =
                                                        let uu____2130 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____2130 in
                                                      FStar_ST.write sigelts
                                                        uu____2128);
=======
                                                   env1 uu____2094 uu____2095 in
                                               (match uu____2091 with
                                                | (sigelt,fv) ->
                                                    ((let uu____2099 =
                                                        let uu____2101 =
                                                          FStar_ST.read
                                                            sigelts in
                                                        sigelt :: uu____2101 in
                                                      FStar_ST.write sigelts
                                                        uu____2099);
>>>>>>> origin/guido_tactics
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
<<<<<<< HEAD
                                         ((let uu____2141 =
                                             let uu____2143 =
=======
                                         ((let uu____2112 =
                                             let uu____2114 =
>>>>>>> origin/guido_tactics
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
<<<<<<< HEAD
                                             let uu____2144 =
                                               FStar_ST.read sigelts in
                                             uu____2143 :: uu____2144 in
                                           FStar_ST.write sigelts uu____2141);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2154 =
                                              let uu____2156 =
=======
                                             let uu____2115 =
                                               FStar_ST.read sigelts in
                                             uu____2114 :: uu____2115 in
                                           FStar_ST.write sigelts uu____2112);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           (let uu____2125 =
                                              let uu____2127 =
>>>>>>> origin/guido_tactics
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     (FStar_Syntax_Syntax.SetOptions
                                                        "--admit_smt_queries false")) in
<<<<<<< HEAD
                                              let uu____2157 =
                                                FStar_ST.read sigelts in
                                              uu____2156 :: uu____2157 in
                                            FStar_ST.write sigelts uu____2154);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2167 =
                                               let uu____2169 =
=======
                                              let uu____2128 =
                                                FStar_ST.read sigelts in
                                              uu____2127 :: uu____2128 in
                                            FStar_ST.write sigelts uu____2125);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            (let uu____2138 =
                                               let uu____2140 =
>>>>>>> origin/guido_tactics
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
<<<<<<< HEAD
                                               let uu____2170 =
                                                 FStar_ST.read sigelts in
                                               uu____2169 :: uu____2170 in
                                             FStar_ST.write sigelts
                                               uu____2167);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2180 =
                                                let uu____2182 =
=======
                                               let uu____2141 =
                                                 FStar_ST.read sigelts in
                                               uu____2140 :: uu____2141 in
                                             FStar_ST.write sigelts
                                               uu____2138);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             (let uu____2151 =
                                                let uu____2153 =
>>>>>>> origin/guido_tactics
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       (FStar_Syntax_Syntax.SetOptions
                                                          "--admit_smt_queries false")) in
<<<<<<< HEAD
                                                let uu____2183 =
                                                  FStar_ST.read sigelts in
                                                uu____2182 :: uu____2183 in
                                              FStar_ST.write sigelts
                                                uu____2180);
                                             (let uu____2191 =
                                                FStar_List.fold_left
                                                  (fun uu____2225  ->
                                                     fun action  ->
                                                       match uu____2225 with
=======
                                                let uu____2154 =
                                                  FStar_ST.read sigelts in
                                                uu____2153 :: uu____2154 in
                                              FStar_ST.write sigelts
                                                uu____2151);
                                             (let uu____2162 =
                                                FStar_List.fold_left
                                                  (fun uu____2169  ->
                                                     fun action  ->
                                                       match uu____2169 with
>>>>>>> origin/guido_tactics
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
<<<<<<< HEAD
                                                           let uu____2238 =
                                                             let uu____2242 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2242
                                                               params_un in
                                                           (match uu____2238
                                                            with
                                                            | (action_params,env',uu____2248)
=======
                                                           let uu____2182 =
                                                             let uu____2186 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2186
                                                               params_un in
                                                           (match uu____2182
                                                            with
                                                            | (action_params,env',uu____2192)
>>>>>>> origin/guido_tactics
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
<<<<<<< HEAD
                                                                    uu____2261
                                                                     ->
                                                                    match uu____2261
=======
                                                                    uu____2201
                                                                     ->
                                                                    match uu____2201
>>>>>>> origin/guido_tactics
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
<<<<<<< HEAD
                                                                    let uu____2268
                                                                    =
                                                                    let uu___100_2269
                                                                    = bv in
                                                                    let uu____2270
=======
                                                                    let uu____2208
                                                                    =
                                                                    let uu___102_2209
                                                                    = bv in
                                                                    let uu____2210
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
<<<<<<< HEAD
                                                                    (uu___100_2269.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___100_2269.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2270
                                                                    } in
                                                                    (uu____2268,
=======
                                                                    (uu___102_2209.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___102_2209.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2210
                                                                    } in
                                                                    (uu____2208,
>>>>>>> origin/guido_tactics
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
<<<<<<< HEAD
                                                                let uu____2274
=======
                                                                let uu____2214
>>>>>>> origin/guido_tactics
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
<<<<<<< HEAD
                                                                (match uu____2274
=======
                                                                (match uu____2214
>>>>>>> origin/guido_tactics
                                                                 with
                                                                 | (dmff_env4,action_t,action_wp,action_elab)
                                                                    ->
                                                                    let name
                                                                    =
                                                                    ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText in
                                                                    let action_typ_with_wp
                                                                    =
                                                                    FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp in
                                                                    let action_params2
                                                                    =
                                                                    FStar_Syntax_Subst.close_binders
                                                                    action_params1 in
                                                                    let action_elab1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab in
                                                                    let action_typ_with_wp1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp in
                                                                    let action_elab2
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    action_params2
                                                                    action_elab1
                                                                    None in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
<<<<<<< HEAD
                                                                    uu____2300
                                                                    ->
                                                                    let uu____2301
=======
                                                                    uu____2235
                                                                    ->
                                                                    let uu____2236
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
<<<<<<< HEAD
                                                                    uu____2301 in
                                                                    ((
                                                                    let uu____2305
=======
                                                                    uu____2236 in
                                                                    ((
                                                                    let uu____2240
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
<<<<<<< HEAD
                                                                    uu____2305
                                                                    then
                                                                    let uu____2306
=======
                                                                    uu____2240
                                                                    then
                                                                    let uu____2241
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
<<<<<<< HEAD
                                                                    let uu____2307
=======
                                                                    let uu____2242
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
<<<<<<< HEAD
                                                                    let uu____2308
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____2309
=======
                                                                    let uu____2243
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____2244
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
<<<<<<< HEAD
                                                                    uu____2306
                                                                    uu____2307
                                                                    uu____2308
                                                                    uu____2309
=======
                                                                    uu____2241
                                                                    uu____2242
                                                                    uu____2243
                                                                    uu____2244
>>>>>>> origin/guido_tactics
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2 in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2 in
<<<<<<< HEAD
                                                                    let uu____2313
                                                                    =
                                                                    let uu____2315
=======
                                                                    let uu____2248
                                                                    =
                                                                    let uu____2250
                                                                    =
                                                                    let uu___103_2251
                                                                    = action in
                                                                    let uu____2252
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    let uu___101_2316
                                                                    = action in
                                                                    let uu____2317
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
<<<<<<< HEAD
                                                                    let uu____2318
=======
                                                                    let uu____2253
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
<<<<<<< HEAD
                                                                    (uu___101_2316.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___101_2316.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___101_2316.FStar_Syntax_Syntax.action_univs);
=======
                                                                    (uu___103_2251.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___103_2251.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___103_2251.FStar_Syntax_Syntax.action_univs);
>>>>>>> origin/guido_tactics
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
<<<<<<< HEAD
                                                                    uu____2317;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2318
                                                                    } in
                                                                    uu____2315
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____2313))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2191 with
=======
                                                                    uu____2252;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2253
                                                                    } in
                                                                    uu____2250
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____2248))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____2162 with
>>>>>>> origin/guido_tactics
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
<<<<<<< HEAD
                                                      let uu____2338 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2339 =
                                                        let uu____2341 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2341] in
                                                      uu____2338 ::
                                                        uu____2339 in
                                                    let uu____2342 =
                                                      let uu____2343 =
                                                        let uu____2344 =
                                                          let uu____2345 =
                                                            let uu____2355 =
                                                              let uu____2359
                                                                =
                                                                let uu____2362
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2363
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2362,
                                                                  uu____2363) in
                                                              [uu____2359] in
                                                            (repr,
                                                              uu____2355) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2345 in
                                                        mk1 uu____2344 in
                                                      let uu____2371 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2343
                                                        uu____2371 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2342 None in
=======
                                                      let uu____2273 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____2274 =
                                                        let uu____2276 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____2276] in
                                                      uu____2273 ::
                                                        uu____2274 in
                                                    let uu____2277 =
                                                      let uu____2278 =
                                                        let uu____2279 =
                                                          let uu____2280 =
                                                            let uu____2290 =
                                                              let uu____2294
                                                                =
                                                                let uu____2297
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____2298
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2297,
                                                                  uu____2298) in
                                                              [uu____2294] in
                                                            (repr,
                                                              uu____2290) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2280 in
                                                        mk1 uu____2279 in
                                                      let uu____2306 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2278
                                                        uu____2306 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2277 None in
>>>>>>> origin/guido_tactics
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
<<<<<<< HEAD
                                                  let uu____2379 =
                                                    let uu____2384 =
                                                      let uu____2385 =
                                                        let uu____2388 =
=======
                                                  let uu____2309 =
                                                    let uu____2314 =
                                                      let uu____2315 =
                                                        let uu____2318 =
>>>>>>> origin/guido_tactics
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
<<<<<<< HEAD
                                                          uu____2388 in
                                                      uu____2385.FStar_Syntax_Syntax.n in
                                                    match uu____2384 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2396)
                                                        ->
                                                        let uu____2423 =
                                                          let uu____2432 =
=======
                                                          uu____2318 in
                                                      uu____2315.FStar_Syntax_Syntax.n in
                                                    match uu____2314 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2326)
                                                        ->
                                                        let uu____2343 =
                                                          let uu____2352 =
>>>>>>> origin/guido_tactics
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
<<<<<<< HEAD
                                                          match uu____2432
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2463 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2423
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2491 =
                                                               let uu____2492
                                                                 =
                                                                 let uu____2495
=======
                                                          match uu____2352
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2383 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____2343
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2411 =
                                                               let uu____2412
                                                                 =
                                                                 let uu____2415
>>>>>>> origin/guido_tactics
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
<<<<<<< HEAD
                                                                   uu____2495 in
                                                               uu____2492.FStar_Syntax_Syntax.n in
                                                             (match uu____2491
=======
                                                                   uu____2415 in
                                                               uu____2412.FStar_Syntax_Syntax.n in
                                                             (match uu____2411
>>>>>>> origin/guido_tactics
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
<<<<<<< HEAD
                                                                  let uu____2512
=======
                                                                  let uu____2432
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
<<<<<<< HEAD
                                                                  (match uu____2512
=======
                                                                  (match uu____2432
>>>>>>> origin/guido_tactics
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
<<<<<<< HEAD
                                                                    let uu____2521
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2536
                                                                     ->
                                                                    match uu____2536
                                                                    with
                                                                    | 
                                                                    (bv,uu____2540)
                                                                    ->
                                                                    let uu____2541
                                                                    =
                                                                    let uu____2542
=======
                                                                    let uu____2441
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2452
                                                                     ->
                                                                    match uu____2452
                                                                    with
                                                                    | 
                                                                    (bv,uu____2456)
                                                                    ->
                                                                    let uu____2457
                                                                    =
                                                                    let uu____2458
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
<<<<<<< HEAD
                                                                    uu____2542
=======
                                                                    uu____2458
>>>>>>> origin/guido_tactics
                                                                    (FStar_Util.set_mem
                                                                    (fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
<<<<<<< HEAD
                                                                    uu____2541
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2521
=======
                                                                    uu____2457
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____2441
>>>>>>> origin/guido_tactics
                                                                    with
                                                                    | 
                                                                    (pre_args,post_args)
                                                                    ->
                                                                    let post
                                                                    =
                                                                    match post_args
                                                                    with
                                                                    | 
                                                                    post::[]
                                                                    -> post
                                                                    | 
<<<<<<< HEAD
                                                                    uu____2575
                                                                    ->
                                                                    let uu____2579
                                                                    =
                                                                    let uu____2580
=======
                                                                    uu____2491
                                                                    ->
                                                                    let uu____2495
                                                                    =
                                                                    let uu____2496
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
<<<<<<< HEAD
                                                                    uu____2580 in
                                                                    failwith
                                                                    uu____2579 in
                                                                    let uu____2583
=======
                                                                    uu____2496 in
                                                                    failwith
                                                                    uu____2495 in
                                                                    let uu____2499
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
<<<<<<< HEAD
                                                                    let uu____2586
=======
                                                                    let uu____2502
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (fst post).FStar_Syntax_Syntax.sort
                                                                    None in
<<<<<<< HEAD
                                                                    (uu____2583,
                                                                    uu____2586)))
                                                              | uu____2596 ->
                                                                  let uu____2597
                                                                    =
                                                                    let uu____2598
=======
                                                                    (uu____2499,
                                                                    uu____2502)))
                                                              | uu____2507 ->
                                                                  let uu____2508
                                                                    =
                                                                    let uu____2509
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
<<<<<<< HEAD
                                                                    uu____2598 in
                                                                  failwith
                                                                    uu____2597))
                                                    | uu____2603 ->
                                                        let uu____2604 =
                                                          let uu____2605 =
=======
                                                                    uu____2509 in
                                                                  failwith
                                                                    uu____2508))
                                                    | uu____2514 ->
                                                        let uu____2515 =
                                                          let uu____2516 =
>>>>>>> origin/guido_tactics
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1 in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
<<<<<<< HEAD
                                                            uu____2605 in
                                                        failwith uu____2604 in
                                                  (match uu____2379 with
                                                   | (pre,post) ->
                                                       ((let uu____2622 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2624 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2626 =
=======
                                                            uu____2516 in
                                                        failwith uu____2515 in
                                                  (match uu____2309 with
                                                   | (pre,post) ->
                                                       ((let uu____2533 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____2535 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____2537 =
>>>>>>> origin/guido_tactics
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
<<<<<<< HEAD
                                                           let uu___102_2628
                                                             = ed in
                                                           let uu____2629 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2630 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2631 =
                                                             let uu____2632 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2632) in
                                                           let uu____2638 =
                                                             let uu____2639 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2639) in
                                                           let uu____2645 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2646 =
                                                             let uu____2647 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2647) in
                                                           let uu____2653 =
                                                             let uu____2654 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2654) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___102_2628.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___102_2628.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___102_2628.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2629;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2630;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2631;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2638;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___102_2628.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___102_2628.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___102_2628.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___102_2628.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___102_2628.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___102_2628.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___102_2628.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___102_2628.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2645;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2646;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2653;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2660 =
=======
                                                           let uu___104_2539
                                                             = ed in
                                                           let uu____2540 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____2541 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____2542 =
                                                             let uu____2543 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____2543) in
                                                           let uu____2549 =
                                                             let uu____2550 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____2550) in
                                                           let uu____2556 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____2557 =
                                                             let uu____2558 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____2558) in
                                                           let uu____2564 =
                                                             let uu____2565 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____2565) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2540;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2541;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2542;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2549;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___104_2539.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2556;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2557;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2564;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____2571 =
>>>>>>> origin/guido_tactics
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
<<<<<<< HEAD
                                                         match uu____2660
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2671
=======
                                                         match uu____2571
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2582
>>>>>>> origin/guido_tactics
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
<<<<<<< HEAD
                                                               if uu____2671
                                                               then
                                                                 let uu____2672
=======
                                                               if uu____2582
                                                               then
                                                                 let uu____2583
>>>>>>> origin/guido_tactics
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
<<<<<<< HEAD
                                                                   uu____2672
=======
                                                                   uu____2583
>>>>>>> origin/guido_tactics
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    (Prims.parse_int
                                                                    "0")
                                                                 then
                                                                   let lift_from_pure
                                                                    =
<<<<<<< HEAD
                                                                    let uu____2682
=======
                                                                    let uu____2595
                                                                    =
                                                                    let uu____2597
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    let uu____2603
                                                                    =
                                                                    let uu____2690
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
<<<<<<< HEAD
                                                                    uu____2690) in
                                                                    Some
                                                                    uu____2684 in
=======
                                                                    uu____2603) in
                                                                    Some
                                                                    uu____2597 in
>>>>>>> origin/guido_tactics
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
<<<<<<< HEAD
                                                                    uu____2682;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   let uu____2701
=======
                                                                    uu____2595;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   let uu____2614
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   Some
<<<<<<< HEAD
                                                                    uu____2701
                                                                 else None in
                                                               let uu____2703
                                                                 =
                                                                 let uu____2705
                                                                   =
                                                                   let uu____2707
=======
                                                                    uu____2614
                                                                 else None in
                                                               let uu____2616
                                                                 =
                                                                 let uu____2618
                                                                   =
                                                                   let uu____2620
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts in
                                                                   FStar_List.rev
<<<<<<< HEAD
                                                                    uu____2707 in
                                                                 FStar_List.append
                                                                   uu____2705
                                                                   sigelts' in
                                                               (uu____2703,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t env ses quals lids =
  match ses with
  | {
      FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ
        (lex_t1,[],[],t,uu____2753,uu____2754);
      FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = [];
      FStar_Syntax_Syntax.sigmeta = uu____2756;_}::{
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       FStar_Syntax_Syntax.Sig_datacon
                                                       (lex_top1,[],_t_top,_lex_t_top,_0_29,uu____2760);
                                                     FStar_Syntax_Syntax.sigrng
                                                       = r1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = [];
                                                     FStar_Syntax_Syntax.sigmeta
                                                       = uu____2762;_}::
      {
        FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
          (lex_cons,[],_t_cons,_lex_t_cons,_0_30,uu____2766);
        FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = [];
        FStar_Syntax_Syntax.sigmeta = uu____2768;_}::[]
      when
      ((_0_29 = (Prims.parse_int "0")) && (_0_30 = (Prims.parse_int "0"))) &&
        (((FStar_Ident.lid_equals lex_t1 FStar_Syntax_Const.lex_t_lid) &&
            (FStar_Ident.lid_equals lex_top1 FStar_Syntax_Const.lextop_lid))
           &&
           (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))
      ->
      let u = FStar_Syntax_Syntax.new_univ_name (Some r) in
      let t1 =
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u)) None r in
      let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1 in
      let tc =
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_inductive_typ
               (lex_t1, [u], [], t2, [],
                 [FStar_Syntax_Const.lextop_lid;
                 FStar_Syntax_Const.lexcons_lid]));
          FStar_Syntax_Syntax.sigrng = r;
          FStar_Syntax_Syntax.sigquals = [];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta
        } in
      let utop = FStar_Syntax_Syntax.new_univ_name (Some r1) in
      let lex_top_t =
        let uu____2807 =
          let uu____2810 =
            let uu____2811 =
              let uu____2816 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
                  FStar_Syntax_Syntax.Delta_constant None in
              (uu____2816, [FStar_Syntax_Syntax.U_name utop]) in
            FStar_Syntax_Syntax.Tm_uinst uu____2811 in
          FStar_Syntax_Syntax.mk uu____2810 in
        uu____2807 None r1 in
      let lex_top_t1 = FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
      let dc_lextop =
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_datacon
               (lex_top1, [utop], lex_top_t1, FStar_Syntax_Const.lex_t_lid,
                 (Prims.parse_int "0"), []));
          FStar_Syntax_Syntax.sigrng = r1;
          FStar_Syntax_Syntax.sigquals = [];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta
        } in
      let ucons1 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
      let ucons2 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
      let lex_cons_t =
        let a =
          let uu____2836 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type
                 (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
          FStar_Syntax_Syntax.new_bv (Some r2) uu____2836 in
        let hd1 =
          let uu____2842 = FStar_Syntax_Syntax.bv_to_name a in
          FStar_Syntax_Syntax.new_bv (Some r2) uu____2842 in
        let tl1 =
          let uu____2844 =
            let uu____2845 =
              let uu____2848 =
                let uu____2849 =
                  let uu____2854 =
                    FStar_Syntax_Syntax.fvar
                      (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid
                         r2) FStar_Syntax_Syntax.Delta_constant None in
                  (uu____2854, [FStar_Syntax_Syntax.U_name ucons2]) in
                FStar_Syntax_Syntax.Tm_uinst uu____2849 in
              FStar_Syntax_Syntax.mk uu____2848 in
            uu____2845 None r2 in
          FStar_Syntax_Syntax.new_bv (Some r2) uu____2844 in
        let res =
          let uu____2867 =
            let uu____2870 =
              let uu____2871 =
                let uu____2876 =
                  FStar_Syntax_Syntax.fvar
                    (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid
                       r2) FStar_Syntax_Syntax.Delta_constant None in
                (uu____2876,
                  [FStar_Syntax_Syntax.U_max
                     [FStar_Syntax_Syntax.U_name ucons1;
                     FStar_Syntax_Syntax.U_name ucons2]]) in
              FStar_Syntax_Syntax.Tm_uinst uu____2871 in
            FStar_Syntax_Syntax.mk uu____2870 in
          uu____2867 None r2 in
        let uu____2886 = FStar_Syntax_Syntax.mk_Total res in
        FStar_Syntax_Util.arrow
          [(a, (Some FStar_Syntax_Syntax.imp_tag)); (hd1, None); (tl1, None)]
          uu____2886 in
      let lex_cons_t1 =
        FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2] lex_cons_t in
      let dc_lexcons =
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_datacon
               (lex_cons, [ucons1; ucons2], lex_cons_t1,
                 FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"), []));
          FStar_Syntax_Syntax.sigrng = r2;
          FStar_Syntax_Syntax.sigquals = [];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta
        } in
      let uu____2908 = FStar_TypeChecker_Env.get_range env in
      {
        FStar_Syntax_Syntax.sigel =
          (FStar_Syntax_Syntax.Sig_bundle ([tc; dc_lextop; dc_lexcons], lids));
        FStar_Syntax_Syntax.sigrng = uu____2908;
        FStar_Syntax_Syntax.sigquals = [];
        FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta
      }
  | uu____2911 ->
      let uu____2913 =
        let uu____2914 =
          let uu____2915 =
            FStar_Syntax_Syntax.mk_sigelt
              (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
          FStar_Syntax_Print.sigelt_to_string uu____2915 in
        FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2914 in
      failwith uu____2913
let tc_assume:
=======
                                                                    uu____2620 in
                                                                 FStar_List.append
                                                                   uu____2618
                                                                   sigelts' in
                                                               (uu____2616,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
and tc_lex_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          match ses with
          | {
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (lex_t1,[],[],t,uu____2643,uu____2644);
              FStar_Syntax_Syntax.sigrng = r;
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta = uu____2646;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top1,[],_t_top,_lex_t_top,_0_39,uu____2650);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____2652;_}::
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons,[],_t_cons,_lex_t_cons,_0_40,uu____2656);
                FStar_Syntax_Syntax.sigrng = r2;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta = uu____2658;_}::[]
              when
              ((_0_39 = (Prims.parse_int "0")) &&
                 (_0_40 = (Prims.parse_int "0")))
                &&
                (((FStar_Ident.lid_equals lex_t1 FStar_Syntax_Const.lex_t_lid)
                    &&
                    (FStar_Ident.lid_equals lex_top1
                       FStar_Syntax_Const.lextop_lid))
                   &&
                   (FStar_Ident.lid_equals lex_cons
                      FStar_Syntax_Const.lexcons_lid))
              ->
              let u = FStar_Syntax_Syntax.new_univ_name (Some r) in
              let t1 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u))
                  None r in
              let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1 in
              let tc =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_inductive_typ
                       (lex_t1, [u], [], t2, [],
                         [FStar_Syntax_Const.lextop_lid;
                         FStar_Syntax_Const.lexcons_lid]));
                  FStar_Syntax_Syntax.sigrng = r;
                  FStar_Syntax_Syntax.sigquals = [];
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
                } in
              let utop = FStar_Syntax_Syntax.new_univ_name (Some r1) in
              let lex_top_t =
                let uu____2697 =
                  let uu____2700 =
                    let uu____2701 =
                      let uu____2706 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None in
                      (uu____2706, [FStar_Syntax_Syntax.U_name utop]) in
                    FStar_Syntax_Syntax.Tm_uinst uu____2701 in
                  FStar_Syntax_Syntax.mk uu____2700 in
                uu____2697 None r1 in
              let lex_top_t1 =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
              let dc_lextop =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_datacon
                       (lex_top1, [utop], lex_top_t1,
                         FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"),
                         []));
                  FStar_Syntax_Syntax.sigrng = r1;
                  FStar_Syntax_Syntax.sigquals = [];
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
                } in
              let ucons1 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let ucons2 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let lex_cons_t =
                let a =
                  let uu____2726 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2726 in
                let hd1 =
                  let uu____2732 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2732 in
                let tl1 =
                  let uu____2734 =
                    let uu____2735 =
                      let uu____2738 =
                        let uu____2739 =
                          let uu____2744 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None in
                          (uu____2744, [FStar_Syntax_Syntax.U_name ucons2]) in
                        FStar_Syntax_Syntax.Tm_uinst uu____2739 in
                      FStar_Syntax_Syntax.mk uu____2738 in
                    uu____2735 None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2734 in
                let res =
                  let uu____2757 =
                    let uu____2760 =
                      let uu____2761 =
                        let uu____2766 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None in
                        (uu____2766,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]]) in
                      FStar_Syntax_Syntax.Tm_uinst uu____2761 in
                    FStar_Syntax_Syntax.mk uu____2760 in
                  uu____2757 None r2 in
                let uu____2776 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2776 in
              let lex_cons_t1 =
                FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                  lex_cons_t in
              let dc_lexcons =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_datacon
                       (lex_cons, [ucons1; ucons2], lex_cons_t1,
                         FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"),
                         []));
                  FStar_Syntax_Syntax.sigrng = r2;
                  FStar_Syntax_Syntax.sigquals = [];
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
                } in
              let uu____2798 = FStar_TypeChecker_Env.get_range env in
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_bundle
                     ([tc; dc_lextop; dc_lexcons], lids));
                FStar_Syntax_Syntax.sigrng = uu____2798;
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta
              }
          | uu____2801 ->
              let uu____2803 =
                let uu____2804 =
                  let uu____2805 =
                    FStar_Syntax_Syntax.mk_sigelt
                      (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                  FStar_Syntax_Print.sigelt_to_string uu____2805 in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2804 in
              failwith uu____2803
and tc_assume:
>>>>>>> origin/guido_tactics
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.formula ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Range.range -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun lid  ->
      fun phi  ->
        fun quals  ->
          fun r  ->
            let env1 = FStar_TypeChecker_Env.set_range env r in
<<<<<<< HEAD
            let uu____2936 = FStar_Syntax_Util.type_u () in
            match uu____2936 with
            | (k,uu____2940) ->
                let phi1 =
                  let uu____2942 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2942
=======
            let uu____2815 = FStar_Syntax_Util.type_u () in
            match uu____2815 with
            | (k,uu____2819) ->
                let phi1 =
                  let uu____2821 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____2821
>>>>>>> origin/guido_tactics
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____2944 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____2944 with
                  | (us,phi2) ->
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_assume (lid, us, phi2));
                        FStar_Syntax_Syntax.sigrng = r;
                        FStar_Syntax_Syntax.sigquals = quals;
                        FStar_Syntax_Syntax.sigmeta =
                          FStar_Syntax_Syntax.default_sigmeta
                      }))
let tc_inductive:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
            Prims.list)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
<<<<<<< HEAD
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive" in
          let uu____2973 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____2973 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2992 =
=======
          let env0 = env in
          let uu____2831 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2831 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____2850 =
>>>>>>> origin/guido_tactics
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
<<<<<<< HEAD
                FStar_All.pipe_right uu____2992 FStar_List.flatten in
              ((let uu____3000 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____3000
=======
                FStar_All.pipe_right uu____2850 FStar_List.flatten in
              ((let uu____2858 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2858
>>>>>>> origin/guido_tactics
                then ()
                else
                  (let env2 =
                     FStar_TypeChecker_Env.push_sigelt env1 sig_bndle in
                   FStar_List.iter
                     (fun ty  ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env2 in
                        if Prims.op_Negation b
                        then
<<<<<<< HEAD
                          let uu____3011 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____3017,uu____3018,uu____3019,uu____3020,uu____3021)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____3026 -> failwith "Impossible!" in
                          match uu____3011 with
=======
                          let uu____2864 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2870,uu____2871,uu____2872,uu____2873,uu____2874)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____2879 -> failwith "Impossible!" in
                          match uu____2864 with
>>>>>>> origin/guido_tactics
                          | (lid,r) ->
                              FStar_Errors.err r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
<<<<<<< HEAD
               (let skip_prims_type uu____3035 =
=======
               (let skip_prims_type uu____2888 =
>>>>>>> origin/guido_tactics
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
<<<<<<< HEAD
                        (lid,uu____3039,uu____3040,uu____3041,uu____3042,uu____3043)
                        -> lid
                    | uu____3048 -> failwith "Impossible" in
=======
                        (lid,uu____2892,uu____2893,uu____2894,uu____2895,uu____2896)
                        -> lid
                    | uu____2901 -> failwith "Impossible" in
>>>>>>> origin/guido_tactics
                  let types_to_skip =
                    ["c_False";
                    "c_True";
                    "equals";
                    "h_equals";
                    "c_and";
                    "c_or"] in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    types_to_skip in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals in
<<<<<<< HEAD
                let res =
                  let uu____3061 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Syntax_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____3061
                  then ([sig_bndle], data_ops_ses)
                  else
                    (let is_unopteq =
                       FStar_List.existsb
                         (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals in
                     let ses1 =
                       if is_unopteq
                       then
                         FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                           sig_bndle tcs datas env1 tc_assume
                       else
                         FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                           sig_bndle tcs datas env1 tc_assume in
                     let uu____3078 =
                       let uu____3080 =
                         let uu____3081 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____3081;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta
                         } in
                       uu____3080 :: ses1 in
                     (uu____3078, data_ops_ses)) in
                (let uu____3087 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive" in
                 ());
                res))
let tc_decl:
=======
                let uu____2907 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                if uu____2907
                then ([sig_bndle], data_ops_ses)
                else
                  (let is_unopteq =
                     FStar_List.existsb
                       (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals in
                   let ses1 =
                     if is_unopteq
                     then
                       FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                         sig_bndle tcs datas env0 tc_assume
                     else
                       FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                         sig_bndle tcs datas env0 tc_assume in
                   let uu____2925 =
                     let uu____2927 =
                       let uu____2928 = FStar_TypeChecker_Env.get_range env0 in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle
                              ((FStar_List.append tcs datas), lids));
                         FStar_Syntax_Syntax.sigrng = uu____2928;
                         FStar_Syntax_Syntax.sigquals = quals;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta
                       } in
                     uu____2927 :: ses1 in
                   (uu____2925, data_ops_ses))))
and tc_decl:
>>>>>>> origin/guido_tactics
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list)
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se in
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (let r = se.FStar_Syntax_Syntax.sigrng in
       match se.FStar_Syntax_Syntax.sigel with
<<<<<<< HEAD
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____3109 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____3122 ->
=======
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____2946 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____2959 ->
>>>>>>> origin/guido_tactics
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))
           ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let se1 = tc_lex_t env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
<<<<<<< HEAD
           let uu____3152 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____3152 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____3177 = FStar_Options.set_options t s in
             match uu____3177 with
=======
           let uu____2989 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____2989 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____3014 = FStar_Options.set_options t s in
             match uu____3014 with
>>>>>>> origin/guido_tactics
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 raise
                   (FStar_Errors.Error
                      ("Failed to process pragma: use 'fstar --help' to see which options are available",
                        r))
             | FStar_Getopt.Error s1 ->
                 raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Failed to process pragma: " s1), r)) in
           (match p with
            | FStar_Syntax_Syntax.LightOff  ->
                (if p = FStar_Syntax_Syntax.LightOff
                 then FStar_Options.set_ml_ish ()
                 else ();
                 ([se], []))
            | FStar_Syntax_Syntax.SetOptions o ->
                (set_options1 FStar_Options.Set o; ([se], []))
            | FStar_Syntax_Syntax.ResetOptions sopt ->
<<<<<<< HEAD
                ((let uu____3194 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____3194 FStar_Pervasives.ignore);
=======
                ((let uu____3031 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____3031 FStar_Pervasives.ignore);
>>>>>>> origin/guido_tactics
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
<<<<<<< HEAD
           let uu____3200 = cps_and_elaborate env1 ne in
           (match uu____3200 with
=======
           let uu____3037 = cps_and_elaborate env1 ne in
           (match uu____3037 with
>>>>>>> origin/guido_tactics
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
<<<<<<< HEAD
                      [(let uu___103_3222 = se in
=======
                      [(let uu___105_3058 = se in
>>>>>>> origin/guido_tactics
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                            (uu___103_3222.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___103_3222.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___103_3222.FStar_Syntax_Syntax.sigmeta)
                        });
                      lift]
                  | None  ->
                      [(let uu___104_3224 = se in
=======
                            (uu___105_3058.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___105_3058.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___105_3058.FStar_Syntax_Syntax.sigmeta)
                        });
                      lift]
                  | None  ->
                      [(let uu___106_3059 = se in
>>>>>>> origin/guido_tactics
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                            (uu___104_3224.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___104_3224.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___104_3224.FStar_Syntax_Syntax.sigmeta)
=======
                            (uu___106_3059.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___106_3059.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___106_3059.FStar_Syntax_Syntax.sigmeta)
>>>>>>> origin/guido_tactics
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
<<<<<<< HEAD
             let uu___105_3230 = se in
=======
             let uu___107_3065 = se in
>>>>>>> origin/guido_tactics
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                 (uu___105_3230.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___105_3230.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___105_3230.FStar_Syntax_Syntax.sigmeta)
=======
                 (uu___107_3065.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___107_3065.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___107_3065.FStar_Syntax_Syntax.sigmeta)
>>>>>>> origin/guido_tactics
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
<<<<<<< HEAD
           let uu____3236 =
             let uu____3241 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3241 in
           (match uu____3236 with
            | (a,wp_a_src) ->
                let uu____3252 =
                  let uu____3257 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3257 in
                (match uu____3252 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3269 =
                         let uu____3271 =
                           let uu____3272 =
                             let uu____3277 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3277) in
                           FStar_Syntax_Syntax.NT uu____3272 in
                         [uu____3271] in
                       FStar_Syntax_Subst.subst uu____3269 wp_b_tgt in
                     let expected_k =
                       let uu____3281 =
                         let uu____3285 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3286 =
                           let uu____3288 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3288] in
                         uu____3285 :: uu____3286 in
                       let uu____3289 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3281 uu____3289 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3310 =
                           let uu____3311 =
                             let uu____3314 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3315 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3314, uu____3315) in
                           FStar_Errors.Error uu____3311 in
                         raise uu____3310 in
                       let uu____3318 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3318 with
=======
           let uu____3071 =
             let uu____3076 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3076 in
           (match uu____3071 with
            | (a,wp_a_src) ->
                let uu____3087 =
                  let uu____3092 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____3092 in
                (match uu____3087 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____3104 =
                         let uu____3106 =
                           let uu____3107 =
                             let uu____3112 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____3112) in
                           FStar_Syntax_Syntax.NT uu____3107 in
                         [uu____3106] in
                       FStar_Syntax_Subst.subst uu____3104 wp_b_tgt in
                     let expected_k =
                       let uu____3116 =
                         let uu____3120 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____3121 =
                           let uu____3123 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____3123] in
                         uu____3120 :: uu____3121 in
                       let uu____3124 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____3116 uu____3124 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____3145 =
                           let uu____3146 =
                             let uu____3149 =
                               FStar_Util.format1
                                 "Effect %s cannot be reified"
                                 l.FStar_Ident.str in
                             let uu____3150 =
                               FStar_TypeChecker_Env.get_range env1 in
                             (uu____3149, uu____3150) in
                           FStar_Errors.Error uu____3146 in
                         raise uu____3145 in
                       let uu____3153 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____3153 with
>>>>>>> origin/guido_tactics
                       | None  -> no_reify eff_name
                       | Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
<<<<<<< HEAD
                           let uu____3337 =
                             let uu____3338 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3338 in
                           if uu____3337
                           then no_reify eff_name
                           else
                             (let uu____3343 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3344 =
                                let uu____3347 =
                                  let uu____3348 =
                                    let uu____3358 =
                                      let uu____3360 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3361 =
                                        let uu____3363 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3363] in
                                      uu____3360 :: uu____3361 in
                                    (repr, uu____3358) in
                                  FStar_Syntax_Syntax.Tm_app uu____3348 in
                                FStar_Syntax_Syntax.mk uu____3347 in
                              uu____3344 None uu____3343) in
                     let uu____3373 =
=======
                           let uu____3172 =
                             let uu____3173 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____3173 in
                           if uu____3172
                           then no_reify eff_name
                           else
                             (let uu____3178 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____3179 =
                                let uu____3182 =
                                  let uu____3183 =
                                    let uu____3193 =
                                      let uu____3195 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____3196 =
                                        let uu____3198 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____3198] in
                                      uu____3195 :: uu____3196 in
                                    (repr, uu____3193) in
                                  FStar_Syntax_Syntax.Tm_app uu____3183 in
                                FStar_Syntax_Syntax.mk uu____3182 in
                              uu____3179 None uu____3178) in
                     let uu____3208 =
>>>>>>> origin/guido_tactics
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
<<<<<<< HEAD
                       | (lift,Some (uu____3388,lift_wp)) ->
                           let uu____3401 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3401)
                       | (Some (what,lift),None ) ->
                           ((let uu____3416 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3416
                             then
                               let uu____3417 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3417
=======
                       | (lift,Some (uu____3223,lift_wp)) ->
                           let uu____3236 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____3236)
                       | (Some (what,lift),None ) ->
                           ((let uu____3251 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____3251
                             then
                               let uu____3252 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____3252
>>>>>>> origin/guido_tactics
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant
                                    FStar_Range.dummyRange) in
<<<<<<< HEAD
                             let uu____3420 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3420 with
                             | (lift1,comp,uu____3429) ->
                                 let uu____3430 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3430 with
                                  | (uu____3437,lift_wp,lift_elab) ->
                                      let uu____3440 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3441 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3373 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___106_3464 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___106_3464.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___106_3464.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___106_3464.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___106_3464.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___106_3464.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___106_3464.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___106_3464.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___106_3464.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___106_3464.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___106_3464.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___106_3464.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___106_3464.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___106_3464.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___106_3464.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___106_3464.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___106_3464.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___106_3464.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___106_3464.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___106_3464.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___106_3464.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___106_3464.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___106_3464.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___106_3464.FStar_TypeChecker_Env.qname_and_index)
=======
                             let uu____3255 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____3255 with
                             | (lift1,comp,uu____3264) ->
                                 let uu____3265 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____3265 with
                                  | (uu____3272,lift_wp,lift_elab) ->
                                      let uu____3275 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____3276 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((Some ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____3208 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___108_3299 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___108_3299.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___108_3299.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___108_3299.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___108_3299.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___108_3299.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___108_3299.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___108_3299.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___108_3299.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___108_3299.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___108_3299.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___108_3299.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___108_3299.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___108_3299.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___108_3299.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___108_3299.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___108_3299.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___108_3299.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___108_3299.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___108_3299.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___108_3299.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___108_3299.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___108_3299.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___108_3299.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___108_3299.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___108_3299.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___108_3299.FStar_TypeChecker_Env.is_native_tactic)
>>>>>>> origin/guido_tactics
                            } in
                          let lift1 =
                            match lift with
                            | None  -> None
<<<<<<< HEAD
                            | Some (uu____3468,lift1) ->
                                let uu____3475 =
                                  let uu____3480 =
=======
                            | Some (uu____3303,lift1) ->
                                let uu____3310 =
                                  let uu____3315 =
>>>>>>> origin/guido_tactics
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
<<<<<<< HEAD
                                    uu____3480 in
                                (match uu____3475 with
=======
                                    uu____3315 in
                                (match uu____3310 with
>>>>>>> origin/guido_tactics
                                 | (a1,wp_a_src1) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv None
                                         wp_a_src1 in
                                     let a_typ =
                                       FStar_Syntax_Syntax.bv_to_name a1 in
                                     let wp_a_typ =
                                       FStar_Syntax_Syntax.bv_to_name wp_a in
                                     let repr_f =
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.source
                                         a_typ wp_a_typ in
                                     let repr_result =
                                       let lift_wp1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.EraseUniverses;
                                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                           env2 (snd lift_wp) in
                                       let lift_wp_a =
<<<<<<< HEAD
                                         let uu____3502 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3503 =
                                           let uu____3506 =
                                             let uu____3507 =
                                               let uu____3517 =
                                                 let uu____3519 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3520 =
                                                   let uu____3522 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3522] in
                                                 uu____3519 :: uu____3520 in
                                               (lift_wp1, uu____3517) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3507 in
                                           FStar_Syntax_Syntax.mk uu____3506 in
                                         uu____3503 None uu____3502 in
=======
                                         let uu____3337 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____3338 =
                                           let uu____3341 =
                                             let uu____3342 =
                                               let uu____3352 =
                                                 let uu____3354 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____3355 =
                                                   let uu____3357 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____3357] in
                                                 uu____3354 :: uu____3355 in
                                               (lift_wp1, uu____3352) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____3342 in
                                           FStar_Syntax_Syntax.mk uu____3341 in
                                         uu____3338 None uu____3337 in
>>>>>>> origin/guido_tactics
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
<<<<<<< HEAD
                                       let uu____3535 =
                                         let uu____3539 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3540 =
                                           let uu____3542 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3543 =
                                             let uu____3545 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3545] in
                                           uu____3542 :: uu____3543 in
                                         uu____3539 :: uu____3540 in
                                       let uu____3546 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3535
                                         uu____3546 in
                                     let uu____3549 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3549 with
                                      | (expected_k2,uu____3555,uu____3556)
=======
                                       let uu____3370 =
                                         let uu____3374 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____3375 =
                                           let uu____3377 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____3378 =
                                             let uu____3380 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____3380] in
                                           uu____3377 :: uu____3378 in
                                         uu____3374 :: uu____3375 in
                                       let uu____3381 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____3370
                                         uu____3381 in
                                     let uu____3384 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____3384 with
                                      | (expected_k2,uu____3390,uu____3391)
>>>>>>> origin/guido_tactics
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          Some lift2)) in
                          let sub2 =
<<<<<<< HEAD
                            let uu___107_3559 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___107_3559.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___107_3559.FStar_Syntax_Syntax.target);
=======
                            let uu___109_3394 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___109_3394.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___109_3394.FStar_Syntax_Syntax.target);
>>>>>>> origin/guido_tactics
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
<<<<<<< HEAD
                            let uu___108_3561 = se in
=======
                            let uu___110_3396 = se in
>>>>>>> origin/guido_tactics
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                                (uu___108_3561.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___108_3561.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___108_3561.FStar_Syntax_Syntax.sigmeta)
=======
                                (uu___110_3396.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___110_3396.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___110_3396.FStar_Syntax_Syntax.sigmeta)
>>>>>>> origin/guido_tactics
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
<<<<<<< HEAD
           let uu____3575 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3575 with
            | (tps1,c1) ->
                let uu____3584 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3584 with
                 | (tps2,env3,us) ->
                     let uu____3595 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3595 with
=======
           let uu____3409 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____3409 with
            | (tps1,c1) ->
                let uu____3418 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____3418 with
                 | (tps2,env3,us) ->
                     let uu____3429 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____3429 with
>>>>>>> origin/guido_tactics
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
<<<<<<< HEAD
                            let uu____3609 =
                              let uu____3610 =
=======
                            let uu____3443 =
                              let uu____3444 =
>>>>>>> origin/guido_tactics
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
<<<<<<< HEAD
                                env0 uu____3610 in
                            match uu____3609 with
                            | (uvs1,t) ->
                                let uu____3623 =
                                  let uu____3631 =
                                    let uu____3634 =
                                      let uu____3635 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3635.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3634) in
                                  match uu____3631 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3645,c4)) -> ([], c4)
                                  | (uu____3669,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3687 -> failwith "Impossible" in
                                (match uu____3623 with
=======
                                env0 uu____3444 in
                            match uu____3443 with
                            | (uvs1,t) ->
                                let uu____3457 =
                                  let uu____3465 =
                                    let uu____3468 =
                                      let uu____3469 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____3469.FStar_Syntax_Syntax.n in
                                    (tps3, uu____3468) in
                                  match uu____3465 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3479,c4)) -> ([], c4)
                                  | (uu____3503,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3521 -> failwith "Impossible" in
                                (match uu____3457 with
>>>>>>> origin/guido_tactics
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
<<<<<<< HEAD
                                        (let uu____3716 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3716 with
                                         | (uu____3719,t1) ->
                                             let uu____3721 =
                                               let uu____3722 =
                                                 let uu____3725 =
                                                   let uu____3726 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3727 =
=======
                                        (let uu____3552 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____3552 with
                                         | (uu____3555,t1) ->
                                             let uu____3557 =
                                               let uu____3558 =
                                                 let uu____3561 =
                                                   let uu____3562 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid in
                                                   let uu____3563 =
>>>>>>> origin/guido_tactics
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int in
<<<<<<< HEAD
                                                   let uu____3730 =
=======
                                                   let uu____3568 =
>>>>>>> origin/guido_tactics
                                                     FStar_Syntax_Print.term_to_string
                                                       t1 in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
<<<<<<< HEAD
                                                     uu____3726 uu____3727
                                                     uu____3730 in
                                                 (uu____3725, r) in
                                               FStar_Errors.Error uu____3722 in
                                             raise uu____3721)
                                      else ();
                                      (let se1 =
                                         let uu___109_3733 = se in
=======
                                                     uu____3562 uu____3563
                                                     uu____3568 in
                                                 (uu____3561, r) in
                                               FStar_Errors.Error uu____3558 in
                                             raise uu____3557)
                                      else ();
                                      (let se1 =
                                         let uu___111_3571 = se in
>>>>>>> origin/guido_tactics
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags));
                                           FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                                             (uu___109_3733.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___109_3733.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___109_3733.FStar_Syntax_Syntax.sigmeta)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3743,uu____3744,uu____3745) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___83_3748  ->
                   match uu___83_3748 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3749 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____3752,uu____3753,uu____3754) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___83_3761  ->
                   match uu___83_3761 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3762 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3769 =
             if uvs = []
             then
               let uu____3770 =
                 let uu____3771 = FStar_Syntax_Util.type_u () in
                 fst uu____3771 in
               check_and_gen env2 t uu____3770
             else
               (let uu____3775 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3775 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3781 =
                        let uu____3782 = FStar_Syntax_Util.type_u () in
                        fst uu____3782 in
                      tc_check_trivial_guard env2 t1 uu____3781 in
=======
                                             (uu___111_3571.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___111_3571.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___111_3571.FStar_Syntax_Syntax.sigmeta)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3581,uu____3582,uu____3583) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___85_3585  ->
                   match uu___85_3585 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3586 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____3589,uu____3590,uu____3591) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___85_3597  ->
                   match uu___85_3597 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3598 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____3605 =
             if uvs = []
             then
               let uu____3606 =
                 let uu____3607 = FStar_Syntax_Util.type_u () in
                 fst uu____3607 in
               check_and_gen env2 t uu____3606
             else
               (let uu____3611 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____3611 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3617 =
                        let uu____3618 = FStar_Syntax_Util.type_u () in
                        fst uu____3618 in
                      tc_check_trivial_guard env2 t1 uu____3617 in
>>>>>>> origin/guido_tactics
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2 in
<<<<<<< HEAD
                    let uu____3786 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3786)) in
           (match uu____3769 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___110_3796 = se in
=======
                    let uu____3622 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                    (uvs1, uu____3622)) in
           (match uu____3605 with
            | (uvs1,t1) ->
                let se1 =
                  let uu___112_3632 = se in
>>>>>>> origin/guido_tactics
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                      (uu___110_3796.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___110_3796.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___110_3796.FStar_Syntax_Syntax.sigmeta)
=======
                      (uu___112_3632.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___112_3632.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___112_3632.FStar_Syntax_Syntax.sigmeta)
>>>>>>> origin/guido_tactics
                  } in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____3803 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____3803 with
            | (uu____3810,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_TypeChecker_Common.t_unit in
<<<<<<< HEAD
           let uu____3818 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3818 with
            | (e1,c,g1) ->
                let uu____3829 =
                  let uu____3833 =
                    let uu____3835 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3835 in
                  let uu____3836 =
                    let uu____3839 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3839) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3833 uu____3836 in
                (match uu____3829 with
                 | (e2,uu____3849,g) ->
                     ((let uu____3852 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3852);
                      (let se1 =
                         let uu___111_3854 = se in
=======
           let uu____3644 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____3644 with
            | (e1,c,g1) ->
                let uu____3655 =
                  let uu____3659 =
                    let uu____3661 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r in
                    Some uu____3661 in
                  let uu____3662 =
                    let uu____3665 = c.FStar_Syntax_Syntax.comp () in
                    (e1, uu____3665) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3659 uu____3662 in
                (match uu____3655 with
                 | (e2,uu____3675,g) ->
                     ((let uu____3678 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3678);
                      (let se1 =
                         let uu___113_3680 = se in
>>>>>>> origin/guido_tactics
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                             (uu___111_3854.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___111_3854.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___111_3854.FStar_Syntax_Syntax.sigmeta)
=======
                             (uu___113_3680.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___113_3680.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___113_3680.FStar_Syntax_Syntax.sigmeta)
>>>>>>> origin/guido_tactics
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids,attrs) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
<<<<<<< HEAD
                 let uu____3890 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3890
                 then Some q
                 else
                   (let uu____3899 =
                      let uu____3900 =
                        let uu____3903 =
                          let uu____3904 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3905 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3906 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3904 uu____3905 uu____3906 in
                        (uu____3903, r) in
                      FStar_Errors.Error uu____3900 in
                    raise uu____3899) in
           let uu____3909 =
             FStar_All.pipe_right (snd lbs)
               (FStar_List.fold_left
                  (fun uu____3940  ->
                     fun lb  ->
                       match uu____3940 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3964 =
                             let uu____3970 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3970 with
=======
                 let uu____3716 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____3716
                 then Some q
                 else
                   (let uu____3729 =
                      let uu____3730 =
                        let uu____3733 =
                          let uu____3734 = FStar_Syntax_Print.lid_to_string l in
                          let uu____3735 =
                            FStar_Syntax_Print.quals_to_string q in
                          let uu____3736 =
                            FStar_Syntax_Print.quals_to_string q' in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3734 uu____3735 uu____3736 in
                        (uu____3733, r) in
                      FStar_Errors.Error uu____3730 in
                    raise uu____3729) in
           let uu____3739 =
             FStar_All.pipe_right (snd lbs)
               (FStar_List.fold_left
                  (fun uu____3760  ->
                     fun lb  ->
                       match uu____3760 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____3784 =
                             let uu____3790 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____3790 with
>>>>>>> origin/guido_tactics
                             | None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | Some ((uvs,tval),quals) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals in
                                 ((match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  -> ()
<<<<<<< HEAD
                                   | uu____4014 ->
=======
                                   | uu____3842 ->
>>>>>>> origin/guido_tactics
                                       FStar_Errors.warn r
                                         "Annotation from val declaration overrides inline type annotation");
                                  if
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    raise
                                      (FStar_Errors.Error
                                         ("Inline universes are incoherent with annotation from val declaration",
                                           r))
                                  else ();
<<<<<<< HEAD
                                  (let uu____4022 =
=======
                                  (let uu____3854 =
>>>>>>> origin/guido_tactics
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
<<<<<<< HEAD
                                   (false, uu____4022, quals_opt1))) in
                           (match uu____3964 with
=======
                                   (false, uu____3854, quals_opt1))) in
                           (match uu____3784 with
>>>>>>> origin/guido_tactics
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then None
                     else Some (se.FStar_Syntax_Syntax.sigquals)))) in
<<<<<<< HEAD
           (match uu____3909 with
=======
           (match uu____3739 with
>>>>>>> origin/guido_tactics
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
<<<<<<< HEAD
                      let uu____4075 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___84_4078  ->
                                match uu___84_4078 with
=======
                      let uu____3907 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___86_3909  ->
                                match uu___86_3909 with
>>>>>>> origin/guido_tactics
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
<<<<<<< HEAD
                                | uu____4079 -> false)) in
                      if uu____4075
=======
                                | uu____3910 -> false)) in
                      if uu____3907
>>>>>>> origin/guido_tactics
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
<<<<<<< HEAD
                  let uu____4087 =
                    let uu____4090 =
                      let uu____4091 =
                        let uu____4099 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((fst lbs), lbs'1), uu____4099) in
                      FStar_Syntax_Syntax.Tm_let uu____4091 in
                    FStar_Syntax_Syntax.mk uu____4090 in
                  uu____4087 None r in
                let uu____4121 =
                  let uu____4127 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___112_4133 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___112_4133.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___112_4133.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___112_4133.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___112_4133.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___112_4133.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___112_4133.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___112_4133.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___112_4133.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___112_4133.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___112_4133.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___112_4133.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___112_4133.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___112_4133.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___112_4133.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___112_4133.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___112_4133.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___112_4133.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___112_4133.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___112_4133.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___112_4133.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___112_4133.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___112_4133.FStar_TypeChecker_Env.qname_and_index)
                       }) e in
                  match uu____4127 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____4141;
                       FStar_Syntax_Syntax.pos = uu____4142;
                       FStar_Syntax_Syntax.vars = uu____4143;_},uu____4144,g)
=======
                  let uu____3918 =
                    let uu____3921 =
                      let uu____3922 =
                        let uu____3930 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r in
                        (((fst lbs), lbs'1), uu____3930) in
                      FStar_Syntax_Syntax.Tm_let uu____3922 in
                    FStar_Syntax_Syntax.mk uu____3921 in
                  uu____3918 None r in
                let uu____3952 =
                  let uu____3958 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___114_3962 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___114_3962.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___114_3962.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___114_3962.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___114_3962.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___114_3962.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___114_3962.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___114_3962.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___114_3962.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___114_3962.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___114_3962.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___114_3962.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___114_3962.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___114_3962.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___114_3962.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___114_3962.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___114_3962.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___114_3962.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___114_3962.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___114_3962.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___114_3962.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___114_3962.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___114_3962.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___114_3962.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___114_3962.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___114_3962.FStar_TypeChecker_Env.is_native_tactic)
                       }) e in
                  match uu____3958 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____3970;
                       FStar_Syntax_Syntax.pos = uu____3971;
                       FStar_Syntax_Syntax.vars = uu____3972;_},uu____3973,g)
>>>>>>> origin/guido_tactics
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
<<<<<<< HEAD
                            (uu____4163,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____4168 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___85_4173  ->
                             match uu___85_4173 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____4175 =
                                   let uu____4176 =
=======
                            (uu____3992,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____3997 -> quals in
                      let quals2 =
                        FStar_List.choose
                          (fun uu___87_4000  ->
                             match uu___87_4000 with
                             | FStar_Syntax_Syntax.Inline_for_extraction  ->
                                 let uu____4002 =
                                   let uu____4003 =
>>>>>>> origin/guido_tactics
                                     FStar_List.for_all
                                       (fun lb  ->
                                          let ok =
                                            FStar_Syntax_Util.is_pure_or_ghost_function
                                              lb.FStar_Syntax_Syntax.lbtyp in
                                          if Prims.op_Negation ok
                                          then
<<<<<<< HEAD
                                            (let uu____4183 =
=======
                                            (let uu____4007 =
>>>>>>> origin/guido_tactics
                                               FStar_Syntax_Print.lbname_to_string
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             FStar_Util.print1_warning
                                               "Dropping inline_for_extraction from %s because it is not a pure function\n"
<<<<<<< HEAD
                                               uu____4183)
                                          else ();
                                          ok) (snd lbs1) in
                                   Prims.op_Negation uu____4176 in
                                 if uu____4175
=======
                                               uu____4007)
                                          else ();
                                          ok) (snd lbs1) in
                                   Prims.op_Negation uu____4003 in
                                 if uu____4002
>>>>>>> origin/guido_tactics
                                 then None
                                 else
                                   Some
                                     FStar_Syntax_Syntax.Inline_for_extraction
                             | q -> Some q) quals1 in
<<<<<<< HEAD
                      ((let uu___113_4193 = se in
=======
                      ((let uu___115_4016 = se in
>>>>>>> origin/guido_tactics
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs1, lids, attrs));
                          FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                            (uu___113_4193.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___113_4193.FStar_Syntax_Syntax.sigmeta)
                        }), lbs1)
                  | uu____4199 -> failwith "impossible" in
                (match uu____4121 with
=======
                            (uu___115_4016.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals2;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___115_4016.FStar_Syntax_Syntax.sigmeta)
                        }), lbs1)
                  | uu____4022 -> failwith "impossible" in
                (match uu____3952 with
>>>>>>> origin/guido_tactics
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Common.insert_fv fv
                                lb.FStar_Syntax_Syntax.lbtyp));
<<<<<<< HEAD
                      (let uu____4228 = log env2 in
                       if uu____4228
                       then
                         let uu____4229 =
                           let uu____4230 =
=======
                      (let uu____4049 = log env2 in
                       if uu____4049
                       then
                         let uu____4050 =
                           let uu____4051 =
>>>>>>> origin/guido_tactics
                             FStar_All.pipe_right (snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
<<<<<<< HEAD
                                       let uu____4241 =
                                         let uu____4246 =
                                           let uu____4247 =
                                             let uu____4249 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4249.FStar_Syntax_Syntax.fv_name in
                                           uu____4247.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4246 in
                                       match uu____4241 with
                                       | None  -> true
                                       | uu____4253 -> false in
                                     if should_log
                                     then
                                       let uu____4258 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4259 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4258 uu____4259
                                     else "")) in
                           FStar_All.pipe_right uu____4230
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____4229
=======
                                       let uu____4058 =
                                         let uu____4063 =
                                           let uu____4064 =
                                             let uu____4069 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____4069.FStar_Syntax_Syntax.fv_name in
                                           uu____4064.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4063 in
                                       match uu____4058 with
                                       | None  -> true
                                       | uu____4076 -> false in
                                     if should_log
                                     then
                                       let uu____4081 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____4082 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4081 uu____4082
                                     else "")) in
                           FStar_All.pipe_right uu____4051
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____4050
>>>>>>> origin/guido_tactics
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____4106 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____4106 with
                              | (bs1,c1) ->
                                  let uu____4111 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____4111
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____4121 =
                                            let uu____4122 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____4122.FStar_Syntax_Syntax.n in
                                          (match uu____4121 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____4141 =
                                                 let uu____4142 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____4142.FStar_Syntax_Syntax.n in
                                               (match uu____4141 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____4152 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Syntax_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____4152 in
                                                    let uu____4153 =
                                                      let uu____4154 =
                                                        let uu____4155 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____4155 args in
                                                      uu____4154 None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____4153 u
                                                | uu____4160 -> c1)
                                           | uu____4161 -> c1)
                                      | uu____4162 -> c1 in
                                    let uu___116_4163 = t1 in
                                    let uu____4164 =
                                      let uu____4165 =
                                        let uu____4173 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____4173) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____4165 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____4164;
                                      FStar_Syntax_Syntax.tk =
                                        (uu___116_4163.FStar_Syntax_Syntax.tk);
                                      FStar_Syntax_Syntax.pos =
                                        (uu___116_4163.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___116_4163.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____4195 =
                               let uu____4196 = FStar_Syntax_Subst.compress h in
                               uu____4196.FStar_Syntax_Syntax.n in
                             (match uu____4195 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____4206 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Syntax_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____4206 in
                                  let uu____4207 =
                                    let uu____4208 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____4208
                                      args in
                                  uu____4207 None t1.FStar_Syntax_Syntax.pos
                              | uu____4213 -> t1)
                         | uu____4214 -> t1 in
                       let reified_tactic_decl assm_lid lb =
                         let t =
                           reified_tactic_type assm_lid
                             lb.FStar_Syntax_Syntax.lbtyp in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (assm_lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                  t));
                           FStar_Syntax_Syntax.sigrng =
                             (FStar_Ident.range_of_lid assm_lid);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta
                         } in
                       let reflected_tactic_decl b lb bs assm_lid comp =
                         let reified_tac =
                           let uu____4241 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____4241 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____4250 =
                                  FStar_Syntax_Syntax.bv_to_name (fst x) in
                                (uu____4250, (snd x))) bs in
                         let reflect_head =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_constant
                                (FStar_Const.Const_reflect
                                   FStar_Syntax_Const.tac_effect_lid)) None
                             FStar_Range.dummyRange in
                         let refl_arg =
                           FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args
                             None FStar_Range.dummyRange in
                         let app =
                           FStar_Syntax_Syntax.mk_Tm_app reflect_head
                             [(refl_arg, None)] None FStar_Range.dummyRange in
                         let unit_binder =
                           let uu____4282 =
                             FStar_Syntax_Syntax.new_bv None
                               FStar_TypeChecker_Common.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____4282 in
                         let body =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs [unit_binder] app)
                             (Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp)) in
                         let func =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs bs body)
                             (Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp)) in
                         let uu___117_4287 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___118_4294 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___118_4294.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___118_4294.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___118_4294.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___118_4294.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func
                                     })]), lids, attrs));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___117_4287.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___117_4287.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___117_4287.FStar_Syntax_Syntax.sigmeta)
                         } in
                       let tactic_decls =
                         match snd lbs1 with
                         | hd1::[] ->
                             let uu____4304 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____4304 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____4324 =
                                    let uu____4325 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____4325.FStar_Syntax_Syntax.n in
                                  (match uu____4324 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____4349 =
                                           let uu____4354 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____4354.FStar_Syntax_Syntax.fv_name in
                                         uu____4349.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____4359 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____4359 in
                                       let uu____4360 =
                                         (is_native_tactic env2 assm_lid h1)
                                           &&
                                           (let uu____4361 =
                                              let uu____4362 =
                                                FStar_TypeChecker_Env.try_lookup_val_decl
                                                  env2 tac_lid in
                                              FStar_All.pipe_left
                                                FStar_Util.is_some uu____4362 in
                                            Prims.op_Negation uu____4361) in
                                       if uu____4360
                                       then
                                         let se_assm =
                                           reified_tactic_decl assm_lid hd1 in
                                         let se_refl =
                                           reflected_tactic_decl (fst lbs1)
                                             hd1 bs assm_lid comp in
                                         Some (se_assm, se_refl)
                                       else None
                                   | uu____4385 -> None))
                         | uu____4388 -> None in
                       match tactic_decls with
                       | Some (se_assm,se_refl) ->
                           ((let uu____4401 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____4401
                             then
                               let uu____4402 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____4403 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____4402 uu____4403
                             else ());
                            ([se_assm; se_refl], []))
                       | None  -> ([se1], []))))))
let for_export:
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Ident.lident Prims.list)
  =
  fun hidden  ->
    fun se  ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
<<<<<<< HEAD
             (fun uu___86_4289  ->
                match uu___86_4289 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4290 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____4296) ->
=======
             (fun uu___88_4436  ->
                match uu___88_4436 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4437 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____4443) ->
>>>>>>> origin/guido_tactics
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
<<<<<<< HEAD
        | uu____4300 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4305 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4308 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____4321 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4334) ->
          let uu____4339 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4339
          then
            let for_export_bundle se1 uu____4358 =
              match uu____4358 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4381,uu____4382) ->
                       let dec =
                         let uu___114_4388 = se1 in
                         let uu____4389 =
                           let uu____4390 =
                             let uu____4394 =
                               let uu____4397 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4397 in
                             (l, us, uu____4394) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4390 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4389;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___114_4388.FStar_Syntax_Syntax.sigrng);
=======
        | uu____4447 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____4452 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4455 ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_datacon uu____4468 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4481) ->
          let uu____4486 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4486
          then
            let for_export_bundle se1 uu____4505 =
              match uu____4505 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4528,uu____4529) ->
                       let dec =
                         let uu___119_4535 = se1 in
                         let uu____4536 =
                           let uu____4537 =
                             let uu____4541 =
                               let uu____4544 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____4544 in
                             (l, us, uu____4541) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____4537 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____4536;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___119_4535.FStar_Syntax_Syntax.sigrng);
>>>>>>> origin/guido_tactics
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
<<<<<<< HEAD
                             (uu___114_4388.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4407,uu____4408,uu____4409) ->
                       let dec =
                         let uu___115_4413 = se1 in
=======
                             (uu___119_4535.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4554,uu____4555,uu____4556) ->
                       let dec =
                         let uu___120_4560 = se1 in
>>>>>>> origin/guido_tactics
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                             (uu___115_4413.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___115_4413.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4416 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4428,uu____4429,uu____4430) ->
          let uu____4431 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4431 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4444 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4444
          then
            ([(let uu___116_4453 = se in
=======
                             (uu___120_4560.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___120_4560.FStar_Syntax_Syntax.sigmeta)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____4563 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____4575,uu____4576) ->
          let uu____4577 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4577 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____4590 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____4590
          then
            ([(let uu___121_4598 = se in
>>>>>>> origin/guido_tactics
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                   (uu___116_4453.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___116_4453.FStar_Syntax_Syntax.sigmeta)
               })], (l :: hidden))
          else
            (let uu____4455 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___87_4458  ->
                       match uu___87_4458 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____4459 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____4462 -> true
                       | uu____4463 -> false)) in
             if uu____4455 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4473 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____4476 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4479 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4482 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4485 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4495,uu____4496)
=======
                   (uu___121_4598.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___121_4598.FStar_Syntax_Syntax.sigmeta)
               })], (l :: hidden))
          else
            (let uu____4600 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___89_4602  ->
                       match uu___89_4602 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____4603 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____4606 -> true
                       | uu____4607 -> false)) in
             if uu____4600 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4617 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____4620 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4623 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____4626 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4629 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____4639,uu____4640)
>>>>>>> origin/guido_tactics
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
<<<<<<< HEAD
          let uu____4508 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4508
=======
          let uu____4656 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____4656
>>>>>>> origin/guido_tactics
          then ([], hidden)
          else
            (let dec =
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp)));
                 FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid lid);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta
               } in
             ([dec], (lid :: hidden)))
<<<<<<< HEAD
      | FStar_Syntax_Syntax.Sig_let (lbs,l,uu____4525) ->
          let uu____4530 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4530
          then
            let uu____4535 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___117_4544 = se in
                      let uu____4545 =
                        let uu____4546 =
                          let uu____4550 =
                            let uu____4551 =
                              let uu____4553 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4553.FStar_Syntax_Syntax.fv_name in
                            uu____4551.FStar_Syntax_Syntax.v in
                          (uu____4550, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4546 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4545;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___117_4544.FStar_Syntax_Syntax.sigrng);
=======
      | FStar_Syntax_Syntax.Sig_let (lbs,l,uu____4677) ->
          let uu____4682 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____4682
          then
            let uu____4687 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___122_4693 = se in
                      let uu____4694 =
                        let uu____4695 =
                          let uu____4699 =
                            let uu____4700 =
                              let uu____4705 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____4705.FStar_Syntax_Syntax.fv_name in
                            uu____4700.FStar_Syntax_Syntax.v in
                          (uu____4699, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____4695 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____4694;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___122_4693.FStar_Syntax_Syntax.sigrng);
>>>>>>> origin/guido_tactics
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
<<<<<<< HEAD
                          (uu___117_4544.FStar_Syntax_Syntax.sigmeta)
                      })) in
            (uu____4535, hidden)
=======
                          (uu___122_4693.FStar_Syntax_Syntax.sigmeta)
                      })) in
            (uu____4687, hidden)
>>>>>>> origin/guido_tactics
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
<<<<<<< HEAD
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4568 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4577 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4586 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                env)
           | uu____4589 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4590 -> env
=======
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____4725 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____4734 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (match p with
           | FStar_Syntax_Syntax.ResetOptions uu____4743 ->
               ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ();
                (let uu____4746 = FStar_Options.using_facts_from () in
                 match uu____4746 with
                 | Some ns ->
                     let proof_ns =
                       let uu____4758 =
                         let uu____4763 =
                           FStar_List.map
                             (fun s  -> ((FStar_Ident.path_of_text s), true))
                             ns in
                         FStar_List.append uu____4763 [([], false)] in
                       [uu____4758] in
                     let uu___123_4791 = env in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___123_4791.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___123_4791.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___123_4791.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___123_4791.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___123_4791.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___123_4791.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___123_4791.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___123_4791.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___123_4791.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___123_4791.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___123_4791.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___123_4791.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___123_4791.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___123_4791.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___123_4791.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___123_4791.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___123_4791.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___123_4791.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___123_4791.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___123_4791.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___123_4791.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___123_4791.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___123_4791.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___123_4791.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns = proof_ns;
                       FStar_TypeChecker_Env.synth =
                         (uu___123_4791.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___123_4791.FStar_TypeChecker_Env.is_native_tactic)
                     }
                 | None  -> env))
           | uu____4793 -> env)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____4794 -> env
>>>>>>> origin/guido_tactics
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
<<<<<<< HEAD
                    let uu____4599 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4599) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____4600,uu____4601,uu____4602) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___88_4605  ->
                  match uu___88_4605 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4606 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____4607,uu____4608,uu____4609) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___88_4616  ->
                  match uu___88_4616 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4617 -> false))
          -> env
      | uu____4618 -> FStar_TypeChecker_Env.push_sigelt env se
=======
                    let uu____4800 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____4800) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____4801,uu____4802,uu____4803) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___90_4805  ->
                  match uu___90_4805 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4806 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____4807,uu____4808,uu____4809) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___90_4815  ->
                  match uu___90_4815 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____4816 -> false))
          -> env
      | uu____4817 -> FStar_TypeChecker_Env.push_sigelt env se
>>>>>>> origin/guido_tactics
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
<<<<<<< HEAD
      let rec process_one_decl uu____4654 se =
        match uu____4654 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4684 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____4684
              then
                let uu____4685 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4685
              else ());
             (let uu____4687 = tc_decl env1 se in
              match uu____4687 with
=======
      let rec process_one_decl uu____4855 se =
        match uu____4855 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4885 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____4885
              then
                let uu____4886 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4886
              else ());
             (let uu____4888 = tc_decl env1 se in
              match uu____4888 with
>>>>>>> origin/guido_tactics
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____4716 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____4716
                             then
                               let uu____4717 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____4717
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  let env2 =
                    FStar_All.pipe_right ses'1
                      (FStar_List.fold_left
                         (fun env2  -> fun se1  -> add_sigelt_to_env env2 se1)
                         env1) in
<<<<<<< HEAD
                  (FStar_Syntax_Unionfind.reset ();
                   (let uu____4733 =
=======
                  ((let uu____4914 =
>>>>>>> origin/guido_tactics
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes")) in
<<<<<<< HEAD
                    if uu____4733
                    then
                      let uu____4734 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4740 =
                                 let uu____4741 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____4741 "\n" in
                               Prims.strcat s uu____4740) "" ses'1 in
                      FStar_Util.print1 "Checked: %s\n" uu____4734
=======
                    if uu____4914
                    then
                      let uu____4915 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4918 =
                                 let uu____4919 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 Prims.strcat uu____4919 "\n" in
                               Prims.strcat s uu____4918) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" uu____4915
>>>>>>> origin/guido_tactics
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
<<<<<<< HEAD
                          env2 se1) ses'1;
                   (let uu____4746 =
                      let accum_exports_hidden uu____4764 se1 =
                        match uu____4764 with
                        | (exports1,hidden1) ->
                            let uu____4780 = for_export hidden1 se1 in
                            (match uu____4780 with
=======
                          env2 se1) ses';
                   (let uu____4923 =
                      let accum_exports_hidden uu____4941 se1 =
                        match uu____4941 with
                        | (exports1,hidden1) ->
                            let uu____4957 = for_export hidden1 se1 in
                            (match uu____4957 with
>>>>>>> origin/guido_tactics
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2)) in
                      FStar_List.fold_left accum_exports_hidden
<<<<<<< HEAD
                        (exports, hidden) ses'1 in
                    match uu____4746 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses'1 ses1), exports1, env2,
                           hidden1), ses_elaborated1))))) in
      let uu____4830 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____4830 with
      | (ses1,exports,env1,uu____4856) ->
=======
                        (exports, hidden) ses' in
                    match uu____4923 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated))))) in
      let uu____5007 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____5007 with
      | (ses1,exports,env1,uu____5033) ->
>>>>>>> origin/guido_tactics
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
let tc_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_Syntax_Syntax.sigelt Prims.list*
        FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let verify =
        FStar_Options.should_verify
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      let action = if verify then "Verifying" else "Lax-checking" in
      let label1 =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
<<<<<<< HEAD
      (let uu____4881 = FStar_Options.debug_any () in
       if uu____4881
=======
      (let uu____5060 = FStar_Options.debug_any () in
       if uu____5060
>>>>>>> origin/guido_tactics
       then
         FStar_Util.print3 "%s %s of %s\n" action label1
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       else ());
      (let name =
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
       let msg = Prims.strcat "Internals for " name in
       let env1 =
<<<<<<< HEAD
         let uu___118_4887 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___118_4887.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___118_4887.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___118_4887.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___118_4887.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___118_4887.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___118_4887.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___118_4887.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___118_4887.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___118_4887.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___118_4887.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___118_4887.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___118_4887.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___118_4887.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___118_4887.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___118_4887.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___118_4887.FStar_TypeChecker_Env.use_eq);
=======
         let uu___124_5066 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___124_5066.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___124_5066.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___124_5066.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___124_5066.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___124_5066.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___124_5066.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___124_5066.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___124_5066.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___124_5066.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___124_5066.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___124_5066.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___124_5066.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___124_5066.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___124_5066.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___124_5066.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___124_5066.FStar_TypeChecker_Env.use_eq);
>>>>>>> origin/guido_tactics
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
<<<<<<< HEAD
             (uu___118_4887.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___118_4887.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___118_4887.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___118_4887.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___118_4887.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___118_4887.FStar_TypeChecker_Env.qname_and_index)
=======
             (uu___124_5066.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___124_5066.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___124_5066.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___124_5066.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___124_5066.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___124_5066.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___124_5066.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___124_5066.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___124_5066.FStar_TypeChecker_Env.is_native_tactic)
>>>>>>> origin/guido_tactics
         } in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name in
<<<<<<< HEAD
        let uu____4890 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____4890 with
        | (ses,exports,env3) ->
            ((let uu___119_4909 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___119_4909.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___119_4909.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___119_4909.FStar_Syntax_Syntax.is_interface)
=======
        let uu____5069 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
        match uu____5069 with
        | (ses,exports,env3) ->
            ((let uu___125_5087 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___125_5087.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___125_5087.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___125_5087.FStar_Syntax_Syntax.is_interface)
>>>>>>> origin/guido_tactics
              }), exports, env3)))
let tc_more_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul* FStar_Syntax_Syntax.sigelt Prims.list*
          FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
<<<<<<< HEAD
        let uu____4925 = tc_decls env decls in
        match uu____4925 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___120_4943 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___120_4943.FStar_Syntax_Syntax.name);
=======
        let uu____5106 = tc_decls env decls in
        match uu____5106 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___126_5124 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___126_5124.FStar_Syntax_Syntax.name);
>>>>>>> origin/guido_tactics
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
<<<<<<< HEAD
                  (uu___120_4943.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___120_4943.FStar_Syntax_Syntax.is_interface)
=======
                  (uu___126_5124.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___126_5124.FStar_Syntax_Syntax.is_interface)
>>>>>>> origin/guido_tactics
              } in
            (modul1, exports, env1)
let check_exports:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
<<<<<<< HEAD
          let uu___121_4957 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___121_4957.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___121_4957.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___121_4957.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___121_4957.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___121_4957.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___121_4957.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___121_4957.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___121_4957.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___121_4957.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___121_4957.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___121_4957.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___121_4957.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___121_4957.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___121_4957.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___121_4957.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___121_4957.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___121_4957.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___121_4957.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___121_4957.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___121_4957.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___121_4957.FStar_TypeChecker_Env.qname_and_index)
          } in
        let check_term lid univs1 t =
          let uu____4968 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____4968 with
          | (univs2,t1) ->
              ((let uu____4974 =
                  let uu____4975 =
                    let uu____4978 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____4978 in
                  FStar_All.pipe_left uu____4975
                    (FStar_Options.Other "Exports") in
                if uu____4974
                then
                  let uu____4979 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____4980 =
                    let uu____4981 =
=======
          let uu___127_5141 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___127_5141.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___127_5141.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___127_5141.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___127_5141.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___127_5141.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___127_5141.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___127_5141.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___127_5141.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___127_5141.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___127_5141.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___127_5141.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___127_5141.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___127_5141.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___127_5141.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___127_5141.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___127_5141.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___127_5141.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___127_5141.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___127_5141.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___127_5141.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___127_5141.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___127_5141.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___127_5141.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___127_5141.FStar_TypeChecker_Env.is_native_tactic)
          } in
        let check_term lid univs1 t =
          let uu____5152 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____5152 with
          | (univs2,t1) ->
              ((let uu____5158 =
                  let uu____5159 =
                    let uu____5162 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____5162 in
                  FStar_All.pipe_left uu____5159
                    (FStar_Options.Other "Exports") in
                if uu____5158
                then
                  let uu____5163 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____5164 =
                    let uu____5165 =
>>>>>>> origin/guido_tactics
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
<<<<<<< HEAD
                    FStar_All.pipe_right uu____4981
                      (FStar_String.concat ", ") in
                  let uu____4987 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____4979 uu____4980 uu____4987
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____4990 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____4990 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____5008 =
             let uu____5009 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____5010 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____5009 uu____5010 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5008);
=======
                    FStar_All.pipe_right uu____5165
                      (FStar_String.concat ", ") in
                  let uu____5170 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____5163 uu____5164 uu____5170
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____5173 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____5173 FStar_Pervasives.ignore)) in
        let check_term1 lid univs1 t =
          (let uu____5191 =
             let uu____5192 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____5193 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____5192 uu____5193 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5191);
>>>>>>> origin/guido_tactics
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
<<<<<<< HEAD
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5017) ->
              let uu____5022 =
                let uu____5023 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5023 in
              if uu____5022
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____5031,uu____5032) ->
              let t =
                let uu____5040 =
                  let uu____5043 =
                    let uu____5044 =
                      let uu____5052 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____5052) in
                    FStar_Syntax_Syntax.Tm_arrow uu____5044 in
                  FStar_Syntax_Syntax.mk uu____5043 in
                uu____5040 None se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____5064,uu____5065,uu____5066) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____5072 =
                let uu____5073 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5073 in
              if uu____5072 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____5076,lbs),uu____5078,uu____5079) ->
              let uu____5089 =
                let uu____5090 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5090 in
              if uu____5089
=======
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5200) ->
              let uu____5205 =
                let uu____5206 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5206 in
              if uu____5205
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____5214,uu____5215) ->
              let t =
                let uu____5223 =
                  let uu____5226 =
                    let uu____5227 =
                      let uu____5235 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____5235) in
                    FStar_Syntax_Syntax.Tm_arrow uu____5227 in
                  FStar_Syntax_Syntax.mk uu____5226 in
                uu____5223 None se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____5247,uu____5248,uu____5249) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____5255 =
                let uu____5256 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5256 in
              if uu____5255 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____5259,lbs),uu____5261,uu____5262) ->
              let uu____5272 =
                let uu____5273 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5273 in
              if uu____5272
>>>>>>> origin/guido_tactics
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        check_term1
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs1,binders,comp,flags) ->
<<<<<<< HEAD
              let uu____5105 =
                let uu____5106 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5106 in
              if uu____5105
=======
              let uu____5290 =
                let uu____5291 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5291 in
              if uu____5290
>>>>>>> origin/guido_tactics
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp)) None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
<<<<<<< HEAD
          | FStar_Syntax_Syntax.Sig_main uu____5116 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____5117 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5121 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5122 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5123 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5124 -> () in
=======
          | FStar_Syntax_Syntax.Sig_main uu____5305 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____5306 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5309 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____5310 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5311 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5312 -> () in
>>>>>>> origin/guido_tactics
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
let finish_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelts ->
        (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let modul1 =
<<<<<<< HEAD
          let uu___122_5138 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___122_5138.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___122_5138.FStar_Syntax_Syntax.declarations);
=======
          let uu___128_5329 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___128_5329.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___128_5329.FStar_Syntax_Syntax.declarations);
>>>>>>> origin/guido_tactics
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
<<<<<<< HEAD
        (let uu____5141 =
           let uu____5142 = FStar_Options.lax () in
           Prims.op_Negation uu____5142 in
         if uu____5141 then check_exports env1 modul1 exports else ());
=======
        (let uu____5332 =
           let uu____5333 = FStar_Options.lax () in
           Prims.op_Negation uu____5333 in
         if uu____5332 then check_exports env1 modul1 exports else ());
>>>>>>> origin/guido_tactics
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
<<<<<<< HEAD
        (let uu____5148 =
           let uu____5149 = FStar_Options.interactive () in
           Prims.op_Negation uu____5149 in
         if uu____5148
         then
           let uu____5150 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____5150 FStar_Pervasives.ignore
=======
        (let uu____5339 =
           let uu____5340 = FStar_Options.interactive () in
           Prims.op_Negation uu____5340 in
         if uu____5339
         then
           let uu____5341 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right uu____5341 FStar_Pervasives.ignore
>>>>>>> origin/guido_tactics
         else ());
        (modul1, env1)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
<<<<<<< HEAD
      let uu____5160 = tc_partial_modul env modul in
      match uu____5160 with
=======
      let uu____5353 = tc_partial_modul env modul in
      match uu____5353 with
>>>>>>> origin/guido_tactics
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
<<<<<<< HEAD
      (let uu____5181 = FStar_Options.debug_any () in
       if uu____5181
       then
         let uu____5182 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5182
       else ());
      (let env1 =
         let uu___123_5186 = env in
         let uu____5187 =
           let uu____5188 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5188 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___123_5186.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___123_5186.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___123_5186.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___123_5186.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___123_5186.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___123_5186.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___123_5186.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___123_5186.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___123_5186.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___123_5186.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___123_5186.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___123_5186.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___123_5186.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___123_5186.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___123_5186.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___123_5186.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___123_5186.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___123_5186.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5187;
           FStar_TypeChecker_Env.lax_universes =
             (uu___123_5186.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___123_5186.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___123_5186.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___123_5186.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___123_5186.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____5189 = tc_modul env1 m in
       match uu____5189 with
       | (m1,env2) ->
           ((let uu____5197 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5197
             then
               let uu____5198 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5198
             else ());
            (let uu____5201 =
=======
      (let uu____5376 = FStar_Options.debug_any () in
       if uu____5376
       then
         let uu____5377 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____5377
       else ());
      (let env1 =
         let uu___129_5381 = env in
         let uu____5382 =
           let uu____5383 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____5383 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___129_5381.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___129_5381.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___129_5381.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___129_5381.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___129_5381.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___129_5381.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___129_5381.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___129_5381.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___129_5381.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___129_5381.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___129_5381.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___129_5381.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___129_5381.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___129_5381.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___129_5381.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___129_5381.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___129_5381.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___129_5381.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____5382;
           FStar_TypeChecker_Env.lax_universes =
             (uu___129_5381.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___129_5381.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___129_5381.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___129_5381.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___129_5381.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___129_5381.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___129_5381.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___129_5381.FStar_TypeChecker_Env.is_native_tactic)
         } in
       let uu____5384 = tc_modul env1 m in
       match uu____5384 with
       | (m1,env2) ->
           ((let uu____5392 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____5392
             then
               let uu____5393 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____5393
             else ());
            (let uu____5396 =
>>>>>>> origin/guido_tactics
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
<<<<<<< HEAD
             if uu____5201
=======
             if uu____5396
>>>>>>> origin/guido_tactics
             then
               let normalize_toplevel_lets se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_let ((b,lbs),ids,attrs) ->
                     let n1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.Eager_unfolding;
                         FStar_TypeChecker_Normalize.Reify;
                         FStar_TypeChecker_Normalize.Inlining;
                         FStar_TypeChecker_Normalize.Primops;
                         FStar_TypeChecker_Normalize.UnfoldUntil
                           FStar_Syntax_Syntax.Delta_constant;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
                     let update lb =
<<<<<<< HEAD
                       let uu____5228 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5228 with
                       | (univnames1,e) ->
                           let uu___124_5233 = lb in
                           let uu____5234 =
                             let uu____5237 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5237 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___124_5233.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___124_5233.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___124_5233.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___124_5233.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5234
                           } in
                     let uu___125_5238 = se in
                     let uu____5239 =
                       let uu____5240 =
                         let uu____5246 =
                           let uu____5250 = FStar_List.map update lbs in
                           (b, uu____5250) in
                         (uu____5246, ids, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5240 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5239;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___125_5238.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___125_5238.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___125_5238.FStar_Syntax_Syntax.sigmeta)
                     }
                 | uu____5258 -> se in
               let normalized_module =
                 let uu___126_5260 = m1 in
                 let uu____5261 =
=======
                       let uu____5423 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____5423 with
                       | (univnames1,e) ->
                           let uu___130_5428 = lb in
                           let uu____5429 =
                             let uu____5432 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____5432 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___130_5428.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___130_5428.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___130_5428.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___130_5428.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5429
                           } in
                     let uu___131_5433 = se in
                     let uu____5434 =
                       let uu____5435 =
                         let uu____5441 =
                           let uu____5445 = FStar_List.map update lbs in
                           (b, uu____5445) in
                         (uu____5441, ids, attrs) in
                       FStar_Syntax_Syntax.Sig_let uu____5435 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____5434;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___131_5433.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___131_5433.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___131_5433.FStar_Syntax_Syntax.sigmeta)
                     }
                 | uu____5453 -> se in
               let normalized_module =
                 let uu___132_5455 = m1 in
                 let uu____5456 =
>>>>>>> origin/guido_tactics
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
<<<<<<< HEAD
                     (uu___126_5260.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5261;
                   FStar_Syntax_Syntax.exports =
                     (uu___126_5260.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___126_5260.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5262 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5262
=======
                     (uu___132_5455.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____5456;
                   FStar_Syntax_Syntax.exports =
                     (uu___132_5455.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___132_5455.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____5457 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____5457
>>>>>>> origin/guido_tactics
             else ());
            (m1, env2)))