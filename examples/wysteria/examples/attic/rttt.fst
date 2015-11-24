type same_c (c:config) (c':config) =
  Conf.l c = Conf.l c' /\ Conf.m c = Conf.m c' /\ Conf.t c = Conf.t c' /\ Conf.tr c = Conf.tr c'

type neq_p_p' (#a:Type) (#b:Type) (x:a) (y:b) = (EqTyp a b) /\ not (x = y)

type same_pi (ps:prins) (pi:protocol ps) (pi':protocol ps) (p:prin{mem p ps}) =
  forall p'.{:pattern (neq_p_p' p p')} neq_p_p' p p' ==> select p' (fst pi) = select p' (fst pi')

val tstep_assec_lemma:
  ps':prins -> pi:protocol ps' -> ps:prins -> x:varname -> e:exp{tpre_assec pi ps x e}
  -> pi':protocol ps'{pi' = tstep_assec #ps' pi ps x e}
  -> Lemma (requires (True))
          (ensures (fst pi' = step_ps_to_wait #ps' (fst pi) ps /\
	            snd pi' =
		    update ps (Conf Target (Mode Sec ps) [] (update_env (compose_envs_m ps (get_env_m pi ps)) x V_unit) (T_exp e) (hide [])) (snd pi)))
let tstep_assec_lemma ps' pi ps x e pi' = admit ()

#set-options "--z3timeout 15"

val sec_enter_is_parametric:
  ps:prins -> pi:protocol ps -> pi':protocol ps
  -> h:pstep #ps pi pi'{is_P_sec_enter h /\ P_sec_enter.ps h = ps}
  -> p:prin{contains p (fst pi)} -> c:tconfig_par{same_c (Some.v (select p (fst pi))) c}
  -> Tot (h':(pstep #ps (update #prin #tconfig_par #p_cmp p c (fst pi), snd pi)
                       (update #prin #tconfig_par #p_cmp p (step_p_to_wait c p) (fst pi'), snd pi'))
            {is_P_sec_enter h'})
let sec_enter_is_parametric ps pi pi' h p c =
  let x = P_sec_enter.x h in
  let e = P_sec_enter.e h in
  let (pi_p, pi_s) = pi in
  let (pi'_p, pi'_s) = pi' in
  let pi_c = (update p c pi_p, pi_s) in
  let pi'_c = (update p (step_p_to_wait c p) pi'_p, pi'_s) in
  let (pi_pstep, pi_sstep) = tstep_assec #ps pi_c ps x e in
  let en_m = get_env_m #ps pi ps in
  let en_c_m = get_env_m #ps pi_c ps in

  (* let _ = admitP (b2t (pi_pstep = step_ps_to_wait #ps (fst pi_c) ps)) in *)
  (* let _ = admitP (b2t (pi_sstep = update #prins #tconfig_sec #ps_cmp ps (Conf Target (Mode Sec ps) [] (update_env (compose_envs_m ps (get_env_m #ps pi_c ps)) x V_unit) (T_exp e) (hide [])) (snd pi_c))) in *)

  let _ = OrdMap.eq_lemma en_m en_c_m in

  let _ = OrdMap.eq_lemma pi_pstep (step_ps_to_wait #ps (fst pi_c) ps) in
  let _ = OrdMap.eq_lemma (fst pi'_c) (step_ps_to_wait #ps (fst pi_c) ps) in
  let _ = OrdMap.eq_lemma pi_pstep (fst pi'_c) in

  let _ = OrdMap.eq_lemma pi_sstep (snd pi'_c) in

  let h' = P_sec_enter #ps pi_c ps x e (pi_pstep, pi_sstep) in h'

#reset-options

val sec_step_is_parametric:
  ps:prins -> pi:protocol ps -> pi':protocol ps
  -> h:pstep #ps pi pi'{is_P_sec h /\ P_sec.ps h = ps}
  -> p:prin{contains p (fst pi)} -> c:tconfig_par{same_c (Some.v (select p (fst pi))) c}
  -> Tot (h':(pstep #ps (update #prin #tconfig_par #p_cmp p c (fst pi), snd pi)
                       (update #prin #tconfig_par #p_cmp p c (fst pi), snd pi'))
	    {is_P_sec h'})
let sec_step_is_parametric ps pi pi' h p c =
  P_sec #ps #(P_sec.c' h) (update p c (fst pi), snd pi) ps (P_sec.h h) (update p c (fst pi), snd pi')

val sec_step_star_is_parametric:
  ps:prins -> pi:protocol ps -> pi':protocol ps -> h:pstep_star #ps pi pi'{all_sec_steps ps pi pi' h ps}
  -> p:prin{contains p (fst pi)} -> c:tconfig_par{same_c (Some.v (select p (fst pi))) c}
  -> Tot (h':(pstep_star #ps (update p c (fst pi), snd pi) (update p c (fst pi'), snd pi'))
            {all_sec_steps ps (update p c (fst pi), snd pi) (update p c (fst pi'), snd pi') h' ps /\
	     fst pi = fst pi'})
    (decreases h)
let rec sec_step_star_is_parametric ps pi pi' h p c = match h with
  | PS_refl _                        -> PS_refl #ps (update p c (fst pi), snd pi)
  | PS_tran #ps #pi #pi' #pi'' h1 h2 ->
    let h2' = sec_step_star_is_parametric ps pi' pi'' h2 p c in
    let h1' = sec_step_is_parametric ps pi pi' h1 p c in
    PS_tran #ps #(update p c (fst pi), snd pi) #(update p c (fst pi'), snd pi')
            #(update p c (fst pi''), snd pi'') h1' h2'

val conf_with_value: config -> dvalue -> Tot config
let conf_with_value (Conf l m s en t tr) dv =
  Conf l m s en (T_val (D_v.v dv)) (concat_traces tr (hide [ Tr_val (D_v.v dv) ]))

opaque type pi_exit_witness (#a:Type) (x:a) = True

val value_lemma:
  p:prin -> c:tconfig_par -> c_sec:tconfig{is_sec c_sec /\ is_sterminal c_sec}
  -> Lemma (requires (True))
          (ensures (ret_sec_value_to_p c_sec (step_p_to_wait c p) p =
	            conf_with_value c (slice_v p (D_v.v (c_value c_sec)))))
let value_lemma p c c_sec = ()

#set-options "--z3timeout 10"

val sec_comp_is_parametric:
  ps:prins
  -> pi:tpar ps
  -> pi_enter:protocol ps
  -> pi_final:protocol ps{contains ps (snd pi_final) /\
                         Conf.m (Some.v (select ps (snd pi_final))) = Mode Sec ps /\
		         is_sterminal (Some.v (select ps (snd pi_final)))}
  -> h1:pstep #ps (pi, OrdMap.empty #prins #tconfig_sec #ps_cmp) pi_enter{is_P_sec_enter h1 /\ P_sec_enter.ps h1 = ps}
  -> h2:pstep_star #ps pi_enter pi_final{all_sec_steps ps pi_enter pi_final h2 ps}
  -> p:prin{contains p pi} -> c:tconfig_par{same_c (Some.v (select p pi)) c}
  -> dv:dvalue{dv = slice_v p (D_v.v (c_value (Some.v (select ps (snd pi_final)))))}
  -> Lemma (requires (True))
          (ensures (exists (pi_exit:protocol ps).{:pattern (pi_exit_witness pi_exit)}
	            (pstep_star #ps (update p c pi, OrdMap.empty #prins #tconfig_sec #ps_cmp) pi_exit /\
		     Some.v (select p (fst pi_exit)) = conf_with_value c dv)))
let sec_comp_is_parametric ps pi pi_enter pi_final h1 h2 p c dv =
  let pi_c = (update p c pi, OrdMap.empty #prins #tconfig_sec #ps_cmp) in

  let c' = step_p_to_wait c p in

  let pi_enter_c = (update p c' (fst pi_enter), snd pi_enter) in

  let s1 = sec_enter_is_parametric ps (pi, OrdMap.empty #prins #tconfig_sec #ps_cmp) pi_enter h1 p c in

  let (pi_final_p, pi_final_s) = pi_final in
  let (pi_final_c_p, pi_final_c_s) =
    (update #prin #tconfig_par #p_cmp p c' pi_final_p, pi_final_s) in

  let s2 = sec_step_star_is_parametric ps pi_enter pi_final h2 p c' in

  let _ = cut (b2t (fst pi_enter_c = pi_final_c_p)) in

  let _ = cut (b2t (contains #prins #tconfig_sec #ps_cmp ps pi_final_c_s)) in
  //let _ = admitP (b2t (Conf.m (Some.v (select ps pi_final_c_s)) = Mode Sec ps)) in
  let _ = cut (ps_sec_waiting #ps (pi_final_c_p, pi_final_c_s) ps) in

  let c_sec = Some.v (select #prins #tconfig_sec #ps_cmp ps pi_final_c_s) in
  value_lemma p c c_sec;

  let pi_exit_c_p = ret_sec_value_to_ps #ps pi_final_c_p (Some.v (select #prins #tconfig_sec #ps_cmp ps pi_final_c_s)) ps in
  let pi_exit_c_s = OrdMap.remove #prins #tconfig_sec #ps_cmp ps pi_final_c_s in

  let s3 = P_sec_exit #ps (pi_final_c_p, pi_final_c_s) ps (pi_exit_c_p, pi_exit_c_s) in

  let sstitched = PS_tran s1 (pss_ps_to_pss #ps #pi_enter_c #(pi_final_c_p, pi_final_c_s)
                                            #(pi_exit_c_p, pi_exit_c_s) s2 s3) in
  squash_pstep_star ps pi_c (pi_exit_c_p, pi_exit_c_s) sstitched;

  cut (pi_exit_witness #(protocol ps) (pi_exit_c_p, pi_exit_c_s))

#reset-options



diff --git a/examples/wysteria/psem.fst b/examples/wysteria/psem.fst
index ad86356..90e3641 100644
--- a/examples/wysteria/psem.fst
+++ b/examples/wysteria/psem.fst
@@ -202,11 +202,21 @@ type consistent_ts (ts:tsec) (ps:prins) =
   not (contains ps ts) /\
   (forall ps'. contains ps' ts ==> is_empty_eq (intersect ps ps'))
 
+val all_sec_steps:
+  ps:prins -> pi:protocol ps -> pi':protocol ps -> h:pstep_star #ps pi pi' -> ps':prins -> Tot bool
+  (decreases h)
+let rec all_sec_steps ps pi pi' h ps' = match h with
+  | PS_refl _                        -> true
+  | PS_tran #ps #pi #pi' #pi'' h1 h2 -> is_P_sec h1 && P_sec.ps h1 = ps' && all_sec_steps ps pi' pi'' h2 ps'
+
 opaque val sec_sstep_star_to_pstep_star:
   c:config{is_sec_comp c} -> c':config{is_sec_comp c'} -> h:sstep_star c c'
   -> ps:prins -> tp:tpar ps -> ts:tsec{consistent_ts ts (Mode.ps (Conf.m c))}
-  -> Tot (pstep_star #ps (tp, update (Mode.ps (Conf.m c)) c ts)
-                        (tp, update (Mode.ps (Conf.m c)) c' ts)) (decreases h)
+  -> Tot (h:(pstep_star #ps (tp, update (Mode.ps (Conf.m c)) c ts)
+                           (tp, update (Mode.ps (Conf.m c)) c' ts))
+          {all_sec_steps ps (tp, update (Mode.ps (Conf.m c)) c ts)
+                            (tp, update (Mode.ps (Conf.m c)) c' ts) h (Mode.ps (Conf.m c))})
+    (decreases h)
 let rec sec_sstep_star_to_pstep_star c c' h ps tp ts = match h with
   | SS_refl _                 -> PS_refl (tp, update (Mode.ps (Conf.m c)) c ts)
   | SS_tran #c #c' #c'' h1 h2 ->
