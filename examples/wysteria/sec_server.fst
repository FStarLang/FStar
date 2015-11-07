(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi FStar.IO --admit_fsi FStar.String --__temp_no_proj --admit_fsi FStar.Squash;
    other-files:ghost.fst squash.fsti listTot.fst ordset.fsi ordmap.fsi classical.fst set.fsi heap.fst st.fst all.fst list.fst io.fsti string.fsi prins.fst ast.fst ffibridge.fsi sem.fst runtime.fsi print.fst ckt.fst interpreter.fst
 --*)

module SecServer

open FStar.Ghost

open FStar.OrdMap
open FStar.OrdSet

open Runtime

open Prins
open AST
open Semantics
open Interpreter

type en_map = ordmap prin env p_cmp
type out_map = ordmap prin chan_out p_cmp
type redex_map = ordmap prin redex p_cmp

(*
 * ps    -- parties requires for this secure computation
 * ps'   -- parties already checked-in
 * pi    -- the protocol (mapping p to c) accumulated so far
 * x,e   -- \x.e is the secure computation
 * en_m  -- the map of p |-> env accumulated so far
 * red_m -- the map of p |-> redex accumulated so far
 *)
type tpre_assec' (ps:prins) (ps':prins) (pi:tpar ps') (x:varname) (e:exp) (en_m:en_map) (red_m:redex_map) =
  forall p. contains p pi ==>
       (contains p en_m /\ contains p red_m /\
        (Let (Some.v (select p pi))
         (fun c ->
	  is_T_red (Conf.t c) /\
	  (Let (T_red.r (Conf.t c))
	   (fun r ->
	    r = Some.v (select p red_m) /\
	    is_R_assec r /\ R_assec.ps r = ps /\ is_clos (R_assec.v r) /\
	    MkTuple3._2 (get_en_b (R_assec.v r)) = x /\
	    MkTuple3._3 (get_en_b (R_assec.v r)) = e /\
	    Some.v (select p en_m) = MkTuple3._1 (get_en_b (R_assec.v r)))))))

(*
 * Data type to accumulate the info for a secure computation as parties keep checking in
 *)
type psmap_v =
  | Mk_psmap:
    ps:prins -> ps':prins{subset ps' ps}
    -> en_m:en_map{forall p. mem p ps' = contains p en_m}
    -> out_m:out_map{forall p. mem p ps' = contains p out_m}
    -> red_m:redex_map{forall p. mem p ps' = contains p red_m}
    -> x:varname
    -> e:exp{exists (pi:tpar ps'). tpre_assec' ps ps' pi x e en_m red_m}
    -> psmap_v

type psmap = ordmap prins psmap_v ps_cmp

(* Forcing instantiation of type variables in extracted OCaml code *)
type psmap_ref_t =
  | Mk_ref: r:ref (ordmap prins psmap_v ps_cmp) -> psmap_ref_t

(* private *)
let psmap_ref = Mk_ref (alloc (OrdMap.empty #prins #psmap_v #ps_cmp))

(* call interpreter step_star on the input config *)
val do_sec_comp':
  c:config -> ML (c':config{is_sterminal c'} & (sstep_star c c'))
let do_sec_comp' c =
  let (| c_opt, h |) = step_star c in
  if is_sterminal c_opt then
    (| c_opt, h |)
  else
    failwith "Secure computation did not end in terminal state"

(* convert a pi ->* pi' -> pi'' to pi ->* pi'' *)
val pss_ps_to_pss:
  #ps:prins -> #pi:protocol ps -> #pi':protocol ps -> #pi'':protocol ps
  -> h1:pstep_star #ps pi pi' -> h2:pstep #ps pi' pi''
  -> Tot (pstep_star #ps pi pi'') (decreases h1)
let rec pss_ps_to_pss #ps #pi #pi' #pi'' h1 h2 = match h1 with
  | PS_refl _       -> PS_tran h2 (PS_refl pi'')
  | PS_tran h1' h2' ->
    let hh = pss_ps_to_pss h2' h2 in
    PS_tran h1' hh

(* that two protocols pi and pi' differ only in parties' terms *)
type eq_proto' (ps:prins) (pi:tpar ps) (pi':tpar ps) =
  forall p. contains p pi ==>
       (Let (Some.v (select p pi))
        (fun c ->
	 (Let (Some.v (select p pi'))
	  (fun c' ->
           Conf.l c = Conf.l c' /\
           Conf.m c = Conf.m c' /\
           Conf.s c = Conf.s c' /\
           Conf.en c = Conf.en c'))))

(* that pi contains slice of c's value for each party *)
type final_prop (ps:prins) (pi:tpar ps) (c:config{is_value c}) =
  forall p. contains p pi ==>
       (Let (Conf.t (Some.v (select p pi)))
        (fun t ->
	 is_T_val t /\
	 (Let (D_v (T_val.meta t) (T_val.v t))
	  (fun dvt ->
	   b2t (dvt = slice_v #(T_val.meta (Conf.t c)) p
			      (T_val.v (Conf.t c)))))))

(* that ret_sec_value_to_ps gives a final_prop protocol *)
val ret_sec_value_to_ps_helper_lemma:
  #ps:prins
  -> pi:tpar ps{forall p. mem p ps ==>
                    (contains p pi /\ waiting_config (Some.v (select p pi)))}
  -> c:tconfig{is_sec c /\ is_value c}
  -> pi':tpar ps{pi' = ret_sec_value_to_ps #ps pi c ps}
  -> Lemma (requires (True))
          (ensures (final_prop ps pi' c))
let ret_sec_value_to_ps_helper_lemma #ps pi c pi' = ()

(* property that we prove for the secure computation *)
type sec_comp_prop (ps:prins) (c:config{is_sterminal c}) (pi:tpar ps) (pi_final:protocol ps) =
  final_prop ps (fst pi_final) c                                           /\
  pstep_star #ps (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp)) pi_final /\
  eq_proto' ps pi (fst pi_final)

val init_sec_conf:
  ps:prins -> en_m:en_map{contains_ps ps en_m} -> varname -> exp -> Tot tconfig_sec
let init_sec_conf ps en_m x e =
  Conf Target (Mode Sec ps) [] (update_env (compose_envs_m ps en_m) x V_unit)
       (T_exp e) (hide [])

val get_sec_enter_step:
  ps:prins -> en_m:en_map{forall p. mem p ps = contains p en_m}
  -> red_m:redex_map{forall p.mem p ps = contains p red_m}
  -> x:varname -> e:exp
  -> pi:tpar ps{tpre_assec' ps ps pi x e en_m red_m}
  -> Tot (pi_enter:protocol ps{pi_enter = tstep_assec #ps (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp)) ps x e} &
         pstep #ps (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp)) pi_enter)
let get_sec_enter_step ps en_m red_m x e pi =
  let pi_enter = tstep_assec #ps (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp)) ps x e in
  (| pi_enter,
     P_sec_enter #ps (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp))
                 ps x e (tstep_assec #ps (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp)) ps x e) |)

val squash_pstep_star:
  ps:prins -> pi_init:protocol ps -> pi_final:protocol ps
  -> h:pstep_star #ps pi_init pi_final
  -> Tot (u:unit{pstep_star #ps pi_init pi_final})
let squash_pstep_star ps pi_init pi_final h =
  let sq_h = FStar.Squash.return_squash #(pstep_star #ps pi_init pi_final) h in
  FStar.Squash.give_proof #(pstep_star #ps pi_init pi_final) sq_h

val stitch_steps:
  ps:prins
  -> pi_init:protocol ps
  -> pi_enter:protocol ps
  -> pi_sec_terminal:protocol ps
  -> pi_final:protocol ps
  -> s1:pstep #ps pi_init pi_enter
  -> ss:pstep_star #ps pi_enter pi_sec_terminal
  -> s2:pstep #ps pi_sec_terminal pi_final
  -> Tot (pstep_star #ps pi_init pi_final)
let stitch_steps ps pi_init pi_enter pi_sec_terminal pi_final s1 ss s2 =
  let h1:pstep_star #ps pi_enter pi_final =
    pss_ps_to_pss #ps #pi_enter #pi_sec_terminal #pi_final ss s2
  in

  let h2:pstep_star #ps pi_init pi_final =
    PS_tran #ps #pi_init #pi_enter #pi_final s1 h1
  in
  h2

#set-options "--z3timeout 25"

val create_pstep_star:
  ps:prins -> en_m:en_map{forall p. mem p ps = contains p en_m}
  -> red_m:redex_map{forall p.mem p ps = contains p red_m}
  -> x:varname -> e:exp -> c_sec:config{is_sterminal c_sec}
  -> h:sstep_star (init_sec_conf ps en_m x e) c_sec
  -> pi:tpar ps{tpre_assec' ps ps pi x e en_m red_m}
  -> Tot (pi_final:protocol ps{sec_comp_prop ps c_sec pi pi_final})
let create_pstep_star ps en_m red_m x e c_sec h pi =
  let pi_init = (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp)) in
  let en_m' = get_env_m #ps pi_init ps in
  let _ = cut (OrdMap.Equal en_m' en_m) in

  //tpre_assec_lemma ps en_m red_m x e pi;
  //let _ = cut (tpre_assec #ps pi_init ps x e) in

  //let pi_enter = tstep_assec #ps pi_init ps x e in
  //let (pi_enter_par, pi_enter_sec) = pi_enter in

  (* first step, enter secure block to pi_enter *)
  //let s1:pstep #ps pi_init pi_enter = P_sec_enter #ps pi_init ps x e pi_enter in
  let (| pi_enter,  s1 |) = get_sec_enter_step ps en_m red_m x e pi in
  let (pi_enter_par, pi_enter_sec) = pi_enter in

  let c_sec_init = init_sec_conf ps en_m x e in

  //let _ = cut (b2t (pi_enter_sec = update ps c_sec_init (snd pi_init))) in

  sec_comp_step_star_same_mode #c_sec_init #c_sec h;

  //let _ = cut (is_sec c_sec_terminal /\ Conf.l c_sec_terminal = Target) in
  
  let tsec_terminal = update ps c_sec (snd pi_init) in
  let pi_sec_terminal = (pi_enter_par, tsec_terminal) in

  (* steps taken in secure computation *)
  let ss:pstep_star #ps pi_enter pi_sec_terminal =
    sec_sstep_star_to_pstep_star c_sec_init c_sec h ps pi_enter_par (snd pi_init) in

  //let _ = cut (b2t (Some.v (select ps (snd pi_sec_terminal)) = c_sec)) in

  //let _ = cut (b2t (Conf.m c_sec_terminal = Mode Sec ps)) in
  //let _ = cut (b2t (is_value c_sec_terminal)) in
  //let _ = cut (b2t (Conf.s c_sec_terminal = [])) in
  //let _ = cut (tpre_assec_ret #ps pi_sec_terminal ps) in

  //let _ = cut (is_sec c_sec_terminal /\ is_value c_sec_terminal) in

  let _ = cut (tpre_assec_ret #ps pi_sec_terminal ps) in

  let pi_final_par = ret_sec_value_to_ps #ps pi_enter_par c_sec ps in
  let pi_final = (pi_final_par, OrdMap.remove ps tsec_terminal) in
  
  (* TODO: FIXME: this also verifies, but with this the whole thing times out *)
  let _ = admitP (eq_proto' ps pi pi_final_par) in
  ret_sec_value_to_ps_helper_lemma #ps pi_enter_par c_sec pi_final_par;

  let _ = cut (final_prop ps pi_final_par c_sec) in

  let s2 = P_sec_exit #ps pi_sec_terminal ps pi_final in

  (* let h1:pstep_star #ps pi_enter pi_final = pss_ps_to_pss #ps #pi_enter #pi_sec_terminal #pi_final ss s2 in *)

  (* let h2:pstep_star #ps pi_init pi_final = PS_tran #ps #pi_init #pi_enter #pi_final s1 h1 in *)
  let h2 = stitch_steps ps pi_init pi_enter pi_sec_terminal pi_final s1 ss s2 in
  squash_pstep_star ps pi_init pi_final h2;
  //let _ = cut (pstep_star #ps pi_init pi_final) in
  pi_final

#reset-options

type config_prop (ps:prins) (x:varname) (e:exp) (p:prin) (r:redex) (c:config) =
  mem p ps /\ is_R_assec r /\ is_clos (R_assec.v r) /\ R_assec.ps r = ps /\
  MkTuple3._2 (get_en_b (R_assec.v r)) = x /\ MkTuple3._3 (get_en_b (R_assec.v r)) = e /\
  Conf.t c = T_red r /\ Conf.l c = Target /\ Conf.m c = Mode Par (singleton p)

opaque type witness_build_pi (#a:Type) (x:a) = True

val build_pi:
  ps:prins -> ps':prins{subset ps' ps}
  -> en_m:en_map{forall p. mem p ps' = contains p en_m}
  -> red_m:redex_map{forall p. mem p ps' = contains p red_m}
  -> x:varname -> e:exp
  -> p:prin
  -> r:redex
  -> c:config{config_prop ps x e p r c}
  -> pi:tpar ps'{tpre_assec' ps ps' pi x e en_m red_m}
  -> Lemma (requires (True))
          (ensures (exists (pi':tpar (union ps' (singleton p))).{:pattern (witness_build_pi pi')}
                      tpre_assec' ps (union #prin #p_cmp ps' (singleton p)) pi' x e
	                          (update #prin #env #p_cmp p (MkTuple3._1 (get_en_b (R_assec.v r))) en_m)
	                          (update #prin #redex #p_cmp p r red_m)))
    [SMTPatT (config_prop ps x e p r c);
     SMTPatT (tpre_assec' ps ps' pi x e en_m red_m)]
let build_pi ps ps' en_m red_m x e p r c pi =
  let pi' = update p c pi in
  let _ = cut (tpre_assec' ps (union ps' (singleton p)) pi' x e
	                      (update p (MkTuple3._1 (get_en_b (R_assec.v r))) en_m)
	                      (update p r red_m)) in
  let _ = cut (witness_build_pi pi') in
  ()

val build_pi_lemma:
  ps:prins -> ps':prins{subset ps' ps}
  -> en_m:en_map{forall p. mem p ps' = contains p en_m}
  -> red_m:redex_map{forall p. mem p ps' = contains p red_m}
  -> x:varname -> e:exp
  -> p:prin
  -> r:redex{is_R_assec r /\ is_clos (R_assec.v r) /\ R_assec.ps r = ps /\
            MkTuple3._2 (get_en_b (R_assec.v r)) = x /\
	    MkTuple3._3 (get_en_b (R_assec.v r)) = e}
  -> Lemma (requires (exists (c:config) (pi:tpar ps').
                       config_prop ps x e p r c /\
                       tpre_assec' ps ps' pi x e en_m red_m))
          (ensures (exists (pi':tpar (union ps' (singleton p))).
                      tpre_assec' ps (union #prin #p_cmp ps' (singleton p)) pi' x e
	                          (update #prin #env #p_cmp p (MkTuple3._1 (get_en_b (R_assec.v r))) en_m)
	                          (update #prin #redex #p_cmp p r red_m)))
let build_pi_lemma ps ps' en_m red_m x e p r = admit ()

opaque type witness_build_pstep_star (#a:Type) (x:a) = True

opaque type Good (#a:Type) (x:a) = True

val build_pstep_star:
  ps:prins
  -> en_m:en_map{forall p. mem p ps = contains p en_m}
  -> red_m:redex_map{forall p. mem p ps = contains p red_m}
  -> x:varname -> e:exp -> c_sec:config{is_sterminal c_sec}
  -> h:sstep_star (init_sec_conf ps en_m x e) c_sec
  -> pi:tpar ps{tpre_assec' ps ps pi x e en_m red_m}
  -> Lemma (requires (True))
          (ensures (exists (pi_final:protocol ps).{:pattern (witness_build_pstep_star pi_final)} sec_comp_prop ps c_sec pi pi_final))
    [SMTPatT (tpre_assec' ps ps pi x e en_m red_m); SMTPat (is_sterminal c_sec);
     SMTPatT (Good h)]
let build_pstep_star ps en_m red_m x e c_sec h pi =
  let pi_final = create_pstep_star ps en_m red_m x e c_sec h pi in
  let _ = cut (witness_build_pstep_star pi_final) in
  ()

val build_pstep_star_lemma:
  ps:prins
  -> en_m:en_map{forall p. mem p ps = contains p en_m}
  -> red_m:redex_map{forall p. mem p ps = contains p red_m}
  -> x:varname -> e:exp -> c_sec:config{is_sterminal c_sec}
  -> h:sstep_star (init_sec_conf ps en_m x e) c_sec{Good h}
  -> Lemma (requires (exists (pi:tpar ps). tpre_assec' ps ps pi x e en_m red_m))
          (ensures (exists (pi:tpar ps) (pi_final:protocol ps). sec_comp_prop ps c_sec pi pi_final))
let build_pstep_star_lemma ps en_m red_m x e c_sec h = admit ()

val tpre_assec_lemma:
  ps:prins -> pi:tpar ps -> x:varname -> e:exp
  -> en_m:en_map -> red_m:redex_map{tpre_assec' ps ps pi x e en_m red_m}
  -> Lemma (requires (True)) (ensures (tpre_assec #ps (pi, OrdMap.empty #prins #tconfig_sec #ps_cmp)  ps x e))
let tpre_assec_lemma ps pi x e en_m red_m = ()

val send_output:
  ps':prins
  -> ps:prins{subset ps' ps} -> x:varname -> e:exp
  -> en_m:en_map{forall p. mem p ps = contains p en_m}
  -> red_m:redex_map{forall p. mem p ps = contains p red_m}
  -> out_m:out_map{forall p. mem p ps = contains p out_m}
  -> c_sec:config{is_sterminal c_sec /\
                 (exists pi pi_final. (tpre_assec' ps ps pi x e en_m red_m /\
		                  sec_comp_prop ps c_sec pi pi_final))}
  -> ML unit
let rec send_output ps' ps x e en_m red_m out_m c_sec =
  let Some p = choose ps' in
  let Some out = select p out_m in
  let Some r = select p red_m in
  let dv = slice_v p (D_v.v (c_value c_sec)) in

  (* This is the server property *)
  let _ = assert (server_prop p r ps x e dv) in

  server_write out (p, r, ps, x, e, dv);

  let ps'_rest = remove p ps' in
  if ps'_rest = empty then ()
  else send_output ps'_rest ps x e en_m red_m out_m c_sec

val handle_connection: chan_in -> chan_out -> ML unit
let handle_connection c_in c_out =
  let p, r = server_read c_in in

  (* This is the client property *)
  let _ = admitP (client_prop p r) in
  
  let R_assec #meta ps v = r in
  let (en, x, e) = get_en_b v in

  let psmap_ref = Mk_ref.r psmap_ref in

  let ps', en_m, out_m, red_m =
    if contains ps !psmap_ref then
      let Some (Mk_psmap ps1 ps' en_m out_m red_m x' e') = select ps !psmap_ref in
      let _ = admitP (b2t (e = e')) in
      if ps = ps1 && x = x' then
	let _ = cut (exists c. config_prop ps x e p r c) in
	let _ = cut (exists pi. tpre_assec' ps ps' pi x e en_m red_m) in

        let _ = cut (forall p. mem p ps' = contains p en_m) in
        let _ = cut (forall p. mem p ps' = contains p red_m) in
        let _ = cut (b2t (subset ps' ps)) in
        (* let _ = admitP (exists pi'. tpre_assec' ps *)
	(*                        (union #prin #p_cmp  ps' (singleton p)) pi' x e *)
	(*                        (update #prin #env #p_cmp p (MkTuple3._1 (get_en_b (R_assec.v r))) en_m) (update p r red_m)) in *)

	let en_m = update #prin #env #p_cmp p en en_m in
	let out_m = update #prin #chan_out #p_cmp p c_out out_m in
	let red_m = update #prin #redex #p_cmp p r red_m in

        let ps' = union #prin #p_cmp ps' (singleton p) in

        let _ = admitP (exists pi'. tpre_assec' ps ps' pi' x e en_m red_m) in

	ps', en_m, out_m, red_m
      else failwith "Not a valid secure computation request"
    else
      let en_m = update #prin #env #p_cmp p en OrdMap.empty in
      let out_m = update #prin #chan_out #p_cmp p c_out OrdMap.empty in
      let red_m = update #prin #redex #p_cmp p r OrdMap.empty in
      let ps' = singleton p in

      let _ = admitP (exists pi'. tpre_assec' ps ps' pi' x e en_m red_m) in

      ps', en_m, out_m, red_m
  in

  let _ = cut (exists pi'. tpre_assec' ps ps' pi' x e en_m red_m) in

  let _ = assert (Equal (dom #prin #env #p_cmp en_m) (dom #prin #chan_out #p_cmp out_m)) in
  let _ = assert (Equal (dom #prin #env #p_cmp en_m) (dom #prin #redex #p_cmp red_m)) in

  if ps = ps' then
    let c_sec_init = Conf Target (Mode Sec ps) [] (update_env (compose_envs_m ps en_m) x V_unit) (T_exp e) (hide []) in
    let (| c_sec, sstep_h |) = do_sec_comp' c_sec_init in

    let _ = cut (b2t (is_sterminal c_sec)) in
    let _ = admitP (Good sstep_h) in

    //let _ = assert (exists pi_final pi'. sec_comp_prop ps c_sec pi' pi_final) in
    let _ = admitP (exists pi pi_final. tpre_assec' ps ps pi x e en_m red_m /\
                                   sec_comp_prop ps c_sec pi pi_final) in

    let _ = send_output ps ps x e en_m red_m out_m c_sec in
    psmap_ref := OrdMap.remove ps (!psmap_ref)
  else
    psmap_ref := (update ps (Mk_psmap ps ps' en_m out_m red_m x e) (!psmap_ref))

(* (\*     //let _ = create_thread (do_sec_comp ps env_m' out_m' x e) in *\) *)
