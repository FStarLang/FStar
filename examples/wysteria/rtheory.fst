(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Ffibridge --admit_fsi FStar.Squash --__temp_no_proj  PSemantics;
    other-files:classical.fst ghost.fst squash.fsti listTot.fst ordset.fsi ordmap.fsi prins.fst ast.fst ffibridge.fsi sem.fst psem.fst
 --*)

module RuntimeTheory

open FStar.Ghost

open FStar.OrdMap
open FStar.OrdSet

open Prins
open AST
open Semantics
open PSemantics

type en_map = ordmap prin env p_cmp
type redex_map = ordmap prin redex p_cmp

(*
 * ps    -- parties requires for this secure computation
 * ps'   -- parties already checked-in
 * pi    -- the protocol (mapping p to c) accumulated so far
 * x,e   -- \x.e is the secure computation
 * en_m  -- the map of p |-> env accumulated so far
 * red_m -- the map of p |-> redex accumulated so far
 *)
opaque type tpre_assec' (ps:prins) (ps':prins) (pi:tpar ps') (x:varname) (e:exp) (en_m:en_map) (red_m:redex_map) =
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

(* convert a pi ->* pi' -> pi'' to pi ->* pi'' *)
opaque val pss_ps_to_pss:
  #ps:prins -> #pi:protocol ps -> #pi':protocol ps -> #pi'':protocol ps
  -> h1:pstep_star #ps pi pi' -> h2:pstep #ps pi' pi''
  -> Tot (pstep_star #ps pi pi'') (decreases h1)
let rec pss_ps_to_pss #ps #pi #pi' #pi'' h1 h2 = match h1 with
  | PS_refl _       -> PS_tran h2 (PS_refl pi'')
  | PS_tran h1' h2' ->
    let hh = pss_ps_to_pss h2' h2 in
    PS_tran h1' hh

(* that two protocols pi and pi' differ only in parties' terms *)
opaque type eq_proto' (ps:prins) (pi:tpar ps) (pi':tpar ps) =
  forall p.{:pattern (contains p pi)} contains p pi ==>
       (Let (Some.v (select p pi))
        (fun c ->
	 (Let (Some.v (select p pi'))
	  (fun c' ->
           Conf.l c = Conf.l c' /\
           Conf.m c = Conf.m c' /\
           Conf.s c = Conf.s c' /\
           Conf.en c = Conf.en c'))))

(* that pi contains slice of c's value for each party *)
opaque type final_prop (ps:prins) (pi:tpar ps) (c:config{is_value c}) =
  forall p.{:pattern (contains p pi)} contains p pi ==>
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
opaque type sec_comp_prop (ps:prins) (c:config{is_sterminal c}) (pi:tpar ps) (pi_final:protocol ps) =
  final_prop ps (fst pi_final) c                                           /\
  pstep_star #ps (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp)) pi_final
  //eq_proto' ps pi (fst pi_final)

val init_sec_conf:
  ps:prins -> en_m:en_map{contains_ps ps en_m} -> varname -> exp -> Tot tconfig_sec
let init_sec_conf ps en_m x e =
  Conf Target (Mode Sec ps) [] (update_env (compose_envs_m ps en_m) x V_unit)
       (T_exp e) (hide [])

(*
 * TODO: Writing this proof without binding h makes create_pstep_star proof fast
 * but then extraction fails
 *)
val get_sec_enter_step:
  ps:prins -> en_m:en_map{forall p. mem p ps = contains p en_m}
  -> red_m:redex_map{forall p.mem p ps = contains p red_m}
  -> x:varname -> e:exp
  -> pi:tpar ps{tpre_assec' ps ps pi x e en_m red_m}
  -> Tot (pi_enter:protocol ps{pi_enter = tstep_assec #ps (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp)) ps x e} &
         pstep #ps (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp)) pi_enter)
let get_sec_enter_step ps en_m red_m x e pi =
  let pi_enter = tstep_assec #ps (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp)) ps x e in
  let h = P_sec_enter #ps (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp))
                      ps x e (tstep_assec #ps (pi, (OrdMap.empty #prins #tconfig_sec #ps_cmp)) ps x e) in
  (| pi_enter, h |)

opaque val squash_pstep_star:
  ps:prins -> pi_init:protocol ps -> pi_final:protocol ps
  -> h:pstep_star #ps pi_init pi_final
  -> Tot (u:unit{pstep_star #ps pi_init pi_final})
let squash_pstep_star ps pi_init pi_final h =
  let sq_h = FStar.Squash.return_squash #(pstep_star #ps pi_init pi_final) h in
  FStar.Squash.give_proof #(pstep_star #ps pi_init pi_final) sq_h

opaque val stitch_steps:
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

val create_pstep_star:
  ps:prins -> en_m:en_map{forall p.{:pattern (mem p ps)} mem p ps = contains p en_m}
  -> red_m:redex_map{forall p.{:pattern (mem p ps)} mem p ps = contains p red_m}
  -> x:varname -> e:exp -> c_sec:config{is_sterminal c_sec}
  -> h:sstep_star (init_sec_conf ps en_m x e) c_sec
  -> pi:tpar ps{tpre_assec' ps ps pi x e en_m red_m}
  -> Tot (erased (pi_final:protocol ps{sec_comp_prop ps c_sec pi pi_final}))
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

  //let _ = cut (tpre_assec_ret #ps pi_sec_terminal ps) in

  let pi_final_par = ret_sec_value_to_ps #ps pi_enter_par c_sec ps in
  let pi_final = (pi_final_par, OrdMap.remove ps tsec_terminal) in
  
  (* TODO: FIXME: this also verifies, but with this the whole thing times out *)
  //let _ = cut (eq_proto' ps pi pi_final_par) in

  ret_sec_value_to_ps_helper_lemma #ps pi_enter_par c_sec pi_final_par;

  //let _ = cut (final_prop ps pi_final_par c_sec) in

  let s2 = P_sec_exit #ps pi_sec_terminal ps pi_final in

  (* let h1:pstep_star #ps pi_enter pi_final = pss_ps_to_pss #ps #pi_enter #pi_sec_terminal #pi_final ss s2 in *)

  (* let h2:pstep_star #ps pi_init pi_final = PS_tran #ps #pi_init #pi_enter #pi_final s1 h1 in *)
  let h2 = stitch_steps ps pi_init pi_enter pi_sec_terminal pi_final s1 ss s2 in
  //let _ = admitP (pstep_star #ps pi_init pi_final) in
  squash_pstep_star ps pi_init pi_final h2;
  
  //let _ = admitP (eq_proto' ps pi (fst pi_final)) in
  //let _ = cut (pstep_star #ps pi_init pi_final) in
  hide pi_final
