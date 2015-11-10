(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Prins --admit_fsi Ffibridge --__temp_no_proj PSemantics --verify_module PSemantics;
    other-files:ghost.fst listTot.fst ordset.fsi ordmap.fsi classical.fst prins.fsi ast.fst ffibridge.fsi sem.fst
 --*)

module PSemantics

open FStar.OrdMap
open FStar.OrdSet

open FStar.Ghost


open Prins
open AST
open Semantics

val is_empty_eq: eprins -> Tot bool
let is_empty_eq eps = eps = empty

val is_empty_eq_lemma: eps:eprins -> Lemma (requires (Equal eps empty))
                                          (ensures (is_empty_eq eps))
		       [SMTPat (is_empty_eq eps)]
let is_empty_eq_lemma eps = ()

type tconfig_par = c:tconfig{Mode.m (Conf.m c) = Par}

type tpar (ps:prins) = m:OrdMap.ordmap prin tconfig_par p_cmp{forall p. mem p ps = contains p m}

type tconfig_sec = c:tconfig{Mode.m (Conf.m c) = Sec}

type tsec =
  m:OrdMap.ordmap prins tconfig_sec ps_cmp{forall ps1 ps2.
                                           (contains ps1 m /\ contains ps2 m /\ not (ps1 = ps2) ==>
                                           is_empty_eq (intersect ps1 ps2))}

//type protocol (ps:prins) = tpar ps * option tconfig_sec
type protocol (ps:prins) = tpar ps * tsec

val mempty: #key:Type -> #value:Type -> #f:cmp key -> Tot (OrdMap.ordmap key value f)
let mempty (#k:Type) (#v:Type) #f = OrdMap.empty #k #v #f

type tpre_assec (#ps':prins) (pi:protocol ps') (ps:prins) (x:varname) (e:exp) =
  not (contains ps (snd pi)) /\
  (forall ps1. contains ps1 (snd pi) ==> is_empty_eq (intersect ps1 ps)) /\
  (forall p. mem p ps ==> (contains p (fst pi) /\
                           Let (Some.v (select p (fst pi)))
                             (fun c ->
                               is_T_red (Conf.t c) /\
                               is_R_assec (T_red.r (Conf.t c)) /\
                               R_assec.ps (T_red.r (Conf.t c)) = ps /\
                               is_clos (R_assec.v (T_red.r (Conf.t c))) /\
                               MkTuple3._2 (get_en_b (R_assec.v (T_red.r (Conf.t c)))) = x /\
                               MkTuple3._3 (get_en_b (R_assec.v (T_red.r (Conf.t c)))) = e)))

opaque val get_env_m:
  #ps':prins -> pi:protocol ps' -> ps:prins{forall p. (mem p ps ==>
                                                       contains p (fst pi) /\
                                                       Let (Some.v (select p (fst pi)))
                                                       (fun c -> is_T_red (Conf.t c) /\
                                                                 is_R_assec (T_red.r (Conf.t c)) /\
                                                                 is_clos (R_assec.v (T_red.r (Conf.t c)))))}
  -> Tot (m:env_map ps{(forall p. (mem p ps ==>
                                   select p m = Some (
                                   MkTuple3._1 (get_en_b (R_assec.v (T_red.r (Conf.t (Some.v (select p (fst pi))))))))) /\
                                  (not (mem p ps) ==> select p m = None))})
     (decreases (size ps))
let rec get_env_m #ps' pi ps =
  let Some p = choose ps in
  let ps_rest = remove p ps in
  let Some (Conf _ _ _ _ (T_red (R_assec _ v)) _) = select p (fst pi) in
  let (en, _, _) = get_en_b v in
  if is_empty ps_rest then update p en mempty
  else
    let m = get_env_m pi ps_rest in
    update p en m

val step_p_to_wait: c:tconfig -> p:prin -> Tot tconfig
let step_p_to_wait c p =
  let Conf l m s en _ tr = c in
  Conf l m ((Frame m en F_assec_ret tr)::s) en T_sec_wait (hide [])

opaque val step_ps_to_wait:
  #ps':prins -> pi:tpar ps' -> ps:prins{forall p. mem p ps ==> contains p pi}
  -> Tot (pi':tpar ps'{forall p. (mem p ps ==>
                                  select p pi' =
                                  Some (step_p_to_wait (Some.v (select p pi)) p)) /\
                                 (not (mem p ps) ==>
                                  select p pi' = select p pi)})
     (decreases (size ps))
let rec step_ps_to_wait #ps' pi ps =
  let Some p = choose ps in
  let ps_rest = remove p ps in
  let c' = step_p_to_wait (Some.v (select p pi)) p in
  if ps_rest = empty then update p c' pi
  else
    let pi' = step_ps_to_wait #ps' pi ps_rest in
    update p c' pi'

val tstep_assec:
  #ps':prins -> pi:protocol ps' -> ps:prins -> x:varname -> e:exp{tpre_assec pi ps x e}
  -> Tot (protocol ps')
let tstep_assec #ps' pi ps x e =
  let env = update_env (compose_envs_m ps (get_env_m pi ps)) x V_unit in
  let tsec = Conf Target (Mode Sec ps) [] env (T_exp e) (hide []) in
  (step_ps_to_wait #ps' (fst pi) ps, update ps tsec (snd pi))

type waiting_config (c:tconfig) =
  is_T_sec_wait (Conf.t c) /\
  is_Cons (Conf.s c) /\
  is_F_assec_ret (Frame.f (Cons.hd (Conf.s c)))

type ps_sec_waiting (#ps':prins) (pi:protocol ps') (ps:prins) =
  (forall p. mem p ps ==> (contains p (fst pi) /\ waiting_config (Some.v (select p (fst pi)))))

type tpre_assec_ret (#ps':prins) (pi:protocol ps') (ps:prins) =
  contains ps (snd pi) /\ (Conf.m (Some.v (select ps (snd pi))) = Mode Sec ps)  /\
  is_value (Some.v (select ps (snd pi))) /\ (Conf.s (Some.v (select ps (snd pi))) = []) /\
  ps_sec_waiting pi ps

val ret_sec_value_to_p: sec_c:tconfig{is_sec sec_c /\ is_value sec_c} -> c:tconfig{waiting_config c}
                        -> p:prin -> Tot tconfig
let ret_sec_value_to_p sec_c c p =
  let Conf l _ ((Frame m en F_assec_ret tr)::s) _ _ _ = c in
  let D_v _ v = c_value sec_c in
  let D_v _ v' = slice_v p v in
  Conf l m s en (T_val v') (concat_traces tr (hide [ Tr_val v' ]))

opaque val ret_sec_value_to_ps:
  #ps':prins -> pi:tpar ps' -> sec_c:tconfig{is_sec sec_c /\ is_value sec_c}
  -> ps:prins{forall p. mem p ps ==> (contains p pi /\ waiting_config (Some.v (select p pi)))}
  -> Tot (pi':tpar ps'{forall p. (mem p ps ==>
                                  select p pi' =
                                  Some (ret_sec_value_to_p sec_c (Some.v (select p pi)) p)) /\
                                 (not (mem p ps) ==>
                                  select p pi' = select p pi)})
     (decreases (size ps))
let rec ret_sec_value_to_ps #ps' pi sec_c ps =
  let Some p = choose ps in
  let ps_rest = remove p ps in
  let c' = ret_sec_value_to_p sec_c (Some.v (select p pi)) p in
  if is_empty ps_rest then update p c' pi
  else
    let pi' = ret_sec_value_to_ps #ps' pi sec_c ps_rest in
    update p c' pi'

type pstep: #ps:prins -> protocol ps -> protocol ps -> Type =

  | P_par:
    #ps:prins -> #c':tconfig_par -> pi:protocol ps
    -> p:prin{contains p (fst pi)}
    -> h:sstep (Some.v (select p (fst pi))) c'
    -> pi':protocol ps{pi' = (update p c' (fst pi), (snd pi))}
    -> pstep #ps pi pi'

  | P_sec:
    #ps':prins -> #c':tconfig_sec -> pi:protocol ps'
    -> ps:prins{contains ps (snd pi)}
    -> h:sstep (Some.v (select ps (snd pi))) c'
    -> pi':protocol ps'{pi' = (fst pi, update ps c' (snd pi))}
    -> pstep #ps' pi pi'

  | P_sec_enter:
    #ps':prins -> pi:protocol ps' -> ps:prins
    -> x:varname -> e:exp{tpre_assec pi ps x e}
    -> pi':protocol ps'{pi' = tstep_assec pi ps x e}
    -> pstep #ps' pi pi'

  | P_sec_exit:
    #ps':prins -> pi:protocol ps' -> ps:prins{tpre_assec_ret pi ps}
    -> pi':protocol ps'{pi' = (ret_sec_value_to_ps #ps' (fst pi) (Some.v (select ps (snd pi))) ps, OrdMap.remove ps (snd pi))}
    -> pstep #ps' pi pi'

type pstep_star: #ps:prins -> protocol ps -> protocol ps -> Type =
  | PS_refl: #ps:prins -> pi:protocol ps -> pstep_star #ps pi pi

  | PS_tran:
    #ps:prins -> #pi:protocol ps -> #pi':protocol ps -> #pi'':protocol ps
    -> h1:pstep #ps pi pi' -> h2:pstep_star #ps pi' pi''
    -> pstep_star #ps pi pi''

type is_sec_comp (c:config) =
  Conf.l c = Target /\
  is_sec c /\ (forall f. FStar.List.Tot.mem f (Conf.s c) ==> Frame.m f = Conf.m c)

val sec_comp_step_same_mode:
  #c:config{is_sec_comp c} -> #c':config -> h:sstep c c'
  -> Lemma (requires (True)) (ensures (Conf.m c = Conf.m c' /\ is_sec_comp c'))
let sec_comp_step_same_mode c c' h = ()

val sec_comp_step_star_same_mode:
  #c:config{is_sec_comp c} -> #c':config -> h:sstep_star c c'
  -> Lemma (requires (True)) (ensures (Conf.m c = Conf.m c' /\ is_sec_comp c')) (decreases h)
let rec sec_comp_step_star_same_mode #c #c' h = match h with
  | SS_refl _     -> ()
  | SS_tran h1 h2 -> sec_comp_step_same_mode h1; sec_comp_step_star_same_mode h2

val singleton_tsec: c:config{is_sec_comp c} -> Tot tsec
let singleton_tsec c = update (Mode.ps (Conf.m c)) c OrdMap.empty

type consistent_ts (ts:tsec) (ps:prins) =
  not (contains ps ts) /\
  (forall ps'. contains ps' ts ==> is_empty_eq (intersect ps ps'))

opaque val sec_sstep_star_to_pstep_star:
  c:config{is_sec_comp c} -> c':config{is_sec_comp c'} -> h:sstep_star c c'
  -> ps:prins -> tp:tpar ps -> ts:tsec{consistent_ts ts (Mode.ps (Conf.m c))}
  -> Tot (pstep_star #ps (tp, update (Mode.ps (Conf.m c)) c ts)
                        (tp, update (Mode.ps (Conf.m c)) c' ts)) (decreases h)
let rec sec_sstep_star_to_pstep_star c c' h ps tp ts = match h with
  | SS_refl _                 -> PS_refl (tp, update (Mode.ps (Conf.m c)) c ts)
  | SS_tran #c #c' #c'' h1 h2 ->
    sec_comp_step_same_mode #c #c' h1;
    sec_comp_step_star_same_mode #c' #c'' h2;
    let pi = (tp, update #prins #tconfig_sec #ps_cmp (Mode.ps (Conf.m c)) c ts) in
    let pi'' = (tp, update #prins #tconfig_sec #ps_cmp (Mode.ps (Conf.m c)) c'' ts) in

    let pi' = (tp, update #prins #tconfig_sec #ps_cmp (Mode.ps (Conf.m c)) c' ts) in
    let ph = P_sec #ps #c' pi (Mode.ps (Conf.m c)) h1 pi' in
    let h' = sec_sstep_star_to_pstep_star c' c'' h2 ps tp ts in
    PS_tran #ps #pi #pi' #pi'' ph h'

opaque val par_sstep_to_pstep_star:
  p:prin -> c:tconfig_par -> c':tconfig_par -> h:sstep c c'
  -> ps:prins{mem p ps} -> tp:tpar ps{Some.v (select p tp) = c} -> ts:tsec
  -> Tot (pstep_star #ps (tp, ts) (update p c' tp, ts))
let par_sstep_to_pstep_star p c c' h ps tp ts =
  let pi' = (update #prin #tconfig_par p c' tp, ts) in
  let ph = P_par #ps #c' (tp, ts) p h pi' in
  PS_tran #ps #(tp, ts) #pi' #pi' ph (PS_refl #ps pi')
