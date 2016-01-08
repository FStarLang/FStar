(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.Seq --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi FStar.IO --admit_fsi FStar.String --admit_fsi FStar.Squash --__temp_no_proj  PSemantics --__temp_no_proj SecServer --verify_module SecServer;
    variables:CONTRIB=../../contrib;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti FStar.List.Tot.fst ordset.fsi ordmap.fsi FStar.List.fst FStar.IO.fsti string.fsi prins.fst ast.fst ffibridge.fsi sem.fst psem.fst rtheory.fst $CONTRIB/Platform/fst/Bytes.fst runtime.fsi print.fst ckt.fst $CONTRIB/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst FStar.Crypto.fst interpreter.fst
 --*)

module SecServer

open FStar.Ghost

open FStar.OrdMap
open FStar.OrdSet

open Runtime

open Prins
open AST
open Semantics
open PSemantics
open RuntimeTheory
open Interpreter

open Crypto

type out_map = ordmap prin chan_out p_cmp

(*
 * Data type to accumulate the info for a secure computation as parties keep checking in
 *)
type psmap_v =
  | Mk_psmap:
    ps:prins -> ps':prins{subset ps' ps}
    -> en_m:en_map{forall p.{:pattern (mem p ps')} mem p ps' = contains p en_m}
    -> out_m:out_map{forall p.{:pattern (mem p ps')} mem p ps' = contains p out_m}
    -> red_m:redex_map{forall p.{:pattern (mem p ps')} mem p ps' = contains p red_m}
    -> x:varname
    -> e:exp{exists (pi:tpar ps'). tpre_assec' ps ps' pi x e en_m red_m}
    -> psmap_v

type psmap = ordmap prins psmap_v ps_cmp

(* Forcing instantiation of type variables in extracted OCaml code *)
type psmap_ref_t =
  | Mk_ref: r:ref (ordmap prins psmap_v ps_cmp) -> psmap_ref_t

val r_of_ref: x:psmap_ref_t -> Tot (ref (ordmap prins psmap_v ps_cmp))
let r_of_ref = function
  | Mk_ref r -> r

(* private *)
let psmap_ref = Mk_ref (alloc (OrdMap.empty #prins #psmap_v #ps_cmp))

(* call interpreter step_star on the input config *)
val do_sec_comp':
  c:config -> ML (d:(c':config & (sstep_star c c')){is_sterminal (dfst d)})
let do_sec_comp' c =
  let MkDTuple2 'a 'b c_opt h = step_star c in
  if is_sterminal c_opt then
    let h = h in
    (| c_opt, h |)
  else
    failwith "Secure computation did not end in terminal state"

(* Using non opaque types as patterns is risky *)
opaque type config_prop (ps:prins) (x:varname) (e:exp) (p:prin) (r:redex) (c:config) =
  mem p ps /\ is_R_assec r /\ is_clos (R_assec.v r) /\ R_assec.ps r = ps /\
  MkTuple3._2 (get_en_b (R_assec.v r)) = x /\ MkTuple3._3 (get_en_b (R_assec.v r)) = e /\
  Conf.t c = T_red r /\ Conf.l c = Target /\ Conf.m c = Mode Par (singleton p)

val build_pi:
  ps:prins -> ps':prins{subset ps' ps}
  -> en_m:en_map{forall p.{:pattern (mem p ps')} mem p ps' = contains p en_m}
  -> red_m:redex_map{forall p.{:pattern (mem p ps')} mem p ps' = contains p red_m}
  -> x:varname -> e:exp
  -> p:prin
  -> r:redex
  -> c:config{config_prop ps x e p r c}
  -> pi:tpar ps'{tpre_assec' ps ps' pi x e en_m red_m}
  -> Lemma (requires (True))
          (ensures (exists (pi':tpar (union ps' (singleton p))).
	              {:pattern (tpre_assec' ps (union #prin #p_cmp ps' (singleton p)) pi' x e
	                         (update #prin #env #p_cmp p (MkTuple3._1 (get_en_b (R_assec.v r))) en_m)
	                         (update #prin #redex #p_cmp p r red_m))}
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
  ()

val build_pi_lemma:
  ps:prins -> ps':prins{subset ps' ps}
  -> en_m:en_map{forall p.{:pattern (mem p ps')} mem p ps' = contains p en_m}
  -> red_m:redex_map{forall p.{:pattern (mem p ps')} mem p ps' = contains p red_m}
  -> x:varname -> e:exp
  -> p:prin
  -> r:redex{is_R_assec r /\ is_clos (R_assec.v r) /\ R_assec.ps r = ps /\
            MkTuple3._2 (get_en_b (R_assec.v r)) = x /\
	    MkTuple3._3 (get_en_b (R_assec.v r)) = e}
  -> Lemma (requires (exists (c:config) (pi:tpar ps').
                       config_prop ps x e p r c /\
                       tpre_assec' ps ps' pi x e en_m red_m))
          (ensures (exists (pi':tpar (union ps' (singleton p))).
                      {:pattern (tpre_assec' ps (union #prin #p_cmp ps' (singleton p)) pi' x e
	                                    (update #prin #env #p_cmp p (MkTuple3._1 (get_en_b (R_assec.v r))) en_m)
	                                    (update #prin #redex #p_cmp p r red_m))}
                      tpre_assec' ps (union #prin #p_cmp ps' (singleton p)) pi' x e
	                          (update #prin #env #p_cmp p (MkTuple3._1 (get_en_b (R_assec.v r))) en_m)
	                          (update #prin #redex #p_cmp p r red_m)))
let build_pi_lemma ps ps' en_m red_m x e p r = ()

opaque type Good (#a:Type) (x:a) = True

val get_erased_prop: #a:Type -> #p:(a -> Type) -> e:erased (x:a{p x}) -> Tot (u:unit{p (reveal e)})
let get_erased_prop e = ()

val build_pstep_star:
  ps:prins
  -> en_m:en_map{forall p.{:pattern (mem p ps)} mem p ps = contains p en_m}
  -> red_m:redex_map{forall p.{:pattern (mem p ps)} mem p ps = contains p red_m}
  -> x:varname -> e:exp -> c_sec:config{is_sterminal c_sec}
  -> h:sstep_star (init_sec_conf ps en_m x e) c_sec
  -> pi:tpar ps{tpre_assec' ps ps pi x e en_m red_m}
  -> Lemma (requires (True))
          (ensures (exists (pi_final:protocol ps).{:pattern sec_comp_prop ps c_sec pi pi_final}
	            sec_comp_prop ps c_sec pi pi_final /\
		    tpre_assec' ps ps pi x e en_m red_m))
    [SMTPatT (tpre_assec' ps ps pi x e en_m red_m); SMTPat (is_sterminal c_sec);
     SMTPatT (Good h)]
let build_pstep_star ps en_m red_m x e c_sec h pi =
  let pi_final = create_pstep_star ps en_m red_m x e c_sec h pi in
  get_erased_prop pi_final

opaque type eq_pi_pi' (#a:Type) (#b:Type) (x:a) (y:b) = (EqTyp a b) /\ x = y

val build_pstep_star_lemma:
  ps:prins
  -> en_m:en_map{forall p.{:pattern (mem p ps)} mem p ps = contains p en_m}
  -> red_m:redex_map{forall p.{:pattern (mem p ps)} mem p ps = contains p red_m}
  -> x:varname -> e:exp -> c_sec:config{is_sterminal c_sec}
  -> h:sstep_star (init_sec_conf ps en_m x e) c_sec{Good h}
  -> Lemma (requires (exists (pi:tpar ps). tpre_assec' ps ps pi x e en_m red_m))
          (ensures (forall ps'.{:pattern eq_pi_pi' ps' ps}
	            ps'= ps ==>
		    (exists (pi:tpar ps') (pi_final:protocol ps').
		     {:pattern (sec_comp_prop ps' c_sec pi pi_final)}
	             sec_comp_prop ps' c_sec pi pi_final /\ eq_pi_pi' ps' ps /\
		     tpre_assec' ps' ps' pi x e en_m red_m)))
let build_pstep_star_lemma ps en_m red_m x e c_sec h = ()

val tpre_assec_lemma:
  ps:prins -> pi:tpar ps -> x:varname -> e:exp
  -> en_m:en_map -> red_m:redex_map{tpre_assec' ps ps pi x e en_m red_m}
  -> Lemma (requires (True)) (ensures (tpre_assec #ps (pi, OrdMap.empty #prins #tconfig_sec #ps_cmp)  ps x e))
let tpre_assec_lemma ps pi x e en_m red_m = ()

opaque type server_prop' (p:prin) (r:redex) (ps:prins) (x:varname) (e:exp) (dv:dvalue) =
  (forall ps'.{:pattern (eq_pi_pi' ps' ps)} ps = ps' ==> server_prop p r ps x e dv)

val build_pstep_star_lemma':
  p:prin -> r:redex -> ps:prins -> x:varname -> e:exp -> dv:dvalue
  -> Lemma (requires (server_prop' p r ps x e dv))
          (ensures (server_prop p r ps x e dv))
let build_pstep_star_lemma' p r ps x e dv = cut (eq_pi_pi' ps ps)

val send_output:
  ps':prins
  -> ps:prins{subset ps' ps} -> x:varname -> e:exp
  -> en_m:en_map{forall p.{:pattern (mem p ps)} mem p ps = contains p en_m}
  -> red_m:redex_map{forall p.{:pattern (mem p ps)} mem p ps = contains p red_m}
  -> out_m:out_map{forall p.{:pattern (mem p ps)} mem p ps = contains p out_m}
  -> c_sec:config{is_sterminal c_sec /\
                 (forall ps'.{:pattern (eq_pi_pi' ps' ps)} ps = ps' ==>
		  (exists pi pi_final.{:pattern (sec_comp_prop ps' c_sec pi pi_final)}
		   (tpre_assec' ps' ps' pi x e en_m red_m /\
		    sec_comp_prop ps' c_sec pi pi_final /\
                    server_prop_witness pi pi_final)))}
  -> ML unit
let rec send_output ps' ps x e en_m red_m out_m c_sec =
  let Some p = choose ps' in
  let Some out = select p out_m in
  let Some r = select p red_m in
  let dv = slice_v p (D_v.v (c_value c_sec)) in

  let _ = cut (eq_pi_pi' ps ps) in
  build_pstep_star_lemma' p r ps x e dv;

  (* This is the server property *)
  let _ = assert (server_prop p r ps x e dv) in

  let (m, t) = mac_server_msg p r ps x e dv Interpreter.server_key in
  send out m;
  send out t;

  let ps'_rest = remove p ps' in
  if ps'_rest = empty then ()
  else send_output ps'_rest ps x e en_m red_m out_m c_sec

val build_initial_pi:
  ps:prins -> p:prin{mem p ps} -> x:varname -> e:exp -> r:redex
  -> c:config{config_prop ps x e p r c}
  -> Lemma (requires (True))
          (ensures (exists (pi:tpar (singleton p)).	              
	              {:pattern (tpre_assec' ps (singleton p) pi x e
		                             (update #prin #env #p_cmp p (MkTuple3._1 (get_en_b (R_assec.v r)))
				                     (OrdMap.empty #prin #env #p_cmp))
				             (update #prin #redex #p_cmp p r (OrdMap.empty #prin #redex #p_cmp)))}
	              tpre_assec' ps (singleton p) pi x e
		                  (update #prin #env #p_cmp p (MkTuple3._1 (get_en_b (R_assec.v r)))
				          (OrdMap.empty #prin #env #p_cmp))
				  (update #prin #redex #p_cmp p r (OrdMap.empty #prin #redex #p_cmp))))
    [SMTPatT (config_prop ps x e p r c)]
let build_initial_pi ps p x e r c =
  let pi = update p c (OrdMap.empty #prin #tconfig_par #p_cmp) in
  let _ = cut (tpre_assec' ps (singleton p) pi x e
		           (update #prin #env #p_cmp p (MkTuple3._1 (get_en_b (R_assec.v r)))
				   (OrdMap.empty #prin #env #p_cmp))
	                   (update #prin #redex #p_cmp p r (OrdMap.empty #prin #redex #p_cmp))) in
  ()

val build_initial_pi_lemma:
  ps:prins -> p:prin{mem p ps} -> x:varname -> e:exp
  -> r:redex{is_R_assec r /\ is_clos (R_assec.v r) /\
            R_assec.ps r = ps /\
	    MkTuple3._2 (get_en_b (R_assec.v r)) = x /\
	    MkTuple3._3 (get_en_b (R_assec.v r)) = e}
  -> Lemma (requires (exists (c:config). config_prop ps x e p r c))
          (ensures (exists (pi:tpar (singleton p)).
	              {:pattern (tpre_assec' ps (singleton p) pi x e
		                             (update #prin #env #p_cmp p (MkTuple3._1 (get_en_b (R_assec.v r)))
				                     (OrdMap.empty #prin #env #p_cmp))
				             (update #prin #redex #p_cmp p r (OrdMap.empty #prin #redex #p_cmp)))}
	              tpre_assec' ps (singleton p) pi x e
		                  (update #prin #env #p_cmp p (MkTuple3._1 (get_en_b (R_assec.v r)))
				          (OrdMap.empty #prin #env #p_cmp))
				  (update #prin #redex #p_cmp p r (OrdMap.empty #prin #redex #p_cmp))))
let build_initial_pi_lemma ps p x e r = ()

val handle_connection: chan_in -> chan_out -> ML unit
let handle_connection c_in c_out =
  let c_m = recv c_in in
  let c_t = recv c_in in

  let c_opt = verify_client_msg Interpreter.client_key c_m c_t in
  if c_opt = None then failwith "Failed to verify client's mac"
  else
    let Some (p, r) = c_opt in

    (* This is the client property *)
    let _ = assert (client_prop p r) in
  
    let R_assec #meta ps v = r in
    let (en, x, e) = get_en_b v in

    let psmap_ref = r_of_ref psmap_ref in

    let ps', en_m, out_m, red_m =
      if contains ps !psmap_ref then
        let Some (Mk_psmap ps1 ps' en_m out_m red_m x' e') = select ps !psmap_ref in
        let _ = admitP (b2t (e = e')) in
        if ps = ps1 && x = x' then
	  let _ = build_pi_lemma ps ps' en_m red_m x e p r in
	  
	  let en_m = update #prin #env #p_cmp p en en_m in
	  let out_m = update #prin #chan_out #p_cmp p c_out out_m in
	  let red_m = update #prin #redex #p_cmp p r red_m in

          let ps' = union #prin #p_cmp ps' (singleton p) in
	  ps', en_m, out_m, red_m
        else failwith "Not a valid secure computation request"
      else
        let _ = build_initial_pi_lemma ps p x e r in
        let en_m = update #prin #env #p_cmp p en OrdMap.empty in
        let out_m = update #prin #chan_out #p_cmp p c_out OrdMap.empty in
        let red_m = update #prin #redex #p_cmp p r OrdMap.empty in
        let ps' = singleton p in

        ps', en_m, out_m, red_m
    in
    let _ = cut (forall p.{:pattern (mem p ps')} mem p ps' = contains p en_m) in
    let _ = cut (forall p.{:pattern (mem p ps')} mem p ps' = contains p out_m) in
    let _ = cut (forall p.{:pattern (mem p ps')} mem p ps' = contains p red_m) in

    if ps = ps' then
      let c_sec_init = Conf Target (Mode Sec ps) [] (update_env (compose_envs_m ps en_m) x V_unit) (T_exp e) (hide []) in
      let MkDTuple2 'a 'b c_sec sstep_h = do_sec_comp' c_sec_init in
      let _ = cut (Good sstep_h) in
      build_pstep_star_lemma ps en_m red_m x e c_sec sstep_h;
      
      //let _ = assert (exists pi_final pi'. sec_comp_prop ps c_sec pi' pi_final) in
      let _ = cut (eq_pi_pi' ps ps) in
      let _ = send_output ps ps x e en_m red_m out_m c_sec in
      psmap_ref := OrdMap.remove ps (!psmap_ref)
    else
      psmap_ref := (update ps (Mk_psmap ps ps' en_m out_m red_m x e) (!psmap_ref))

(* (\*     //let _ = create_thread (do_sec_comp ps env_m' out_m' x e) in *\) *)
