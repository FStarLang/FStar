(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Prins --admit_fsi FFI --z3timeout 10 --__temp_no_proj;
    other-files:ghost.fst listTot.fst set.fsi ordset.fsi ordmap.fsi constr.fst ext.fst classical.fst prins.fsi ast.fst ffi.fsi sem.fst
 --*)

module Metatheory

open FStar.Ghost
open FStar.List.Tot

open FStar.OrdMap
open FStar.OrdSet

open Prins
open AST
open Semantics

opaque val slice_wire_sps:
  #eps:eprins -> ps:prins -> w:v_wire eps
  -> Tot (r:v_wire (intersect eps ps)
            {forall p. contains p r ==>
                       Some.v (select p r) = (Some.v (select p w))})
     (decreases (size ps))
let rec slice_wire_sps #eps ps w =
  let Some p = choose ps in
  let ps_rest = remove p ps in
  if ps_rest = empty then
    if mem p eps then
      update p (Some.v (select p w)) OrdMap.empty
    else OrdMap.empty
  else
    let w' = slice_wire_sps #eps ps_rest w in
    if mem p eps then
      update p (Some.v (select p w)) w'
    else w'

val slice_v_sps : #meta:v_meta -> prins -> v:value meta
                  -> Tot (r:dvalue{slice_v_meta_inv meta (D_v.meta r)})
                     (decreases %[v])
val slice_en_sps: prins -> en:env
                  -> Tot (varname -> Tot (option dvalue))
                     (decreases %[en])
let rec slice_v_sps #meta ps v =
  let def = D_v meta v in
  let emp = D_v (Meta empty Can_b empty Can_w) V_emp in
  match v with
   | V_const _           -> def

   | V_box ps' v         ->
     let D_v meta' v' =
       if intersect ps' ps = empty then emp
       else slice_v_sps ps v
     in
     D_v (Meta ps' Can_b (Meta.wps meta') Cannot_w) (V_box ps' v')
     
   | V_wire eps m        -> D_v (Meta empty Can_b (intersect eps ps) Cannot_w)
                                (V_wire (intersect eps ps) (slice_wire_sps #eps ps m))

   | V_clos en x e       -> D_v meta (V_clos (slice_en_sps ps en) x e)

   | V_fix_clos en f x e -> D_v meta (V_fix_clos (slice_en_sps ps en) f x e)

   | V_emp_clos _ _      -> def

   | V_emp               -> emp

and slice_en_sps ps en =
 let _ = () in
 fun x -> preceds_axiom en x;
          if en x = None then None
          else
            Some (slice_v_sps ps (D_v.v (Some.v (en x))))

open FStar.FunctionalExtensionality

val slice_emp_en_sps: ps:prins
                      -> Lemma (requires (True))
                               (ensures (slice_en_sps ps empty_env = empty_env))
                         [SMTPat (slice_en_sps ps empty_env)]
let slice_emp_en_sps ps =
  let _ = cut (FEq (slice_en_sps ps empty_env) empty_env) in
  ()

val slice_e_sps: prins -> exp -> Tot exp
let slice_e_sps ps e = e

val slice_vs_sps: prins -> list dvalue -> Tot (list dvalue)
let rec slice_vs_sps ps vs = match vs with
  | []               -> []
  | (D_v meta v)::tl -> (slice_v_sps ps v)::(slice_vs_sps ps tl)

val slice_r_sps: prins -> r:redex{is_sec_redex r} -> Tot redex
let slice_r_sps ps r = match r with
  | R_box ps' v        -> R_box ps' (D_v.v (slice_v_sps ps v))
  | R_assec ps' v      -> R_assec ps' (D_v.v (slice_v_sps ps v))
  | R_unbox v          -> R_unbox (D_v.v (slice_v_sps ps v))
  | R_mkwire v1 v2     -> R_mkwire (D_v.v (slice_v_sps ps v1)) (D_v.v (slice_v_sps ps v2))
  | R_projwire p v     -> R_projwire p (D_v.v (slice_v_sps ps v))
  | R_concatwire v1 v2 -> R_concatwire (D_v.v (slice_v_sps ps v1)) (D_v.v (slice_v_sps ps v2))
  | R_let x v1 e2      -> R_let x (D_v.v (slice_v_sps ps v1)) e2
  | R_app v1 v2        -> R_app (D_v.v (slice_v_sps ps v1)) (D_v.v (slice_v_sps ps v2))
  | R_ffi fn vs        -> R_ffi fn (slice_vs_sps ps vs)
  | R_match v pats     -> R_match (D_v.v (slice_v_sps ps v)) pats

val slice_f'_sps: ps:prins -> f:frame'{is_sec_frame f} -> Tot frame'
let slice_f'_sps ps f = match f with
  | F_box_ps     _    -> f
  | F_box_e      _    -> f
  | F_assec_ps   _    -> f
  | F_assec_e    _    -> f
  | F_assec_ret       -> f
  | F_unbox           -> f
  | F_mkwire_ps  _    -> f
  | F_mkwire_e   v    -> F_mkwire_e (D_v.v (slice_v_sps ps v))
  | F_projwire_p _    -> f
  | F_projwire_e _    -> f
  | F_concatwire_e1 _ -> f
  | F_concatwire_e2 v -> F_concatwire_e2 (D_v.v (slice_v_sps ps v))
  | F_let      _ _    -> f
  | F_app_e1     _    -> f
  | F_app_e2     v    -> F_app_e2  (D_v.v (slice_v_sps ps v))
  | F_ffi fn es vs    -> F_ffi fn es (slice_vs_sps ps vs)
  | F_match      _    -> f

val slice_tr_sps_h: prins -> tr:trace -> Tot trace
let rec slice_tr_sps_h ps tr = match tr with
  | []            -> []
  | (Tr_val v)::tl -> Tr_val (D_v.v (slice_v_sps ps v))::slice_tr_sps_h ps tl
  | _::tl          -> slice_tr_sps_h ps tl // this case never arises

val slice_tr_sps_h_vals_lemma:
  ps:prins -> tr:trace
  -> Lemma (requires (True))
          (ensures (vals_trace_h (slice_tr_sps_h ps tr)))
let rec slice_tr_sps_h_vals_lemma ps tr = match tr with
  | []   -> ()
  | _::tl -> slice_tr_sps_h_vals_lemma ps tl

assume val slice_tr_sps_h_vals_lemma_forall:
  unit -> Lemma (requires (True))
               (ensures (forall ps tr. vals_trace_h (slice_tr_sps_h ps tr)))

val vals_trace_h_vals_trace_lemma:
  tr:erased trace{vals_trace_h (reveal tr)}
  -> Lemma (requires (True)) (ensures (vals_trace tr))
let vals_trace_h_vals_trace_lemma tr = ()

val slice_tr_sps: prins -> tr:erased trace -> Tot (tr':erased trace{vals_trace tr'})
let slice_tr_sps ps tr =
  let tr' = elift1 (slice_tr_sps_h ps) tr in
  slice_tr_sps_h_vals_lemma_forall ();
  let _ = cut (b2t (reveal tr' = slice_tr_sps_h ps (reveal tr))) in
  let _ = cut (b2t (vals_trace_h (reveal tr'))) in
  tr'

val slice_f_sps: ps:prins -> f:frame{Frame.m f = Mode Sec ps /\
                                     is_sec_frame (Frame.f f)}
                 -> Tot frame
let slice_f_sps ps (Frame m en f' tr) = Frame m (slice_en_sps ps en)
                                                (slice_f'_sps ps f')
				      	        (slice_tr_sps ps tr)

val slice_s_sps: ps:prins -> s:stack{stack_inv s (Mode Sec ps) Source}
                 -> Tot (r:stack{stack_target_inv r (Mode Sec ps)})
let rec slice_s_sps ps s = match s with
  | []     -> []
  | hd::tl ->
    if Frame.m hd = Mode Sec ps then
      (slice_f_sps ps hd)::(slice_s_sps ps tl)
    else
      []

val slice_t_sps: ps:prins -> t:term{term_inv t (Mode Sec ps) Source} -> Tot term
let slice_t_sps ps t = match t with
  | T_exp _ -> t
  | T_red r -> T_red (slice_r_sps ps r)
  | T_val v -> T_val (D_v.v (slice_v_sps ps v))

val slice_c_sps: c:sconfig{is_sec c} -> Tot tconfig
let slice_c_sps (Conf _ (Mode Sec ps) s en t tr) =
    Conf Target (Mode Sec ps) (slice_s_sps ps s) (slice_en_sps ps en)
                (slice_t_sps ps t) (slice_tr_sps ps tr)

val env_upd_slice_lemma_ps: #meta:v_meta -> ps:prins -> en:env -> x:varname
                            -> v:value meta
                            -> Lemma (requires (True))
                                     (ensures (slice_en_sps ps (update_env en x v) =
                                               update_env (slice_en_sps ps en) x (D_v.v (slice_v_sps ps v))))
                                     [SMTPat (slice_en_sps ps (update_env en x v))]
let env_upd_slice_lemma_ps #meta ps en x v =
  cut (FEq (slice_en_sps ps (update_env en x v))
      (update_env (slice_en_sps ps en) x (D_v.v (slice_v_sps ps v))))

val env_upd_upd_slice_lemma_ps: #meta1:v_meta -> #meta2:v_meta -> ps:prins
                                -> en:env -> x1:varname -> x2:varname
                                -> v1:value meta1 -> v2:value meta2
                                -> Lemma (requires (True))
                                         (ensures (slice_en_sps ps (update_env #meta2 (update_env #meta1 en x1 v1) x2 v2) =
                                                   update_env #(D_v.meta (slice_v_sps ps v2)) (update_env #(D_v.meta (slice_v_sps ps v1)) (slice_en_sps ps en) x1 (D_v.v (slice_v_sps ps v1))) x2 (D_v.v (slice_v_sps ps v2))))
                                   [SMTPat (slice_en_sps ps (update_env #meta2 (update_env #meta1 en x1 v1) x2 v2))]
let env_upd_upd_slice_lemma_ps #meta1 #meta2 ps en x1 x2 v1 v2 =
  cut (FEq (slice_en_sps ps (update_env #meta2 (update_env #meta1 en x1 v1) x2 v2))
           (update_env #(D_v.meta (slice_v_sps ps v2)) (update_env #(D_v.meta (slice_v_sps ps v1)) (slice_en_sps ps en) x1 (D_v.v (slice_v_sps ps v1))) x2 (D_v.v (slice_v_sps ps v2))))

open FStar.Constructive

val if_exit_sec_then_to_sec: #c:sconfig -> #c':config -> h:sstep c c' -> Tot bool
let if_exit_sec_then_to_sec #c #c' h = not (is_C_assec_ret h) || is_sec c'

val subset_intersect_lemma: ps1:prins -> ps2:prins{subset ps2 ps1}
                            -> Lemma (requires (True))
                                     (ensures (intersect ps2 ps1 = ps2))
                               //[SMTPat (subset ps2 ps1); SMTPat (intersect ps2 ps1)]
let subset_intersect_lemma ps1 ps2 = ()

val meta_empty_can_b_same_slice: v:value (Meta empty Can_b empty Can_w) -> ps:prins
                                 -> Lemma (requires (True))
                                          (ensures (D_v.v (slice_v_sps ps v) = v))
                                    //[SMTPat (slice_v_sps #(empty, Can_b) ps v)]
let meta_empty_can_b_same_slice v ps = ()

val slice_const_wire_sps_lemma:
  ps:prins -> ps'':prins{subset ps'' ps} -> v:value (Meta empty Can_b empty Can_w)
  -> Lemma (requires (True))
           (ensures (slice_wire_sps #ps'' ps (mconst_on ps'' v) =
                     mconst_on ps'' (D_v.v (slice_v_sps ps v))))
     //[SMTPat (slice_wire_sps #ps'' ps (mconst_on ps'' v))]
let slice_const_wire_sps_lemma ps ps'' v = ()

val get_en_b_slice_lemma_ps:
  #meta:v_meta -> v:value meta{is_clos v} -> ps:prins
  -> Lemma (requires (True))
           (ensures (MkTuple3._1 (get_en_b (D_v.v (slice_v_sps ps v))) = slice_en_sps ps (MkTuple3._1 (get_en_b v))))
let get_en_b_slice_lemma_ps #meta v ps = ()

val slice_wire_compose_lemma_ps:
  #eps1:eprins -> #eps2:eprins{intersect eps1 eps2 = empty}
  -> w1:v_wire eps1 -> w2:v_wire eps2 -> ps:prins
  -> Lemma (requires (True))
           (ensures (slice_wire_sps #(union eps1 eps2) ps (compose_wires #eps1 #eps2 w1 w2 eps1) =
                     compose_wires #(intersect eps1 ps) #(intersect eps2 ps)
                                   (slice_wire_sps #eps1 ps w1)
                                   (slice_wire_sps #eps2 ps w2) (intersect eps1 ps)))
let slice_wire_compose_lemma_ps #eps1 #eps2 w1 w2 ps = ()

val de_morgan_intersect_over_union: eps1:eprins -> eps2:eprins -> ps:prins
                                    -> Lemma (requires (True))
                                       (ensures (intersect (union eps1 eps2) ps =
                                                 union (intersect eps1 ps) (intersect eps2 ps)))
let de_morgan_intersect_over_union eps1 eps2 ps = ()

assume val exec_ffi_axiom_ps:
  ps:prins -> fn:string -> vs:list dvalue
  -> Lemma (requires (True))
           (ensures (slice_v_sps ps (D_v.v (FFI.exec_ffi fn vs)) = FFI.exec_ffi fn (slice_vs_sps ps vs)))

(*val valid_ffi_vs_slice_lemma_ps:
  ps:prins -> vs:list dvalue{is_valid_ffi_vs vs}
  -> Lemma (requires (True))
           (ensures (slice_vs_sps ps vs = vs))
let rec valid_ffi_vs_slice_lemma_ps ps vs = match vs with
  | []    -> ()
  | v::tl -> valid_ffi_vs_slice_lemma_ps ps tl*)

val get_next_match_exp_lemma_ps:
  #meta:v_meta -> ps:prins -> pats:list (pat * exp) -> v:value meta
  -> Lemma (requires (True))
           (ensures (get_next_exp pats v = get_next_exp pats (D_v.v (slice_v_sps ps v))))
     (decreases pats)
let rec get_next_match_exp_lemma_ps #meta ps pats v = match pats with
  | []    -> ()
  | _::tl -> get_next_match_exp_lemma_ps #meta ps tl v

val slice_h_append_lemma_sps:
  ps:prins -> tr1:trace -> tr2:trace
  -> Lemma (requires (True))
          (ensures (slice_tr_sps_h ps (append tr1 tr2) = append (slice_tr_sps_h ps tr1) (slice_tr_sps_h ps tr2)))
let rec slice_h_append_lemma_sps ps tr1 tr2 = match tr1 with
  | []   -> ()
  | _::tl -> slice_h_append_lemma_sps ps tl tr2

assume val slice_h_append_lemma_forall_sps:
  unit -> Lemma (requires (True))
               (ensures (forall ps tr1 tr2. slice_tr_sps_h ps (append tr1 tr2) = append (slice_tr_sps_h ps tr1) (slice_tr_sps_h ps tr2)))

val slice_concat_lemma_sps:
  ps:prins -> tr1:erased trace -> tr2:erased trace
  -> Lemma (requires (True))
          (ensures (slice_tr_sps ps (concat_traces tr1 tr2) = concat_traces (slice_tr_sps ps tr1) (slice_tr_sps ps tr2)))
    [SMTPat (slice_tr_sps ps (concat_traces tr1 tr2))]
let slice_concat_lemma_sps ps tr1 tr2 =
  slice_h_append_lemma_forall_sps ();
  let _ = assert (slice_tr_sps_h ps (append (reveal tr1) (reveal tr2)) = append (slice_tr_sps_h ps (reveal tr1)) (slice_tr_sps_h ps (reveal tr2))) in
  ()

(* val slice_flat_lemma: *)
(*   ps:prins -> t:trace *)
(*   -> Lemma (requires (is_flat_trace t)) *)
(*           (ensures (is_flat_trace (slice_tr_sps ps t))) *)
(*     [SMTPat (is_flat_trace (slice_tr_sps ps t))] *)
(* let rec slice_flat_lemma ps t = match t with *)
(*   | []   -> () *)
(*   | _::tl -> slice_flat_lemma ps tl *)

opaque val sstep_sec_slice_lemma: c:sconfig{is_sec c}
                                  -> c':sconfig -> h:sstep c c'{if_exit_sec_then_to_sec h}
                                  -> Tot (cand (u:unit{Conf.m c' = Conf.m c})
                                               (sstep (slice_c_sps c) (slice_c_sps c')))
#set-options "--split_cases 1"
let sstep_sec_slice_lemma c c' h = match h with
  | C_box_ps c c'          -> Conj () (C_box_ps (slice_c_sps c) (slice_c_sps c'))
  | C_unbox c c'           -> Conj () (C_unbox (slice_c_sps c) (slice_c_sps c'))
  | C_mkwire_e1 c c'       -> Conj () (C_mkwire_e1 (slice_c_sps c) (slice_c_sps c'))
  | C_projwire_p c c'      -> Conj () (C_projwire_p (slice_c_sps c) (slice_c_sps c'))
  | C_concatwire_e1 c c'   -> Conj () (C_concatwire_e1 (slice_c_sps c) (slice_c_sps c'))
  | C_const c c'           -> Conj () (C_const (slice_c_sps c) (slice_c_sps c'))
  | C_var c c'             -> Conj () (C_var (slice_c_sps c) (slice_c_sps c'))
  | C_let_e1 c c'          -> Conj () (C_let_e1 (slice_c_sps c) (slice_c_sps c'))
  | C_abs c c'             -> Conj () (C_abs (slice_c_sps c) (slice_c_sps c'))
  | C_fix c c'             -> Conj () (C_fix (slice_c_sps c) (slice_c_sps c'))
  | C_empabs c c'          -> Conj () (C_empabs (slice_c_sps c) (slice_c_sps c'))
  | C_app_e1 c c'          -> Conj () (C_app_e1 (slice_c_sps c) (slice_c_sps c'))
  | C_ffi_e c c'           -> Conj () (C_ffi_e (slice_c_sps c) (slice_c_sps c'))
  | C_match_e c c'         -> Conj () (C_match_e (slice_c_sps c) (slice_c_sps c'))
  | C_box_e c c'           -> Conj () (C_box_e (slice_c_sps c) (slice_c_sps c'))
  | C_mkwire_e2 c c'       -> Conj () (C_mkwire_e2 (slice_c_sps c) (slice_c_sps c'))
  | C_projwire_e c c'      -> Conj () (C_projwire_e (slice_c_sps c) (slice_c_sps c'))
  | C_concatwire_e2 c c'   -> Conj () (C_concatwire_e2 (slice_c_sps c) (slice_c_sps c'))
  | C_app_e2 c c'          -> Conj () (C_app_e2 (slice_c_sps c) (slice_c_sps c'))
  | C_ffi_l c c'           ->
    let Conf l (Mode Sec ps) ((Frame _ _ (F_ffi _ es vs) tr)::_) _ (T_val #meta v) tr' = c in
    let _ = cut (b2t (slice_vs_sps ps ((D_v meta v)::vs) = (slice_v_sps ps v)::(slice_vs_sps ps vs))) in
    Conj () (C_ffi_l (slice_c_sps c) (slice_c_sps c'))

  | C_box_red c c'         -> Conj () (C_box_red (slice_c_sps c) (slice_c_sps c'))
  | C_match_red c c'       -> Conj () (C_match_red (slice_c_sps c) (slice_c_sps c'))
  | C_unbox_red c c'       -> Conj () (C_unbox_red (slice_c_sps c) (slice_c_sps c'))
  | C_mkwire_red c c'      -> Conj () (C_mkwire_red (slice_c_sps c) (slice_c_sps c'))
  | C_projwire_red c c'    -> Conj () (C_projwire_red (slice_c_sps c) (slice_c_sps c'))
  | C_concatwire_red c c'  -> Conj () (C_concatwire_red (slice_c_sps c) (slice_c_sps c'))
  | C_let_red c c'         -> Conj () (C_let_red (slice_c_sps c) (slice_c_sps c'))
  | C_app_red c c'         -> Conj () (C_app_red (slice_c_sps c) (slice_c_sps c'))
  | C_box_beta c c'        -> Conj () (C_box_beta (slice_c_sps c) (slice_c_sps c'))
  | C_let_beta c c'        -> Conj () (C_let_beta (slice_c_sps c) (slice_c_sps c'))
  | C_app_beta c c'        ->
    let Conf _ (Mode Sec ps) _ _ (T_red (R_app v _)) _ = c in
    get_en_b_slice_lemma_ps v ps;
    Conj () (C_app_beta (slice_c_sps c) (slice_c_sps c'))
  | C_ffi_beta c c'        ->
    let Conf _ (Mode Sec ps) _ _ (T_red (R_ffi fn vs)) _ = c in
    //valid_ffi_vs_slice_lemma_ps ps vs;
    exec_ffi_axiom_ps ps fn vs;
    Conj () (C_ffi_beta (slice_c_sps c) (slice_c_sps c'))
  | C_match_beta c c'      ->
    let Conf _ (Mode Sec ps) _ _ (T_red (R_match v pats)) _ = c in
    get_next_match_exp_lemma_ps ps pats v;
    Conj () (C_match_beta (slice_c_sps c) (slice_c_sps c'))
  | C_unbox_beta c c'      -> Conj () (C_unbox_beta (slice_c_sps c) (slice_c_sps c'))
  | C_mkwire_beta c c'     ->
    let Conf _ (Mode _ ps) _ _ (T_red (R_mkwire (V_const (C_prins ps')) v)) _ = c in
    subset_intersect_lemma ps ps';
    meta_empty_can_b_same_slice v ps;
    slice_const_wire_sps_lemma ps ps' v;
    Conj () (C_mkwire_beta (slice_c_sps c) (slice_c_sps c'))
  | C_projwire_beta c c'   ->
    let Conf _ (Mode Sec ps) _ _ (T_red (R_projwire p (V_wire eps _))) _ = c in
    let _ = cut (b2t (mem p (intersect eps ps))) in
    Conj () (C_projwire_beta (slice_c_sps c) (slice_c_sps c'))
  | C_concatwire_beta c c' ->
    let Conf _ (Mode _ ps) _ _ (T_red (R_concatwire (V_wire eps1 w1) (V_wire eps2 w2))) _ = c in
    de_morgan_intersect_over_union eps1 eps2 ps;
    slice_wire_compose_lemma_ps #eps1 #eps2 w1 w2 ps;
    Conj () (C_concatwire_beta (slice_c_sps c) (slice_c_sps c'))
  | C_assec_ps c c'        -> Conj () (C_assec_ps (slice_c_sps c) (slice_c_sps c'))
  | C_assec_e c c'         -> Conj () (C_assec_e (slice_c_sps c) (slice_c_sps c'))
  | C_assec_red c c'       -> Conj () (C_assec_red (slice_c_sps c) (slice_c_sps c'))
  | C_assec_beta c c'      ->
    let Conf _ (Mode Sec ps) _ _ (T_red (R_assec _ v)) _ = c in
    get_en_b_slice_lemma_ps v ps;
    Conj () (C_assec_beta (slice_c_sps c) (slice_c_sps c'))
  | C_assec_ret c c'       -> Conj () (C_assec_ret (slice_c_sps c) (slice_c_sps c'))

#reset-options
(**********)

val slice_emp_en: p:prin
                  -> Lemma (requires (True))
                           (ensures (slice_en p empty_env = empty_env))
                           [SMTPat (slice_en p empty_env)]
 let slice_emp_en p =
  let _ = cut (FEq (slice_en p empty_env) empty_env) in
  ()

val slice_emp_en_forall: unit -> Lemma (requires (True))
                                       (ensures (forall p. slice_en p empty_env = empty_env))
let slice_emp_en_forall _ = admit ()
  (* TODO: FIXME: because of SMTPat in slice_emp_en, this doesn't work *)
  //forall_intro #prin #(fun x -> b2t (slice_en x empty_env = empty_env)) slice_emp_en

val slice_e: prin -> exp -> Tot exp
let slice_e p e = e

val slice_vs: prin -> list dvalue -> Tot (list dvalue)
let rec slice_vs p vs = match vs with
  | []               -> []
  | (D_v meta v)::tl -> (slice_v p v)::(slice_vs p tl)

val slice_r: prin -> redex -> Tot redex
let slice_r p r = match r with
  | R_aspar ps v       -> R_aspar ps (D_v.v (slice_v p v))
  | R_assec ps v       -> R_assec ps (D_v.v (slice_v p v))
  | R_box ps v         -> R_box ps (D_v.v (slice_v p v))
  | R_unbox v          -> R_unbox (D_v.v (slice_v p v))
  | R_mkwire v1 v2     -> R_mkwire (D_v.v (slice_v p v1)) (D_v.v (slice_v p v2))
  | R_projwire p' v    -> R_projwire p' (D_v.v (slice_v p v))
  | R_concatwire v1 v2 -> R_concatwire (D_v.v (slice_v p v1)) (D_v.v (slice_v p v2))
  | R_let x v1 e2      -> R_let x (D_v.v (slice_v p v1)) e2
  | R_app v1 v2        -> R_app (D_v.v (slice_v p v1)) (D_v.v (slice_v p v2))
  | R_ffi fn vs        -> R_ffi fn (slice_vs p vs)
  | R_match v pats     -> R_match (D_v.v (slice_v p v)) pats

val slice_f': p:prin -> f:frame' -> Tot frame'
let slice_f' p f = match f with
  | F_aspar_ps      _ -> f
  | F_aspar_e       _ -> f
  | F_box_ps        _ -> f
  | F_box_e         _ -> f
  | F_assec_ps      _ -> f
  | F_assec_e       _ -> f
  | F_assec_ret       -> f
  | F_aspar_ret     _ -> f
  | F_unbox           -> f
  | F_mkwire_ps     _ -> f
  | F_mkwire_e      v -> F_mkwire_e (D_v.v (slice_v p v))
  | F_projwire_p    _ -> f
  | F_projwire_e    _ -> f
  | F_concatwire_e1 _ -> f
  | F_concatwire_e2 v -> F_concatwire_e2  (D_v.v (slice_v p v))
  | F_let         _ _ -> f
  | F_app_e1        _ -> f
  | F_app_e2        v -> F_app_e2  (D_v.v (slice_v p v))
  | F_ffi    fn es vs -> F_ffi fn es (slice_vs p vs)
  | F_match         _ -> f

val slice_tr_h: prin -> trace -> Tot trace
let rec slice_tr_h p = function
  | []                -> []
  | (Tr_val v)::tl       -> (Tr_val (D_v.v (slice_v p v)))::slice_tr_h p tl
  | (Tr_scope ps tr)::tl ->
    let tr' = if mem p ps then slice_tr_h p tr else [] in
    append tr' (slice_tr_h p tl)

val slice_tr: prin -> erased trace -> Tot (erased trace)
let slice_tr p tr = elift1 (slice_tr_h p) tr

val slice_f: p:prin -> f:frame{Mode.m (Frame.m f) = Par    /\
                               mem p (Mode.ps (Frame.m f))}
                    -> Tot frame
let slice_f p (Frame _ en f tr) = Frame (Mode Par (singleton p)) (slice_en p en)
                                        (slice_f' p f) (slice_tr p tr)

val slice_s: p:prin -> s:stack
             -> Tot (r:stack{stack_target_inv r (Mode Par (singleton p))})
let rec slice_s p s = match s with
  | []     -> []
  | hd::tl ->
    if Mode.m (Frame.m hd) = Par    &&
       mem p (Mode.ps (Frame.m hd))
     then
      (slice_f p hd)::(slice_s p tl)
    else
      slice_s p tl

val slice_t: p:prin -> t:term{not (t = T_sec_wait)} -> Tot term
let slice_t p t = match t with
  | T_val v -> T_val (D_v.v (slice_v p v))
  | T_exp e -> t
  | T_red r -> T_red (slice_r p r)

val get_sec_ret_env: m:mode{Mode.m m = Sec} -> s:stack{stack_source_inv s m}
                     -> Tot env
let rec get_sec_ret_env m (Cons (Frame m' en _ _) tl) =
  if Mode.m m' = Par then en else get_sec_ret_env m tl

val slice_c: prin -> sconfig -> Tot tconfig
let rec slice_c p (Conf Source (Mode as_m ps) s en t tr) =
  let en', t', tr' =
    if not (mem p ps) then empty_env, T_val V_emp, hide []
    else
      if as_m = Par then slice_en p en, slice_t p t, slice_tr p tr
      else slice_en p (get_sec_ret_env (Mode as_m ps) s), T_sec_wait, hide []
  in
  Conf Target (Mode Par (singleton p)) (slice_s p s) en' t' tr'

(**********)

open FStar.Classical

val slice_lem_singl_wire: #eps:eprins -> w:v_wire eps -> p:prin
                          -> Lemma (requires (True))
                                   (ensures (slice_wire #eps p w =
                                             slice_wire_sps #eps (singleton p) w))
let slice_lem_singl_wire #eps w p = ()

val slice_lem_singl_v: #m:v_meta -> v:value m -> p:prin
                      -> Lemma (requires (True))
                               (ensures (slice_v p v =
                                         slice_v_sps (singleton p) v))
                         (decreases %[v])
val slice_lem_singl_en_x: en:env -> p:prin -> x:varname
                          -> Lemma (requires (True))
                                   (ensures ((slice_en p en) x =
                                             (slice_en_sps (singleton p) en) x))
                            (decreases %[en; 0])
val slice_lem_singl_en: en:env -> p:prin
                        -> Lemma (requires (True))
                                 (ensures (slice_en p en =
                                           slice_en_sps (singleton p) en))
                          (decreases %[en; 1])
let rec slice_lem_singl_v #m v p = match v with
  | V_const _           -> ()
  | V_box ps v          -> if mem p ps then slice_lem_singl_v v p else ()
  | V_wire eps w        -> slice_lem_singl_wire #eps w p
  | V_clos en _ _       -> slice_lem_singl_en en p
  | V_fix_clos en _ _ _ -> slice_lem_singl_en en p
  | V_emp_clos _ _      -> ()
  | V_emp               -> ()

and slice_lem_singl_en_x en p x =
  if en x = None then ()
  else (preceds_axiom en x; slice_lem_singl_v (D_v.v (Some.v (en x))) p)

and slice_lem_singl_en en p =
  forall_intro #varname #(fun x -> b2t ((slice_en p en) x =
                                        (slice_en_sps (singleton p) en) x))
                        (slice_lem_singl_en_x en p);
  let _ = cut (FEq (slice_en p en) (slice_en_sps (singleton p) en)) in
  ()

val boxed_wire_slice_lem: ps1:prins -> ps2:prins{not (intersect ps1 ps2 = empty)}
                          -> eps:eprins{subset eps ps2} -> w:v_wire eps
                          -> Lemma (requires (True))
                                   (ensures (slice_wire_sps #eps ps1 w =
                                            (slice_wire_sps #eps (intersect ps1 ps2) w)))
let boxed_wire_slice_lem ps1 ps2 eps w = if intersect eps ps1 = empty then () else ()

val boxed_wire_value_slice_lem:
  ps1:prins -> ps2:prins{not (intersect ps1 ps2 = empty)}
  -> eps:eprins{subset eps ps2} -> w:v_wire eps
  -> Lemma (requires (True))
           (ensures (slice_v_sps #(Meta empty Can_b eps Cannot_w) ps1 (V_wire eps w) =
                    (slice_v_sps #(Meta empty Can_b eps Cannot_w) (intersect ps1 ps2) (V_wire eps w))))
let boxed_wire_value_slice_lem ps1 ps2 eps w =
  if intersect eps ps1 = empty then
    let _ = cut (b2t (intersect eps ps1 = intersect eps (intersect ps1 ps2))) in
    boxed_wire_slice_lem ps1 ps2 eps w;
    ()
  else
    let _ = cut (b2t (intersect eps ps1 = intersect eps (intersect ps1 ps2))) in
    boxed_wire_slice_lem ps1 ps2 eps w;
    ()

val box_slice_lem: #m:v_meta -> v:value m
                   -> ps1:prins -> ps2:prins{not (intersect ps1 ps2 = empty) /\
                                             subset (Meta.vps m) ps2 /\
                                             subset (Meta.wps m) ps2 /\
                                             Meta.cb m = Can_b}
                   -> Lemma (requires (True))
                            (ensures (slice_v_sps ps1 (V_box ps2 v) =
                                      slice_v_sps (intersect ps1 ps2) (V_box ps2 v)))
                      (decreases v)
let rec box_slice_lem #m v ps1 ps2 = match v with
  | V_const _        -> ()
  | V_box #m' ps' v' ->
    let _ = cut (b2t (subset ps' ps2)) in
    if intersect ps1 ps' = empty then ()
    else
      let _ = cut (b2t (intersect ps1 ps' = intersect (intersect ps1 ps2) ps')) in
      box_slice_lem v' ps1 ps';
      box_slice_lem v' (intersect ps1 ps2) ps';
      ()
  | V_wire eps w     ->
    let _ = cut (b2t (subset eps ps2)) in
    boxed_wire_value_slice_lem ps1 ps2 eps w    
  | V_emp_clos _ _   -> ()
  | V_emp            -> ()

val de_morgan_union_over_intersect:
  eps:eprins -> ps1:prins -> ps2:prins
  -> Lemma (requires (True))
           (ensures (union (intersect eps ps1) (intersect eps ps2) =
                     intersect eps (union ps1 ps2)))
let de_morgan_union_over_intersect eps ps1 ps2 = ()

val slc_wire_lem_ps: #eps:eprins -> w:v_wire eps -> p:prin -> ps:prins{not (mem p ps)}
                     -> Lemma (requires (True))
                              (ensures (compose_wires #(intersect eps (singleton p))
                                                      #(intersect eps ps)
                                                      (slice_wire #eps p w)
                                                      (slice_wire_sps #eps ps w)
                                                      (intersect eps (singleton p)) =
                                        slice_wire_sps #eps (union (singleton p) ps) w))
let slc_wire_lem_ps #eps w p ps = ()

val slc_v_lem_ps: #m:v_meta -> v:value m -> p:prin -> ps:prins{not (mem p ps)}
                       -> Lemma (requires (True))
                                (ensures (compose_vals (D_v.v (slice_v p v))
                                                       (D_v.v (slice_v_sps ps v)) =
                                          slice_v_sps (union (singleton p) ps) v))
                          (decreases %[v])
val slc_en_x_lem_ps: en:env -> p:prin -> ps:prins{not (mem p ps)} -> x:varname
                     -> Lemma (requires (True))
                              (ensures ((compose_envs (slice_en p en)
                                                      (slice_en_sps ps en)) x
                                        = (slice_en_sps (union (singleton p) ps) en) x))
                        (decreases %[en; 0])
val slc_en_lem_ps: en:env -> p:prin -> ps:prins{not (mem p ps)}
                     -> Lemma (requires (True))
                              (ensures (compose_envs (slice_en p en)
                                                     (slice_en_sps ps en)
                                        = slice_en_sps (union (singleton p) ps) en))
                        (decreases %[en; 1])
let rec slc_v_lem_ps #m v p ps = match v with
  | V_const _           -> ()

  | V_box ps' v'        ->
    let psp = singleton p in
    if mem p ps' && not (intersect ps ps' = empty) then
      slc_v_lem_ps v' p ps
    else if mem p ps' && intersect ps ps' = empty then
      //let _ = cut (forall p. mem p (union psp ps) = mem p psp || mem p ps) in
      let _ = cut (forall p. not (mem p (intersect ps ps'))) in
      let _ = cut (forall p. mem p (intersect (union psp ps) ps') = mem p psp) in
      let _ = OrdSet.eq_lemma (intersect (union psp ps) ps') psp in

      box_slice_lem v' (union psp ps) ps';
      slice_lem_singl_v v' p;
      ()
    else if not (mem p ps') && not (intersect ps ps' = empty) then
      //let _ = cut (forall p. mem p (union psp ps) = mem p psp || mem p ps) in
      let _ = cut (forall p. not (mem p (intersect psp ps'))) in
      let _ = cut (forall p. mem p (intersect (union psp ps) ps') = mem p (intersect ps ps')) in
      let _ = OrdSet.eq_lemma (intersect (union psp ps) ps') (intersect ps ps') in

      box_slice_lem v' (union (singleton p) ps) ps';
      box_slice_lem v' ps ps';
      ()
    else
      //let _ = cut (forall p. mem p (union psp ps) = mem p psp || mem p ps) in
      let _ = cut (forall p. not (mem p (intersect psp ps'))) in
      let _ = cut (forall p. not (mem p (intersect ps ps'))) in
      let _ = cut (forall p. not (mem p (intersect (union psp ps) ps'))) in
      let _ = OrdSet.eq_lemma (intersect (union psp ps) ps') empty in

      ()
  | V_wire eps w        ->
    de_morgan_union_over_intersect eps (singleton p) ps; slc_wire_lem_ps #eps w p ps
  | V_clos en _ _       -> slc_en_lem_ps en p ps
  | V_fix_clos en _ _ _ -> slc_en_lem_ps en p ps
  | V_emp_clos _ _      -> ()
  | V_emp               -> ()

and slc_en_x_lem_ps en p ps x =
  if en x = None then ()
  else (preceds_axiom en x; slc_v_lem_ps (D_v.v (Some.v (en x))) p ps)

and slc_en_lem_ps en p ps =
  forall_intro #varname #(fun x -> b2t ((compose_envs (slice_en p en)
                                                      (slice_en_sps ps en)) x
                                         = (slice_en_sps (union (singleton p) ps) en) x))
                        (slc_en_x_lem_ps en p ps);
  let _ = cut (FEq (compose_envs (slice_en p en) (slice_en_sps ps en))
                   (slice_en_sps (union (singleton p) ps) en)) in
  ()

val mempty: #key:Type -> #value:Type -> #f:cmp key -> Tot (OrdMap.ordmap key value f)
let mempty (#k:Type) (#v:Type) #f = OrdMap.empty #k #v #f

val slc_v_lem_m: #meta:v_meta -> v:value meta -> ps:prins
                 -> m:value_map ps{(forall p. mem p ps ==>
                                              (Some.v (select p m) = slice_v p v))}
                 -> Lemma (requires (True))
                          (ensures (compose_vals_m ps m = slice_v_sps ps v))
                    (decreases (size ps))
let rec slc_v_lem_m #meta v ps m =
  let Some p = choose ps in
  let Some (D_v meta' v') = select p m in
  let ps_rest = remove p ps in
  if ps_rest = empty then
    let _ = cut (b2t (ps = singleton p)) in
    slice_lem_singl_v v p
  else
    let _ = cut (b2t (ps = union (singleton p) ps_rest)) in
    slc_v_lem_m v ps_rest m; slc_v_lem_ps v p ps_rest

val slc_en_lem_m: en:env -> ps:prins
                  -> m:env_map ps{(forall p. mem p ps ==>
                                             (Some.v (select p m) = slice_en p en))}
                  -> Lemma (requires (True))
                           (ensures (compose_envs_m ps m = slice_en_sps ps en))
                     (decreases (size ps))
let rec slc_en_lem_m en ps m =
let Some p = choose ps in
let Some en' = select p m in
let ps_rest = remove p ps in
if ps_rest = empty then
  let _ = cut (b2t (ps = singleton p)) in
  slice_lem_singl_en en p
else
  let _ = cut (b2t (ps = union (singleton p) ps_rest)) in
  slc_en_lem_m en ps_rest m; slc_en_lem_ps en p ps_rest

val env_upd_slice_lemma: #m:v_meta -> p:prin -> en:env -> x:varname -> v:value m
                         -> Lemma (requires (True))
                                  (ensures (slice_en p (update_env en x v) =
                                            update_env (slice_en p en) x (D_v.v (slice_v p v))))
                            [SMTPat (slice_en p (update_env en x v))]
let env_upd_slice_lemma #m p en x v =
  cut (FEq (slice_en p (update_env en x v))
      (update_env (slice_en p en) x (D_v.v (slice_v p v))))

val env_upd_upd_slice_lemma: #meta1:v_meta -> #meta2:v_meta -> p:prin
                             -> en:env -> x1:varname -> x2:varname
                             -> v1:value meta1 -> v2:value meta2
                             -> Lemma (requires (True))
                                      (ensures (slice_en p (update_env #meta2 (update_env #meta1 en x1 v1) x2 v2) =
                                                update_env #(D_v.meta (slice_v p v2)) (update_env #(D_v.meta (slice_v p v1)) (slice_en p en) x1 (D_v.v (slice_v p v1))) x2 (D_v.v (slice_v p v2))))
                                [SMTPat (slice_en p (update_env #meta2 (update_env #meta1 en x1 v1) x2 v2))]
let env_upd_upd_slice_lemma #meta1 #meta2 p en x1 x2 v1 v2 =
  cut (FEq (slice_en p (update_env #meta2 (update_env #meta1 en x1 v1) x2 v2))
           (update_env #(D_v.meta (slice_v p v2)) (update_env #(D_v.meta (slice_v p v1)) (slice_en p en) x1 (D_v.v (slice_v p v1))) x2 (D_v.v (slice_v p v2))))

val if_enter_sec_then_from_sec: #c:sconfig -> #c':sconfig -> h:sstep c c' -> Tot bool
let if_enter_sec_then_from_sec #c #c' h = not (is_C_assec_beta h) || is_sec c

val slice_wire_p_lemma_mem:
  p:prin -> ps:prins{mem p ps} -> v:value (Meta empty Can_b empty Can_w)
  -> Lemma (requires (True))
           (ensures (slice_wire #ps p (mconst_on ps v) =
                     mconst_on (singleton p) (D_v.v (slice_v p v))))
     //[SMTPat (slice_wire #ps p (mconst_on ps v))]
let slice_wire_p_lemma_mem p ps v = ()

val slice_wire_p_lemma_not_mem:
  p:prin -> ps:prins{not (mem p ps)} -> v:value (Meta empty Can_b empty Can_w)
  -> Lemma (requires (True))
           (ensures (slice_wire #ps p (mconst_on ps v) = OrdMap.empty))
     //[SMTPat (slice_wire #ps p (mconst_on ps v))]
let slice_wire_p_lemma_not_mem p ps v = ()

val mem_intersect_lemma_not_mem: p:prin -> eps:eprins{not (mem p eps)}
                             -> Lemma (requires (True))
                                      (ensures (intersect eps (singleton p) = empty))
                                //[SMTPat (not (mem p eps)); SMTPat (intersect eps (singleton p))]
let mem_intersect_lemma_not_mem p eps = ()

val mem_intersect_lemma_mem: p:prin -> eps:eprins{mem p eps}
                             -> Lemma (requires (True))
                                      (ensures (intersect eps (singleton p) = singleton p))
                                //[SMTPat (mem p eps); SMTPat (intersect eps (singleton p))]
let mem_intersect_lemma_mem p eps = ()

val get_en_b_slice_lemma:
  #meta:v_meta -> v:value meta{is_clos v} -> p:prin
  -> Lemma (requires (True))
           (ensures (MkTuple3._1 (get_en_b (D_v.v (slice_v p v))) = slice_en p (MkTuple3._1 (get_en_b v))))
let get_en_b_slice_lemma #meta v p = ()

val slice_wire_compose_lemma:
  #eps1:eprins -> #eps2:eprins{intersect eps1 eps2 = empty}
  -> w1:v_wire eps1 -> w2:v_wire eps2 -> p:prin
  -> Lemma (requires (True))
           (ensures (slice_wire #(union eps1 eps2) p (compose_wires #eps1 #eps2 w1 w2 eps1) =
                     compose_wires #(intersect eps1 (singleton p)) #(intersect eps2 (singleton p))
                                   (slice_wire #eps1 p w1)
                                   (slice_wire #eps2 p w2) (intersect eps1 (singleton p))))
let slice_wire_compose_lemma #eps1 #eps2 w1 w2 p = ()

assume val exec_ffi_axiom:
  p:prin -> fn:string -> vs:list dvalue
  -> Lemma (requires (True))
           (ensures (slice_v p (D_v.v (FFI.exec_ffi fn vs)) = FFI.exec_ffi fn (slice_vs p vs)))

(*val valid_ffi_vs_slice_lemma:
  p:prin -> vs:list dvalue{is_valid_ffi_vs vs}
  -> Lemma (requires (True))
           (ensures (slice_vs p vs = vs))
let rec valid_ffi_vs_slice_lemma p vs = match vs with
  | []    -> ()
  | v::tl -> valid_ffi_vs_slice_lemma p tl*)

val get_next_match_exp_lemma:
  #meta:v_meta -> p:prin -> pats:list (pat * exp) -> v:value meta
  -> Lemma (requires (True))
           (ensures (get_next_exp pats v = get_next_exp pats (D_v.v (slice_v p v))))
     (decreases pats)
let rec get_next_match_exp_lemma #meta p pats v = match pats with
  | []    -> ()
  | _::tl -> get_next_match_exp_lemma #meta p tl v

val append_assoc: l1:list 'a -> l2:list 'a -> l3:list 'a ->
  Lemma (requires True)
        (ensures ((append l1 (append l2 l3)) = (append (append l1 l2) l3)))
let rec append_assoc l1 l2 l3 = match l1 with
    | [] -> ()
    | hd::tl -> append_assoc tl l2 l3

val slice_h_append_lemma:
  p:prin -> tr1:trace -> tr2:trace
  -> Lemma (requires (True))
          (ensures (slice_tr_h p (append tr1 tr2) = append (slice_tr_h p tr1) (slice_tr_h p tr2)))
let rec slice_h_append_lemma p tr1 tr2 = match tr1 with
  | []                  -> ()
  | (Tr_val _)::tl       -> slice_h_append_lemma p tl tr2
  | (Tr_scope ps tr)::tl ->
    if mem p ps then
      let _ = slice_h_append_lemma p tl tr2 in
      let _ = append_assoc (slice_tr_h p tr) (slice_tr_h p tl) (slice_tr_h p tr2) in
      ()
    else
      slice_h_append_lemma p tl tr2

assume val slice_h_append_lemma_forall:
  unit -> Lemma (requires (True))
               (ensures (forall p tr1 tr2. slice_tr_h p (append tr1 tr2) = append (slice_tr_h p tr1) (slice_tr_h p tr2)))

val slice_concat_lemma:
  p:prin -> tr1:erased trace -> tr2:erased trace
  -> Lemma (requires (True))
          (ensures (slice_tr p (concat_traces tr1 tr2) = concat_traces (slice_tr p tr1) (slice_tr p tr2)))
    [SMTPat (slice_tr p (concat_traces tr1 tr2))]
let slice_concat_lemma p tr1 tr2 =
  slice_h_append_lemma_forall ();
  let _ = assert (slice_tr_h p (append (reveal tr1) (reveal tr2)) = append (slice_tr_h p (reveal tr1)) (slice_tr_h p (reveal tr2))) in
  ()

val append_l_nil: l:list 'a ->
  Lemma (requires True)
        (ensures (append l [] = l))
let rec append_l_nil = function
  | [] -> ()
  | hd::tl -> append_l_nil tl

val scoped_trace_mem_slice_lemma_h:
  p:prin -> ps:prins{mem p ps} -> tr:trace
  -> Lemma (requires (True))
          (ensures (slice_tr_h p [ Tr_scope ps tr] = slice_tr_h p tr))
let scoped_trace_mem_slice_lemma_h p ps tr = append_l_nil (slice_tr_h p tr)

assume val scoped_trace_mem_slice_lemma_forall_h:
  unit ->
  Lemma (requires (True))
        (ensures (forall p ps tr. mem p ps ==> slice_tr_h p [ Tr_scope ps tr] = slice_tr_h p tr))

val scoped_trace_mem_slice_lemma:
  p:prin -> ps:prins{mem p ps} -> tr:erased trace
  -> Lemma (requires (True))
          (ensures (slice_tr p (hide ([ Tr_scope ps (reveal tr) ])) = slice_tr p tr))
let scoped_trace_mem_slice_lemma p ps tr =
  scoped_trace_mem_slice_lemma_forall_h ()

val scoped_trace_not_mem_slice_lemma_h:
  p:prin -> ps:prins{not (mem p ps)} -> tr:trace
  -> Lemma (requires (True))
          (ensures (slice_tr_h p [ Tr_scope ps tr ] = []))
let scoped_trace_not_mem_slice_lemma_h p ps tr = append_l_nil []	  

assume val scoped_trace_not_mem_slice_lemma_forall_h:
  unit ->
  Lemma (requires (True))
        (ensures (forall p (ps:prins) tr. not (mem p ps) ==> slice_tr_h p [ Tr_scope ps tr] = []))

val scoped_trace_not_mem_slice_lemma:
  p:prin -> ps:prins{not (mem p ps)} -> tr:erased trace
  -> Lemma (requires (True))
          (ensures (slice_tr p (hide ([ Tr_scope ps (reveal tr) ])) = hide []))
let scoped_trace_not_mem_slice_lemma p ps tr =
  scoped_trace_not_mem_slice_lemma_forall_h ()

opaque val sstep_par_slice_lemma: c:sconfig -> c':sconfig
                                  -> h:sstep c c'{if_enter_sec_then_from_sec h /\
                                                  if_exit_sec_then_to_sec h}
                                  -> p:prin
                                  -> Tot (cor (u:unit{slice_c p c = slice_c p c'})
                                         (sstep (slice_c p c) (slice_c p c')))
#set-options "--split_cases 1"
let sstep_par_slice_lemma c c' h p =
  (* TODO: FIXME: wanted to write this, but does not split then *)
  (*if is_sec c then IntroL ()
  else*)
  match h with
    | C_aspar_ps (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_aspar_ps (slice_c p c) (slice_c p c'))
    | C_box_ps (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_box_ps (slice_c p c) (slice_c p c'))
    | C_unbox (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_unbox (slice_c p c) (slice_c p c'))
    | C_mkwire_e1 (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_mkwire_e1 (slice_c p c) (slice_c p c'))
    | C_projwire_p (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_projwire_p (slice_c p c) (slice_c p c'))
    | C_concatwire_e1 (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_concatwire_e1 (slice_c p c) (slice_c p c'))
    | C_const (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_const (slice_c p c) (slice_c p c'))
    | C_var (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_var (slice_c p c) (slice_c p c'))
    | C_let_e1 (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_let_e1 (slice_c p c) (slice_c p c'))
    | C_abs (Conf _ m _ en _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_abs (slice_c p c) (slice_c p c'))
    | C_fix (Conf _ m _ en _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_fix (slice_c p c) (slice_c p c'))
    | C_empabs (Conf _ m _ en _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_empabs (slice_c p c) (slice_c p c'))
    | C_app_e1 (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_app_e1 (slice_c p c) (slice_c p c'))
    | C_ffi_e (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_ffi_e (slice_c p c) (slice_c p c'))
    | C_match_e (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_match_e (slice_c p c) (slice_c p c'))
    | C_aspar_e (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_aspar_e (slice_c p c) (slice_c p c'))
    | C_box_e (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_box_e (slice_c p c) (slice_c p c'))
    | C_mkwire_e2 (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_mkwire_e2 (slice_c p c) (slice_c p c'))
    | C_projwire_e (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_projwire_e (slice_c p c) (slice_c p c'))
    | C_concatwire_e2 (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_concatwire_e2 (slice_c p c) (slice_c p c'))
    | C_app_e2 (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_app_e2 (slice_c p c) (slice_c p c'))
    | C_ffi_l (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_ffi_l (slice_c p c) (slice_c p c'))
    | C_match_red (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_match_red (slice_c p c) (slice_c p c'))
    | C_aspar_red (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_aspar_red (slice_c p c) (slice_c p c'))
    | C_box_red (Conf _ m s _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_box_red (slice_c p c) (slice_c p c'))
    | C_unbox_red (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_unbox_red (slice_c p c) (slice_c p c'))
    | C_mkwire_red (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_mkwire_red (slice_c p c) (slice_c p c'))
    | C_projwire_red (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_projwire_red (slice_c p c) (slice_c p c'))
    | C_concatwire_red (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_concatwire_red (slice_c p c) (slice_c p c'))
    | C_let_red (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_let_red (slice_c p c) (slice_c p c'))
    | C_app_red (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_app_red (slice_c p c) (slice_c p c'))
    | C_let_beta (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        let Conf _ _ _ en (T_red (R_let x v _)) _ = c in
        let _ = env_upd_slice_lemma p en x v in
        IntroR (C_let_beta (slice_c p c) (slice_c p c'))
    | C_app_beta (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        let T_red (R_app f v) = Conf.t c in
        let (en, x, _) = get_en_b f in
        env_upd_slice_lemma p en x v;
        IntroR (C_app_beta (slice_c p c) (slice_c p c'))
    | C_ffi_beta (Conf _ m _ _ _ _) c' ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        let Conf _ _ _ _ (T_red (R_ffi fn vs)) _ = c in
        //valid_ffi_vs_slice_lemma p vs;
        exec_ffi_axiom p fn vs;
        IntroR (C_ffi_beta (slice_c p c) (slice_c p c'))
    | C_match_beta (Conf _ m _ _ _ _) c' ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        let Conf _ _ _ _ (T_red (R_match v pats)) _ = c in
        get_next_match_exp_lemma p pats v;
        IntroR (C_match_beta (slice_c p c) (slice_c p c'))
    | C_aspar_beta (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        let T_red (R_aspar _ v) = Conf.t c in
        let (en, x, _) = get_en_b v in
        env_upd_slice_lemma p en x (V_const (C_unit));
        IntroR (C_aspar_beta (slice_c p c) (slice_c p c'))
    | C_box_beta (Conf _ m _ _ (T_red (R_box ps _)) _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_box_beta (slice_c p c) (slice_c p c'))
    | C_unbox_beta (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_unbox_beta (slice_c p c) (slice_c p c'))
    | C_mkwire_beta (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        let Conf _ (Mode Par _) _ _ (T_red (R_mkwire (V_const (C_prins ps')) (V_box ps'' v))) _ = c in
        if not (mem p ps') then
          let _ =
            slice_wire_p_lemma_not_mem p ps' v;
            mem_intersect_lemma_not_mem p ps'
          in
          IntroR (C_mkwire_beta (slice_c p c) (slice_c p c'))
        else
          let _ =
            slice_wire_p_lemma_mem p ps' v;
            mem_intersect_lemma_mem p ps'
          in
          IntroR (C_mkwire_beta (slice_c p c) (slice_c p c'))
    | C_projwire_beta (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_projwire_beta (slice_c p c) (slice_c p c'))
    | C_concatwire_beta (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        let Conf _ _ _ _ (T_red (R_concatwire (V_wire eps1 w1) (V_wire eps2 w2))) _ = c in
        slice_wire_compose_lemma #eps1 #eps2 w1 w2 p;
        de_morgan_intersect_over_union eps1 eps2 (singleton p);
        IntroR (C_concatwire_beta (slice_c p c) (slice_c p c'))
    | C_aspar_ret (Conf _ m s _ _ _) _ ->
      let Conf _ (Mode _ ps) ((Frame m' _ (F_aspar_ret ps') tr)::s) _ _ tr' = c in
      if mem p ps then
	let _ = scoped_trace_mem_slice_lemma p ps tr' in
	IntroR (C_aspar_ret (slice_c p c) (slice_c p c'))
      else if mem p (Mode.ps m') then
	let _ = scoped_trace_not_mem_slice_lemma p ps tr' in
	IntroR (C_aspar_ret (slice_c p c) (slice_c p c'))
      else IntroL ()
    | C_assec_ps (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_assec_ps (slice_c p c) (slice_c p c'))
    | C_assec_e (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_assec_e (slice_c p c) (slice_c p c'))
    | C_assec_red (Conf _ m _ _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_assec_red (slice_c p c) (slice_c p c'))
    | C_assec_beta _ _ -> IntroL ()
    | C_assec_ret _ _ -> IntroL ()

#reset-options
(**********)

type tconfig_par = c:tconfig{Mode.m (Conf.m c) = Par}

type tpar (ps:prins) = m:OrdMap.ordmap prin tconfig_par p_cmp{forall p. mem p ps = contains p m}

type tconfig_sec = c:tconfig{Mode.m (Conf.m c) = Sec}

type tsec =
  m:OrdMap.ordmap prins tconfig_sec ps_cmp{forall ps1 ps2.
                                           (contains ps1 m /\ contains ps2 m /\ not (ps1 = ps2) ==>
                                           intersect ps1 ps2 = empty)}

//type protocol (ps:prins) = tpar ps * option tconfig_sec
type protocol (ps:prins) = tpar ps * tsec

type tpre_assec (#ps':prins) (pi:protocol ps') (ps:prins) (x:varname) (e:exp) =
  not (contains ps (snd pi)) /\
  (forall ps1. contains ps1 (snd pi) ==> intersect ps1 ps = empty) /\
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
  if ps_rest = empty then update p en mempty
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
  let env = update_env (compose_envs_m ps (get_env_m pi ps)) x (V_const C_unit) in
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
  if ps_rest = empty then update p c' pi
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

opaque val slice_c_ps_par:
  ps:prins -> c:sconfig
  -> Tot (pi:tpar ps{forall p. (mem p ps ==> select p pi = Some (slice_c p c)) /\
                               (not (mem p ps) ==> select p pi = None)})
     (decreases (size ps))
let rec slice_c_ps_par ps c =
  let Some p = choose ps in
  let ps_rest = remove p ps in
  if ps_rest = empty then
    update p (slice_c p c) mempty
  else
    let pi_rest = slice_c_ps_par ps_rest c in
    update p (slice_c p c) pi_rest

val slice_c_ps: ps:prins -> c:sconfig
                -> Tot (pi:protocol ps{(forall p. (mem p ps ==>
                                                   select p (fst pi) = Some (slice_c p c)) /\
                                                  (not (mem p ps) ==>
                                                   select p (fst pi) = None)) /\
                                        (is_par c ==> snd pi = mempty)        /\
                                        (is_sec c ==> snd pi = update (Mode.ps (Conf.m c)) (slice_c_sps c) mempty)})
let slice_c_ps ps c =
  let pi = slice_c_ps_par ps c in
  let tsec = if is_sec c then update (Mode.ps (Conf.m c)) (slice_c_sps c) mempty else mempty in
  pi, tsec

val slice_remains_same_in_sec_step_p: #c:sconfig -> #c':sconfig
                                      -> h:sstep c c'{is_sec c /\ if_exit_sec_then_to_sec h}
                                      -> p:prin
                                      -> Lemma (requires (True))
                                               (ensures (slice_c p c = slice_c p c'))
let slice_remains_same_in_sec_step_p c c' h p = ()

val slice_remains_same_in_sec_step: #c:sconfig -> #c':sconfig
                                    -> h:sstep c c'{is_sec c /\ if_exit_sec_then_to_sec h}
                                    -> Lemma (requires (True))
                                             (ensures (forall p. slice_c p c = slice_c p c'))
let slice_remains_same_in_sec_step #c #c' h =
  forall_intro #prin #(fun (p:prin) -> b2t (slice_c p c = slice_c p c'))
               (slice_remains_same_in_sec_step_p #c #c' h)

opaque val forward_simulation_sec: #c:sconfig -> #c':sconfig -> ps:prins
                                   -> h:sstep c c'{is_sec c /\ if_exit_sec_then_to_sec h}
                                   -> Tot (pstep #ps (slice_c_ps ps c)
                                                     (slice_c_ps ps c'))
let forward_simulation_sec #c #c' ps h =
  let (pi, s) = slice_c_ps ps c in
  let (pi', s') = slice_c_ps ps c' in
  let Conj _ h' = sstep_sec_slice_lemma c c' h in
  slice_remains_same_in_sec_step h;
  //sel_contains_tpar ps pi; sel_contains_tpar ps pi';
  cut (forall p. select p pi = select p pi');
  OrdMap.eq_lemma pi pi';
  P_sec (pi, s) (Mode.ps (Conf.m c)) h' (pi', s')

type pstep_par_star: #ps:prins -> protocol ps -> protocol ps -> Type =
  | PP_refl: #ps:prins -> pi:protocol ps -> pstep_par_star #ps pi pi

  | PP_tran:
    #ps:prins -> #pi:protocol ps -> #pi':protocol ps -> #pi'':protocol ps
    -> h:pstep #ps pi pi'{is_P_par h} -> h':pstep_par_star #ps pi' pi''
    -> pstep_par_star #ps pi pi''

val update_tpar: #ps:prins -> p:prin{not (mem p ps)}
                 -> c:tconfig{is_Par (Mode.m (Conf.m c))} -> pi:protocol ps
                 -> Tot (protocol (union (singleton p) ps))
let update_tpar #ps p c pi = update p c (fst pi), snd pi

opaque val pstep_par_upd: #ps:prins -> #pi:protocol ps -> #pi':protocol ps
                          -> h:pstep #ps pi pi'{is_P_par h}
                          -> p:prin{not (contains p (fst pi))}
                          -> c:tconfig{is_Par (Mode.m (Conf.m c))}
                          -> Tot (r:pstep #(union (singleton p) ps) (update_tpar p c pi) (update_tpar p c pi'){is_P_par r})
let pstep_par_upd #ps #pi #pi' h p c = match h with
  | P_par #d #c' _ p' h' _ -> P_par #(union (singleton p) ps) #c' (update_tpar p c pi) p' h' (update_tpar p c pi')

opaque val pstep_par_star_upd_same:
  #ps:prins -> #pi:protocol ps -> #pi':protocol ps -> h:pstep_par_star #ps pi pi'
  -> p:prin{not (contains p (fst pi))}
  -> c:tconfig{is_Par (Mode.m (Conf.m c))}
  -> Tot (pstep_par_star #(union (singleton p) ps) (update_tpar p c pi) (update_tpar p c pi'))
     (decreases h)
let rec pstep_par_star_upd_same #ps #pi #pi' h p c = match h with
  | PP_refl #ps pi -> PP_refl #(union (singleton p) ps)(update_tpar p c pi)

  | PP_tran #ps #pi #pi' #pi'' h1 h2 ->
    PP_tran (pstep_par_upd h1 p c) (pstep_par_star_upd_same h2 p c)

opaque val pstep_par_star_upd_step:
  #ps:prins -> #pi:protocol ps -> #pi':protocol ps
  -> #c:tconfig{is_Par (Mode.m (Conf.m c))}
  -> #c':tconfig{is_Par (Mode.m (Conf.m c))}
  -> h1:pstep_par_star #ps pi pi' -> h2:sstep c c'
  -> p:prin{not (contains p (fst pi))}
  -> Tot (pstep_par_star #(union (singleton p) ps) (update_tpar p c pi) (update_tpar p c' pi'))
     (decreases h1)
let rec pstep_par_star_upd_step #ps #pi #pi' #c #c' h1 h2 p =
  let (pi1, s1)   = update p c (fst pi), snd pi in
  let (pi1', s1') = update p c' (fst pi), snd pi in
  let ps' = union (singleton p) ps in
  let ht1 = P_par #ps' #c' (pi1, s1) p h2 (pi1', s1') in
  let (pi1'', s1'') = update p c' (fst pi'), snd pi' in
  let ht2 = pstep_par_star_upd_same #ps #pi #pi' h1 p c' in
  PP_tran #ps' #(pi1, s1) #(pi1', s1') #(pi1'', s1'') ht1 ht2

(* TODO: FIXME: this is a weird behavior *)
val slice_c_snd_lemma: ps:prins -> c:sconfig{is_par c}
                       -> Lemma (requires (True))
                                (ensures (snd (slice_c_ps ps c) = mempty))
let slice_c_snd_lemma ps c =
  let _, _ = slice_c_ps ps c in
  ()

val if_par_and_enter_sec_from_sec_then_par: #c:sconfig -> #c':sconfig
                                            -> h:sstep c c'{is_par c /\ if_enter_sec_then_from_sec h}
                                            -> Lemma (requires (True))
                                                     (ensures (is_par c'))
let if_par_and_enter_sec_from_sec_then_par #c #c' h = match h with
  | C_assec_beta _ _ -> ()
  | _                -> ()

val sstep_par_slc_snd_lemma: #c:sconfig -> #c':sconfig -> ps:prins
                             -> h:sstep c c'{is_par c /\ if_enter_sec_then_from_sec h}
                             -> Lemma (requires (True))
                                      (ensures (snd (slice_c_ps ps c) = snd (slice_c_ps ps c') /\
                                                snd (slice_c_ps ps c) = mempty))
let sstep_par_slc_snd_lemma #c #c' ps h =
  slice_c_snd_lemma ps c;
  if_par_and_enter_sec_from_sec_then_par #c #c' h;
  slice_c_snd_lemma ps c'

val if_par_then_exit_sec_to_sec: #c:sconfig -> #c':sconfig
                                 -> h:sstep c c'{is_par c}
                                 -> Lemma (requires (True))
                                          (ensures (if_exit_sec_then_to_sec h))
let if_par_then_exit_sec_to_sec #c #c' h = match h with
  | C_assec_ret _ _ -> ()
  | _               -> ()

(* CH: this sometimes timed out on my laptop *)
#set-options "--z3timeout 20"

opaque val forward_simulation_par: #c:sconfig -> #c':sconfig
                                   -> h:sstep c c'{is_par c /\
                                                   if_enter_sec_then_from_sec h}
                                   -> ps:prins
                                   -> Tot (pstep_par_star #ps (slice_c_ps ps c)
                                                              (slice_c_ps ps c'))
                                      (decreases (size ps))
let rec forward_simulation_par #c #c' h ps =
  let pi, s = slice_c_ps ps c in
  let pi', s' = slice_c_ps ps c' in
  sstep_par_slc_snd_lemma ps h;
  let _ = cut (b2t (s = s')) in

  let Some p = choose ps in
  let ps_rest = remove p ps in

  let c_p = slice_c p c in
  let c_p' = slice_c p c' in

  if_par_then_exit_sec_to_sec #c #c' h;
  let h1 = sstep_par_slice_lemma c c' h p in

  if ps_rest = empty then
    let _ = cut (b2t (pi = update p c_p mempty)) in
    let _ = cut (b2t (pi' = update p c_p' mempty)) in
    match h1 with
      | IntroL _  ->
        let _ = cut (b2t (c_p = c_p')) in
        let _ = cut (b2t (pi = pi')) in
        PP_refl (pi, s)
      | IntroR h' ->
        let _ = cut (b2t (pi' = update p c_p' pi)) in
        PP_tran (P_par (pi, s) p h' (pi', s')) (PP_refl (pi', s'))

  else
    let pi_rest, s_rest = slice_c_ps ps_rest c in
    let pi_rest', s_rest' = slice_c_ps ps_rest c' in

    let _ = cut (b2t (pi = update p c_p pi_rest)) in
    let _ = cut (b2t (pi' = update p c_p' pi_rest')) in
    let _ = cut (b2t (s_rest = mempty)) in
    let _ = cut (b2t (s_rest' = mempty)) in

    let h_ind = forward_simulation_par #c #c' h ps_rest in

    match h1 with
      | IntroL _  ->
        let _ = cut (b2t (c_p = c_p')) in
        pstep_par_star_upd_same #ps_rest #(pi_rest, s_rest) #(pi_rest', s_rest') h_ind p (slice_c p c)
      | IntroR h' ->
        pstep_par_star_upd_step #ps_rest #(pi_rest, s_rest) #(pi_rest', s_rest')
                                         #c_p #c_p' h_ind h' p

#reset-options

val slice_wire_helper_lemma:
  eps:eprins -> ps:prins -> p:prin{mem p ps}
  -> Lemma (requires (True)) (ensures (intersect (intersect  eps ps) (singleton p) =
				   intersect eps (singleton p)))
let slice_wire_helper_lemma eps ps p = ()

val slice_wire_lem_singl_of_ps: #eps:eprins -> w:v_wire eps
                                -> ps:prins -> p:prin{mem p ps}
                                -> Lemma (requires (True))
                                         (ensures (slice_wire #(intersect eps ps) p (slice_wire_sps #eps ps w) =
                                                   slice_wire #eps p w))
let slice_wire_lem_singl_of_ps #eps w ps p = ()

val slice_v_lem_singl_of_ps: #m:v_meta -> v:value m -> ps:prins -> p:prin{mem p ps}
                             -> Lemma (requires (True))
                                      (ensures (slice_v p (D_v.v (slice_v_sps ps v)) =
                                                slice_v p v))
                                (decreases %[v])
val slice_en_x_lem_singl_of_ps: en:env -> ps:prins -> p:prin{mem p ps} -> x:varname
                                -> Lemma (requires (True))
                                         (ensures ((slice_en p (slice_en_sps ps en)) x =
                                                   (slice_en p en) x))
                                   (decreases %[en;0])
val slice_en_lem_singl_of_ps: en:env -> ps:prins -> p:prin{mem p ps}
                              -> Lemma (requires (True))
                                       (ensures (slice_en p (slice_en_sps ps en) =
                                                 slice_en p en))
                                 (decreases %[en;1])
let rec slice_v_lem_singl_of_ps #m v ps p = match v with
  | V_const _           -> ()
  | V_box ps' v'        ->
    if intersect ps ps' = empty then
      let _ = cut (mem p ps' ==> mem p (intersect ps ps')) in
      ()
    else if not (mem p ps') then ()
    else slice_v_lem_singl_of_ps v' ps p
  | V_wire eps w        ->
    let _ = slice_wire_helper_lemma eps ps p in
    //let _ = admitP (b2t (intersect (intersect eps ps) (singleton p) = intersect eps (singleton p))) in
    slice_wire_lem_singl_of_ps #eps w ps p
  | V_clos en _ _       -> slice_en_lem_singl_of_ps en ps p
  | V_fix_clos en _ _ _ -> slice_en_lem_singl_of_ps en ps p
  | V_emp_clos _ _      -> ()
  | V_emp               -> ()

and slice_en_x_lem_singl_of_ps en ps p x =
  if en x = None then ()
  else (preceds_axiom en x; slice_v_lem_singl_of_ps (D_v.v (Some.v (en x))) ps p)

and slice_en_lem_singl_of_ps en ps p =
  forall_intro #varname #(fun x -> b2t ((slice_en p (slice_en_sps ps en)) x =
                                        (slice_en p en) x))
               (slice_en_x_lem_singl_of_ps en ps p);
  let _ = cut (FEq (slice_en p (slice_en_sps ps en)) (slice_en p en)) in
  ()

val slice_v_lem_singl_of_ps_forall:
  #m:v_meta -> v:value m -> ps:prins
  -> Lemma (requires (True))
           (ensures (forall p. mem p ps ==>
                               slice_v p (D_v.v (slice_v_sps ps v)) =
                               slice_v p v))
let slice_v_lem_singl_of_ps_forall #m v ps =
  forall_intro (slice_v_lem_singl_of_ps #m v ps)

val sstep_sec_to_par_slice_par_others:
  #c:sconfig -> #c':sconfig -> h:sstep c c'{is_C_assec_ret h /\ is_par c'}
  -> Lemma (requires (True))
           (ensures (forall p. not (mem p (Mode.ps (Conf.m c))) ==>
                               slice_c p c = slice_c p c'))
let sstep_sec_to_par_slice_par_others #c #c' _ = ()

val sstep_sec_to_par_slice_par_mems:
  #c:sconfig -> #c':sconfig -> h:sstep c c'{is_C_assec_ret h /\ is_par c'}
  -> Lemma (requires (True))
           (ensures (forall p. mem p (Mode.ps (Conf.m c)) ==>
                               ret_sec_value_to_p (slice_c_sps c) (slice_c p c) p = slice_c p c'))
                               //sstep_sec_to_par_p #c #c' h p = slice_c p c'))
let sstep_sec_to_par_slice_par_mems #c #c' h =
  let ps = Mode.ps (Conf.m c) in
  let v = D_v.v (c_value c) in
  let _ = slice_v_lem_singl_of_ps_forall v ps in
  ()

val not_contains_lemma: #ps:prins -> pi:tpar ps
                        -> Lemma (requires (True)) (ensures (forall p. not (mem p ps) ==> select p pi = None))
let not_contains_lemma #ps pi = ()

(**********)
(*assume val cand_intro: #a:Type -> #b:Type -> =h:(a /\ b) -> Tot (cand a b)
assume val cand_elim : #a:Type -> #b:Type -> =h:cand a b -> Lemma (a /\ b)

assume val cor_intro: #a:Type -> #b:Type -> =h:(a \/ b) -> Tot (cor a b)
assume val cor_elim : #a:Type -> #b:Type -> =h:cor a b -> Lemma (a \/ b)

assume val imp_intro: #a:Type -> #b:Type -> =h:(a ==> b) -> Tot (cimp a b)
assume val imp_elim: #a :Type -> #b:Type -> =h:cimp a b -> Lemma (a ==> b)

assume val forall_intro_t: #a:Type -> #p:(a -> Type) -> =h:(forall x. p x) -> Tot (x:a -> Tot (p x))
assume val forall_elim   : #a:Type -> #p:(a -> Type) -> =f:(x:a -> Tot (p x)) -> Lemma (forall x. p x)

assume val ceq_intro: #a:Type -> #x:a -> #y:a -> =h:b2t (x = y) -> Tot (ceq x y)
assume val ceq_elim : #a:Type -> #x:a -> #y:a -> =h:ceq x y -> Lemma (x = y)

assume val t_intro: #a:Type -> u:unit{a} -> Tot a
assume val t_elim : #a:Type -> =h:a -> Lemma (a)

assume val rewrite : #a:Type -> #p:(a -> Type) -> #x:a -> #y:a -> =h:ceq x y -> =h':p x -> Tot (p y)
assume val ceq_symm: #a:Type -> #x:a -> #y:a -> =h:ceq x y -> Tot (ceq y x)*)
(**********)

(*opaque val slice_c_ps_cons:
  ps:prins -> c:sconfig -> pi:protocol ps{pi = slice_c_ps ps c}
  -> Tot (p:prin -> Tot ((mem p ps       ==> select p (fst pi) = Some (slice_c p c)) /\
                         (not (mem p ps) ==> select p (fst pi) = None)))
let slice_c_ps_cons ps c pi =
  forall_intro_t #prin #(fun p -> (mem p ps       ==> select p (fst pi) = Some (slice_c p c)) /\
                                  (not (mem p ps) ==> select p (fst pi) = None))
                 (t_intro #(forall p. (mem p ps       ==> select p (fst pi) = Some (slice_c p c)) /\
                                      (not (mem p ps) ==> select p (fst pi) = None)) ())

opaque val tstep_assec_ret_cons:
  #ps':prins -> pi:protocol ps' -> ps:prins{tpre_assec_ret pi ps}
  -> pi':protocol ps'{pi' = (ret_sec_value_to_ps #ps' (fst pi) (Some.v (snd pi)) ps, None)}
  -> Tot (p:prin -> Tot ((mem p ps ==> select p (fst pi') =
                                       Some (ret_sec_value_to_p (Some.v (snd pi)) (Some.v (select p (fst pi))) p)) /\
                         (not (mem p ps) ==> select p (fst pi') = select p (fst pi))))
let tstep_assec_ret_cons #ps' pi ps pi' =
  forall_intro_t #prin #(fun p -> (mem p ps ==> select p (fst pi') =
                                                Some (ret_sec_value_to_p (Some.v (snd pi)) (Some.v (select p (fst pi))) p)) /\
                                  (not (mem p ps) ==> select p (fst pi') = select p (fst pi)))
                 (t_intro #(forall p. (mem p ps ==> select p (fst pi') =
                                                    Some (ret_sec_value_to_p (Some.v (snd pi)) (Some.v (select p (fst pi))) p)) /\
                                      (not (mem p ps) ==> select p (fst pi') = select p (fst pi))) ())

opaque val sstep_sec_to_par_slice_par_mems_cons:
  #c:config -> #c':config -> h:sstep c c'{is_C_assec_ret h /\ is_par c'}
  -> ps':prins{ps' = Mode.ps (Conf.m c)} -> sec_c:tconfig{sec_c = slice_c_sps c}
  -> Tot (p:prin -> Tot (mem p ps' ==> ret_sec_value_to_p sec_c (slice_c p c) p = slice_c p c'))
let sstep_sec_to_par_slice_par_mems_cons #c #c' h ps' sec_c =
  sstep_sec_to_par_slice_par_mems #c #c' h;
  forall_intro_t #prin #(fun p -> (mem p ps' ==> ret_sec_value_to_p sec_c (slice_c p c) p = slice_c p c'))
                 #(t_intro #(forall p. (mem p ps' ==> ret_sec_value_to_p sec_c (slice_c p c) p = slice_c p c')) ())

opaque val sstep_sec_to_par_slice_par_others_cons:
 #c:config -> #c':config -> h:sstep c c'{is_C_assec_ret h /\ is_par c'}
 -> ps':prins{ps' = Mode.ps (Conf.m c)}
 -> Tot (p:prin -> Tot (not (mem p ps') ==> slice_c p c = slice_c p c'))
let sstep_sec_to_par_slice_par_others_cons #c #c' h ps' =
  sstep_sec_to_par_slice_par_others #c #c' h;
  forall_intro_t #prin #(fun p -> (not (mem p ps') ==> slice_c p c = slice_c p c'))
                 #(t_intro #(forall p. (not (mem p ps') ==> slice_c p c = slice_c p c')) ())*)

opaque val forward_simulation_exit_sec: #c:sconfig -> #c':sconfig
                                        -> h:sstep c c'{is_C_assec_ret h /\ is_par c'}
                                        -> ps:prins{subset (Mode.ps (Conf.m c)) ps}
                                        -> Tot (pstep #ps (slice_c_ps ps c) (slice_c_ps ps c'))
let forward_simulation_exit_sec #c #c' h ps =
  (*let ps' = Mode.ps (Conf.m c) in

  let pi, s = slice_c_ps ps c in
  let pi', s' = slice_c_ps ps c' in
  let pi_s = ret_sec_value_to_ps #ps pi (Some.v s) ps' in //writing this and next on one line does not work
  let s_s = None in

  (*sstep_sec_to_par_slice_par_others #c #c' h;
  sstep_sec_to_par_slice_par_mems #c #c' h;

  not_contains_lemma #ps pi; not_contains_lemma #ps pi'; not_contains_lemma #ps pi_s;*)

  (* p:prin -> mem p ps ==> select p pi = Some (slice_c p c) /\ ~ mem p ps ==> select p pi = None *)
  let f1 = slice_c_ps_cons ps c (pi, s) in

  (* p:prin -> mem p ps ==> select p pi' = Some (slice_c p c') /\ ~ mem p ps ==> select p pi' = None *)
  let f2 = slice_c_ps_cons ps c' (pi', s') in

  (* p:prin -> mem p ps' ==> select p pi_s = Some (ret_sec_value_to_p (Some.v s) (Some.v (select p pi)) p)  /\
             ~ mem p ps' ==> select p pi_s = select p pi *)
  let f3 = tstep_assec_ret_cons #ps (pi, s) ps' (pi_s, s_s) in

  (* p:prin -> mem p ps' ==> ret_sec_value_to_p (Some.v s) (slice_c p c) p = slice_c p c' *)
  let f4 = sstep_sec_to_par_slice_par_mems_cons #c #c' h ps' (Some.v s) in

  (* p:prin -> ~ mem p ps' ==> slice_c p c = slice_c p c' *)
  let f5 = sstep_sec_to_par_slice_par_others_cons #c #c' h ps' in

  (* TODO: FIXME: annotations and implicits required at certain places.
   * Marking = in assumes matters ? How about function calls everywhere ? Bind to temps ?
   * can do more ? *)
  let f6: p:prin -> q1:(b2t (mem p ps)) -> q2:(b2t (not (mem p ps')))
          -> Tot (b2t (select p pi_s = select p pi')) =
    fun p q1 q2 ->
      let k1 = cand_intro (f3 p) in
      let Conj k2 k3 = k1 in
      let k4 = imp_intro k3 in
      let k5:(b2t (select p pi_s = select p pi)) = k4 q2 in

      let k6 = cand_intro (f1 p) in
      let Conj k7 k8 = k6 in
      let k9 = (imp_intro k7) q1 in
      let k10 = rewrite (ceq_intro #_ #(select p pi) #(Some (slice_c p c)) k9) k5 in
      let k11 = (imp_intro (f5 p)) q2 in
      let k12 = rewrite (ceq_intro #_ #(slice_c p c) #(slice_c p c') k11) k10 in
      let k13:(b2t (select p pi' = Some (slice_c p c'))) = (imp_intro (Conj.h1 (cand_intro (f2 p)))) q1 in
      rewrite (ceq_symm #_ #(select p pi') #(Some (slice_c p c')) (ceq_intro #_ #(select p pi') #(Some (slice_c p c')) k13)) k12
  in

  let f7: p:prin -> q1:(b2t (mem p ps)) -> q2:(b2t (mem p ps'))
          -> Tot (b2t (select p pi_s = select p pi')) =
    fun p q1 q2 ->
      let _ = admitP (b2t (is_Some (select p pi))) in
      let k1 = cand_intro (f3 p) in
      let Conj k2 k3 = k1 in
      let k4:(b2t (select p pi_s = Some (ret_sec_value_to_p (Some.v s) (Some.v (select p pi)) p))) = (imp_intro k2) q2 in

      let k5 = cand_intro (f1 p) in
      let Conj k6 k7 = k5 in
      let k8 = (imp_intro k6) q1 in
      let k9:(b2t (select p pi_s = Some (ret_sec_value_to_p (Some.v s) (slice_c p c) p))) =
        rewrite (ceq_intro #_ #(select p pi) #(Some (slice_c p c)) k8) k4 in

      let k10 = f4 p in
      let k11 = (imp_intro k10) q2 in
      let k12:(b2t (select p pi_s = Some (slice_c p c'))) =
        rewrite (ceq_intro #_ #(ret_sec_value_to_p (Some.v s) (slice_c p c) p) #(slice_c p c') k11) k9 in

      let k13 = cand_intro (f2 p) in
      let Conj k14 k15 = k13 in
      let k16:(b2t (select p pi' = Some (slice_c p c'))) = (imp_intro k14) q1 in
      let k17:ceq #_ (select p pi') (Some (slice_c p c')) = ceq_intro k16 in
      let k18:(b2t (select p pi_s = select p pi')) =
        rewrite (ceq_symm #_ #(select p pi') #(Some (slice_c p c')) k17) k12 in
      k18
  in

  let f8: p:prin -> q:(b2t (mem p ps)) -> Tot (b2t (select p pi_s = select p pi')) =
    fun p q ->
      if mem p ps' then f7 p q (t_intro #(b2t (mem p ps')) ())
      else f6 p q (t_intro #(b2t (not (mem p ps'))) ())
  in

  let f9: p:prin -> q:(b2t (not (mem p ps))) -> Tot (b2t (select p pi_s = select p pi')) =
    fun p q ->
      let k1 = cand_intro (f1 p) in
      let Conj k2 k3 = k1 in
      let k4:(b2t (select p pi = None)) = (imp_intro k3) q in

      let k5 = cand_intro (f3 p) in
      let Conj k6 k7 = k5 in
      let k8:(not (mem p ps) ==> not (mem p ps')) = t_intro #(not (mem p ps) ==> not (mem p ps')) () in
      let k9:(b2t (not (mem p ps'))) = (imp_intro k8) q in
      let k10:(b2t (select p pi_s = select p pi)) = (imp_intro k7) k9 in
      let k11:(b2t (select p pi_s = None)) = rewrite (ceq_intro #_ #(select p pi) #None k4) k10 in

      let k12 = cand_intro (f2 p) in
      let Conj k13 k14 = k12 in
      let k15:(b2t (select p pi' = None)) = (imp_intro k14) q in

      let k16:(ceq #_ None (select p pi')) = ceq_symm #_ #(select p pi') #None (ceq_intro #_ #(select p pi') #None k15) in

      let k17:(b2t (select p pi_s = select p pi')) = rewrite k16 k11 in

      k17
  in

  let f10: p:prin -> Tot (b2t (select p pi_s = select p pi')) =
    fun p -> if mem p ps then f8 p (t_intro #(b2t (mem p ps)) ())
             else f9 p (t_intro #(b2t (not (mem p ps))) ())
  in

  let _ = forall_elim #prin #(fun p -> b2t (select p pi_s = select p pi')) f10 in

  OrdMap.eq_lemma pi_s pi';
  P_sec_exit #ps (pi, s) ps' (pi_s, s_s)*)

  let ps' = Mode.ps (Conf.m c) in

  let pi, s = slice_c_ps ps c in
  let pi', s' = slice_c_ps ps c' in
  let pi_s = ret_sec_value_to_ps #ps pi (Some.v (select ps' s)) ps' in //writing this and next on one line does not work
  let s_s = mempty #prins #tconfig_sec #ps_cmp in

  sstep_sec_to_par_slice_par_others #c #c' h;
  sstep_sec_to_par_slice_par_mems #c #c' h;

  not_contains_lemma #ps pi; not_contains_lemma #ps pi'; not_contains_lemma #ps pi_s;

  let _ = cut (forall p. mem p ps ==> select p pi = Some (slice_c p c)) in
  let _ = cut (forall p. not (mem p ps) ==> select p pi = None) in

  let _ = cut (forall p. mem p ps ==> select p pi' = Some (slice_c p c')) in
  let _ = cut (forall p. not (mem p ps) ==> select p pi' = None) in

  let _ = cut (forall p. not (mem p ps') ==> select p pi_s = select p pi) in
  let _ = cut (forall p. mem p ps' ==> select p pi_s = Some (slice_c p c')) in
  let _ = cut (forall p. not (mem p ps') ==> slice_c p c = slice_c p c') in

  let _ = cut (forall p. mem p ps ==>
                         ((not (mem p ps') ==> select p pi_s = Some (slice_c p c')) /\
                          (mem p ps' ==> select p pi_s = Some (slice_c p c')))) in

  let _ = cut (forall p. mem p ps ==> select p pi_s = Some (slice_c p c')) in

  //let _ = cut (forall p. mem p ps ==> select p pi_s = Some (slice_c p c')) in
  //let _ = cut (forall p. not (mem p ps) ==> select p pi_s = None) in

  OrdMap.eq_lemma pi_s (fst (slice_c_ps ps c'));
  let _ = cut (b2t (OrdMap.remove ps' s = mempty)) in
  P_sec_exit #ps (pi, s) ps' (pi_s, s_s)

opaque val sstep_par_to_sec_slice_par_others:
  #c:sconfig -> #c':sconfig -> h:sstep c c'{is_C_assec_beta h /\ is_par c}
  -> Lemma (requires (True))
           (ensures (forall p. not (mem p (Mode.ps (Conf.m c))) ==>
                               slice_c p c = slice_c p c'))
let sstep_par_to_sec_slice_par_others #c #c' h = ()

opaque val sstep_par_to_sec_slice_par_mems:
  #c:sconfig -> #c':sconfig -> h:sstep c c'{is_C_assec_beta h /\ is_par c}
  -> Lemma (requires (True))
           (ensures (forall p. mem p (Mode.ps (Conf.m c)) ==>
                               step_p_to_wait (slice_c p c) p = slice_c p c'))
let sstep_par_to_sec_slice_par_mems #c #c' h = ()

opaque val sstep_par_to_sec_slice_par:
  #c:sconfig -> #c':sconfig -> h:sstep c c'{is_C_assec_beta h /\ is_par c}
  -> ps:prins{subset (Mode.ps (Conf.m c)) ps} -> x:varname
  -> e:exp{tpre_assec #ps (slice_c_ps ps c) (Mode.ps (Conf.m c)) x e}
  -> Lemma (requires (True))
           (ensures (step_ps_to_wait #ps (fst (slice_c_ps ps c)) (Mode.ps (Conf.m c)) =
                     (fst (slice_c_ps ps c'))))
let sstep_par_to_sec_slice_par #c #c' h ps x e =
  let ps' = Mode.ps (Conf.m c) in
  let pi, _ = slice_c_ps ps c in
  let pi', _ = slice_c_ps ps c' in
  let pi_s = step_ps_to_wait #ps pi ps' in

  sstep_par_to_sec_slice_par_others #c #c' h; sstep_par_to_sec_slice_par_mems #c #c' h;
  not_contains_lemma #ps pi; not_contains_lemma #ps pi'; not_contains_lemma #ps pi_s;

  let _ = cut (forall p. mem p ps ==> select p pi = Some (slice_c p c)) in
  let _ = cut (forall p. not (mem p ps) ==> select p pi = None) in

  let _ = cut (forall p. not (mem p ps') ==> select p pi_s = select p pi) in
  let _ = cut (forall p. mem p ps' ==> select p pi_s = Some (step_p_to_wait (Some.v (select p pi)) p)) in
  let _ = cut (forall p. mem p ps' ==> select p pi_s = Some (slice_c p c')) in

  let _ = cut (forall p. not (mem p ps') ==> slice_c p c = slice_c p c') in

  let _ = cut (forall p. mem p ps ==>
                         ((not (mem p ps') ==> select p pi_s = Some (slice_c p c')) /\
                          (mem p ps' ==> select p pi_s = Some (slice_c p c')))) in

  let _ = cut (forall p. mem p ps ==> select p pi_s = Some (slice_c p c')) in
  let _ = cut (forall p. not (mem p ps) ==> select p pi_s = None) in

  let _ = cut (forall p. mem p ps ==> select p pi' = Some (slice_c p c')) in
  let _ = cut (forall p. not (mem p ps) ==> select p pi' = None) in

  OrdMap.eq_lemma pi_s pi'

opaque val slice_clos_lem: #meta:v_meta -> v:value meta{is_clos v}
                           -> Lemma (requires (True))
                                    (ensures (forall p.
                                              is_clos (D_v.v (slice_v p v)) /\
                                              MkTuple3._1 (get_en_b (D_v.v (slice_v p v))) =
                                              slice_en p (MkTuple3._1 (get_en_b v))))
let slice_clos_lem #meta v = ()

opaque val sstep_par_to_sec_en_compose_lemma:
  #c:sconfig -> #c':sconfig -> h:sstep c c'{is_C_assec_beta h /\ is_par c}
  -> ps:prins{subset (Mode.ps (Conf.m c)) ps}
  -> Lemma (requires (True))
           (ensures (forall p. mem p (Mode.ps (Conf.m c)) ==>
                               select p (get_env_m #ps (slice_c_ps ps c) (Mode.ps (Conf.m c))) =
                               Some (slice_en p (MkTuple3._1 (get_en_b (R_assec.v (T_red.r (Conf.t c))))))))
let sstep_par_to_sec_en_compose_lemma #c #c' h ps =
  let Conf _ _ _ _ (T_red (R_assec _ v)) _ = c in
  slice_clos_lem v

opaque val forward_simulation_enter_sec:
  #c:sconfig -> #c':sconfig -> h:sstep c c'{is_C_assec_beta h /\ is_par c}
  -> ps:prins{subset (Mode.ps (Conf.m c)) ps}
  -> Tot (pstep #ps (slice_c_ps ps c) (slice_c_ps ps c'))
let forward_simulation_enter_sec #c #c' h ps =
  let Conf Source (Mode Par ps') s en (T_red (R_assec _ v)) _ = c in
  let (en1, x, e) = get_en_b v in

  let pi, s = slice_c_ps ps c in
  let pi', s' = slice_c_ps ps c' in

  let _ = cut (tpre_assec #ps (pi, s) ps' x e) in

  (* TODO: FIXME: If I write pi_s, s_s = ... and then try to say pi_s = step_ps_to_wait, it takes long time,
   * whereas should be immediate from tstep_assec *)
  let pi_s = step_ps_to_wait #ps pi ps' in
  let pi_tmp, s_s = tstep_assec #ps (pi, s) ps' x e in

  let _ = cut (b2t (pi_tmp = pi_s)) in

  sstep_par_to_sec_slice_par #c #c' h ps x e;
  let _ = cut (b2t (pi_s = pi')) in

  let Some (Conf _ _ st_s en_s t_s _) = select ps' s_s in
  let Some (Conf _ _ st' en' t' _) = select ps' s' in

  let _ = cut (b2t (st_s = [])) in
  let _ = cut (b2t (st' = [])) in
  let _ = cut (b2t (t_s = t')) in

  let en2 = update_env en1 x (V_const C_unit) in
  let _ = cut (b2t (Conf.en c' = en2)) in

  let _ = cut (b2t (en' = slice_en_sps ps' en2)) in

  let env_m = get_env_m #ps (pi, s) ps' in
  let composed_env_m = compose_envs_m ps' env_m in

  let updated_composed_envs_m = update_env composed_env_m x (V_const C_unit) in

  let _ = cut (b2t (en_s = updated_composed_envs_m)) in

  let _ = cut (forall p. mem p ps' ==> select p pi = Some (slice_c p c)) in

  let _ = cut (forall p. mem p ps' ==>
               select p env_m = Some (
               MkTuple3._1 (get_en_b (R_assec.v (T_red.r (Conf.t (Some.v (select p pi)))))))) in
  let _ = cut (forall p. mem p ps' ==>
               select p env_m = Some (
               MkTuple3._1 (get_en_b (R_assec.v (T_red.r (Conf.t (slice_c p c))))))) in

  let _ = sstep_par_to_sec_en_compose_lemma #c #c' h ps in
  let _ = cut (forall p. mem p ps' ==> select p env_m = Some (slice_en p en1)) in

  let _ = slc_en_lem_m en1 ps' env_m in

  let _ = cut (b2t (composed_env_m = slice_en_sps ps' en1)) in

  let _ = env_upd_slice_lemma_ps ps' en1 x (V_const C_unit) in

  let _ = cut (b2t (en_s = en')) in
  let _ = cut (b2t (s' = s_s)) in

  let _ = cut (b2t ((pi', s') = (pi_tmp, s_s))) in

  P_sec_enter #ps (pi, s) ps' x e (pi_tmp, s_s)

opaque val forward_simulation: #c:sconfig -> #c':sconfig -> h:sstep c c'
                               -> ps:prins{subset (Mode.ps (Conf.m c)) ps}
                               -> Tot (cor (pstep #ps (slice_c_ps ps c) (slice_c_ps ps c'))
                                           (pstep_par_star #ps (slice_c_ps ps c)
                                                               (slice_c_ps ps c')))
let forward_simulation #c #c' h ps =
  if is_sec c && if_exit_sec_then_to_sec h then
    IntroL (forward_simulation_sec #c #c' ps h)
  else if is_sec c && not (if_exit_sec_then_to_sec h) then
    IntroL (forward_simulation_exit_sec #c #c' h ps)
  else if is_par c && if_enter_sec_then_from_sec h then
    IntroR (forward_simulation_par #c #c' h ps)
  else IntroL (forward_simulation_enter_sec #c #c' h ps)

type pstep_star: #ps:prins -> protocol ps -> protocol ps -> Type =
  | PS_refl: #ps:prins -> pi:protocol ps -> pstep_star #ps pi pi

  | PS_tran:
    #ps:prins -> #pi:protocol ps -> #pi':protocol ps -> #pi'':protocol ps
    -> h1:pstep #ps pi pi' -> h2:pstep_star #ps pi' pi''
    -> pstep_star #ps pi pi''

opaque val pstep_par_star_to_pstep_star:
  #ps:prins -> #pi:protocol ps -> #pi':protocol ps
  -> h:pstep_par_star #ps pi pi'
  -> Tot (pstep_star #ps pi pi')
     (decreases h)
let rec pstep_par_star_to_pstep_star #ps #pi #pi' h = match h with
  | PP_refl _ -> PS_refl pi
  | PP_tran h1 h2 ->
    PS_tran h1 (pstep_par_star_to_pstep_star h2)

opaque val forward_simulation_theorem:
  #c:sconfig -> #c':sconfig -> h:sstep c c' -> ps:prins{ps = all_prins ()}
  -> Tot (pstep_star #ps (slice_c_ps ps c) (slice_c_ps ps c'))
let forward_simulation_theorem #c #c' h ps =
  all_prins_superset_lemma ();
  let h1 = forward_simulation #c #c' h ps in
  match h1 with
    | IntroL h' -> PS_tran h' (PS_refl (slice_c_ps ps c'))
    | IntroR h' -> pstep_par_star_to_pstep_star h'

val sstep_deterministic:
  c:config -> c1:config -> h1:sstep c c1 -> c2:config -> h2:sstep c c2
  -> Lemma (requires (True)) (ensures (c1 = c2 /\ h1 = h2))
let sstep_deterministic c c1 h1 c2 h2 = ()

opaque val pstep_ppar_ppar_confluence:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_par h1} -> h2:pstep #ps pi pi2{is_P_par h2}
  -> Tot (cor (u:unit{pi1 = pi2}) (cexists #(protocol ps) (fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3))))
let pstep_ppar_ppar_confluence #ps pi pi1 pi2 h1 h2 =
  let p1, c1' = P_par.p h1, P_par.c' h1 in
  let p2, c2' = P_par.p h2, P_par.c' h2 in

  let pi_m, s = pi in
  let pi1_m, s1 = pi1 in
  let pi2_m, s2 = pi2 in

  if p1 = p2 then IntroL ()
  else
    let hp1:sstep (Some.v (select p1 pi_m)) c1' = P_par.h h1 in
    let hp2:sstep (Some.v (select p2 pi_m)) c2' = P_par.h h2 in
    
    let pi13_m = update p2 c2' pi1_m in
    let pi23_m = update p1 c1' pi2_m in
    
    let h13:pstep #ps pi1 (pi13_m, s) = P_par #ps #c2' pi1 p2 hp2 (pi13_m, s) in
    let h23:pstep #ps pi2 (pi13_m, s) = P_par #ps #c1' pi2 p1 hp1 (pi23_m, s) in
    
    IntroR (ExIntro #(protocol ps) #((fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3))) (pi13_m, s) (Conj h13 h23))

opaque val pstep_ppar_psec_confluence:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_par h1} -> h2:pstep #ps pi pi2{is_P_sec h2}
  -> Tot (cexists #(protocol ps) (fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)))
let pstep_ppar_psec_confluence #ps pi pi1 pi2 h1 h2 =
  let pi_m, s = pi in
  let pi1_m, s1 = pi1 in
  let pi2_m, s2 = pi2 in
  
  let pi3_m = pi1_m in
  let s3 = s2 in
  
  let h13:pstep #ps pi1 (pi3_m, s3) = P_sec #ps #(P_sec.c' h2) pi1 (P_sec.ps h2) (P_sec.h h2) (pi3_m, s3) in
  let h23:pstep #ps pi2 (pi3_m, s3) = P_par #ps #(P_par.c' h1) pi2 (P_par.p h1) (P_par.h h1) (pi3_m, s3) in
  
  ExIntro #(protocol ps) #(fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)) (pi3_m, s3) (Conj h13 h23)

val step_ps_to_wait_update_lemma:
  ps':prins -> pi:tpar ps' -> ps:prins{forall p. mem p ps ==> contains p pi}
  -> p:prin{not (mem p ps) /\ mem p ps'} -> c:tconfig_par
  -> Lemma (requires (True))
           (ensures (update p c (step_ps_to_wait #ps' pi ps) = step_ps_to_wait #ps' (update p c pi) ps))
let step_ps_to_wait_update_lemma ps' pi ps p c = ()

val target_par_sstep_lemma:
  c:tconfig_par -> c':tconfig_par -> h:sstep c c'
  -> Lemma (requires (True))
           (ensures ((not (is_T_red (Conf.t c) && is_R_assec (T_red.r (Conf.t c)))) /\
                     (not (is_T_sec_wait (Conf.t c)))))
let target_par_sstep_lemma c c' h = ()

val pstep_ppar_psec_enter_excl_lemma:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_par h1} -> h2:pstep #ps pi pi2{is_P_sec_enter h2}
  -> Lemma (requires (True))
           (ensures (not (mem (P_par.p h1) (P_sec_enter.ps h2))))
let pstep_ppar_psec_enter_excl_lemma #ps pi pi1 pi2 h1 h2 =
  let _ = cut (forall p. mem p (P_sec_enter.ps h2) ==> (is_T_red (Conf.t (Some.v (select p (fst pi)))) /\
                                                        is_R_assec (T_red.r (Conf.t (Some.v (select p (fst pi))))))) in
  target_par_sstep_lemma (Some.v (select (P_par.p h1) (fst pi))) (P_par.c' h1) (P_par.h h1)

opaque val pstep_ppar_psec_enter_confluence:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_par h1} -> h2:pstep #ps pi pi2{is_P_sec_enter h2}
  -> Tot (cexists #(protocol ps) (fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)))
let pstep_ppar_psec_enter_confluence #ps pi pi1 pi2 h1 h2 =
  pstep_ppar_psec_enter_excl_lemma #ps pi pi1 pi2 h1 h2;
  //let _ = admitP (b2t (not (mem (P_par.p h1) (P_sec_enter.ps h2)))) in
  
  let pi_m, s = pi in
  let pi1_m, s1 = pi1 in
  let pi2_m, s2 = pi2 in
    
  let pi3_m = update (P_par.p h1) (P_par.c' h1) pi2_m in
  let s3 = s2 in
    
  let _ = cut (tpre_assec #ps pi1 (P_sec_enter.ps h2) (P_sec_enter.x h2) (P_sec_enter.e h2)) in
  //let _ = cut (b2t (step_ps_to_wait #ps pi_m (P_sec_enter.ps h2) = pi2_m)) in
  //let _ = cut (b2t (update (P_par.p h1) (P_par.c' h1) (step_ps_to_wait #ps pi_m (P_sec_enter.ps h2)) = update (P_par.p h1) (P_par.c' h1) pi2_m)) in
  step_ps_to_wait_update_lemma ps pi_m (P_sec_enter.ps h2) (P_par.p h1) (P_par.c' h1);
  let _ = cut (b2t (step_ps_to_wait #ps pi1_m (P_sec_enter.ps h2) = pi3_m)) in
  let _ = cut (forall p. mem p (P_sec_enter.ps h2) ==> select p pi_m = select p pi1_m) in
  let _ = cut (b2t (get_env_m pi (P_sec_enter.ps h2) = get_env_m pi1 (P_sec_enter.ps h2))) in
  
  //let _ = assert (forall p. mem p (P_sec_enter.ps h2) ==> select p pi3_m = select p pi2_m) in
  let _ = cut (b2t (tstep_assec #ps pi1 (P_sec_enter.ps h2) (P_sec_enter.x h2) (P_sec_enter.e h2) = (pi3_m, s3))) in
  let h13:pstep #ps pi1 (pi3_m, s3) = P_sec_enter #ps pi1 (P_sec_enter.ps h2) (P_sec_enter.x h2) (P_sec_enter.e h2) (pi3_m, s3) in
  let h23:pstep #ps pi2 (pi3_m, s3) = P_par #ps #(P_par.c' h1) pi2 (P_par.p h1) (P_par.h h1) (pi3_m, s3) in  
  ExIntro #(protocol ps) #(fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)) (pi3_m, s3) (Conj h13 h23)

val ret_sec_value_to_ps_update_lemma:
  ps':prins -> pi:tpar ps' -> sec_c:tconfig{is_sec sec_c /\ is_value sec_c} -> ps:prins{forall p. mem p ps ==> (contains p pi /\ waiting_config (Some.v (select p pi)))}
  -> p:prin{not (mem p ps) /\ mem p ps'} -> c:tconfig_par
  -> Lemma (requires (True))
           (ensures (update p c (ret_sec_value_to_ps #ps' pi sec_c ps) = ret_sec_value_to_ps #ps' (update p c pi) sec_c ps))
let ret_sec_value_to_ps_update_lemma ps' pi sec_c ps p c = ()

val pstep_ppar_psec_exit_excl_lemma:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_par h1} -> h2:pstep #ps pi pi2{is_P_sec_exit h2}
  -> Lemma (requires (True))
           (ensures (not (mem (P_par.p h1) (P_sec_exit.ps h2))))
let pstep_ppar_psec_exit_excl_lemma #ps pi pi1 pi2 h1 h2 =
  let _ = cut (forall p. mem p (P_sec_exit.ps h2) ==> (is_T_sec_wait (Conf.t (Some.v (select p (fst pi)))))) in
  target_par_sstep_lemma (Some.v (select (P_par.p h1) (fst pi))) (P_par.c' h1) (P_par.h h1)

opaque val pstep_ppar_psec_exit_confluence:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_par h1} -> h2:pstep #ps pi pi2{is_P_sec_exit h2}
  -> Tot (cexists #(protocol ps) (fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)))
let pstep_ppar_psec_exit_confluence #ps pi pi1 pi2 h1 h2 =
  pstep_ppar_psec_exit_excl_lemma #ps pi pi1 pi2 h1 h2;
  //let _ = admitP (b2t (not (mem (P_par.p h1) (P_sec_exit.ps h2)))) in
  
  let pi_m, s = pi in
  let pi1_m, s1 = pi1 in
  let pi2_m, s2 = pi2 in
  
  let pi3_m = update (P_par.p h1) (P_par.c' h1) pi2_m in
  let s3 = s2 in

  let _ = cut (tpre_assec_ret #ps pi1 (P_sec_exit.ps h2)) in
  ret_sec_value_to_ps_update_lemma ps pi_m (Some.v (select (P_sec_exit.ps h2) s)) (P_sec_exit.ps h2) (P_par.p h1) (P_par.c' h1);
  let h13:pstep #ps pi1 (pi3_m, s3) = P_sec_exit #ps pi1 (P_sec_exit.ps h2) (pi3_m, s3) in
  let h23:pstep #ps pi2 (pi3_m, s3) = P_par #ps #(P_par.c' h1) pi2 (P_par.p h1) (P_par.h h1) (pi3_m, s3) in
  ExIntro #(protocol ps) #(fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)) (pi3_m, s3) (Conj h13 h23)

opaque val pstep_psec_psec_confluence:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_sec h1} -> h2:pstep #ps pi pi2{is_P_sec h2}
  -> Tot (cor (u:unit{pi1 = pi2}) (cexists #(protocol ps) (fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3))))
let pstep_psec_psec_confluence #ps pi pi1 pi2 h1 h2 =
  let pi_m, s = pi in
  let pi1_m, s1 = pi1 in
  let pi2_m, s2 = pi2 in

  if P_sec.ps h1 = P_sec.ps h2 then IntroL ()
  else
    let pi3_m = pi_m in
    let s3 = update (P_sec.ps h1) (P_sec.c' h1) s2 in
    let h13:pstep #ps pi1 (pi3_m, s3) = P_sec #ps #(P_sec.c' h2) pi1 (P_sec.ps h2) (P_sec.h h2) (pi3_m, s3) in
    let h23:pstep #ps pi2 (pi3_m, s3) = P_sec #ps #(P_sec.c' h1) pi2 (P_sec.ps h1) (P_sec.h h1) (pi3_m, s3) in
    IntroR (ExIntro #(protocol ps) #(fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)) (pi3_m, s3) (Conj h13 h23))

opaque val pstep_psec_psec_enter_confluence:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_sec h1} -> h2:pstep #ps pi pi2{is_P_sec_enter h2}
  -> Tot (cexists #(protocol ps) (fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)))
let pstep_psec_psec_enter_confluence #ps pi pi1 pi2 h1 h2 =
  let _ = cut (b2t (intersect (P_sec.ps h1) (P_sec_enter.ps h2) = empty)) in
  
  let pi_m, s = pi in
  let pi1_m, s1 = pi1 in
  let pi2_m, s2 = pi2 in
  
  let pi3_m = pi2_m in
  let s3 = update (P_sec.ps h1) (P_sec.c' h1) s2 in

  let _ = cut (tpre_assec #ps pi1 (P_sec_enter.ps h2) (P_sec_enter.x h2) (P_sec_enter.e h2)) in
  
  //let _ = cut (b2t (step_ps_to_wait #ps pi_m (P_sec_enter.ps h2) = pi2_m)) in
  //let _ = cut (b2t (update (P_par.p h1) (P_par.c' h1) (step_ps_to_wait #ps pi_m (P_sec_enter.ps h2)) = update (P_par.p h1) (P_par.c' h1) pi2_m)) in
  //step_ps_to_wait_update_lemma ps pi_m (P_sec_enter.ps h2) (P_par.p h1) (P_par.c' h1);
  //let _ = cut (b2t (step_ps_to_wait #ps pi1_m (P_sec_enter.ps h2) = pi3_m)) in
  let _ = cut (forall p. mem p (P_sec_enter.ps h2) ==> select p pi_m = select p pi1_m) in
  let _ = cut (b2t (get_env_m pi (P_sec_enter.ps h2) = get_env_m pi1 (P_sec_enter.ps h2))) in
  
  //let _ = assert (forall p. mem p (P_sec_enter.ps h2) ==> select p pi3_m = select p pi2_m) in
  //let _ = cut (b2t (tstep_assec #ps pi1 (P_sec_enter.ps h2) (P_sec_enter.x h2) (P_sec_enter.e h2) = (pi3_m, s3))) in admit ()
  let pi13_m, s13 = tstep_assec #ps pi1 (P_sec_enter.ps h2) (P_sec_enter.x h2) (P_sec_enter.e h2) in
  
  let env13 = update_env (compose_envs_m (P_sec_enter.ps h2) (get_env_m pi1 (P_sec_enter.ps h2)))
                         (P_sec_enter.x h2) (V_const C_unit) in
  let tsec13 = Conf Target (Mode Sec (P_sec_enter.ps h2)) [] env13 (T_exp (P_sec_enter.e h2)) in
  (*let env2 = update_env (compose_envs_m (P_sec_enter.ps h2) (get_env_m pi (P_sec_enter.ps h2)))
                        (P_sec_enter.x h2) (V_const C_unit) in
  let tsec2 = Conf Target (Mode Sec (P_sec_enter.ps h2)) [] env2 (T_exp (P_sec_enter.e h2)) in*)
  //let _ = assert (tsec2 = tsec13) in

  //let _ = assert (select (P_sec_enter.ps h2) s13 = Some tsec13) in
  //let _ = assert (select (P_sec_enter.ps h2) s2 = Some tsec2) in
  
  //let _ = assert (select (P_sec_enter.ps h2) s13 = select (P_sec_enter.ps h2) s2) in
  
  //let _ = assert (s13 = s3) in
  
  let h13:pstep #ps pi1 (pi3_m, s3) = P_sec_enter #ps pi1 (P_sec_enter.ps h2) (P_sec_enter.x h2) (P_sec_enter.e h2) (pi3_m, s3) in
  let h23:pstep #ps pi2 (pi3_m, s3) = P_sec #ps #(P_sec.c' h1) pi2 (P_sec.ps h1) (P_sec.h h1) (pi3_m, s3) in
  ExIntro #(protocol ps) #(fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)) (pi3_m, s3) (Conj h13 h23)

val pstep_psec_psec_exit_excl_lemma:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_sec h1} -> h2:pstep #ps pi pi2{is_P_sec_exit h2}
  -> Lemma (requires (True))
           (ensures (not (P_sec.ps h1 = P_sec_exit.ps h2)))
let pstep_psec_psec_exit_excl_lemma #ps pi pi1 pi2 h1 h2 = () // TODO: FIXME: make it faster ?

opaque val pstep_psec_psec_exit_confluence:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_sec h1} -> h2:pstep #ps pi pi2{is_P_sec_exit h2}
  -> Tot (cexists #(protocol ps) (fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)))
let pstep_psec_psec_exit_confluence #ps pi pi1 pi2 h1 h2 =
  pstep_psec_psec_exit_excl_lemma #ps pi pi1 pi2 h1 h2;
  let _ = cut (b2t (intersect (P_sec.ps h1) (P_sec_exit.ps h2) = empty)) in
  
  let pi_m, s = pi in
  let pi1_m, s1 = pi1 in
  let pi2_m, s2 = pi2 in

  let pi3_m = pi2_m in
  let s3 = update (P_sec.ps h1) (P_sec.c' h1) s2 in

  let _ = cut (tpre_assec_ret #ps pi1 (P_sec_exit.ps h2)) in

  let pi13_m, s13 = ret_sec_value_to_ps #ps pi1_m (Some.v (select (P_sec_exit.ps h2) s1)) (P_sec_exit.ps h2),
                    OrdMap.remove (P_sec_exit.ps h2) s1 in
  
  let h13:pstep #ps pi1 (pi3_m, s3) = P_sec_exit #ps pi1 (P_sec_exit.ps h2) (pi3_m, s3) in
  let h23:pstep #ps pi2 (pi3_m, s3) = P_sec #ps #(P_sec.c' h1) pi2 (P_sec.ps h1) (P_sec.h h1) (pi3_m, s3) in
  ExIntro #(protocol ps) #(fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)) (pi3_m, s3) (Conj h13 h23)

val pstep_psec_enter_psec_enter_empty_intersection:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_sec_enter h1} -> h2:pstep #ps pi pi2{is_P_sec_enter h2 /\ not (P_sec_enter.ps h1 = P_sec_enter.ps h2)}
  -> Lemma (requires (True)) (ensures (intersect (P_sec_enter.ps h1) (P_sec_enter.ps h2) = empty))
let pstep_psec_enter_psec_enter_empty_intersection #ps pi pi1 pi2 h1 h2 = ()

opaque val pstep_psec_enter_psec_enter_confluence:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_sec_enter h1} -> h2:pstep #ps pi pi2{is_P_sec_enter h2}
  -> Tot (cor (u:unit{pi1 = pi2}) (cexists #(protocol ps) (fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3))))
let pstep_psec_enter_psec_enter_confluence #ps pi pi1 pi2 h1 h2 =
  let pi_m, s = pi in
  let pi1_m, s1 = pi1 in
  let pi2_m, s2 = pi2 in
  
  if P_sec_enter.ps h1 = P_sec_enter.ps h2 then IntroL ()
  else
    let _ = pstep_psec_enter_psec_enter_empty_intersection #ps pi pi1 pi2 h1 h2 in
    //let _ = cut (b2t (intersect (P_sec_enter.ps h1) (P_sec_enter.ps h2) = empty)) in

    let pi23_m = step_ps_to_wait #ps pi2_m (P_sec_enter.ps h1) in
    let pi13_m = step_ps_to_wait #ps pi1_m (P_sec_enter.ps h2) in
    let _ = cut (b2t (pi13_m = pi23_m)) in

    let _ = cut (forall p. mem p (P_sec_enter.ps h2) ==> select p pi_m = select p pi1_m) in
    let _ = cut (b2t (get_env_m pi (P_sec_enter.ps h2) = get_env_m pi1 (P_sec_enter.ps h2))) in

    let _ = cut (forall p. mem p (P_sec_enter.ps h1) ==> select p pi_m = select p pi2_m) in
    let _ = cut (b2t (get_env_m pi (P_sec_enter.ps h1) = get_env_m pi2 (P_sec_enter.ps h1))) in
    
    //let _ = cut (tpre_assec #ps pi1 (P_sec_enter.ps h2) (P_sec_enter.x h2) (P_sec_enter.e h2)) in admit ()
    
    let env23 = update_env (compose_envs_m (P_sec_enter.ps h1) (get_env_m pi2 (P_sec_enter.ps h1)))
                (P_sec_enter.x h1) (V_const C_unit) in
    let tsec23 = Conf Target (Mode Sec (P_sec_enter.ps h1)) [] env23 (T_exp (P_sec_enter.e h1)) (hide []) in
    let s23 = update (P_sec_enter.ps h1) tsec23 s2 in
    
    let env13 = update_env (compose_envs_m (P_sec_enter.ps h2) (get_env_m pi1 (P_sec_enter.ps h2)))
                (P_sec_enter.x h2) (V_const C_unit) in
    let tsec13 = Conf Target (Mode Sec (P_sec_enter.ps h2)) [] env13 (T_exp (P_sec_enter.e h2)) (hide []) in
    
    let s13 = update (P_sec_enter.ps h2) tsec13 s1 in
    let _ = cut (b2t (s13 = s23)) in
    
    let _ = cut (tpre_assec #ps pi1 (P_sec_enter.ps h2) (P_sec_enter.x h2) (P_sec_enter.e h2)) in
    let _ = cut (tpre_assec #ps pi2 (P_sec_enter.ps h1) (P_sec_enter.x h1) (P_sec_enter.e h1)) in

    let h13:pstep #ps pi1 (pi13_m, s13) = P_sec_enter #ps pi1 (P_sec_enter.ps h2) (P_sec_enter.x h2) (P_sec_enter.e h2) (pi13_m, s13) in
    let h23:pstep #ps pi2 (pi23_m, s23) = P_sec_enter #ps pi2 (P_sec_enter.ps h1) (P_sec_enter.x h1) (P_sec_enter.e h1) (pi23_m, s23) in
    
    IntroR (ExIntro #(protocol ps) #(fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)) (pi13_m, s13) (Conj h13 h23))

opaque val pstep_psec_enter_psec_exit_confluence:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_sec_enter h1} -> h2:pstep #ps pi pi2{is_P_sec_exit h2}
  -> Tot (cexists #(protocol ps) (fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)))
let pstep_psec_enter_psec_exit_confluence #ps pi pi1 pi2 h1 h2 =
  let _ = cut (b2t (intersect (P_sec_enter.ps h1) (P_sec_exit.ps h2) = empty)) in
  
  let pi_m, s = pi in
  let pi1_m, s1 = pi1 in
  let pi2_m, s2 = pi2 in

  let env' = update_env (compose_envs_m (P_sec_enter.ps h1) (get_env_m pi (P_sec_enter.ps h1)))
             (P_sec_enter.x h1) (V_const C_unit) in
  let tsec' = Conf Target (Mode Sec (P_sec_enter.ps h1)) [] env' (T_exp (P_sec_enter.e h1)) (hide []) in
  let _ = assert (s1 = update (P_sec_enter.ps h1) tsec' s) in
  
  OrdMap.sel_upd2 (P_sec_enter.ps h1) tsec' (P_sec_exit.ps h2) s;
  let _ = cut (b2t (select (P_sec_exit.ps h2) s1 = select (P_sec_exit.ps h2) s)) in

  let _ = cut (forall p. mem p (P_sec_exit.ps h2) ==> select p pi_m = select p pi1_m) in

  let _ = cut (forall p. mem p (P_sec_enter.ps h1) ==> select p pi_m = select p pi2_m) in
  let _ = cut (b2t (get_env_m pi (P_sec_enter.ps h1) = get_env_m pi2 (P_sec_enter.ps h1))) in
  
  let pi23_m = step_ps_to_wait #ps pi2_m (P_sec_enter.ps h1) in
  let pi13_m = ret_sec_value_to_ps #ps pi1_m (Some.v (select (P_sec_exit.ps h2) s1)) (P_sec_exit.ps h2) in
  let _ = cut (b2t (pi13_m = pi23_m)) in

  //let _ = cut (tpre_assec #ps pi1 (P_sec_enter.ps h2) (P_sec_enter.x h2) (P_sec_enter.e h2)) in admit ()
  
  let env23 = update_env (compose_envs_m (P_sec_enter.ps h1) (get_env_m pi2 (P_sec_enter.ps h1)))
              (P_sec_enter.x h1) (V_const C_unit) in
  let tsec23 = Conf Target (Mode Sec (P_sec_enter.ps h1)) [] env23 (T_exp (P_sec_enter.e h1)) (hide []) in
  let s23 = update (P_sec_enter.ps h1) tsec23 s2 in
  //let _ = cut (b2t (tsec23 = tsec')) in

  let s13 = OrdMap.remove (P_sec_exit.ps h2) s1 in
  let _ = cut (b2t (s13 = s23)) in
  
  //let _ = cut (tpre_assec #ps pi1 (P_sec_enter.ps h2) (P_sec_enter.x h2) (P_sec_enter.e h2)) in
  let _ = cut (tpre_assec_ret #ps pi1 (P_sec_exit.ps h2)) in
  let _ = cut (tpre_assec #ps pi2 (P_sec_enter.ps h1) (P_sec_enter.x h1) (P_sec_enter.e h1)) in

  let h13:pstep #ps pi1 (pi13_m, s13) = P_sec_exit #ps pi1 (P_sec_exit.ps h2) (pi13_m, s13) in
  let h23:pstep #ps pi2 (pi23_m, s23) = P_sec_enter #ps pi2 (P_sec_enter.ps h1) (P_sec_enter.x h1) (P_sec_enter.e h1) (pi23_m, s23) in
  
  ExIntro #(protocol ps) #(fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)) (pi13_m, s13) (Conj h13 h23)

val pstep_psec_exit_psec_exit_helper_lemma:
  ps1:eprins -> ps2:eprins{intersect ps1 ps2 = empty}
  -> Lemma (requires (True)) (ensures (forall p. mem p ps2 ==> not (mem p ps1)))
let pstep_psec_exit_psec_exit_helper_lemma ps1 ps2 =
  let _ = cut (forall p. mem p (intersect ps1 ps2) = (mem p ps1 && mem p ps2)) in
  let _ = cut (b2t (intersect ps1 ps2 = empty)) in
  let _ = assert (forall p. (mem p (intersect ps1 ps2)) = (mem #prin #p_cmp p empty)) in
  ()

opaque val pstep_psec_exit_psec_exit_confluence:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1{is_P_sec_exit h1} -> h2:pstep #ps pi pi2{is_P_sec_exit h2}
  -> Tot (cor (u:unit{pi1 = pi2}) (cexists #(protocol ps) (fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3))))
let pstep_psec_exit_psec_exit_confluence #ps pi pi1 pi2 h1 h2 =
  let pi_m, s = pi in
  let pi1_m, s1 = pi1 in
  let pi2_m, s2 = pi2 in

  if P_sec_exit.ps h1 = P_sec_exit.ps h2 then IntroL ()
  else
    let _ = cut (b2t (intersect (P_sec_exit.ps h1) (P_sec_exit.ps h2) = empty)) in
    pstep_psec_exit_psec_exit_helper_lemma (P_sec_exit.ps h1) (P_sec_exit.ps h2);
    //let _ = admitP (forall p. mem p (P_sec_exit.ps h2) ==> not (mem p (P_sec_exit.ps h1))) in
    
    (*let _ = cut (b2t (pi1_m = ret_sec_value_to_ps #ps pi_m (Some.v (select (P_sec_exit.ps h1) s)) (P_sec_exit.ps h1))) in
    let _ = cut (b2t (pi2_m = ret_sec_value_to_ps #ps pi_m (Some.v (select (P_sec_exit.ps h2) s)) (P_sec_exit.ps h2))) in*)
        
    let _ = cut (forall p. mem p (P_sec_exit.ps h2) ==> select p pi_m = select p pi1_m) in
    let _ = cut (forall p. mem p (P_sec_exit.ps h1) ==> select p pi_m = select p pi2_m) in
    
    let _ = cut (b2t (select (P_sec_exit.ps h2) s1 = select (P_sec_exit.ps h2) s)) in
    let _ = cut (b2t (select (P_sec_exit.ps h1) s2 = select (P_sec_exit.ps h1) s)) in
    
    let pi13_m = ret_sec_value_to_ps #ps pi1_m (Some.v (select (P_sec_exit.ps h2) s1)) (P_sec_exit.ps h2) in
    let pi23_m = ret_sec_value_to_ps #ps pi2_m (Some.v (select (P_sec_exit.ps h1) s2)) (P_sec_exit.ps h1) in
    let _ = cut (b2t (pi13_m = pi23_m)) in
    
    let s13 = OrdMap.remove (P_sec_exit.ps h2) s1 in
    let s23 = OrdMap.remove (P_sec_exit.ps h1) s2 in
    let _ = cut (b2t (s13 = s23)) in

    let h13:pstep #ps pi1 (pi13_m, s13) = P_sec_exit #ps pi1 (P_sec_exit.ps h2) (pi13_m, s13) in
    let h23:pstep #ps pi2 (pi23_m, s23) = P_sec_exit #ps pi2 (P_sec_exit.ps h1) (pi23_m, s23) in

    IntroR (ExIntro #(protocol ps) #(fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3)) (pi13_m, s13) (Conj h13 h23))

opaque val pstep_confluence_theorem:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> pi2:protocol ps
  -> h1:pstep #ps pi pi1 -> h2:pstep #ps pi pi2
  -> Tot (cor (u:unit{pi1 = pi2}) (cexists #(protocol ps) (fun pi3 -> cand (pstep #ps pi1 pi3) (pstep #ps pi2 pi3))))
let pstep_confluence_theorem ps pi pi1 pi2 h1 h2 =
  if is_P_par h1 then
    if is_P_par h2 then pstep_ppar_ppar_confluence #ps pi pi1 pi2 h1 h2
    else if is_P_sec h2 then IntroR (pstep_ppar_psec_confluence #ps pi pi1 pi2 h1 h2)
    else if is_P_sec_enter h2 then IntroR (pstep_ppar_psec_enter_confluence #ps pi pi1 pi2 h1 h2)
    else IntroR (pstep_ppar_psec_exit_confluence #ps pi pi1 pi2 h1 h2)

  else if is_P_sec h1 then
    if is_P_par h2 then
      let ExIntro pi3 (Conj p1 p2) = pstep_ppar_psec_confluence #ps pi pi2 pi1 h2 h1 in
      IntroR (ExIntro pi3 (Conj p2 p1))
    else if is_P_sec h2 then pstep_psec_psec_confluence #ps pi pi1 pi2 h1 h2
    else if is_P_sec_enter h2 then 
      let ExIntro pi3 (Conj p1 p2) = pstep_psec_psec_enter_confluence #ps pi pi1 pi2 h1 h2 in
      IntroR (ExIntro pi3 (Conj p1 p2))
    else
      let ExIntro pi3 (Conj p1 p2) = pstep_psec_psec_exit_confluence #ps pi pi1 pi2 h1 h2 in
      IntroR (ExIntro pi3 (Conj p1 p2))
      
  else if is_P_sec_enter h1 then
    if is_P_par h2 then
      let ExIntro pi3 (Conj p1 p2) = pstep_ppar_psec_enter_confluence #ps pi pi2 pi1 h2 h1 in
      IntroR (ExIntro pi3 (Conj p2 p1))
    else if is_P_sec h2 then
      let ExIntro pi3 (Conj p1 p2) = pstep_psec_psec_enter_confluence #ps pi pi2 pi1 h2 h1 in
      IntroR (ExIntro pi3 (Conj p2 p1))
    else if is_P_sec_enter h2 then pstep_psec_enter_psec_enter_confluence #ps pi pi1 pi2 h1 h2
    else
      let ExIntro pi3 (Conj p1 p2) = pstep_psec_enter_psec_exit_confluence #ps pi pi1 pi2 h1 h2 in
      IntroR (ExIntro pi3 (Conj p1 p2))
          
  else
    if is_P_par h2 then
      let ExIntro pi3 (Conj p1 p2) = pstep_ppar_psec_exit_confluence #ps pi pi2 pi1 h2 h1 in
      IntroR (ExIntro pi3 (Conj p2 p1))
    else if is_P_sec h2 then
      let ExIntro pi3 (Conj p1 p2) = pstep_psec_psec_exit_confluence #ps pi pi2 pi1 h2 h1 in
      IntroR (ExIntro pi3 (Conj p2 p1))
    else if is_P_sec_enter h2 then
      let ExIntro pi3 (Conj p1 p2) = pstep_psec_enter_psec_exit_confluence #ps pi pi2 pi1 h2 h1 in
      IntroR (ExIntro pi3 (Conj p2 p1))
    else pstep_psec_exit_psec_exit_confluence #ps pi pi1 pi2 h1 h2

val terminal_does_not_step:
  #c:config -> #c':config -> h:sstep c c'
  -> Lemma (requires (is_terminal c)) (ensures False)
let terminal_does_not_step #c #c' h = ()

type terminal_protocol (#ps:prins) (pi:protocol ps) =
  (forall p. mem p ps ==> is_terminal (Some.v (select p (fst pi)))) /\
  snd pi = mempty

val terminal_protocol_does_not_step:
  #ps:prins -> pi:protocol ps -> pi':protocol ps -> h:pstep #ps pi pi'
  -> Lemma (requires (terminal_protocol #ps pi)) (ensures False)
let terminal_protocol_does_not_step #ps pi pi' h = ()

val slice_of_terminal_is_terminal_p:
  p:prin -> c:sconfig{is_terminal c}
  -> Lemma (requires (True)) (ensures (is_terminal (slice_c p c)))
    [SMTPat (slice_c p c); SMTPat (is_terminal c)]
let slice_of_terminal_is_terminal_p p c = ()

val sec_slice_of_terminal_is_empty:
  ps:prins -> c:sconfig{is_terminal c}
  -> Lemma (requires (True)) (ensures (snd (slice_c_ps ps c) = mempty))
    [SMTPat (slice_c_ps ps c); SMTPat (is_terminal c)]
let sec_slice_of_terminal_is_empty ps c = slice_c_snd_lemma ps c

val slice_of_terminal_is_terminal:
  ps:prins -> c:sconfig{is_terminal c}
  -> Lemma (requires (True)) (ensures (terminal_protocol #ps (slice_c_ps ps c)))
let slice_of_terminal_is_terminal ps c =
  let pi = slice_c_ps ps c in
  let _ = cut (b2t (snd pi = mempty)) in
  let _ = cut (forall p. is_terminal (slice_c p c)) in
  ()

// val two_sterminating_runs_end_in_same:
//   #c:config -> #c_1:config -> #c_2:config
//   -> h_1:s_terminating_run c c_1 -> h2:s_terminating_run c c_2
//   -> Lemma (requires (True)) (ensures (c_1 = c_2)) (decreases h_1)
// let rec two_sterminating_runs_end_in_same #c #c_1 #c_2 h_1 h_2 = match h_1 with
//   | STRun_refl _ ->
//     (
//       match h_2 with
// 	| STRun_refl _                   -> ()
// 	| STRun_step #c #c' #c_1 hs' h_1' -> terminal_does_not_step #c #c' hs'
//     )

//   | STRun_step #c #c' #c_1 hs' h_1' ->
//     (
//       match h_2 with
// 	| STRun_refl _                     -> terminal_does_not_step #c #c' hs'
// 	| STRun_step #c #c'' #c_2 hs'' h_2' ->
// 	  sstep_deterministic c c' hs' c'' hs'';
// 	  two_sterminating_runs_end_in_same #c' #c_1 #c_2 h_1' h_2'
//     )

type s_terminating_run: config -> config -> Type =
  | STRun_refl: c:config{is_terminal c} -> s_terminating_run c c
  | STRun_step:
    #c:config -> #c':config -> #c'':config
    -> hs:sstep c c' -> ht:s_terminating_run c' c'' -> s_terminating_run c c''

// type not_stuck (c:config) = cexists #config (fun c' -> sstep c c')

// type s_terminates_in: config -> config -> Type =
//   | STerm_refl: c:config{is_terminal c} -> s_terminates_in c c
//   | STerm_step:
//     #c:config -> #c':config -> hns:not_stuck c
//     -> f:(#c_1:config -> hs:sstep c c_1 -> Tot (s_terminates_in c_1 c'))
//     -> s_terminates_in c c'

// val one_sterminating_run_implies_sterminates:
//   #c:config -> #c':config -> ht:s_terminating_run c c'
//   -> Tot (s_terminates_in c c') (decreases ht)
// let rec one_sterminating_run_implies_sterminates #c #c' ht = match ht with
//   | STRun_refl _ -> STerm_refl c
//   | STRun_step #c #c'' #c' hs ht' ->
//     let hns:not_stuck c = ExIntro c'' hs in
//     let f = fun c_1 hs_1 -> let _ = sstep_deterministic c c_1 hs_1 c'' hs in
//                        one_sterminating_run_implies_sterminates #c'' #c' ht'
//    in
//    STerm_step #c #c' hns f

(* TODO: FIXME: This gives an assertion failed *)
// assume val preceds_axiom_st: c:config -> c_1:config -> hs:sstep c c_1
// 		             -> f:(#c':config -> sstep c c' -> Tot (s_terminates c'))
//                              -> Lemma (requires (True)) (ensures (f #c_1 hs << f))

// val sterminates_implies_at_least_one_terminating_run:
//   #c:config -> h:s_terminates c -> Tot (c':config & s_terminating_run c c') (decreases h)
// let rec sterminates_implies_at_least_one_terminating_run #c h = match h with
//   | STerm_refl _        -> (| c, STRun_refl c |)
//   | STerm_step #c hns f ->
//     let ExIntro c' hs = hns in
//     let h' = f #c' hs in
//     let _ = admitP (h' << f) in
//     let (| c'', h'' |) = sterminates_implies_at_least_one_terminating_run #c' h' in
//     (| c'', STRun_step #c #c' #c'' hs h'' |)

type p_terminating_run: #ps:prins -> protocol ps -> protocol ps -> nat -> Type =
  | PTRun_refl:
    #ps:prins -> pi:protocol ps{terminal_protocol pi} -> p_terminating_run #ps pi pi 0
  | PTRun_step:
    #ps:prins -> #pi:protocol ps -> #pi':protocol ps -> #pi'':protocol ps -> #n:nat
    -> hp:pstep #ps pi pi' -> ht:p_terminating_run pi' pi'' n -> p_terminating_run #ps pi pi'' (n + 1)

// val sterminates_in_terminal:
//   #c:config -> #c':config -> h:sterminates_in c c'
//   -> Lemma (requires (True)) (ensures (is_terminal c')) (decreases h)
// let rec sterminates_in_terminal #c #c' h = match h with
//   | STerm_refl _    -> ()
//   | STerm_step _ ht -> sterminates_in_terminal ht

// val pterminates_in_terminal:
//   #ps:prins -> #pi:protocol ps -> #pi':protocol ps -> #n:nat -> h:pterminates_in #ps pi pi' n
//   -> Lemma (requires (True)) (ensures (terminal_protocol #ps pi')) (decreases h)
// let rec pterminates_in_terminal #ps #pi #pi' #n h = match h with
//   | PTerm_refl _    -> ()
//   | PTerm_step _ ht -> pterminates_in_terminal ht

opaque val pstep_star_to_terminating_run_gives_terminating_run:
  #ps:prins -> pi:protocol ps -> pi':protocol ps -> pi'':protocol ps -> n:nat
  -> hp:pstep_star #ps pi pi' -> ht:p_terminating_run #ps pi' pi'' n
  -> Tot (n':nat & p_terminating_run #ps pi pi'' n') (decreases hp)
let rec pstep_star_to_terminating_run_gives_terminating_run #ps pi pi' pi'' n hp ht = match hp with
  | PS_refl _                       -> (| n, ht |)
  | PS_tran #ps #pi #pi_1 #pi' h_1 h_2 ->
    let (| n_1, ht_1 |) = pstep_star_to_terminating_run_gives_terminating_run #ps #pi_1 #pi' #pi'' #n h_2 ht in
    (| n_1 + 1, PTRun_step #ps #pi #pi_1 #pi'' #n_1 h_1 ht_1 |)

opaque val s_terminating_run_gives_p_terminating_run:
  #c:sconfig -> #c':sconfig -> ht:s_terminating_run c c' -> ps:prins{ps = all_prins ()}
  -> Tot (n:nat & (p_terminating_run #ps (slice_c_ps ps c) (slice_c_ps ps c') n))
    (decreases ht)
let rec s_terminating_run_gives_p_terminating_run #c #c' ht ps =
  match ht with
    | STRun_refl _                  ->
      let _ = slice_of_terminal_is_terminal ps c in
      (| 0, PTRun_refl (slice_c_ps ps c) |)
    | STRun_step #c #c'' #c' hs ht' ->
      let (| n', pt |) = s_terminating_run_gives_p_terminating_run #c'' #c' ht' ps in
      let hps = forward_simulation_theorem #c #c'' hs ps in
      pstep_star_to_terminating_run_gives_terminating_run #ps (slice_c_ps ps c) (slice_c_ps ps c'')
                                                          (slice_c_ps ps c') n' hps pt

(* If pi -> pi1 and pi1 terminates in pi' and pi -> pi2
   then pi2 terminates in pi' *)
opaque val p_terminating_one_gives_p_terminating_other:
  #ps:prins -> pi:protocol ps -> pi1:protocol ps -> hs1:pstep #ps pi pi1
  -> n:nat -> pi':protocol ps -> ht:p_terminating_run #ps pi1 pi' n
  -> pi2:protocol ps -> hs2:pstep #ps pi pi2
  -> Tot (p_terminating_run #ps pi2 pi' n) (decreases n)
let rec p_terminating_one_gives_p_terminating_other #ps pi pi1 hs1 n pi' ht pi2 hs2 =
  let p = pstep_confluence_theorem #ps pi pi1 pi2 hs1 hs2 in
  match p with
    | IntroL _ -> ht
    | IntroR p ->
      let ExIntro pi3 (Conj p1 p2) = p in
      match ht with
	| PTRun_refl _ ->
	  let _ = terminal_protocol_does_not_step #ps pi1 pi3 p1 in ht
	| PTRun_step #ps #pi1 #pi3' #pi' #m hs3 ht' ->
	  let ht'' = p_terminating_one_gives_p_terminating_other #ps pi1 pi3' hs3 m pi' ht' pi3 p1 in
	  PTRun_step #ps #pi2 #pi3 #pi' #m p2 ht''

type makes_progress_p (#ps:prins) (pi:protocol ps) =
  cexists #(protocol ps) (fun pi' -> pstep #ps pi pi')

type p_terminates_in: #ps:prins -> protocol ps -> protocol ps -> nat -> Type =
  | PTerm_refl:
    #ps:prins -> pi:protocol ps{terminal_protocol pi} -> p_terminates_in #ps pi pi 0
  | PTerm_step:
    #ps:prins -> #pi:protocol ps -> #pi':protocol ps -> #n:nat
    -> hns:makes_progress_p #ps pi
    -> f:(pi_1:protocol ps -> hs:pstep #ps pi pi_1 -> Tot (p_terminates_in #ps pi_1 pi' n))
    -> p_terminates_in #ps pi pi' (n + 1)

val p_terminates_in_terminal:
  #ps:prins -> #n:nat -> pi:protocol ps -> pi':protocol ps -> h:p_terminates_in pi pi' n
  -> Lemma (requires (True)) (ensures (terminal_protocol pi')) (decreases n)
let rec p_terminates_in_terminal #ps #n pi pi' h = match h with
  | PTerm_refl _                     -> ()
  | PTerm_step #ps #pi #pi' #m hns f ->
    let ExIntro pi_1 hs_1 = hns in
    let h' = f pi_1 hs_1 in
    p_terminates_in_terminal #ps #m pi_1 pi' h'

opaque val p_terminating_run_implies_p_terminates_in:
  #ps:prins -> #pi:protocol ps -> #pi':protocol ps -> #n:nat
  -> h:p_terminating_run #ps pi pi' n
  -> Tot (p_terminates_in #ps pi pi' n) (decreases n)
let rec p_terminating_run_implies_p_terminates_in #ps #pi #pi' #n h = match h with
  | PTRun_refl _ -> PTerm_refl pi

  | PTRun_step #ps #pi #pi_1 #pi' #m hs_1 h' ->
    let hmp = ExIntro pi_1 hs_1 in
    let f = fun (pi_2:protocol ps) (hs_2:pstep #ps pi pi_2) ->
	    let h'' = p_terminating_one_gives_p_terminating_other #ps pi pi_1 hs_1 m pi' h' pi_2 hs_2 in
	    p_terminating_run_implies_p_terminates_in #ps #pi_2 #pi' #m h''
    in
    PTerm_step #ps #pi #pi' #m hmp f

// val pterminates_confluence:
//   #ps:prins -> pi:protocol ps
//   -> pi1:protocol ps -> n1:nat -> h1:pterminates_in #ps pi pi1 n1
//   -> pi2:protocol ps -> n2:nat -> h2:pterminates_in #ps pi pi2 n2
//   -> Lemma (requires (True)) (ensures (pi1 = pi2)) (decreases n1)
// let rec pterminates_confluence #ps pi pi1 n1 h1 pi2 n2 h2 = match h1 with
//   | PTerm_refl _ ->
//     (
//       match h2 with
// 	| PTerm_refl _                         -> ()
// 	| PTerm_step #ps #pi #pi' #pi2 #n hp _ ->
// 	  terminal_protocol_does_not_step #ps pi pi' hp
//     )
  
//   | PTerm_step #ps #pi #pi1' #pi1 #n1' hp1 ht1 ->
//     (
//       match h2 with
// 	| PTerm_refl _                              ->
// 	  terminal_protocol_does_not_step #ps pi pi1' hp1
// 	| PTerm_step #ps #pi #pi2' #pi2 #n2' hp2 ht2 ->
// 	  let p:pterminates_in #ps pi2' pi1 n1' = pterminates_one_and_all #ps pi pi1' hp1 n1' pi1 ht1 pi2' hp2 in
// 	  pterminates_confluence #ps pi2' pi1 n1' p pi2 n2' ht2
//     )
