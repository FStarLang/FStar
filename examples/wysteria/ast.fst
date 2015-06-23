(*--build-config
    options:--admit_fsi OrdSet --admit_fsi OrdMap --logQueries;
    variables:LIB=../../lib;
    other-files:$LIB/ordset.fsi $LIB/ordsetproperties.fst $LIB/ordmap.fsi $LIB/list.fst $LIB/constr.fst $LIB/ext.fst
 --*)

module AST

open OrdMap

open OrdSet

type other_info = nat

type varname = string

type prin = nat

val p_cmp: prin -> prin -> Tot bool
let p_cmp p1 p2 = p1 <= p2

type prins = s:ordset prin p_cmp{not (s = empty)}

type eprins = ordset prin p_cmp

type const =
  | C_prin : c:prin -> const
  | C_prins: c:prins -> const

  | C_unit : const
  | C_nat  : c:nat -> const
  | C_bool : c:bool -> const

type exp' =
  | E_aspar: ps:exp -> e:exp -> exp'
  | E_assec: ps:exp -> e:exp -> exp'
  | E_unbox: e:exp  -> exp'

  | E_const: c:const -> exp'
  | E_var  : x:varname -> exp'
  | E_let  : x:varname -> e1:exp -> e2:exp -> exp'
  | E_abs  : x:varname -> e:exp -> exp'
  | E_app  : e1:exp -> e2:exp -> exp'

and exp =
  | Exp: e:exp' -> info:option other_info -> exp

type value: eprins -> Type =
  | V_const  : c:const -> value empty
  | V_box    : #vps:eprins -> ps:prins -> v:value vps{subset vps ps}
               -> value ps
  | V_clos   : en:env -> x:varname -> e:exp -> value empty

  (* bomb value, comes up in target only *)
  | V_emp    : value empty

and dvalue:Type =
  | DV: vps:eprins -> v:value vps -> dvalue

(* TODO: fix it, option value *)
and env = varname -> Tot dvalue

type redex =
  | R_aspar: #vps:eprins -> ps:prins -> v:value vps -> redex
  | R_assec: #vps:eprins -> ps:prins -> v:value vps -> redex
  | R_box  : #vps:eprins -> ps:prins -> v:value vps -> redex
  | R_unbox: #vps:eprins -> v:value vps -> redex
  | R_let  : #vps:eprins -> x:varname -> v:value vps -> e:exp -> redex
  | R_app  : #vps1:eprins -> #vps2:eprins -> v1:value vps1 -> v2:value vps2
             -> redex

assume val empty_env: env

val update_env: #vps:eprins -> env -> varname -> value vps -> Tot env
let update_env #vps en x v = fun y -> if y = x then DV vps v else en y

type as_mode =
  | Par
  | Sec

type mode =
  | Mode: m:as_mode -> ps:prins -> mode

type frame' =
  | F_aspar_ps : e:exp -> frame'
  | F_aspar_e  : ps:prins -> frame'
  | F_assec_ps : e:exp -> frame'
  | F_assec_e  : ps:prins -> frame'
  | F_assec_ret: frame'
  | F_box_e    : ps:prins -> frame'
  | F_unbox    : frame'
  | F_let      : x:varname -> e2:exp -> frame'
  | F_app_e1   : e2:exp -> frame'
  | F_app_e2   : #vps:eprins -> v:value vps -> frame'
  
type frame =
  | Frame: m:mode -> en:env -> f:frame'-> frame

type stack = list frame

type term =
  | T_exp     : e:exp -> term
  | T_red     : r:redex -> term
  | T_val     : #vps:eprins -> v:value vps -> term
  
  | T_sec_wait: term

type level = | Source | Target

val src: level -> Tot bool
let src = is_Source

type mode_inv (m:mode) (l:level) =
  (is_Target l /\ Mode.m m = Par) ==> is_singleton (Mode.ps m)

val is_sec_frame: f':frame' -> Tot bool
let is_sec_frame f' =
  not (is_F_aspar_ps f' || is_F_aspar_e f' || is_F_box_e f')

val stack_source_inv: stack -> mode -> Tot bool
let rec stack_source_inv s (Mode as_m ps) = match s with
  | []                  -> not (as_m = Sec)
  | (Frame m' _ f')::tl ->
    let Mode as_m' ps' = m' in
    (not (as_m = Par) || as_m' = Par)                             &&
    (not (as_m = Sec) || (not (as_m' = Par) || is_F_assec_ret f')) &&
    (not (as_m' = Sec) || (is_sec_frame f' && is_Cons tl))        &&
    (not (is_F_box_e f') || (ps = F_box_e.ps f'))                 &&
    (ps = ps' || (subset ps ps' && is_F_box_e f'))                &&
    stack_source_inv tl m'

val stack_target_inv: stack -> mode -> Tot bool
let rec stack_target_inv s m = match s with
  | []                  -> true
  | (Frame m' _ f')::tl ->
    m = m'                                             &&
    (not (Mode.m m' = Par) || not (is_F_assec_ret f')) &&
    (not (Mode.m m' = Sec) || is_sec_frame f')         &&
    stack_target_inv tl m

val stack_inv: stack -> mode -> level -> Tot bool
let rec stack_inv s m l =
  if is_Source l then stack_source_inv s m else stack_target_inv s m

val is_sec_redex: redex -> Tot bool
let is_sec_redex r = not (is_R_aspar r || is_R_box r)

val term_inv: term -> mode -> level -> Tot bool
let term_inv t m l =
  (not (is_Source l) || not (t = T_sec_wait)) &&
  (not (is_T_red t && Mode.m m = Sec) || is_sec_redex (T_red.r t))

type config =
  | Conf: l:level -> m:mode{mode_inv m l} -> s:stack{stack_inv s m l}
          -> en:env -> t:term{term_inv t m l} -> config

type sconfig = c:config{is_Source (Conf.l c)}
type tconfig = c:config{is_Target (Conf.l c)}
          
val is_sframe: c:config -> f:(frame' -> Tot bool) -> Tot bool
let is_sframe (Conf _ _ s _ _) f = is_Cons s && f (Frame.f (Cons.hd s))

val is_value: c:config -> Tot bool
let is_value c = is_T_val (Conf.t c)

val is_value_ps: c:config -> Tot bool
let is_value_ps c = match c with
  | Conf _ _ _ _ (T_val (V_const (C_prins _))) -> true
  | _                                          -> false

val c_value: c:config{is_value c} -> Tot (vps:eprins & value vps)
let c_value (Conf _ _ _ _ (T_val #vps v)) = (| vps, v |)

val c_value_ps: c:config{is_value_ps c} -> Tot prins
let c_value_ps c = match c with
  | Conf _ _ _ _ (T_val (V_const (C_prins ps))) -> ps

val is_par: config -> Tot bool
let is_par c = is_Par (Mode.m (Conf.m c))

val is_sec: config -> Tot bool
let is_sec c = is_Sec (Mode.m (Conf.m c))

type pre_easpar (c:config) =
  is_T_exp (Conf.t c) /\ is_E_aspar (Exp.e (T_exp.e (Conf.t c))) /\ is_par c

type pre_eapp (c:config) =
  is_T_exp (Conf.t c) /\ is_E_app (Exp.e (T_exp.e (Conf.t c)))

type pre_eabs (c:config) =
  is_T_exp (Conf.t c) /\ is_E_abs (Exp.e (T_exp.e (Conf.t c)))

type pre_elet (c:config) =
  is_T_exp (Conf.t c) /\ is_E_let (Exp.e (T_exp.e (Conf.t c)))

type pre_evar (c:config) =
  is_T_exp (Conf.t c) /\ is_E_var (Exp.e (T_exp.e (Conf.t c)))

type pre_econst (c:config) =
  is_T_exp (Conf.t c) /\ is_E_const (Exp.e (T_exp.e (Conf.t c)))

type pre_eunbox (c:config) =
  is_T_exp (Conf.t c) /\ is_E_unbox (Exp.e (T_exp.e (Conf.t c)))

(* pre returns comp, for src it's never Skip *)
type comp = | Do | Skip | NA

val step_aspar_e1: c:config{pre_easpar c} -> Tot config
let step_aspar_e1 (Conf l m s en (T_exp (Exp (E_aspar e1 e2) _))) =
  Conf l m ((Frame m en (F_aspar_ps e2))::s) en (T_exp e1)

val step_unbox_e: c:config{pre_eunbox c} -> Tot config
let step_unbox_e (Conf l m s en (T_exp (Exp (E_unbox e) _))) =
  Conf l m ((Frame m en F_unbox)::s) en (T_exp e)

val step_const: c:config{pre_econst c} -> Tot config
let step_const (Conf l m s en (T_exp (Exp (E_const c) _))) =
  Conf l m s en (T_val (V_const c))

val step_var: c:config{pre_evar c} -> Tot config
let step_var (Conf l m s en (T_exp (Exp (E_var x) _))) =
  let DV _ v = en x in
  Conf l m s en (T_val v)

val step_let_e1: c:config{pre_elet c} -> Tot config
let step_let_e1 (Conf l m s en (T_exp (Exp (E_let x e1 e2) _))) =
  Conf l m ((Frame m en (F_let x e2))::s) en (T_exp e1)

val step_abs: c:config{pre_eabs c} -> Tot config
let step_abs (Conf l m s en (T_exp (Exp (E_abs x e) _))) =
  Conf l m s en (T_val (V_clos en x e))

val step_app_e1: c:config{pre_eapp c} -> Tot config
let step_app_e1 (Conf l m s en (T_exp (Exp (E_app e1 e2) _))) =
  Conf l m ((Frame m en (F_app_e1 e2))::s) en (T_exp e1)

val step_aspar_e2: c:config{is_value_ps c /\ is_sframe c is_F_aspar_ps}
                   -> Tot config
let step_aspar_e2 (Conf l _ ((Frame m en (F_aspar_ps e))::s) _
                        (T_val (V_const (C_prins ps)))) =
  Conf l m ((Frame m en (F_aspar_e ps))::s) en (T_exp e)

val step_app_e2: c:config{is_value c /\ is_sframe c is_F_app_e1}
                 -> Tot config
let step_app_e2 (Conf l _ ((Frame m en (F_app_e1 e2))::s) _ (T_val v)) =
  Conf l m ((Frame m en (F_app_e2 v))::s) en (T_exp e2)
  
val step_aspar_red: c:config{is_value c /\ is_sframe c is_F_aspar_e}
                    -> Tot config
let step_aspar_red (Conf l _ ((Frame m en (F_aspar_e ps))::s) _ (T_val v)) =
  Conf l m s en (T_red (R_aspar ps v))

val step_box_red: c:config{is_value c /\ is_sframe c is_F_box_e}
                  -> Tot config
let step_box_red (Conf l _ ((Frame m en (F_box_e ps))::s) _ (T_val v)) =
  Conf l m s en (T_red (R_box ps v))

val step_unbox_red: c:config{is_value c /\ is_sframe c is_F_unbox}
                  -> Tot config
let step_unbox_red (Conf l _ ((Frame m en F_unbox)::s) _ (T_val v)) =
  Conf l m s en (T_red (R_unbox v))

val step_let_red: c:config{is_value c /\ is_sframe c is_F_let}
                  -> Tot config
let step_let_red (Conf l _ ((Frame m en (F_let x e2))::s) _ (T_val v)) =
  Conf l m s en (T_red (R_let x v e2))
  
val step_app_red: c:config{is_value c /\ is_sframe c is_F_app_e2}
                  -> Tot config
let step_app_red (Conf l _ ((Frame m en (F_app_e2 v1))::s) _ (T_val v2)) =
  Conf l m s en (T_red (R_app v1 v2))

val pre_aspar: config -> Tot comp
let pre_aspar c = match c with
  | Conf l (Mode Par ps1) _ _ (T_red (R_aspar ps2 (V_clos _ _ _))) ->
    if src l then
      if subset ps2 ps1 then Do else NA
    else
      if subset ps1 ps2 then Do else Skip
  
  | _ -> NA

val step_aspar: c:config{not (pre_aspar c = NA)} -> Tot config
let step_aspar c = match c with
  | Conf l m s en' (T_red (R_aspar ps (V_clos en x e))) ->
    let m'  = if src l then Mode Par ps else m in
    let s'  = (Frame m en' (F_box_e ps))::s in
    
    (*
     * for parties not in ps, the choice of empty_env is arbitrary
     * perhaps we should prove the theorem using any env and then
     * implementation can make whatever decision (retain env as in F* semantics)
     *)
    let en', t' =
      if src l then update_env en x (V_const C_unit), T_exp e
      else
        if pre_aspar c = Do then update_env en x (V_const C_unit), T_exp e
        else empty_env, T_val V_emp
    in

    Conf l m' s' en' t'

val pre_box: config -> Tot comp
let pre_box c = match c with
  | Conf l (Mode Par ps1) _ _ (T_red (R_box #vps ps2 _)) ->
    if subset vps ps2 then
      if src l then
        if subset ps2 ps1 then Do else NA
      else Do
    else NA

  | _ -> NA

val step_box: c:config{pre_box c = Do} -> Tot config
let step_box c = match c with
  | Conf l m s en (T_red (R_box ps v)) -> Conf l m s en (T_val (V_box ps v))

val pre_unbox: config -> Tot comp
let pre_unbox c = match c with
  | Conf _ (Mode as_m ps1) _ _ (T_red (R_unbox (V_box ps2 _))) ->
    if as_m = Par then
      if subset ps1 ps2 then Do else NA
    else
      if subset ps2 ps1 then Do else NA

  | _ -> NA

val step_unbox: c:config{pre_unbox c = Do} -> Tot config
let step_unbox c = match c with
  | Conf l m s en (T_red (R_unbox (V_box _ v))) -> Conf l m s en (T_val v)

val is_let_redex: c:config -> Tot bool
let is_let_redex c = match c with
  | Conf _ _ _ _ (T_red (R_let _ _ _)) -> true
  | _                                  -> false

val step_let: c:config{is_let_redex c} -> Tot config
let step_let c = match c with
  | Conf l m s en (T_red (R_let x v1 e2)) ->
    Conf l m s (update_env en x v1) (T_exp e2)

val is_app_redex: c:config -> Tot bool
let is_app_redex c = match c with
  | Conf _ _ _ _ (T_red (R_app (V_clos _ _ _) _)) -> true

  | _ -> false

val step_app: c:config{is_app_redex c} -> Tot config
let step_app c = match c with
  | Conf l m s _ (T_red (R_app (V_clos en x e) v)) ->
    Conf l m s (update_env en x v) (T_exp e)

type cstep: config -> config -> Type =

  | C_aspar_ps:
    c:config{pre_easpar c} -> c':config{c' = step_aspar_e1 c}
    -> cstep c c'

  | C_unbox:
    c:config{pre_eunbox c} -> c':config{c' = step_unbox_e c}
    -> cstep c c'

  | C_const:
    c:config{pre_econst c} -> c':config{c' = step_const c}
    -> cstep c c'

  | C_var:
    c:config{pre_evar c} -> c':config{c' = step_var c}
    -> cstep c c'

  | C_let_e1:
    c:config{pre_elet c} -> c':config{c' = step_let_e1 c}
    -> cstep c c'

  | C_abs:
    c:config{pre_eabs c} -> c':config{c' = step_abs c}
    -> cstep c c'

  | C_app_e1:
    c:config{pre_eapp c} -> c':config{c' = step_app_e1 c}
    -> cstep c c'

  | C_aspar_e:
    c:config{is_value_ps c /\ is_sframe c is_F_aspar_ps}
    -> c':config{c' = step_aspar_e2 c}
    -> cstep c c'

  | C_app_e2:
    c:config{is_value c /\ is_sframe c is_F_app_e1}
    -> c':config{c' = step_app_e2 c}
    -> cstep c c'

  | C_aspar_red:
    c:config{is_value c /\ is_sframe c is_F_aspar_e}
    -> c':config{c' = step_aspar_red c}
    -> cstep c c'

  | C_box_red:
    c:config{is_value c /\ is_sframe c is_F_box_e}
    -> c':config{c' = step_box_red c}
    -> cstep c c'

  | C_unbox_red:
    c:config{is_value c /\ is_sframe c is_F_unbox}
    -> c':config{c' = step_unbox_red c}
    -> cstep c c'

  | C_let_red:
    c:config{is_value c /\ is_sframe c is_F_let}
    -> c':config{c' = step_let_red c}
    -> cstep c c'

  | C_app_red:
    c:config{is_value c /\ is_sframe c is_F_app_e2}
    -> c':config{c' = step_app_red c}
    -> cstep c c'

  | C_let_beta:
    c:config{is_let_redex c} -> c':config{c' = step_let c} -> cstep c c'
    
  | C_app_beta:
    c:config{is_app_redex c} -> c':config{c' = step_app c} -> cstep c c'

  | C_aspar_beta:
    c:config{not (pre_aspar c = NA)} -> c':config{c' = step_aspar c}
    -> cstep c c'

  | C_box_beta:
    c:config{pre_box c = Do} -> c':config{c' = step_box c} -> cstep c c'

  | C_unbox_beta:
    c:config{pre_unbox c = Do} -> c':config{c' = step_unbox c}
    -> cstep c c'

(**********)

type pre_eassec (c:config) =
  is_T_exp (Conf.t c) /\ is_E_assec (Exp.e (T_exp.e (Conf.t c)))

val step_assec_e1: c:config{pre_eassec c} -> Tot config
let step_assec_e1 (Conf l m s en (T_exp (Exp (E_assec e1 e2) _))) =
  Conf l m ((Frame m en (F_assec_ps e2))::s) en (T_exp e1)

val step_assec_e2: c:config{is_value_ps c /\ is_sframe c is_F_assec_ps}
                   -> Tot config
let step_assec_e2 (Conf l _ ((Frame m en (F_assec_ps e))::s) _
                        (T_val (V_const (C_prins ps)))) =
  Conf l m ((Frame m en (F_assec_e ps))::s) en (T_exp e)

val step_assec_red: c:config{is_value c /\ is_sframe c is_F_assec_e}
                    -> Tot config
let step_assec_red (Conf l _ ((Frame m en (F_assec_e ps))::s) _ (T_val v)) =
  Conf l m s en (T_red (R_assec ps v))

val pre_assec: config -> Tot comp
let pre_assec c = match c with
  | Conf l (Mode as_m ps1) _ _ (T_red (R_assec ps2 (V_clos _ _ _))) ->
    if l = Source || as_m = Sec then
      if ps1 = ps2 then Do else NA
    else NA

  | _ -> NA

val step_assec: c:config{not (pre_assec c = NA)} -> Tot config
let step_assec c = match c with
  | Conf l m s en' (T_red (R_assec ps (V_clos en x e))) ->  
    Conf l (Mode Sec ps) ((Frame m en' F_assec_ret)::s)
           (update_env en x (V_const C_unit)) (T_exp e)

val step_assec_ret: c:config{is_value c /\ is_sframe c is_F_assec_ret}
                    -> Tot config
let step_assec_ret (Conf l _ ((Frame m en F_assec_ret)::s) _ t) = Conf l m s en t

type sstep: config -> config -> Type =
  
  | C_step:
    c:config -> c':config -> h:cstep c c' -> sstep c c'

  | C_assec_ps:
    c:config{pre_eassec c} -> c':config{c' = step_assec_e1 c}
    -> sstep c c'

  | C_assec_e:
    c:config{is_value_ps c /\ is_sframe c is_F_assec_ps}
    -> c':config{c' = step_assec_e2 c}
    -> sstep c c'
  
  | C_assec_red:
    c:config{is_value c /\ is_sframe c is_F_assec_e}
    -> c':config{c' = step_assec_red c}
    -> sstep c c'
    
  | C_assec_beta:
    c:config{not (pre_assec c = NA)} -> c':config{c' = step_assec c}
    -> sstep c c'
    
  | C_assec_ret:
    c:config{is_value c /\ is_sframe c is_F_assec_ret}
    -> c':config{c' = step_assec_ret c}
    -> sstep c c'

(**********)

assume val preceds_axiom: en:env -> x:varname -> Lemma (ensures (en x << en))

val slice_v_sps : #vps:eprins -> prins -> v:value vps -> Tot (r:dvalue{subset (DV.vps r) vps})  (decreases %[v])
val slice_en_sps: prins -> en:env -> Tot (varname -> Tot dvalue) (decreases %[en])

let rec slice_v_sps #vps ps v =
  match v with
    | V_const _     -> DV vps v
    | V_box ps' v'  ->
      let DV _ v'' =
        if not (intersect ps' ps = empty) then slice_v_sps ps v'
        else DV empty V_emp
      in
      DV ps' (V_box ps' v'')
    | V_clos en x e -> DV empty (V_clos (slice_en_sps ps en) x e)
    | V_emp         -> DV vps v

and slice_en_sps ps en =
  let _ = () in
  fun x -> preceds_axiom en x; slice_v_sps ps (DV.v (en x))

assume val slice_emp_en_sps: ps:prins
                             -> Lemma (requires (True))
                                      (ensures (slice_en_sps ps empty_env = empty_env))
                                [SMTPat (slice_en_sps ps empty_env)]

val slice_e_sps: prins -> exp -> Tot exp
let slice_e_sps ps e = e

val slice_r_sps: prins -> r:redex{is_sec_redex r} -> Tot redex
let slice_r_sps ps r = match r with
  | R_assec ps' v  -> R_assec ps' (DV.v (slice_v_sps ps v))
  | R_unbox v     -> R_unbox (DV.v (slice_v_sps ps v))
  | R_let x v1 e2 -> R_let x (DV.v (slice_v_sps ps v1)) e2
  | R_app v1 v2   -> R_app (DV.v (slice_v_sps ps v1)) (DV.v (slice_v_sps ps v2))

val slice_f'_sps: ps:prins -> f:frame'{is_sec_frame f} -> Tot frame'
let slice_f'_sps ps f = match f with
  | F_assec_ps _ -> f
  | F_assec_e  _ -> f
  | F_assec_ret  -> f
  | F_unbox      -> f
  | F_let    _ _ -> f
  | F_app_e1   _ -> f
  | F_app_e2   v -> F_app_e2  (DV.v (slice_v_sps ps v))

val slice_f_sps: ps:prins -> f:frame{Frame.m f = Mode Sec ps /\
                                     is_sec_frame (Frame.f f)}
                 -> Tot frame
let slice_f_sps ps (Frame m en f') = Frame m (slice_en_sps ps en)
                                             (slice_f'_sps ps f')

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
  | T_val v -> T_val (DV.v (slice_v_sps ps v))

val slice_c_sps: c:sconfig{is_sec c} -> Tot tconfig
let slice_c_sps (Conf _ (Mode Sec ps) s en t) =
    Conf Target (Mode Sec ps) (slice_s_sps ps s) (slice_en_sps ps en)
                (slice_t_sps ps t)

(**********)

open Constructive

open FunctionalExtensionality

val env_upd_slice_lemma_ps: #vps:eprins -> ps:prins -> en:env -> x:varname -> v:value vps
                            -> Lemma (requires (True))
                                     (ensures (slice_en_sps ps (update_env en x v) =
                                               update_env (slice_en_sps ps en) x (DV.v (slice_v_sps ps v))))
                                     [SMTPat (slice_en_sps ps (update_env en x v))]
let env_upd_slice_lemma_ps #vps ps en x v =
  cut (FEq (slice_en_sps ps (update_env en x v))
      (update_env (slice_en_sps ps en) x (DV.v (slice_v_sps ps v))))

val cstep_sec_slice_lemma: c:sconfig{is_sec c} -> c':sconfig -> h:cstep c c'
                           -> Tot (cand (u:unit{Conf.m c' = Conf.m c})
                                        (cstep (slice_c_sps c) (slice_c_sps c')))
#set-options "--split_cases 1"
let cstep_sec_slice_lemma c c' h = match h with
  | C_unbox c c'      -> Conj () (C_unbox (slice_c_sps c) (slice_c_sps c'))
  | C_const c c'      -> Conj () (C_const (slice_c_sps c) (slice_c_sps c'))
  | C_var c c'        -> Conj () (C_var (slice_c_sps c) (slice_c_sps c'))
  | C_let_e1 c c'     -> Conj () (C_let_e1 (slice_c_sps c) (slice_c_sps c'))
  | C_abs c c'        -> Conj () (C_abs (slice_c_sps c) (slice_c_sps c'))
  | C_app_e1 c c'     -> Conj () (C_app_e1 (slice_c_sps c) (slice_c_sps c'))
  | C_app_e2 c c'     -> Conj () (C_app_e2 (slice_c_sps c) (slice_c_sps c'))
  | C_unbox_red c c'  -> Conj () (C_unbox_red (slice_c_sps c) (slice_c_sps c'))
  | C_let_red c c'    -> Conj () (C_let_red (slice_c_sps c) (slice_c_sps c'))
  | C_app_red c c'    -> Conj () (C_app_red (slice_c_sps c) (slice_c_sps c'))
  | C_let_beta c c'   -> Conj () (C_let_beta (slice_c_sps c) (slice_c_sps c'))
  | C_app_beta c c'   -> Conj () (C_app_beta (slice_c_sps c) (slice_c_sps c'))
  | C_unbox_beta c c' -> Conj () (C_unbox_beta (slice_c_sps c) (slice_c_sps c'))

#reset-options

val is_exit_sec_config: c:sconfig -> Tot bool
let is_exit_sec_config c =
  is_sec c && is_value c && (Mode.m (Frame.m (Cons.hd (Conf.s c))) = Par)

val sstep_sec_slice_lemma: c:sconfig{is_sec c /\ not (is_exit_sec_config c)}
                           -> c':sconfig -> h:sstep c c'
                           -> Tot (cand (u:unit{Conf.m c' = Conf.m c})
                                        (sstep (slice_c_sps c) (slice_c_sps c')))
#set-options "--split_cases 1"
let sstep_sec_slice_lemma c c' h = match h with
  | C_step c c' h     ->
    let Conj _ p = cstep_sec_slice_lemma c c' h in
    Conj () (C_step (slice_c_sps c) (slice_c_sps c') p)
  | C_assec_ps c c'   -> Conj () (C_assec_ps (slice_c_sps c) (slice_c_sps c'))
  | C_assec_e c c'    -> Conj () (C_assec_e (slice_c_sps c) (slice_c_sps c'))
  | C_assec_red c c'  -> Conj () (C_assec_red (slice_c_sps c) (slice_c_sps c'))
  | C_assec_beta c c' -> Conj () (C_assec_beta (slice_c_sps c) (slice_c_sps c'))
  | C_assec_ret c c'  -> Conj () (C_assec_ret (slice_c_sps c) (slice_c_sps c'))

#reset-options

(**********)

val slice_v : #vps:eprins -> prin -> v:value vps -> Tot (r:dvalue{subset (DV.vps r) vps}) (decreases %[v])
val slice_en: prin -> en:env -> Tot (varname -> Tot dvalue) (decreases %[en])

let rec slice_v #vps p v =
  match v with
    | V_const _     -> DV vps v
    | V_box ps v'   ->
      let DV _ v'' = if mem p ps then slice_v p v' else DV empty V_emp in
      DV ps (V_box ps v'')
    | V_clos en x e -> DV empty (V_clos (slice_en p en) x e)
    | V_emp         -> DV vps v

and slice_en p en =
  let _ = () in
  fun x -> preceds_axiom en x; slice_v p (DV.v (en x))

assume val slice_emp_en: p:prin
                         -> Lemma (requires (True))
                                  (ensures (slice_en p empty_env = empty_env))
                            [SMTPat (slice_en p empty_env)]

val slice_e: prin -> exp -> Tot exp
let slice_e p e = e

val slice_r: prin -> redex -> Tot redex
let slice_r p r = match r with
  | R_aspar ps v  -> R_aspar ps (DV.v (slice_v p v))
  | R_assec ps v  -> R_assec ps (DV.v (slice_v p v))
  | R_box ps v    ->
    let DV _ v' = if mem p ps then slice_v p v else DV empty V_emp in
    R_box ps v'
  | R_unbox v     -> R_unbox (DV.v (slice_v p v))
  | R_let x v1 e2 -> R_let x (DV.v (slice_v p v1)) e2
  | R_app v1 v2   -> R_app (DV.v (slice_v p v1)) (DV.v (slice_v p v2))

val slice_f': p:prin -> f:frame'{not (is_F_assec_ret f)} -> Tot frame'
let slice_f' p f = match f with
  | F_aspar_ps _ -> f
  | F_aspar_e  _ -> f
  | F_assec_ps _ -> f
  | F_assec_e  _ -> f
  | F_box_e    _ -> f
  | F_unbox      -> f
  | F_let    _ _ -> f
  | F_app_e1   _ -> f
  | F_app_e2   v -> F_app_e2  (DV.v (slice_v p v))

val slice_f: p:prin -> f:frame{Mode.m (Frame.m f) = Par    /\
                               mem p (Mode.ps (Frame.m f)) /\
                               not (is_F_assec_ret (Frame.f f))}
                    -> Tot frame
let slice_f p (Frame _ en f) = Frame (Mode Par (singleton p)) (slice_en p en)
                                     (slice_f' p f)

val slice_s: p:prin -> s:stack
             -> Tot (r:stack{stack_target_inv r (Mode Par (singleton p))})
let rec slice_s p s = match s with
  | []     -> []
  | hd::tl ->
    if Mode.m (Frame.m hd) = Par    &&
       mem p (Mode.ps (Frame.m hd)) &&
       not (is_F_assec_ret (Frame.f hd))
     then
      (slice_f p hd)::(slice_s p tl)
    else
      slice_s p tl

val slice_t: p:prin -> t:term{not (t = T_sec_wait)} -> Tot term
let slice_t p t = match t with
  | T_val v -> T_val (DV.v (slice_v p v))
  | T_exp e -> t
  | T_red r -> T_red (slice_r p r)

val get_sec_ret_env: m:mode{Mode.m m = Sec} -> s:stack{stack_source_inv s m}
                     -> Tot env
let rec get_sec_ret_env m (Cons (Frame m' en s) tl) =
  if Mode.m m' = Par then en else get_sec_ret_env m tl

val slice_c: prin -> sconfig -> Tot tconfig
let rec slice_c p (Conf Source (Mode as_m ps) s en t) =
  let en', t' =
    if not (mem p ps) then empty_env, T_val V_emp
    else
      if as_m = Par then slice_en p en, slice_t p t
      else slice_en p (get_sec_ret_env (Mode as_m ps) s), T_sec_wait
  in
  Conf Target (Mode Par (singleton p)) (slice_s p s) en' t'

(**********)

val compose_vals: #vps1:eprins -> #vps2:eprins -> v1:value vps1 -> v2:value vps2
                  -> Tot (r:dvalue{subset (DV.vps r) (union vps1 vps2)})
                     (decreases %[v1])
val compose_envs: en:env -> env -> Tot (varname -> Tot dvalue) (decreases %[en])

let rec compose_vals #vps1 #vps2 v1 v2 =
  let def = DV empty V_emp in
  match v1 with
    | V_const c1 ->
      if is_V_const v2 && V_const.c v1 = V_const.c v2 then
        DV vps1 v1
      else def
      
    | V_box ps1 v1' ->
      if is_V_box v2 then
        let V_box ps2 v2' = v2 in
        if ps1 = ps2 then
          DV ps1 (V_box ps1 (DV.v (compose_vals v1' v2')))
        else
          def
      else def
      
    | V_clos en1 x1 e1 ->
      if is_V_clos v2 then
        let V_clos en2 x2 e2 = v2 in
        if x1 = x2 && e1 = e2 then
          DV vps1 (V_clos (compose_envs en1 en2) x1 e1)
        else def
      else def
      
    | V_emp -> DV vps2 v2
    
    | _ -> if is_V_emp v2 then DV vps1 v1 else def
      
and compose_envs en1 en2 =
  let _ = () in
  fun x -> preceds_axiom en1 x; compose_vals (DV.v (en1 x)) (DV.v (en2 x))

(*val slice_weakening: #vps:eprins -> v:value vps -> ps:prins
                     -> ps':prins{intersect ps' vps = empty}
                     -> Lemma (requires (True))
                              (ensures (slice_v_sps ps v = slice_v_sps (union ps ps') v))
                        (decreases %[v])
val slice_weakening_en: en:env -> ps:prins
                        -> ps':prins{intersect ps' vps = empty}
                        -> Lemma (requires (True))
                              (ensures (slice_en_sps ps en = slice_en_sps (union ps ps') v))
                           (decreases %[en])

let rec slice_weakening #vps v ps ps' = match v with
  | V_const _ -> ()
  
  | V_box ps'' v'' ->
    if intersect ps'' ps = empty then ()
    else
      slice_weakening v'' ps ps'
      
  | 
  
  | _ -> admit ()
  *)
(* check_marker *)


(*
let t_union (p1:prin) (p2:prin) :prins = insert p1 (insert p2 empty)

val compose_vals_lemma_prin: v:value -> p1:prin -> p2:prin
                             -> Lemma (requires (True))
                                      (ensures (compose_vals (slice_v p1 v)
                                                             (slice_v p2 v)
                                                = slice_v_sps (t_union p1 p2) v))
                                      (decreases %[v])
val compose_envs_lemma_prin: en:env -> p1:prin -> p2:prin
                             -> Lemma (requires (True))
                                      (ensures (compose_envs (slice_en p1 en)
                                                             (slice_en p2 en)
                                                = slice_en_sps (t_union p1 p2) en))
                                      (decreases %[en])

let rec compose_vals_lemma_prin v p1 p2 =
  let ps1, ps2 = singleton p1, singleton p2 in
  match v with
    | V_const _     -> ()
    | V_box ps v'   ->
      if mem p1 ps && mem p2 then
        let _ = mem_intersect p1 ps (t_union p1 p2) in
        let _ = compose_vals_lemma_prin v' p1 p2 in
        ()
      else
        admit ()
    | V_clos en x e -> admit ()//; compose_envs_lemma_prin en p1 p2
    | _ -> admit ()

and compose_envs_lemma_prin en p1 p2 = admit ()
                                      
                              
(* check_marker *)

val compose_vals_lemma: v:value -> ps:prins -> p:prin
                        -> Lemma (requires (True))
                                 (ensures (compose_vals (slice_v p v)
                                                        (slice_v_sps ps v)
                                           = slice_v_sps (insert p ps) v))
                           (decreases %[v; size ps])
val compose_envs_lemma: en:env -> ps:prins -> p:prin
                        -> Lemma (requires (True))
                                 (ensures (compose_envs (slice_en p en)
                                                        (slice_en_sps ps en)
                                           = slice_en_sps (insert p ps) en))
                           (decreases %[en; size ps])

let rec compose_vals_lemma v ps p =
  if is_singleton ps then
    
  else
    admit ()

and compose_envs_lemma en ps p = admit ()*)

(* check_marker *)

(*

type value_map = OrdMap.ordmap prin value p_cmp
type env_map = OrdMap.ordmap prin env p_cmp

val mempty: #key:Type -> #value:Type -> #f:cmp key -> Tot (OrdMap.ordmap key value f)
let mempty (#k:Type) (#v:Type) #f = OrdMap.empty #k #v #f

val mremove  : #key:Type -> #value:Type -> #f:cmp key -> key
               -> OrdMap.ordmap key value f -> Tot (OrdMap.ordmap key value f)
val mchoose  : #key:Type -> #value:Type -> #f:cmp key -> OrdMap.ordmap key value f
               -> Tot (option (key * value))

val msize    : #key:Type -> #value:Type -> #f:cmp key -> OrdMap.ordmap key value f
               -> Tot nat

let mremove (#k:Type) (#v:Type) #f = OrdMap.remove #k #v #f
let mchoose (#k:Type) (#v:Type) #f = OrdMap.choose #k #v #f
let msize (#k:Type) (#v:Type) #f = OrdMap.size #k #v #f

val compose_vals_m: m:value_map{not (m = mempty)} -> Tot value (decreases (msize m))
let rec compose_vals_m m =
  let Some (p, v) = mchoose m in
  let m_rest = mremove p m in
  if m_rest = mempty then v
  else 
    let v' = compose_vals_m m_rest in
    compose_vals v v'

assume val map_axiom: #k:Type -> #v:Type -> #f:cmp k -> m:OrdMap.ordmap k v f
                      -> x:k -> y:v -> Lemma (requires (True))
                                             (ensures (not (update x y m = mempty)))
                                      [SMTPat (update x y m)] 

val get_x_map: m:env_map{not (m = mempty)} -> x:varname
               -> Tot (r:value_map{not (r = mempty)}) (decreases (msize m))
let rec get_x_map m x =
  let Some (p, en) = mchoose m in
  let m_rest = mremove p m in
  if m_rest = mempty then update p (en x) mempty
  else
    let m' = get_x_map (mremove p m) x in
    update p (en x) m'

val compose_envs_m: m:env_map{not (m = mempty)} -> Tot env (decreases (msize m))
let compose_envs_m m = fun x -> compose_vals_m (get_x_map m x)

val compose_vals_lemma: m:value_map{not (m = mempty)} -> v:value
                        -> Lemma (requires (forall p. contains p m ==>
                                                      (Some.v (select p m) = slice_v p v)))
                                 (ensures (compose_vals_m m = slice_v_sps (dom m) v))
                                 (decreases %[msize m; v])
val compose_envs_lemma: m:env_map{not (m = mempty)} -> en:env
                       -> Lemma (requires (forall p. contains p m ==>
                                                     (Some.v (select p m) = slice_en p en)))
                                (ensures (compose_envs_m m = slice_en_sps (dom m) en))
                                (decreases %[msize m; en])
                              
let rec compose_vals_lemma m v = 

and compose_env_lemma m en = admit ()


type tpar = OrdMap.ordmap prin tconfig p_cmp

type protocol = tpar * option tconfig

val slice_c_ps_par: ps:prins -> sconfig -> Tot tpar (decreases (size ps))
let rec slice_c_ps_par ps c =
  if ps = empty then OrdMap.empty
  else
    let Some p = choose ps in
    let ps_rest = remove p ps in
    let pi' = slice_c_ps_par ps_rest c in
    OrdMap.update p (slice_c p c) pi'

val slice_c_ps: ps:prins -> c:sconfig{subset (Mode.ps (Conf.m c)) ps}
                -> Tot protocol
let slice_c_ps ps c =
  let pi = slice_c_ps_par ps c in
  let tsec = if is_sec c then Some (slice_c_sps c) else None in
  pi, tsec


(**********)

type cforall: #a:Type -> (a -> Type) -> Type =
  | ForallIntro: #a:Type -> p:(a -> Type) -> f:(x:a -> p x)
                 -> cforall p

type composable_vals: value -> value -> Type =
  | Composable_const:
    c1:const -> c2:const{c1 = c2}
    -> composable_vals (V_const c1) (V_const c2)
    
  | Composable_box:
    ps1:prins -> ps2:prins{ps1 = ps2} -> v1:value -> v2:value
    -> h:composable_vals v1 v2 -> composable_vals (V_box ps1 v1) (V_box ps2 v2)
  
  | Composable_clos:
    en1:env -> en2:env -> h:(composable_envs en1 en2)
    -> x1:varname -> x2:varname{x1 = x2}
    -> e1:exp -> e2:exp{e1 = e2}
    -> composable_vals (V_clos en1 x1 e1) (V_clos en2 x2 e2)
    
  | Composable_emp_l:
    v:value -> composable_vals V_emp v

  | Composable_emp_r:
    v:value -> composable_vals v V_emp
    
and composable_envs: (env -> env -> Type) =
  | Composable_en:
    en1:env -> en2:env -> h:cforall (fun x -> composable_vals (en1 x) (en2 x))
    -> composable_envs en1 en2*)


(*val compose_vals: value -> value -> Tot value
val compose_ens: varname -> Tot 

let rec compose_vals v1 v2 = match v1, v2 with
  | V_const c1, V_const c2 ->
    if c1 = c2 then Some (V_const c1) else None
    
  | V_box ps1 v1, V_box ps2 v2 ->
    if ps1 = ps2 then V_box ps1 (compose_vals v1 v2) else None
  
  | V_clos 

type tstep: protocol -> protocol -> Type =

  | T_cstep:
    pi:protocol -> p:prin{OrdMap.contains p (fst pi)} -> c':tconfig
    -> h:cstep (Some.v (OrdMap.select p (fst pi))) c'
    -> tstep pi (OrdMap.update p c' (fst pi), snd pi)
  
  | T_secstep:
    pi:protocol{is_Some (snd pi)} -> c':tconfig
    -> h:sstep (Some.v (snd pi)) c'
    -> tstep pi (fst pi, Some c')


(**********)
open Constructive
open FunctionalExtensionality

val env_upd_slice_lemma: p:prin -> en:env -> x:varname -> v:value
                         -> Lemma (requires (True))
                                  (ensures (slice_en p (update_env en x v) =
                                            update_env (slice_en p en) x (slice_v p v)))
let env_upd_slice_lemma p en x v =
  cut (FEq (slice_en p (update_env en x v))
      (update_env (slice_en p en) x (slice_v p v)))

opaque val cstep_lemma: #c:sconfig -> #c':sconfig -> h:cstep c c' -> p:prin
                        -> Tot (cor (u:unit{slice_c p c = slice_c p c'})
                               (cstep (slice_c p c) (slice_c p c')))
#set-options "--max_fuel 2 --initial_fuel 2 --initial_ifuel 2 --max_ifuel 2 --split_cases 1"
let cstep_lemma #c #c' h p = match h with
  | C_aspar_ps (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_aspar_ps (slice_c p c) (slice_c p c'))
  | C_unbox (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_unbox (slice_c p c) (slice_c p c'))
  | C_const (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_const (slice_c p c) (slice_c p c'))
  | C_var (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_var (slice_c p c) (slice_c p c'))
  | C_let_e1 (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_let_e1 (slice_c p c) (slice_c p c'))
  | C_abs (Conf _ m _ en _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      IntroR (C_abs (slice_c p c) (slice_c p c'))
  | C_app_e1 (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_app_e1 (slice_c p c) (slice_c p c'))
  | C_aspar_e (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_aspar_e (slice_c p c) (slice_c p c'))
  | C_app_e2 (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_app_e2 (slice_c p c) (slice_c p c'))
  | C_aspar_red (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_aspar_red (slice_c p c) (slice_c p c'))
  | C_box_red (Conf _ m s _ _) _ ->
    if mem p (Mode.ps m) then
      IntroR (C_box_red (slice_c p c) (slice_c p c'))
    else if mem p (Mode.ps (Frame.m (Cons.hd s))) then
      IntroR (C_box_red (slice_c p c) (slice_c p c'))
    else IntroL ()
  | C_unbox_red (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_unbox_red (slice_c p c) (slice_c p c'))
  | C_let_red (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_let_red (slice_c p c) (slice_c p c'))
  | C_app_red (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_app_red (slice_c p c) (slice_c p c'))
  | C_let_beta (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      let Conf _ _ _ en (T_red (R_let x v _)) = c in
      let _ = env_upd_slice_lemma p en x v in
      IntroR (C_let_beta (slice_c p c) (slice_c p c'))
  | C_app_beta (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      let T_red (R_app (V_clos en x _) v) = Conf.t c in
      env_upd_slice_lemma p en x v;
      IntroR (C_app_beta (slice_c p c) (slice_c p c'))
  | C_aspar_beta (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      let T_red (R_aspar _ (V_clos en x _)) = Conf.t c in
      env_upd_slice_lemma p en x (V_const (C_unit));
      IntroR (C_aspar_beta (slice_c p c) (slice_c p c'))
  | C_box_beta (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      IntroR (C_box_beta (slice_c p c) (slice_c p c'))
  | C_unbox_beta (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      IntroR (C_unbox_beta (slice_c p c) (slice_c p c'))

(**********)

#reset-options

open OrdMap

type protocol = ordmap prin tconfig p_cmp

val slice_c_ps: ps:prins -> sconfig -> Tot protocol (decreases (OrdSet.size ps))
let rec slice_c_ps ps c =
  if ps = OrdSet.empty then OrdMap.empty
  else
    let Some p = OrdSet.choose ps in
    let ps_rest = OrdSet.remove p ps in
    let pi' = slice_c_ps ps_rest c in
    OrdMap.update p (slice_c p c) pi'

val dom_slice_lemma: ps:prins -> c:sconfig
                     -> Lemma (requires (True)) (ensures (dom (slice_c_ps ps c) = ps))
                        (decreases (OrdSet.size ps))
                        [SMTPat (slice_c_ps ps c)]
let rec dom_slice_lemma ps c =
  if ps = OrdSet.empty then ()
  else
    dom_slice_lemma (OrdSet.remove (Some.v (OrdSet.choose ps)) ps) c

type pstep: protocol -> protocol -> Type =

  | P_cstep:
    pi:protocol -> p:prin{contains p pi} -> c':tconfig
    -> h:cstep (Some.v (select p pi)) c'
    -> pstep pi (update p c' pi)

type pstep_star: protocol -> protocol -> Type =

  | PS_refl:
    pi:protocol -> pstep_star pi pi
    
  | PS_tran:
    #pi:protocol -> #pi':protocol -> #pi'':protocol
    -> h1:pstep pi pi' -> h2:pstep_star pi' pi''
    -> pstep_star pi pi''

val pstep_upd: #pi:protocol -> #pi':protocol -> h:pstep pi pi'
               -> p:prin{not (contains p pi)} -> c:tconfig
               -> Tot (pstep (update p c pi) (update p c pi'))
let pstep_upd #pi #pi' h p c =
  let P_cstep _ p' c' h' = h in
  P_cstep (update p c pi) p' c' h'

val pstep_star_upd: #pi:protocol -> #pi':protocol -> h:pstep_star pi pi'
                    -> p:prin{not (contains p pi)} -> c:tconfig
                    -> Tot (pstep_star (update p c pi) (update p c pi'))
                       (decreases h)
let rec pstep_star_upd #pi #pi' h p c = match h with
  | PS_refl pi                -> PS_refl (update p c pi)
  | PS_tran #pi #pi' #pi'' h1 h2 ->
    PS_tran (pstep_upd h1 p c) (pstep_star_upd #pi' #pi'' h2 p c)

opaque val forward_simulation: c:sconfig -> c':sconfig -> h:cstep c c' -> ps:prins
                               -> Tot (cexists (fun pi' -> cand (pstep_star (slice_c_ps ps c) pi')
                                                                (u:unit{pi' = slice_c_ps ps c'})))
                                  (decreases (OrdSet.size ps))
let rec forward_simulation c c' h ps =
  if ps = OrdSet.empty then
    ExIntro empty (Conj (PS_refl empty) ())
  else
    let Some p = OrdSet.choose ps in
    let ps_rest = OrdSet.remove p ps in
    let pi_rest = slice_c_ps ps_rest c in
    //h1 is the pstep_star of ps_rest protocol
    let ExIntro pi_rest' (Conj h1 _) = forward_simulation c c' h ps_rest in
    //h2 is the step or same for p
    let h2 = cstep_lemma h p in
    let tc_p = slice_c p c in
    match h2 with
      | IntroL _  -> ExIntro (update p tc_p pi_rest')
                             (Conj (pstep_star_upd h1 p tc_p) ())
      | IntroR hp ->
        let tc_p' = slice_c p c' in
        let h1' = pstep_star_upd h1 p tc_p' in
        let h2' = P_cstep (update p tc_p pi_rest) p tc_p' hp in
        ExIntro (update p tc_p' pi_rest') (Conj (PS_tran h2' h1') ())*)
