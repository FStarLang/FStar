(*--build-config
    options:--admit_fsi OrdSet --admit_fsi OrdMap --z3timeout 10;
    variables:LIB=../../lib;
    other-files:$LIB/ordset.fsi $LIB/ordmap.fsi $LIB/list.fst $LIB/constr.fst $LIB/ext.fst $LIB/classical.fst
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
  | E_aspar : ps:exp -> e:exp -> exp'
  | E_assec : ps:exp -> e:exp -> exp'
  | E_unbox : e:exp  -> exp'

  | E_const : c:const -> exp'
  | E_var   : x:varname -> exp'
  | E_let   : x:varname -> e1:exp -> e2:exp -> exp'
  | E_abs   : x:varname -> e:exp -> exp'
  | E_empabs: x:varname -> e:exp -> exp'
  | E_app   : e1:exp -> e2:exp -> exp'

and exp =
  | Exp: e:exp' -> info:option other_info -> exp

type canbox = | Can_b | Cannot_b

type v_meta = eprins * canbox

type value: v_meta -> Type =
  | V_const   : c:const -> value (empty, Can_b)

  | V_box     : #meta:v_meta -> ps:prins
                -> v:value meta{subset (fst meta) ps /\ (snd meta) = Can_b}
                -> value (ps, Can_b)

  | V_clos    : en:env -> x:varname -> e:exp -> value (empty, Cannot_b)

  | V_emp_clos: x:varname -> e:exp -> value (empty, Can_b)

  (* bomb value, comes up in target only *)
  | V_emp     : value (empty, Can_b)

and dvalue:Type =
  | D_v: meta:v_meta -> v:value meta -> dvalue

and env = varname -> Tot (option dvalue)

assume val preceds_axiom: en:env -> x:varname -> Lemma (ensures (en x << en))

type redex =
  | R_aspar: #meta:v_meta -> ps:prins -> v:value meta -> redex
  | R_assec: #meta:v_meta -> ps:prins -> v:value meta -> redex
  | R_box  : #meta:v_meta -> ps:prins -> v:value meta -> redex
  | R_unbox: #meta:v_meta -> v:value meta -> redex
  | R_let  : #meta:v_meta -> x:varname -> v:value meta -> e:exp -> redex
  | R_app  : #meta1:v_meta -> #meta2:v_meta -> v1:value meta1 -> v2:value meta2
             -> redex

val empty_env: env
let empty_env = fun _ -> None

val update_env: #meta:v_meta -> env -> varname -> value meta -> Tot env
let update_env #meta en x v = fun y -> if y = x then Some (D_v meta v) else en y

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
  | F_app_e2   : #meta:v_meta -> v:value meta -> frame'

type frame =
  | Frame: m:mode -> en:env -> f:frame'-> frame

type stack = list frame

type term =
  | T_exp     : e:exp -> term
  | T_red     : r:redex -> term
  | T_val     : #meta:v_meta -> v:value meta -> term

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
    (not (as_m = Par) || as_m' = Par)                              &&
    (not (as_m = Par) || not (is_F_assec_ret f'))                  &&
    (not (as_m = Sec) || (not (as_m' = Par) || is_F_assec_ret f')) &&
    (not (as_m' = Sec) || (is_sec_frame f' && is_Cons tl))         &&
    (not (is_F_box_e f') || (ps = F_box_e.ps f'))                  &&
    (ps = ps' || (subset ps ps' && is_F_box_e f'))                 &&
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

val c_value: c:config{is_value c} -> Tot dvalue
let c_value (Conf _ _ _ _ (T_val #meta v)) = D_v meta v

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

type pre_eempabs (c:config) =
  is_T_exp (Conf.t c) /\ is_E_empabs (Exp.e (T_exp.e (Conf.t c)))

type pre_elet (c:config) =
  is_T_exp (Conf.t c) /\ is_E_let (Exp.e (T_exp.e (Conf.t c)))

type pre_evar (c:config) =
  is_T_exp (Conf.t c) /\ is_E_var (Exp.e (T_exp.e (Conf.t c))) /\
  is_Some ((Conf.en c) (E_var.x (Exp.e (T_exp.e (Conf.t c)))))

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
  let Some (D_v _ v) = en x in
  Conf l m s en (T_val v)

val step_let_e1: c:config{pre_elet c} -> Tot config
let step_let_e1 (Conf l m s en (T_exp (Exp (E_let x e1 e2) _))) =
  Conf l m ((Frame m en (F_let x e2))::s) en (T_exp e1)

val step_abs: c:config{pre_eabs c} -> Tot config
let step_abs (Conf l m s en (T_exp (Exp (E_abs x e) _))) =
  Conf l m s en (T_val (V_clos en x e))

val step_empabs: c:config{pre_eempabs c} -> Tot config
let step_empabs (Conf l m s en (T_exp (Exp (E_empabs x e) _))) =
  Conf l m s en (T_val (V_emp_clos x e))

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

val is_clos: #meta:v_meta -> value meta -> Tot bool
let is_clos #meta v = is_V_clos v || is_V_emp_clos v

val get_en_b: #meta:v_meta -> v:value meta{is_clos v} -> Tot (env * varname * exp)
let get_en_b #meta v = match v with
  | V_clos en x e  -> en, x, e
  | V_emp_clos x e -> empty_env, x, e

val pre_aspar: config -> Tot comp
let pre_aspar c = match c with
  | Conf l (Mode Par ps1) _ _ (T_red (R_aspar ps2 v)) ->
    if is_clos v then
      if src l then
        if subset ps2 ps1 then Do else NA
      else
        if subset ps1 ps2 then Do else Skip
    else NA

  | _ -> NA

val step_aspar: c:config{not (pre_aspar c = NA)} -> Tot config
let step_aspar c = match c with
  | Conf l m s en' (T_red (R_aspar ps v)) ->
    let en, x, e = get_en_b v in
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
  | Conf l (Mode Par ps1) _ _ (T_red (R_box #meta ps2 _)) ->
    let (ps', b) = meta in
    if subset ps' ps2 && is_Can_b b then
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
      if not (intersect ps1 ps2 = empty) then Do else NA

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
  | Conf _ _ _ _ (T_red (R_app v _)) -> is_clos v

  | _ -> false

val step_app: c:config{is_app_redex c} -> Tot config
let step_app c = match c with
  | Conf l m s _ (T_red (R_app f v)) ->
    let (en, x, e) = get_en_b f in
    Conf l m s (update_env en x v) (T_exp e)

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
  | Conf l (Mode as_m ps1) _ _ (T_red (R_assec ps2 v)) ->
    if is_clos v then
      if l = Source || as_m = Sec then
        if ps1 = ps2 then Do else NA
      else NA
    else NA

  | _ -> NA

val step_assec: c:config{not (pre_assec c = NA)} -> Tot config
let step_assec c = match c with
  | Conf l m s en' (T_red (R_assec ps v)) ->
    let (en, x, e) = get_en_b v in
    Conf l (Mode Sec ps) ((Frame m en' F_assec_ret)::s)
           (update_env en x (V_const C_unit)) (T_exp e)

val step_assec_ret: c:config{is_value c /\ is_sframe c is_F_assec_ret}
                    -> Tot config
let step_assec_ret (Conf l _ ((Frame m en F_assec_ret)::s) _ t) = Conf l m s en t

type sstep: config -> config -> Type =

  | C_aspar_ps:
    c:config{pre_easpar c} -> c':config{c' = step_aspar_e1 c}
    -> sstep c c'

  | C_unbox:
    c:config{pre_eunbox c} -> c':config{c' = step_unbox_e c}
    -> sstep c c'

  | C_const:
    c:config{pre_econst c} -> c':config{c' = step_const c}
    -> sstep c c'

  | C_var:
    c:config{pre_evar c} -> c':config{c' = step_var c}
    -> sstep c c'

  | C_let_e1:
    c:config{pre_elet c} -> c':config{c' = step_let_e1 c}
    -> sstep c c'

  | C_abs:
    c:config{pre_eabs c} -> c':config{c' = step_abs c}
    -> sstep c c'

  | C_empabs:
    c:config{pre_eempabs c} -> c':config{c' = step_empabs c}
    -> sstep c c'

  | C_app_e1:
    c:config{pre_eapp c} -> c':config{c' = step_app_e1 c}
    -> sstep c c'

  | C_aspar_e:
    c:config{is_value_ps c /\ is_sframe c is_F_aspar_ps}
    -> c':config{c' = step_aspar_e2 c}
    -> sstep c c'

  | C_app_e2:
    c:config{is_value c /\ is_sframe c is_F_app_e1}
    -> c':config{c' = step_app_e2 c}
    -> sstep c c'

  | C_aspar_red:
    c:config{is_value c /\ is_sframe c is_F_aspar_e}
    -> c':config{c' = step_aspar_red c}
    -> sstep c c'

  | C_box_red:
    c:config{is_value c /\ is_sframe c is_F_box_e}
    -> c':config{c' = step_box_red c}
    -> sstep c c'

  | C_unbox_red:
    c:config{is_value c /\ is_sframe c is_F_unbox}
    -> c':config{c' = step_unbox_red c}
    -> sstep c c'

  | C_let_red:
    c:config{is_value c /\ is_sframe c is_F_let}
    -> c':config{c' = step_let_red c}
    -> sstep c c'

  | C_app_red:
    c:config{is_value c /\ is_sframe c is_F_app_e2}
    -> c':config{c' = step_app_red c}
    -> sstep c c'

  | C_let_beta:
    c:config{is_let_redex c} -> c':config{c' = step_let c} -> sstep c c'

  | C_app_beta:
    c:config{is_app_redex c} -> c':config{c' = step_app c} -> sstep c c'

  | C_aspar_beta:
    c:config{not (pre_aspar c = NA)} -> c':config{c' = step_aspar c}
    -> sstep c c'

  | C_box_beta:
    c:config{pre_box c = Do} -> c':config{c' = step_box c} -> sstep c c'

  | C_unbox_beta:
    c:config{pre_unbox c = Do} -> c':config{c' = step_unbox c}
    -> sstep c c'
    
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

type slice_v_meta_inv (meta:v_meta) (smeta:v_meta) =
  subset (fst smeta) (fst meta) && (snd smeta = snd meta)

val slice_v_sps : #meta:v_meta -> prins -> v:value meta
                  -> Tot (r:dvalue{slice_v_meta_inv meta (D_v.meta r)}) (decreases %[v])
val slice_en_sps: prins -> en:env -> Tot (varname -> Tot (option dvalue)) (decreases %[en])

let rec slice_v_sps #meta ps v =
  let def = D_v meta v in
  let emp = D_v (empty, Can_b) V_emp in
  match v with
   | V_const _      -> def

   | V_box ps' v    ->
     let D_v _ v' =
       if intersect ps' ps = empty then emp
       else slice_v_sps ps v
     in
     D_v meta (V_box ps' v')

   | V_clos en x e  -> D_v meta (V_clos (slice_en_sps ps en) x e)

   | V_emp_clos _ _ -> def

   | V_emp          -> emp

and slice_en_sps ps en =
 let _ = () in
 fun x -> preceds_axiom en x;
          if en x = None then None
          else
            Some (slice_v_sps ps (D_v.v (Some.v (en x))))

open FunctionalExtensionality            

val slice_emp_en_sps: ps:prins
                      -> Lemma (requires (True))
                               (ensures (slice_en_sps ps empty_env = empty_env))
                         [SMTPat (slice_en_sps ps empty_env)]
let slice_emp_en_sps ps =
  let _ = cut (FEq (slice_en_sps ps empty_env) empty_env) in
  ()

val slice_e_sps: prins -> exp -> Tot exp
let slice_e_sps ps e = e

val slice_r_sps: prins -> r:redex{is_sec_redex r} -> Tot redex
let slice_r_sps ps r = match r with
  | R_assec ps' v -> R_assec ps' (D_v.v (slice_v_sps ps v))
  | R_unbox v     -> R_unbox (D_v.v (slice_v_sps ps v))
  | R_let x v1 e2 -> R_let x (D_v.v (slice_v_sps ps v1)) e2
  | R_app v1 v2   -> R_app (D_v.v (slice_v_sps ps v1)) (D_v.v (slice_v_sps ps v2))

val slice_f'_sps: ps:prins -> f:frame'{is_sec_frame f} -> Tot frame'
let slice_f'_sps ps f = match f with
  | F_assec_ps _ -> f
  | F_assec_e  _ -> f
  | F_assec_ret  -> f
  | F_unbox      -> f
  | F_let    _ _ -> f
  | F_app_e1   _ -> f
  | F_app_e2   v -> F_app_e2  (D_v.v (slice_v_sps ps v))

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
  | T_val v -> T_val (D_v.v (slice_v_sps ps v))

val slice_c_sps: c:sconfig{is_sec c} -> Tot tconfig
let slice_c_sps (Conf _ (Mode Sec ps) s en t) =
    Conf Target (Mode Sec ps) (slice_s_sps ps s) (slice_en_sps ps en)
                (slice_t_sps ps t)

val env_upd_slice_lemma_ps: #meta:v_meta -> ps:prins -> en:env -> x:varname
                            -> v:value meta
                            -> Lemma (requires (True))
                                     (ensures (slice_en_sps ps (update_env en x v) =
                                               update_env (slice_en_sps ps en) x (D_v.v (slice_v_sps ps v))))
                                     [SMTPat (slice_en_sps ps (update_env en x v))]
let env_upd_slice_lemma_ps #meta ps en x v =
  cut (FEq (slice_en_sps ps (update_env en x v))
      (update_env (slice_en_sps ps en) x (D_v.v (slice_v_sps ps v))))

open Constructive

val if_exit_sec_then_to_sec: #c:sconfig -> #c':config -> h:sstep c c' -> Tot bool
let if_exit_sec_then_to_sec #c #c' h = not (is_C_assec_ret h) || is_sec c'

opaque val sstep_sec_slice_lemma: c:sconfig{is_sec c}
                                  -> c':sconfig -> h:sstep c c'{if_exit_sec_then_to_sec h}
                                  -> Tot (cand (u:unit{Conf.m c' = Conf.m c})
                                               (sstep (slice_c_sps c) (slice_c_sps c')))
#set-options "--split_cases 1"
let sstep_sec_slice_lemma c c' h = match h with
  | C_unbox c c'      -> Conj () (C_unbox (slice_c_sps c) (slice_c_sps c'))
  | C_const c c'      -> Conj () (C_const (slice_c_sps c) (slice_c_sps c'))
  | C_var c c'        -> Conj () (C_var (slice_c_sps c) (slice_c_sps c'))
  | C_let_e1 c c'     -> Conj () (C_let_e1 (slice_c_sps c) (slice_c_sps c'))
  | C_abs c c'        -> Conj () (C_abs (slice_c_sps c) (slice_c_sps c'))
  | C_empabs c c'     -> Conj () (C_empabs (slice_c_sps c) (slice_c_sps c'))
  | C_app_e1 c c'     -> Conj () (C_app_e1 (slice_c_sps c) (slice_c_sps c'))
  | C_app_e2 c c'     -> Conj () (C_app_e2 (slice_c_sps c) (slice_c_sps c'))
  | C_unbox_red c c'  -> Conj () (C_unbox_red (slice_c_sps c) (slice_c_sps c'))
  | C_let_red c c'    -> Conj () (C_let_red (slice_c_sps c) (slice_c_sps c'))
  | C_app_red c c'    -> Conj () (C_app_red (slice_c_sps c) (slice_c_sps c'))
  | C_let_beta c c'   -> Conj () (C_let_beta (slice_c_sps c) (slice_c_sps c'))
  | C_app_beta c c'   -> Conj () (C_app_beta (slice_c_sps c) (slice_c_sps c'))
  | C_unbox_beta c c' -> Conj () (C_unbox_beta (slice_c_sps c) (slice_c_sps c'))
  | C_assec_ps c c'   -> Conj () (C_assec_ps (slice_c_sps c) (slice_c_sps c'))
  | C_assec_e c c'    -> Conj () (C_assec_e (slice_c_sps c) (slice_c_sps c'))
  | C_assec_red c c'  -> Conj () (C_assec_red (slice_c_sps c) (slice_c_sps c'))
  | C_assec_beta c c' -> Conj () (C_assec_beta (slice_c_sps c) (slice_c_sps c'))
  | C_assec_ret c c'  -> Conj () (C_assec_ret (slice_c_sps c) (slice_c_sps c'))

#reset-options

(**********)

val slice_v : #meta:v_meta -> prin -> v:value meta
              -> Tot (r:dvalue{slice_v_meta_inv meta (D_v.meta r)}) (decreases %[v])
val slice_en: prin -> en:env -> Tot (varname -> Tot (option dvalue)) (decreases %[en])

let rec slice_v #meta p v =
  let def = D_v meta v in
  let emp = D_v (empty, Can_b) V_emp in
  match v with
    | V_const _      -> def

    | V_box ps v     ->
      let D_v _ v' = if mem p ps then slice_v p v else emp in
      D_v meta (V_box ps v')

    | V_clos en x e  -> D_v meta (V_clos (slice_en p en) x e)

    | V_emp_clos _ _ -> def

    | V_emp          -> emp

and slice_en p en =
  let _ = () in
  fun x -> preceds_axiom en x;
           if en x = None then None
           else
             Some (slice_v p (D_v.v (Some.v (en x))))

val slice_emp_en: p:prin
                  -> Lemma (requires (True))
                           (ensures (slice_en p empty_env = empty_env))
                     [SMTPat (slice_en p empty_env)]
let slice_emp_en p =
  let _ = cut (FEq (slice_en p empty_env) empty_env) in
  ()

val slice_e: prin -> exp -> Tot exp
let slice_e p e = e

val slice_r: prin -> redex -> Tot redex
let slice_r p r = match r with
  | R_aspar ps v  -> R_aspar ps (D_v.v (slice_v p v))
  | R_assec ps v  -> R_assec ps (D_v.v (slice_v p v))
  | R_box ps v    ->
    let D_v _ v' = if mem p ps then slice_v p v else D_v (empty, Can_b) V_emp in
    R_box ps v'
  | R_unbox v     -> R_unbox (D_v.v (slice_v p v))
  | R_let x v1 e2 -> R_let x (D_v.v (slice_v p v1)) e2
  | R_app v1 v2   -> R_app (D_v.v (slice_v p v1)) (D_v.v (slice_v p v2))

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
  | F_app_e2   v -> F_app_e2  (D_v.v (slice_v p v))

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
  | T_val v -> T_val (D_v.v (slice_v p v))
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
  
type compose_v_meta_inv (m1:v_meta) (m2:v_meta) (cmeta:v_meta) =
  subset (fst cmeta) (union (fst m1) (fst m2)) /\
  ((snd m1 = Can_b /\ snd m2 = Can_b) ==> snd cmeta = Can_b)

val compose_vals: #m1:v_meta -> #m2:v_meta -> v1:value m1 -> v2:value m2
                  -> Tot (r:dvalue{compose_v_meta_inv m1 m2 (D_v.meta r)})
                     (decreases %[v1])
val compose_envs: en:env -> env -> Tot (varname -> Tot (option dvalue)) (decreases %[en])

let rec compose_vals #m1 #m2 v1 v2 =
  if is_V_emp v1 then D_v m2 v2
  else if is_V_emp v2 then D_v m1 v1
  else
    let emp = D_v (empty, Can_b) V_emp in
    match v1 with
      | V_const c1 ->
        if is_V_const v2 && V_const.c v1 = V_const.c v2 then
          D_v m1 v1
        else emp

      | V_box ps1 v1 ->
        if is_V_box v2 then
          let V_box ps2 v2 = v2 in
          if ps1 = ps2 then
            D_v m1 (V_box ps1 (D_v.v (compose_vals v1 v2)))
          else
            emp
        else emp

      | V_clos en1 x1 e1 ->
        if is_V_clos v2 then
          let V_clos en2 x2 e2 = v2 in
          if x1 = x2 && e1 = e2 then
            D_v m1 (V_clos (compose_envs en1 en2) x1 e1)
          else emp
        else emp

      | V_emp_clos x1 e1 ->
        if is_V_emp_clos v2 then
          let V_emp_clos x2 e2 = v2 in
          if x1 = x2 && e1 = e2 then
            D_v m1 (V_emp_clos x1 e1)
          else emp
        else emp

and compose_envs en1 en2 =
  let _ = () in
  fun x -> preceds_axiom en1 x;
           let r1 = en1 x in
           let r2 = en2 x in
           match r1 with
             | None             -> r2
             | Some (D_v m1 v1) ->
               match r2 with
                 | None             -> r1
                 | Some (D_v m2 v2) -> Some (compose_vals v1 v2)

(**********)

open Classical

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
  | V_const _      -> ()
  | V_box ps v     -> if mem p ps then slice_lem_singl_v v p else ()
  | V_clos en _ _  -> slice_lem_singl_en en p
  | V_emp_clos _ _ -> ()
  | V_emp          -> ()

and slice_lem_singl_en_x en p x =
  if en x = None then ()
  else (preceds_axiom en x; slice_lem_singl_v (D_v.v (Some.v (en x))) p)

and slice_lem_singl_en en p =
  forall_intro #varname #(fun x -> b2t ((slice_en p en) x =
                                        (slice_en_sps (singleton p) en) x))
                        (slice_lem_singl_en_x en p);
  let _ = cut (FEq (slice_en p en) (slice_en_sps (singleton p) en)) in
  ()

val box_slice_lem: #m:v_meta -> v:value m
                   -> ps1:prins -> ps2:prins{not (intersect ps1 ps2 = empty) /\
                                             subset (fst m) ps2 /\ snd m = Can_b}
                   -> Lemma (requires (True))
                            (ensures (slice_v_sps ps1 (V_box ps2 v) =
                                      slice_v_sps (intersect ps1 ps2) (V_box ps2 v)))
                      (decreases v)
let rec box_slice_lem #m v ps1 ps2 = match v with
  | V_const _        -> ()  
  | V_box #m' ps' v' ->
    let _ = assert (subset ps' ps2) in
    if intersect ps1 ps' = empty then ()
    else
      let _ = assert (intersect ps1 ps' = intersect (intersect ps1 ps2) ps') in
      box_slice_lem v' ps1 ps';
      box_slice_lem v' (intersect ps1 ps2) ps';
      ()
  | V_emp_clos _ _   -> ()
  | V_emp            -> ()

let t_union (p1:prin) (p2:prin) :prins = union (singleton p1) (singleton p2)

val slc_v_lem_2: #m:v_meta -> v:value m -> p1:prin -> p2:prin
                 -> Lemma (requires (True))
                          (ensures (compose_vals (D_v.v (slice_v p1 v)) (D_v.v (slice_v p2 v)) =
                                    slice_v_sps (t_union p1 p2) v))
                    (decreases %[v])
val slc_en_x_lem_2: en:env -> p1:prin -> p2:prin -> x:varname
                    -> Lemma (requires (True))
                             (ensures ((compose_envs (slice_en p1 en) (slice_en p2 en)) x =
                                       (slice_en_sps (t_union p1 p2) en) x))
                       (decreases %[en;0])
val slc_en_lem_2: en:env -> p1:prin -> p2:prin
                  -> Lemma (requires (True))
                           (ensures (compose_envs (slice_en p1 en) (slice_en p2 en) =
                                     slice_en_sps (t_union p1 p2) en))
                      (decreases %[en;1])
let rec slc_v_lem_2 #m v p1 p2 = match v with
  | V_const _      -> ()
  
  | V_box ps v     ->
    let p1p2 = t_union p1 p2 in
    if mem p1 ps && mem p2 ps then slc_v_lem_2 v p1 p2
    else if mem p1 ps && not (mem p2 ps) then
      let _ = assert (intersect p1p2 ps = intersect (singleton p1) ps) in
      let _ = assert (intersect p1p2 ps = (singleton p1)) in
      box_slice_lem v p1p2 ps;
      box_slice_lem v (singleton p1) ps;
      slice_lem_singl_v (V_box ps v) p1
    else if not (mem p1 ps) && mem p2 ps then
      let _ = assert (intersect p1p2 ps = intersect (singleton p2) ps) in
      let _ = assert (intersect p1p2 ps = (singleton p2)) in
      box_slice_lem v p1p2 ps;
      box_slice_lem v (singleton p2) ps;
      slice_lem_singl_v (V_box ps v) p2
    else ()
  | V_clos en _ _  -> slc_en_lem_2 en p1 p2
  | V_emp_clos _ _ -> ()
  | V_emp          -> ()

and slc_en_x_lem_2 en p1 p2 x =
  if en x = None then ()
  else (preceds_axiom en x; slc_v_lem_2 (D_v.v (Some.v (en x))) p1 p2)

and slc_en_lem_2 en p1 p2 =
  forall_intro #varname #(fun x -> b2t ((compose_envs (slice_en p1 en)
                                                      (slice_en p2 en)) x =
                                        (slice_en_sps (t_union p1 p2) en) x))
                        (slc_en_x_lem_2 en p1 p2);
  let _ = cut (FEq (compose_envs (slice_en p1 en) (slice_en p2 en))
                   (slice_en_sps (t_union p1 p2) en)) in
  ()

val slc_v_lem_ps: #m:v_meta -> v:value m -> p:prin -> ps:prins
                       -> Lemma (requires (True))
                                (ensures (compose_vals (D_v.v (slice_v p v))
                                                       (D_v.v (slice_v_sps ps v))
                                          = slice_v_sps (union (singleton p) ps) v))
                          (decreases %[v])
val slc_en_x_lem_ps: en:env -> p:prin -> ps:prins -> x:varname
                     -> Lemma (requires (True))
                              (ensures ((compose_envs (slice_en p en)
                                                      (slice_en_sps ps en)) x
                                        = (slice_en_sps (union (singleton p) ps) en) x))
                        (decreases %[en; 0])
val slc_en_lem_ps: en:env -> p:prin -> ps:prins
                     -> Lemma (requires (True))
                              (ensures (compose_envs (slice_en p en)
                                                     (slice_en_sps ps en)
                                        = slice_en_sps (union (singleton p) ps) en))
                        (decreases %[en; 1])
let rec slc_v_lem_ps #m v p ps = match v with
  | V_const _      -> ()
  
  | V_box ps' v'   ->
    let psp = singleton p in
    if mem p ps' && not (intersect ps ps' = empty) then
      slc_v_lem_ps v' p ps
    else if mem p ps' && intersect ps ps' = empty then
      let _ = cut (forall p. mem p (union psp ps) = mem p psp || mem p ps) in
      let _ = cut (forall p. not (mem p (intersect ps ps'))) in
      let _ = cut (forall p. mem p (intersect (union psp ps) ps') = mem p psp) in
      let _ = OrdSet.eq_lemma (intersect (union psp ps) ps') psp in

      box_slice_lem v' (union psp ps) ps';
      slice_lem_singl_v v' p;
      ()
    else if not (mem p ps') && not (intersect ps ps' = empty) then
      let _ = cut (forall p. mem p (union psp ps) = mem p psp || mem p ps) in
      let _ = cut (forall p. not (mem p (intersect psp ps'))) in
      let _ = cut (forall p. mem p (intersect (union psp ps) ps') = mem p (intersect ps ps')) in
      let _ = OrdSet.eq_lemma (intersect (union psp ps) ps') (intersect ps ps') in
      
      box_slice_lem v' (union (singleton p) ps) ps';
      box_slice_lem v' ps ps';
      ()    
    else
      let _ = cut (forall p. mem p (union psp ps) = mem p psp || mem p ps) in
      let _ = cut (forall p. not (mem p (intersect psp ps'))) in
      let _ = cut (forall p. not (mem p (intersect ps ps'))) in
      let _ = cut (forall p. not (mem p (intersect (union psp ps) ps'))) in
      let _ = OrdSet.eq_lemma (intersect (union psp ps) ps') empty in

      ()
  | V_clos en _ _  -> slc_en_lem_ps en p ps
  | V_emp_clos _ _ -> ()
  | V_emp          -> ()

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

val mremove  : #key:Type -> #value:Type -> #f:cmp key -> key
              -> OrdMap.ordmap key value f -> Tot (OrdMap.ordmap key value f)
val mchoose  : #key:Type -> #value:Type -> #f:cmp key -> OrdMap.ordmap key value f
              -> Tot (option (key * value))

val msize    : #key:Type -> #value:Type -> #f:cmp key -> OrdMap.ordmap key value f
              -> Tot nat

let mremove (#k:Type) (#v:Type) #f = OrdMap.remove #k #v #f
let mchoose (#k:Type) (#v:Type) #f = OrdMap.choose #k #v #f
let msize (#k:Type) (#v:Type) #f = OrdMap.size #k #v #f

type contains_ps (#v:Type) (ps:prins) (m:OrdMap.ordmap prin v p_cmp) =
  forall p. mem p ps ==> contains p m

type value_map (ps:prins) = m:OrdMap.ordmap prin dvalue p_cmp{contains_ps ps m}

type env_map (ps:prins) = m:OrdMap.ordmap prin env p_cmp{contains_ps ps m}

val compose_vals_m: ps:prins -> m:value_map ps -> Tot dvalue (decreases (size ps))
let rec compose_vals_m ps m =
  let Some p = choose ps in
  let Some (D_v meta v) = select p m in
  let ps_rest = remove p ps in
  if ps_rest = empty then D_v meta v
  else
    let D_v _ v' = compose_vals_m ps_rest m in
    compose_vals v v'

val compose_envs_m: ps:prins -> m:env_map ps -> Tot env (decreases (size ps))
let rec compose_envs_m ps m =
  let Some p = choose ps in
  let Some en = select p m in
  let ps_rest = remove p ps in
  if ps_rest = empty then en
  else
    let en' = compose_envs_m ps_rest m in
    compose_envs en en'

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
let env_upd_slice_lemma #m p en x v =
  cut (FEq (slice_en p (update_env en x v))
      (update_env (slice_en p en) x (D_v.v (slice_v p v))))

val if_enter_sec_then_from_sec: #c:sconfig -> #c':sconfig -> h:sstep c c' -> Tot bool
let if_enter_sec_then_from_sec #c #c' h = not (is_C_assec_beta h) || is_sec c

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
    | C_aspar_ps (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_aspar_ps (slice_c p c) (slice_c p c'))
    | C_unbox (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_unbox (slice_c p c) (slice_c p c'))
    | C_const (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_const (slice_c p c) (slice_c p c'))
    | C_var (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_var (slice_c p c) (slice_c p c'))
    | C_let_e1 (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_let_e1 (slice_c p c) (slice_c p c'))
    | C_abs (Conf _ m _ en _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_abs (slice_c p c) (slice_c p c'))
    | C_empabs (Conf _ m _ en _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_empabs (slice_c p c) (slice_c p c'))
    | C_app_e1 (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_app_e1 (slice_c p c) (slice_c p c'))
    | C_aspar_e (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_aspar_e (slice_c p c) (slice_c p c'))
    | C_app_e2 (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_app_e2 (slice_c p c) (slice_c p c'))
    | C_aspar_red (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_aspar_red (slice_c p c) (slice_c p c'))
    | C_box_red (Conf _ m s _ _) _ ->
      if mem p (Mode.ps m) then
        IntroR (C_box_red (slice_c p c) (slice_c p c'))
      else if mem p (Mode.ps (Frame.m (Cons.hd s))) then
        IntroR (C_box_red (slice_c p c) (slice_c p c'))
      else IntroL ()
    | C_unbox_red (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_unbox_red (slice_c p c) (slice_c p c'))
    | C_let_red (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_let_red (slice_c p c) (slice_c p c'))
    | C_app_red (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else IntroR (C_app_red (slice_c p c) (slice_c p c'))
    | C_let_beta (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        let Conf _ _ _ en (T_red (R_let x v _)) = c in
        let _ = env_upd_slice_lemma p en x v in
        IntroR (C_let_beta (slice_c p c) (slice_c p c'))
    | C_app_beta (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        let T_red (R_app f v) = Conf.t c in
        let (en, x, _) = get_en_b f in
        env_upd_slice_lemma p en x v;
        IntroR (C_app_beta (slice_c p c) (slice_c p c'))
    | C_aspar_beta (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        let T_red (R_aspar _ v) = Conf.t c in
        let (en, x, _) = get_en_b v in
        env_upd_slice_lemma p en x (V_const (C_unit));
        IntroR (C_aspar_beta (slice_c p c) (slice_c p c'))
    | C_box_beta (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_box_beta (slice_c p c) (slice_c p c'))
    | C_unbox_beta (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_unbox_beta (slice_c p c) (slice_c p c'))
    | C_assec_ps (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_assec_ps (slice_c p c) (slice_c p c'))
    | C_assec_e (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_assec_e (slice_c p c) (slice_c p c'))
    | C_assec_red (Conf _ m _ _ _) _ ->
      if is_sec c || not (mem p (Mode.ps m)) then IntroL ()
      else
        IntroR (C_assec_red (slice_c p c) (slice_c p c'))
    | C_assec_beta _ _ -> IntroL ()
    | C_assec_ret (Conf _ m _ _ _) _ -> IntroL ()

(**********)
#reset-options

(**********)

type tconfig_par = c:tconfig{Mode.m (Conf.m c) = Par}

type tpar (ps:prins) = m:OrdMap.ordmap prin tconfig_par p_cmp{forall p. mem p ps = contains p m}

type tconfig_sec = c:tconfig{Mode.m (Conf.m c) = Sec}

type protocol (ps:prins) = tpar ps * option tconfig_sec

(*val tpre_assec: pi:protocol
                -> ps:prins{ps_in_pi ps pi}
                -> x:varname -> e:exp
                -> ps':prins{subset ps' ps}
                -> Tot bool (decreases (size ps'))
let rec tpre_assec pi ps x e ps' =
  let Some p = choose ps' in
  let Some (Conf _ _ _ _ t) = select p (fst pi) in
  let b = match t with
    | T_red (R_assec ps v) ->
      if is_clos v then
        let (_, x1, e1) = get_en_b v in
        x1 = x && e1 = e
      else
        false
    | _ -> false
  in
  let ps_rest = remove p ps' in
  if ps_rest = empty then b
  else b && (tpre_assec pi ps x e ps_rest)*)
  
(*type tpre_assec (#ps':prins) (pi:protocol ps') (ps:prins) (x:varname) (e:exp) =
  forall p. mem p ps ==> (contains p (fst pi) /\
                          is_T_red (Conf.t (Some.v (select p (fst pi)))) /\
                          is_R_assec (T_red.r (Conf.t (Some.v (select p (fst pi))))) /\
                          R_assec.ps (T_red.r (Conf.t (Some.v (select p (fst pi))))) = ps /\
                          is_clos (R_assec.v (T_red.r (Conf.t (Some.v (select p (fst pi)))))) /\
                          MkTuple3._2 (get_en_b (R_assec.v (T_red.r (Conf.t (Some.v (select p (fst pi))))))) = x /\
                          MkTuple3._3 (get_en_b (R_assec.v (T_red.r (Conf.t (Some.v (select p (fst pi))))))) = e)*)

type tpre_assec (#ps':prins) (pi:protocol ps') (ps:prins) (x:varname) (e:exp) =
  is_None (snd pi) /\
  (forall p. mem p ps ==> (contains p (fst pi) /\
                           Let (Some.v (select p (fst pi)))
                             (fun c ->
                               is_T_red (Conf.t c) /\
                               is_R_assec (T_red.r (Conf.t c)) /\
                               R_assec.ps (T_red.r (Conf.t c)) = ps /\
                               is_clos (R_assec.v (T_red.r (Conf.t c))) /\
                               MkTuple3._2 (get_en_b (R_assec.v (T_red.r (Conf.t c)))) = x /\
                               MkTuple3._3 (get_en_b (R_assec.v (T_red.r (Conf.t c)))) = e)))

val get_env_m:
  #ps':prins -> pi:protocol ps' -> ps:prins -> x:varname -> e:exp{tpre_assec pi ps x e}
  -> ps_i:prins{subset ps_i ps}
  -> Tot (m:env_map ps_i{(forall p. mem p ps_i ==>
                                    select p m = Some (
                                    MkTuple3._1 (get_en_b (R_assec.v (T_red.r (Conf.t (Some.v (select p (fst pi)))))))))})
     (decreases (size ps_i))
let rec get_env_m #ps' pi ps x e ps_i =
  let Some p = choose ps_i in
  let ps_rest = remove p ps_i in
  let Some (Conf _ _ _ _ (T_red (R_assec _ v))) = select p (fst pi) in
  let (en, _, _) = get_en_b v in
  if ps_rest = empty then update p en mempty
  else
    let m = get_env_m pi ps x e ps_rest in
    update p en m

val step_p_to_wait: c:tconfig -> p:prin -> Tot tconfig
let step_p_to_wait c p =
  let Conf l m s en _ = c in
  Conf l m s en T_sec_wait

val step_ps_to_wait:
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
  let env = update_env (compose_envs_m ps (get_env_m pi ps x e ps)) x (V_const C_unit) in
  let tsec = Conf Target (Mode Sec ps) [] env (T_exp e) in
  (step_ps_to_wait #ps' (fst pi) ps, Some tsec)

type ps_sec_waiting (#ps':prins) (pi:protocol ps') (ps:prins) =
  (forall p. mem p ps ==> (contains p (fst pi) /\
                           is_T_sec_wait (Conf.t (Some.v (select p (fst pi))))))

type tpre_assec_ret (#ps':prins) (pi:protocol ps') (ps:prins) =
  is_Some (snd pi) /\ (Conf.m (Some.v (snd pi)) = Mode Sec ps)  /\
  is_value (Some.v (snd pi)) /\ (Conf.s (Some.v (snd pi)) = []) /\
  ps_sec_waiting pi ps

val ret_sec_value_to_p: #meta:v_meta -> c:tconfig -> p:prin
                        -> v:value meta -> Tot tconfig
let ret_sec_value_to_p #meta c p v =
  let Conf l m s en _ = c in
  Conf l m s en (T_val (D_v.v (slice_v p v)))

val ret_sec_value_to_ps:
  #ps':prins -> #m:v_meta -> pi:tpar ps' -> ps:prins{forall p. mem p ps ==> contains p pi}
  -> v:value m
  -> Tot (pi':tpar ps'{forall p. (mem p ps ==>
                                  select p pi' =
                                  Some (ret_sec_value_to_p (Some.v (select p pi)) p v)) /\
                                 (not (mem p ps) ==>
                                  select p pi' = select p pi)})
     (decreases (size ps))
let rec ret_sec_value_to_ps #ps' #meta pi ps v =
  let Some p = choose ps in
  let ps_rest = remove p ps in
  let c' = ret_sec_value_to_p (Some.v (select p pi)) p v in
  if ps_rest = empty then update p c' pi
  else
    let pi' = ret_sec_value_to_ps #ps' #meta pi ps_rest v in
    update p c' pi'

val tstep_assec_ret:
  #ps':prins -> pi:protocol ps' -> ps:prins{tpre_assec_ret pi ps}
  -> Tot (protocol ps')
let tstep_assec_ret #ps' pi ps =
  let pi, Some c = pi in
  let D_v _ v = c_value c in
  ret_sec_value_to_ps #ps' pi ps v, None

type pstep: #ps:prins -> protocol ps -> protocol ps -> Type =

  | P_par:
    #ps:prins -> #c':tconfig -> pi:protocol ps
    -> p:prin{contains p (fst pi)}
    -> h:sstep (Some.v (select p (fst pi))) c'
    -> pstep #ps pi (update p c' (fst pi), (snd pi))

  | P_sec:
    #ps:prins -> #c':tconfig -> pi:protocol ps{is_Some (snd pi)}
    -> h:sstep (Some.v (snd pi)) c'
    -> pstep #ps pi (fst pi, Some c')
      
  | P_sec_enter:
    #ps':prins -> pi:protocol ps' -> ps:prins
    -> x:varname -> e:exp{tpre_assec pi ps x e}
    -> pi':protocol ps'{pi' = tstep_assec pi ps x e}
    -> pstep #ps' pi pi'
    
  | P_sec_exit:
    #ps':prins -> pi:protocol ps' -> ps:prins{tpre_assec_ret pi ps}
    -> pi':protocol ps'{pi' = tstep_assec_ret pi ps}
    -> pstep #ps' pi pi'

val slice_c_ps_par: ps:prins -> c:sconfig
                    -> Tot (pi:tpar ps{forall p. (mem p ps ==>
                                                  select p pi = Some (slice_c p c)) /\
                                                 (not (mem p ps) ==>
                                                  select p pi = None)})
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
                -> Tot (pi:protocol ps{forall p. (mem p ps ==>
                                                  select p (fst pi) = Some (slice_c p c)) /\
                                                 (not (mem p ps) ==>
                                                  select p (fst pi) = None)})
let slice_c_ps ps c =
  let pi = slice_c_ps_par ps c in
  let tsec = if is_sec c then Some (slice_c_sps c) else None in
  pi, tsec

(*type slice_c_ps_par_inv (ps:prins) (c:sconfig) (pi:tpar) =
  (forall p. (mem p ps <==> contains p pi) /\
             (is_Some (select p pi) ==> (Some.v (select p pi) = slice_c p c)))

val slice_c_ps_tpar_lemma: ps:prins -> c:sconfig
                           -> Lemma (requires (True))
                                    (ensures (slice_c_ps_par_inv ps c (fst (slice_c_ps ps c))))
                              (decreases (size ps))
let rec slice_c_ps_tpar_lemma ps c =
  let Some p = choose ps in
  let ps_rest = remove p ps in
  if ps_rest = empty then () else slice_c_ps_tpar_lemma ps_rest c
                                              *)
val pre_forward_simulation: #c:sconfig -> #c':sconfig -> h:sstep c c'
                            -> ps:prins -> Tot bool
let pre_forward_simulation #c #c' h ps =
  (not (is_C_assec_beta h || is_C_assec_ret h)) || subset (Mode.ps (Conf.m c)) ps

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

assume val sel_contains_tpar: ps:prins -> pi:tpar ps
                              -> Lemma (requires (True))
                                       (ensures (forall p. (is_Some (select p pi) = contains p pi)))

opaque val forward_simulation_sec: #c:sconfig -> #c':sconfig -> ps:prins
                                   -> h:sstep c c'{is_sec c /\ if_exit_sec_then_to_sec h}
                                   -> Tot (pstep #ps (slice_c_ps ps c)
                                                     (slice_c_ps ps c'))
let forward_simulation_sec #c #c' ps h =
  let (pi, s) = slice_c_ps ps c in
  let (pi', _) = slice_c_ps ps c' in
  let Conj _ h' = sstep_sec_slice_lemma c c' h in
  slice_remains_same_in_sec_step h;
  sel_contains_tpar ps pi; sel_contains_tpar ps pi';
  cut (forall p. select p pi = select p pi');
  OrdMap.eq_lemma pi pi';
  P_sec (pi, s) h'

type pstep_par_star: #ps:prins -> protocol ps -> protocol ps -> Type =
  | PP_refl: #ps:prins -> pi:protocol ps -> pstep_par_star pi pi
    
  | PP_tran:
    #ps:prins -> #pi:protocol ps -> #pi':protocol ps -> #pi'':protocol ps
    -> h:pstep pi pi'{is_P_par h} -> h':pstep_par_star pi' pi''
    -> pstep_par_star pi pi''

val update_tpar: #ps:prins -> p:prin{not (mem p ps)}
                 -> c:tconfig{is_Par (Mode.m (Conf.m c))} -> pi:protocol ps
                 -> Tot (protocol (union (singleton p) ps))
let update_tpar #ps p c pi = update p c (fst pi), snd pi

(*val pstep_par_same_dom_lemma: #pi:protocol -> #pi':protocol
                              -> h:pstep pi pi'{is_P_par h}
                              -> Lemma (requires (True))
                                       (ensures (dom (fst pi) = dom (fst pi')))
let pstep_par_same_dom_lemma #pi #pi h = ()                                       
*)

opaque val pstep_par_upd: #ps:prins -> #pi:protocol ps -> #pi':protocol ps
                          -> h:pstep pi pi'{is_P_par h}
                          -> p:prin{not (contains p (fst pi))}
                          -> c:tconfig{is_Par (Mode.m (Conf.m c))}
                          -> Tot (r:pstep (update_tpar p c pi) (update_tpar p c pi'){is_P_par r})
let pstep_par_upd #ps #pi #pi' h p c = match h with
  | P_par #ps #c' pi p' h' -> P_par #(union (singleton p) ps) #c' (update_tpar p c pi) p' h'

val pstep_par_star_upd_same: #ps:prins -> #pi:protocol ps -> #pi':protocol ps
                             -> h:pstep_par_star pi pi'
                             -> p:prin{not (contains p (fst pi))}
                             -> c:tconfig{is_Par (Mode.m (Conf.m c))}
                             -> Tot (pstep_par_star (update_tpar p c pi) (update_tpar p c pi'))
                                (decreases h)
let rec pstep_par_star_upd_same #ps #pi #pi' h p c = match h with
  | PP_refl pi -> PP_refl (update_tpar p c pi)
  
  | PP_tran #pi #pi' #pi'' h1 h2 ->
    PP_tran (pstep_par_upd h1 p c) (pstep_par_star_upd_same h2 p c)

val pstep_par_star_upd_step: #ps:prins -> #pi:protocol ps -> #pi':protocol ps
                             -> #c:tconfig{is_Par (Mode.m (Conf.m c))}
                             -> #c':tconfig{is_Par (Mode.m (Conf.m c))}
                             -> h1:pstep_par_star pi pi' -> h2:sstep c c'
                             -> p:prin{not (contains p (fst pi))}
                             -> Tot (pstep_par_star (update_tpar p c pi) (update_tpar p c' pi'))
                                (decreases h1)                                
let rec pstep_par_star_upd_step #ps #pi #pi' #c #c' h1 h2 p =
  let pi1 = update_tpar p c pi in
  let pi1' = update_tpar p c' pi' in
  let ps' = union (singleton p) ps in
  match h1 with
    | PP_refl pi ->
      PP_tran #ps' #pi1 #pi1' #pi1' (P_par #ps' #c' pi1 p h2) (PP_refl #ps' pi1')
      
    | PP_tran #ps_1 #pi #pi'' #pi' h h' ->
      (*let P_par #d #c1 _ p1 h'' = h in
      let _ = assert (fst pi'' = update p1 c1 (fst pi)) in*)
      admit ()
      (*let pi1'' = update_tpar p c pi'' in
      
      
      
      let P_par #ps #c1' #d p1 h'' = h in
      let ht1 = P_par #ps' #c1' pi1 p1 h'' in
      let ht2 = pstep_par_star_upd_step #ps #pi'' #pi' #c #c' h' h2 p in
      PP_tran #ps' #pi1 #pi1'' #pi1' ht1 ht2*)

(* TODO: FIXME: this is a weird behavior *)
val slice_c_snd_lemma: ps:prins -> c:sconfig{is_par c}
                       -> Lemma (requires (True))
                                (ensures (snd (slice_c_ps ps c) = None))
let slice_c_snd_lemma ps c =
  let _, _ = slice_c_ps ps c in
  ()

val sstep_par_slc_snd_lemma: #c:sconfig -> #c':sconfig -> ps:prins
                             -> h:sstep c c'{is_par c /\ if_enter_sec_then_from_sec h}
                             -> Lemma (requires (True))
                                      (ensures (snd (slice_c_ps ps c) = snd (slice_c_ps ps c') /\
                                                snd (slice_c_ps ps c) = None))
#set-options "--split_cases 1"                                                
let sstep_par_slc_snd_lemma #c #c' ps h = match h with
  | C_aspar_ps _ _ -> let _, _ = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_unbox _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_const _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_var _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_let_e1 _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_abs _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_empabs _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_app_e1 _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_aspar_e _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_app_e2 _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_aspar_red _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_box_red _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_unbox_red _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_let_red _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_app_red _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_let_beta _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_app_beta _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_aspar_beta _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_box_beta _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_unbox_beta _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_assec_ps _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_assec_e _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_assec_red _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_assec_beta _ _ -> let _, _  = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()
  | C_assec_ret _ _ -> let _, _ = slice_c_ps ps c in let _, _ = slice_c_ps ps c' in ()

#reset-options

opaque val forward_simulation_par: #c:sconfig -> #c':sconfig
                                   -> h:sstep c c'{is_par c /\
                                                   if_enter_sec_then_from_sec h}
                                   -> ps:prins
                                   -> Tot (pstep_par_star #ps (slice_c_ps ps c)
                                                              (slice_c_ps ps c'))
                                      (decreases (size ps))
let rec forward_simulation_par #c #c' h ps = admit ()
  (*let pi, s = slice_c_ps ps c in
  let pi', s' = slice_c_ps ps c' in
  sstep_par_slc_snd_lemma ps h;
  let _ = cut (b2t (s = s')) in
  
  let Some p = choose ps in
  let ps_rest = remove p ps in

  let c_p = slice_c p c in
  let c_p' = slice_c p c' in

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
        PP_tran (P_par (pi, s) p h') (PP_refl (pi', s'))

  else
    let pi_rest, s_rest = slice_c_ps ps_rest c in
    let pi_rest', s_rest' = slice_c_ps ps_rest c' in
    
    let _ = cut (b2t (pi = update p c_p pi_rest)) in
    let _ = cut (b2t (pi' = update p c_p' pi_rest')) in
    let _ = cut (b2t (s_rest = None)) in
    let _ = cut (b2t (s_rest' = None)) in
    
    let h_ind = forward_simulation_par #c #c' h ps_rest in

    match h1 with
      | IntroL _  ->
        let _ = cut (b2t (c_p = c_p')) in
        pstep_par_star_upd_same #ps_rest #(pi_rest, s_rest) #(pi_rest', s_rest') h_ind p (slice_c p c)
      | IntroR h' ->
        pstep_par_star_upd_step #ps_rest #(pi_rest, s_rest) #(pi_rest', s_rest')
                                         #c_p #c_p' h_ind h' p*)

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
  | V_const _ -> ()  
  | V_box ps' v' ->
    if intersect ps ps' = empty then
      let _ = cut (mem p ps' ==> mem p (intersect ps ps')) in
      ()
    else if not (mem p ps') then ()
    else slice_v_lem_singl_of_ps v' ps p  
  | V_clos en _ _ -> slice_en_lem_singl_of_ps en ps p
  | V_emp_clos _ _ -> ()
  | V_emp -> ()

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
  #c:config -> #c':config -> h:sstep c c'{is_C_assec_ret h /\ is_par c'}
  -> Lemma (requires (True))
           (ensures (forall p. not (mem p (Mode.ps (Conf.m c))) ==>
                               slice_c p c = slice_c p c'))
let sstep_sec_to_par_slice_par_others #c #c' _ = ()

val sstep_sec_to_par_p: #c:config -> #c':config
                        -> h:sstep c c'{is_C_assec_ret h /\ is_par c'}
                        -> p:prin{mem p (Mode.ps (Conf.m c))}
                        -> Tot tconfig
let sstep_sec_to_par_p #c #c' _ p =
  let ps = Mode.ps (Conf.m c) in
  let v_ps = slice_v_sps ps (D_v.v (c_value c)) in
  ret_sec_value_to_p #(D_v.meta v_ps) (slice_c p c) p (D_v.v v_ps)

val sstep_sec_to_par_slice_par_mems:
  #c:config -> #c':config -> h:sstep c c'{is_C_assec_ret h /\ is_par c'}
  -> Lemma (requires (True))
           (ensures (forall p. mem p (Mode.ps (Conf.m c)) ==>
                               sstep_sec_to_par_p #c #c' h p = slice_c p c'))
let sstep_sec_to_par_slice_par_mems #c #c' h =
  let ps = Mode.ps (Conf.m c) in
  let v = D_v.v (c_value c) in
  let _ = slice_v_lem_singl_of_ps_forall v ps in
  ()

(*assume val contains_is_some_eq_lemma: pi1:tpar -> pi2:tpar
                                      -> Lemma (requires (forall p. contains p pi1 <==> contains p pi2))
                                               (ensures (forall p. is_Some (select p pi1) =
                                                                   is_Some (select p pi2)))*)

assume val not_contains_lemma: #ps:prins -> pi:tpar ps
                               -> Lemma (requires (True)) (ensures (forall p. not (mem p ps) ==> select p pi = None))
                                                                   
val forward_simulation_exit_sec: #c:config -> #c':config
                                 -> h:sstep c c'{is_C_assec_ret h /\ is_par c'}
                                 -> ps:prins{subset (Mode.ps (Conf.m c)) ps}
                                 -> Tot (pstep #ps (slice_c_ps ps c) (slice_c_ps ps c'))
let forward_simulation_exit_sec #c #c' h ps =
  let ps' = Mode.ps (Conf.m c) in
  
  let pi, s = slice_c_ps ps c in
  let pi', s' = slice_c_ps ps c' in
  let pi_s, s_s = tstep_assec_ret #ps (pi, s) ps' in

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
  P_sec_exit #ps (pi, s) ps' (pi_s, s_s)

val sstep_par_to_sec_slice_par_others:
  #c:config -> #c':config -> h:sstep c c'{is_C_assec_beta h /\ is_par c}
  -> Lemma (requires (True))
           (ensures (forall p. not (mem p (Mode.ps (Conf.m c))) ==>
                               slice_c p c = slice_c p c'))
let sstep_par_to_sec_slice_par_others #c #c' h = ()

val sstep_par_to_sec_slice_par_mems:
  #c:config -> #c':config -> h:sstep c c'{is_C_assec_beta h /\ is_par c}
  -> Lemma (requires (True))
           (ensures (forall p. mem p (Mode.ps (Conf.m c)) ==>
                               step_p_to_wait (slice_c p c) p = slice_c p c'))
let sstep_par_to_sec_slice_par_mems #c #c' h = ()

val sstep_par_to_sec_slice_par:
  #c:config -> #c':config -> h:sstep c c'{is_C_assec_beta h /\ is_par c}
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

val forward_simulation_enter_sec: #c:config -> #c':config
                                  -> h:sstep c c'{is_C_assec_beta h /\ is_par c}
                                  -> ps:prins{subset (Mode.ps (Conf.m c)) ps}
                                  -> Tot (pstep #ps (slice_c_ps ps c) (slice_c_ps ps c'))
let forward_simulation_enter_sec #c #c' h ps =
  let Conf Source (Mode Par ps') s en (T_red (R_assec _ v)) = c in
  let (en1, x, e) = get_en_b v in

  let pi, s = slice_c_ps ps c in
  let pi', s' = slice_c_ps ps c' in
  
  (* TODO: FIXME: this takes too long *)
  let _ = admitP (tpre_assec #ps (pi, s) ps' x e) in
  
  (* TODO: FIXME: If I write pi_s, s_s = ... and then try to say pi_s = step_ps_to_wait, it takes long time,
   * whereas should be immediate from tstep_assec *)
  let pi_s = step_ps_to_wait #ps pi ps' in
  let pi_tmp, s_s = tstep_assec #ps (pi, s) ps' x e in
  
  let _ = cut (b2t (pi_tmp = pi_s)) in
  
  sstep_par_to_sec_slice_par #c #c' h ps x e;
  let _ = cut (b2t (pi_s = pi')) in
  
  let Some (Conf _ _ st_s en_s t_s) = s_s in
  let Some (Conf _ _ st' en' t') = s' in
  
  let _ = cut (b2t (st_s = [])) in
  let _ = cut (b2t (st' = [])) in
  let _ = cut (b2t (t_s = t')) in

  let en2 = update_env en1 x (V_const C_unit) in  
  let _ = cut (b2t (Conf.en c' = en2)) in
  
  let _ = cut (b2t (en' = slice_en_sps ps' en2)) in
  
  let env_m = get_env_m #ps (pi, s) ps' x e ps' in
  let composed_env_m = compose_envs_m ps' env_m in
  
  let updated_composed_envs_m = update_env composed_env_m x (V_const C_unit) in
  
  let _ = cut (b2t (en_s = updated_composed_envs_m)) in
  
  let _ = admitP (forall p. mem p ps' ==> select p env_m = Some (slice_en p en1)) in
  
  let _ = slc_en_lem_m en1 ps' env_m in
  
  let _ = cut (b2t (composed_env_m = slice_en_sps ps' en1)) in
  
  let _ = env_upd_slice_lemma_ps ps' en1 x (V_const C_unit) in
  
  let _ = cut (b2t (en_s = en')) in
  let _ = cut (b2t (s' = s_s)) in

  let _ = cut (b2t ((pi', s') = (pi_tmp, s_s))) in
  
  P_sec_enter #ps (pi, s) ps' x e (pi_tmp, s_s)
  
(* check_marker *)
  
(*assume val slice_clos_lemma: c:sconfig{not (pre_assec c = NA)}
                             -> ps:prins{subset (Mode.ps (Conf.m c)) ps}
                             -> pi:protocol{slice_c_ps ps c = pi}
                             -> Lemma (requires (True))
                                      (ensures (forall p.
                                                mem p (Mode.ps (Conf.m c)) ==>
                                                contains p (fst pi) /\
                                                Conf.t (Some.v (select p (fst pi))) =
                                                slice_t p (Conf.t c)))


assume val slice_emp_en_forall: unit
                                -> Lemma (requires (True))
                                         (ensures (forall p. slice_en p empty_env = empty_env))

val forward_simulation_enter_sec: #c:config -> #c':config
                                  -> h:sstep c c'{is_C_assec_beta h /\ is_par c}
                                  -> ps:prins{subset (Mode.ps (Conf.m c)) ps}
                                  -> Tot (pstep (slice_c_ps ps c) (slice_c_ps ps c'))
let forward_simulation_enter_sec #c #c' h ps =
  let Conf Source (Mode Par ps') s en (T_red (R_assec ps'' v)) = c in
  let (en1, x, e) = get_en_b v in
  
  let Conf Source (Mode Sec ps'') ((Frame (Mode Par ps''') en2 F_assec_ret)::s)
                  en3 (T_exp e1) = c' in
                  
  (*let _ = assert (ps'' = ps' /\ ps''' = ps' /\ en2 = en /\
                  en3 = update_env en1 x (V_const C_unit) /\ e1 = e) in*)
  
  let pi = slice_c_ps ps c in
  let _ = slice_c_ps_tpar_lemma ps c in
  
  let _ = assert (not (pre_assec c = NA)) in
  
  let _ = slice_clos_lemma c ps pi in
  
  let pi' = slice_c_ps ps c' in
  let _ = slice_c_ps_tpar_lemma ps c' in
  
  (*let _ = assert (forall p. mem p ps' ==>
                            Some.v (select p (fst pi')) =
                            step_p_to_wait (Some.v (select p (fst pi))) p) in*)

  (*let _ = contains_is_some_eq_lemma (fst pi) (fst pi') in
  
  let _ = assert (forall p. not (mem p ps') ==> select p (fst pi') =
                                                select p (fst pi)) in*)
                                                
  let pi'' = tstep_assec pi ps' x e in

  (*let _ = assert (forall p. mem p ps' ==>
                            Some.v (select p (fst pi'')) =
                            step_p_to_wait (Some.v (select p (fst pi))) p) in

  let _ = assert (forall p. not (mem p ps') ==> select p (fst pi'') =
                                                select p (fst pi)) in

  let _  = assert (fst pi' = fst pi'') in*)

  (*let Some (Conf Target (Mode Sec _) [] en4 e4) = snd pi' in
  let Some (Conf Target (Mode Sec _) [] en5 e5) = snd pi'' in
  
  let _ = assert (e4 = T_exp e) in
  let _ = assert (e5 = T_exp e) in
  
  let _ = assert (e4 = e5) in
  
  let _ = assert (en4 = slice_en_sps ps' en3) in
  let _ = assert (en3 = update_env en1 x (V_const C_unit)) in
  env_upd_slice_lemma_ps ps' en3 x (V_const C_unit);
  
  let _ = assert (en4 = update_env (slice_en_sps ps' en1) x (V_const C_unit)) in

  let envm = get_env_m pi ps' x e ps' in*)

  //let _ = assert (forall p. mem p ps' = contains p envm) in

  //slice_emp_en_forall ();
  
  (*let _ = assert (forall p. mem p ps' ==>
    is_T_red (Conf.t (Some.v (select p (fst pi)))) /\
    is_R_assec (T_red.r (Conf.t (Some.v (select p (fst pi))))) /\
    is_clos (R_assec.v (T_red.r (Conf.t (Some.v (select p (fst pi)))))) /\
    MkTuple3._1 (get_en_b (R_assec.v (T_red.r (Conf.t (Some.v (select p (fst pi))))))) =
    slice_en p en1) in*)

  (*let _ = admitP (forall p. contains p envm ==>
                            Some.v (select p envm) = slice_en p en1) in*)
                             
  //slc_en_lem_m en1 envm;
  
  //let _ = admitP (b2t (dom envm = ps')) in
  
  //let _ = admitP (b2t (compose_envs_m (get_env_m pi ps' x e ps')  = slice_en_sps ps' en1)) in

  //let _ = admitP (b2t (en5 = update_env (compose_envs_m (get_env_m pi ps' x e ps')) x (V_const C_unit))) in
  
  //let _ = assert (en5 = update_env (slice_en_sps ps' en1) x (V_const C_unit)) in
  
  //let _ = assert (e4 = e5) in
  admit ()

(*


let rec compose_vals_lemma v ps p =
  if is_singleton ps then

  else
    admit ()

and compose_envs_lemma en ps p = admit ()*)

(* check_marker *)

(*


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


open OrdMap

type protocol = ordmap prin tconfig p_cmp


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
        ExIntro (update p tc_p' pi_rest') (Conj (PS_tran h2' h1') ())*)*)
