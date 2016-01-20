(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Prins;
    other-files:FStar.Ghost.fst ordset.fsi ordmap.fsi prins.fsi
 --*)

module AST

open FStar.Ghost

open FStar.OrdMap
open FStar.OrdSet

open Prins

type other_info = nat

type typ =
  | T_prin
  | T_eprins
  | T_unit
  | T_bool
  | T_cons: cname:string -> args:list typ -> typ
  | T_box: c:typ -> typ
  | T_wire: c:typ -> typ
  | T_fun: typ -> typ -> typ  //not emitting it for now
  | T_unknown

type varname =
  | Var: name:string -> ty:typ -> varname

type const =
  | C_prin  : c:prin   -> const
  | C_eprins: c:eprins -> const

  | C_unit  : c:unit -> const
  | C_bool  : c:bool -> const

  | C_opaque: c:'a -> typ -> const

type exp =
  | E_aspar     : ps:exp -> e:exp -> exp
  | E_assec     : ps:exp -> e:exp -> exp
  | E_box       : ps:exp -> e:exp -> exp
  | E_unbox     : e:exp  -> exp
  | E_mkwire    : e1:exp -> e2:exp -> exp
  | E_projwire  : e1:exp -> e2:exp -> exp
  | E_concatwire: e1:exp -> e2:exp -> exp

  | E_const     : c:const -> exp
  | E_var       : x:varname -> exp
  | E_let       : x:varname -> e1:exp -> e2:exp -> exp
  | E_abs       : x:varname -> e:exp -> exp
  | E_fix       : f:varname -> x:varname -> e:exp -> exp
  | E_empabs    : x:varname -> e:exp -> exp
  | E_app       : e1:exp -> e2:exp -> exp
  | E_ffi       : n:nat -> fname:string -> fn:'a -> args:list exp -> inj:'b -> exp
  | E_cond      : e:exp -> e1:exp -> e2:exp -> exp

type canbox = | Can_b | Cannot_b

type canwire = | Can_w | Cannot_w

type v_meta =
  | Meta: bps:eprins -> cb:canbox -> wps:eprins -> cw:canwire -> v_meta

val is_meta_wireable: meta:v_meta -> Tot bool
let is_meta_wireable = function
  | Meta ps Can_b ps' Can_w -> ps = empty && ps' = empty
  | _                       -> false

val is_meta_boxable: ps:prins -> meta:v_meta -> Tot bool
let is_meta_boxable ps = function
  | Meta ps' Can_b ps'' _ -> subset ps' ps && subset ps'' ps
  | _                     -> false

type value: v_meta -> Type =
  | V_prin    : c:prin -> value (Meta empty Can_b empty Can_w)
  | V_eprins  : c:eprins -> value (Meta empty Can_b empty Can_w)

  | V_unit    : value (Meta empty Can_b empty Can_w)
  | V_bool    : c:bool -> value (Meta empty Can_b empty Can_w)

  | V_opaque  : v:'a -> meta:v_meta
                -> slice_fn:(prin -> 'a -> Tot 'a) -> compose_fn:('a -> 'a -> Tot 'a)
		-> slice_fn_sps:(prins -> 'a -> Tot 'a)
		-> value meta

  | V_box     : #meta:v_meta -> ps:prins -> v:value meta{is_meta_boxable ps meta}
                -> value (Meta ps Can_b (Meta.wps meta) Cannot_w)
                
  | V_wire    : all:eprins -> eps:eprins -> m:v_wire eps
                -> value (Meta empty Can_b eps Cannot_w)

  | V_clos    : en:env -> x:varname -> e:exp
                -> value (Meta empty Cannot_b empty Cannot_w)
  
  | V_fix_clos: en:env -> f:varname -> x:varname -> e:exp
                -> value (Meta empty Cannot_b empty Cannot_w)

  | V_emp_clos: x:varname -> e:exp -> value (Meta empty Can_b empty Can_w)

  (* bomb value, comes up in target only *)
  | V_emp     : value (Meta empty Can_b empty Can_w)

and v_wire (eps:eprins) =
  m:ordmap prin (value (Meta empty Can_b empty Can_w)) p_cmp{forall p. mem p eps = contains p m}

and dvalue:Type =
  | D_v: meta:v_meta -> v:value meta -> dvalue

and env = varname -> Tot (option dvalue)

assume val preceds_axiom: en:env -> x:varname -> Lemma (ensures (en x << en))

type telt =
  | Tr_val  : #meta:v_meta -> v:value meta -> telt
  | Tr_scope: ps:prins -> tr:list telt -> telt

type trace = list telt

val vals_trace_h: trace -> Tot bool
let rec vals_trace_h tr = match tr with
  | []            -> true
  | (Tr_val _)::tl -> vals_trace_h tl
  | _             -> false

val vals_trace: erased trace -> GTot bool
let vals_trace tr = reveal (elift1 vals_trace_h tr)

type redex =
  | R_aspar     : #meta:v_meta -> ps:prins -> v:value meta -> redex
  | R_assec     : #meta:v_meta -> ps:prins -> v:value meta -> redex
  | R_box       : #meta:v_meta -> ps:prins -> v:value meta -> redex
  | R_unbox     : #meta:v_meta -> v:value meta -> redex
  | R_mkwire    : #mv:v_meta -> ps:prins -> v:value mv -> redex
  | R_projwire  : #meta:v_meta -> p:prin -> v:value meta -> redex
  | R_concatwire: #meta1:v_meta -> #meta2:v_meta -> v1:value meta1 -> v2:value meta2 -> redex
  | R_let       : #meta:v_meta -> x:varname -> v:value meta -> e:exp -> redex
  | R_app       : #meta1:v_meta -> #meta2:v_meta -> v1:value meta1 -> v2:value meta2
                  -> redex
  | R_ffi       : n:nat -> fn:'a -> args:list dvalue -> inj:'b -> redex
  | R_cond      : #meta:v_meta -> v:value meta -> e1:exp -> e2:exp -> redex

val empty_env: env
let empty_env = fun _ -> None

val name_of_var: varname -> Tot string
let name_of_var (Var s _) = s

val update_env: #meta:v_meta -> env -> varname -> value meta -> Tot env
let update_env #meta en x v = fun y -> if name_of_var y = name_of_var x then Some (D_v meta v) else en y

type as_mode =
  | Par
  | Sec

type mode =
  | Mode: m:as_mode -> ps:prins -> mode

type frame' =
  | F_aspar_ps     : e:exp -> frame'
  | F_aspar_e      : ps:prins -> frame'
  | F_aspar_ret    : ps:prins -> frame'
  | F_assec_ps     : e:exp -> frame'
  | F_assec_e      : ps:prins -> frame'
  | F_assec_ret    : frame'
  | F_box_ps       : e:exp -> frame'
  | F_box_e        : ps:prins -> frame'
  | F_unbox        : frame'
  | F_mkwire_ps    : e:exp -> frame'
  | F_mkwire_e     : ps:prins -> frame'
  | F_projwire_p   : e:exp -> frame'
  | F_projwire_e   : p:prin -> frame'
  | F_concatwire_e1: e:exp -> frame'
  | F_concatwire_e2: #meta:v_meta -> v:value meta -> frame'
  | F_let          : x:varname -> e2:exp -> frame'
  | F_app_e1       : e2:exp -> frame'
  | F_app_e2       : #meta:v_meta -> v:value meta -> frame'
  | F_ffi          : n:nat -> fn:'a -> es:list exp -> vs:list dvalue -> inj:'b -> frame'
  | F_cond         : e1:exp -> e2:exp -> frame'

type frame =
  | Frame: m:mode -> en:env -> f:frame'-> tr:erased trace -> frame

type stack = list frame

type term =
  | T_exp     : e:exp -> term
  | T_red     : r:redex -> term
  | T_val     : #meta:v_meta -> v:value meta -> term

  | T_sec_wait: term

type level = | Source | Target

val src: level -> Tot bool
let src l = is_Source l

(* TODO: FIXME: workaround for projectors *)
val m_of_mode: mode -> Tot as_mode
let m_of_mode (Mode m _) = m

type mode_inv (m:mode) (l:level) =
  (is_Target l /\ m_of_mode m = Par) ==> (size (Mode.ps m) = 1)

val is_sec_frame: f':frame' -> Tot bool
let is_sec_frame f' =
  not (is_F_aspar_ps f' || is_F_aspar_e f' || is_F_aspar_ret f')

(* TODO: FIXME: workaround for projectors *)
val ps_of_aspar_ret_frame: f':frame'{is_F_aspar_ret f'} -> Tot prins
let ps_of_aspar_ret_frame (F_aspar_ret ps) = ps

val stack_source_inv: stack -> mode -> GTot bool
let rec stack_source_inv s (Mode as_m ps) = match s with
  | []                    -> not (as_m = Sec)
  | (Frame m' _ f' tr)::tl ->
    let Mode as_m' ps' = m' in
    (not (as_m = Par) || as_m' = Par)                              &&
    (not (as_m = Par) || not (is_F_assec_ret f'))                  &&
    (not (as_m = Sec) || (not (as_m' = Par) || is_F_assec_ret f')) &&
    (not (as_m' = Sec) || (is_sec_frame f' && is_Cons tl))         &&
    (not (as_m' = Sec) || (vals_trace tr))                         &&
    (not (is_F_aspar_ret f') || (ps = ps_of_aspar_ret_frame f'))   &&
    (ps = ps' || (subset ps ps' && is_F_aspar_ret f'))             &&
    stack_source_inv tl m'

val stack_target_inv: stack -> mode -> GTot bool
let rec stack_target_inv s m = match s with
  | []                  -> true
  | (Frame m' _ f' tr)::tl ->
    m = m'                                         &&
    (not (m_of_mode m' = Sec) || is_sec_frame f')  &&
    (not (m_of_mode m' = Sec) || vals_trace tr)    &&
    stack_target_inv tl m

val stack_inv: stack -> mode -> level -> GTot bool
let rec stack_inv s m l =
  if is_Source l then stack_source_inv s m else stack_target_inv s m

val is_sec_redex: redex -> Tot bool
let is_sec_redex r = not (is_R_aspar r) //|| is_R_box r)

(* TODO: FIXME: workaround for projectors *)
val r_of_t_red: t:term{is_T_red t} -> Tot redex
let r_of_t_red (T_red r) = r

val term_inv: term -> mode -> level -> Tot bool
let term_inv t m l =
  (not (is_Source l) || not (t = T_sec_wait)) &&
  (not (is_T_red t && m_of_mode m = Sec) || is_sec_redex (r_of_t_red t))

val trace_inv: erased trace -> mode -> GTot bool
let trace_inv tr m = not (m_of_mode m = Sec) || (vals_trace tr)

type config =
  | Conf: l:level -> m:mode{mode_inv m l} -> s:stack{stack_inv s m l}
          -> en:env -> t:term{term_inv t m l} -> tr:erased trace{trace_inv tr m}
	  -> config

type sconfig = c:config{is_Source (Conf.l c)}
type tconfig = c:config{is_Target (Conf.l c)}

(* TODO: FIXME: workaround for projectors *)
val f_of_frame: frame -> Tot frame'
let f_of_frame (Frame _ _ f _) = f

(* TODO: FIXME: workaround for projectors *)
val hd_of_list: l:list 'a{is_Cons l} -> Tot 'a
let hd_of_list (Cons hd _) = hd

val is_sframe: c:config -> f:(frame' -> Tot bool) -> Tot bool
let is_sframe (Conf _ _ s _ _ _) f = is_Cons s && f (f_of_frame (hd_of_list s))

(* TODO: FIXME: workaround for projectors *)
val t_of_conf: config -> Tot term
let t_of_conf (Conf _ _ _ _ t _) = t

val is_value: c:config -> Tot bool
let is_value c = is_T_val (t_of_conf c)

val is_value_ps: c:config -> Tot bool
let is_value_ps c = match c with
  | Conf _ _ _ _ (T_val (V_eprins eps)) _ -> not (eps = empty)
  | _                                     -> false

val is_value_p: c:config -> Tot bool
let is_value_p c = match c with
  | Conf _ _ _ _ (T_val (V_prin _)) _ -> true
  | _                                 -> false

val c_value: c:config{is_value c} -> Tot dvalue
let c_value (Conf _ _ _ _ (T_val #meta v) _) = D_v meta v

val c_value_ps: c:config{is_value_ps c} -> Tot prins
let c_value_ps c = match c with
  | Conf _ _ _ _ (T_val (V_eprins ps)) _ -> ps

val c_value_p: c:config{is_value_p c} -> Tot prin
let c_value_p c = match c with
  | Conf _ _ _ _ (T_val (V_prin p)) _ -> p

(* TODO: FIXME: workaround for projectors *)
val m_of_conf: config-> Tot mode
let m_of_conf (Conf _ m _ _ _ _) = m

val is_par: config -> Tot bool
let is_par c = is_Par (m_of_mode (m_of_conf c))

val is_sec: config -> Tot bool
let is_sec c = is_Sec (m_of_mode (m_of_conf c))

(* TODO: FIXME: the discriminators should take extra args for type indices *)
val is_clos: #meta:v_meta -> value meta -> Tot bool
let is_clos #meta v = match v with//is_V_clos v || is_V_fix_clos v || is_V_emp_clos v
  | V_clos _ _ _
  | V_emp_clos _ _
  | V_fix_clos _ _ _ _ -> true
  | _                  -> false

val get_en_b: #meta:v_meta -> v:value meta{is_clos v} -> Tot (env * varname * exp)
let get_en_b #meta v = match v with
  | V_clos en x e       -> en, x, e
  | V_fix_clos en f x e ->
    update_env #(Meta empty Cannot_b empty Cannot_w) en f (V_fix_clos en f x e), x, e
  | V_emp_clos x e      -> empty_env, x, e

val is_terminal: config -> Tot bool
let is_terminal (Conf _ (Mode as_m _) s _ t _) = as_m = Par && s = [] && is_T_val t

val is_sterminal: config -> Tot bool
let is_sterminal (Conf _ _ s _ t _) = s = [] && is_T_val t

//-----//

opaque val mk_aspar: exp -> exp -> Tot exp
let mk_aspar ps e = E_aspar ps e

opaque val mk_assec: exp -> exp -> Tot exp
let mk_assec ps e = E_assec ps e

opaque val mk_box: exp -> exp -> Tot exp
let mk_box ps e = E_box ps e

opaque val mk_unbox: exp -> Tot exp
let mk_unbox e = E_unbox e

opaque val mk_mkwire: exp -> exp -> Tot exp
let mk_mkwire e1 e2 = E_mkwire e1 e2

opaque val mk_projwire: exp -> exp -> Tot exp
let mk_projwire e1 e2 = E_projwire e1 e2

opaque val mk_concatwire: exp -> exp -> Tot exp
let mk_concatwire e1 e2 = E_concatwire e1 e2

opaque val mk_const: const -> Tot exp
let mk_const c = E_const c

opaque val mk_varname: string -> typ -> Tot varname
let mk_varname s t = Var s t

opaque val mk_var: string -> typ -> Tot exp
let mk_var x t = E_var (Var x t)

opaque val mk_let: varname -> exp -> exp -> Tot exp
let mk_let x e1 e2 = E_let x e1 e2

opaque val mk_abs: varname -> exp -> Tot exp
let mk_abs x e = E_abs x e

opaque val mk_fix: varname -> varname -> exp -> Tot exp
let mk_fix f x e = E_fix f x e

opaque val mk_empabs: varname -> exp -> Tot exp
let mk_empabs x e = E_empabs x e

opaque val mk_app: exp -> exp -> Tot exp
let mk_app e1 e2 = E_app e1 e2

opaque val mk_ffi: nat -> string -> 'a -> list exp -> 'b -> Tot exp
let mk_ffi n name a l b = E_ffi n name a l b

opaque val mk_cond: exp -> exp -> exp -> Tot exp
let mk_cond e e1 e2 = E_cond e e1 e2

opaque val mk_v_opaque: 'a -> (prin -> 'a -> Tot 'a) -> ('a -> 'a -> Tot 'a) -> (prins -> 'a -> Tot 'a) -> Tot dvalue
let mk_v_opaque v s c sps = D_v (Meta empty Can_b empty Can_w) (V_opaque v (Meta empty Can_b empty Can_w) s c sps)

(**********)

type compose_v_meta_inv (m1:v_meta) (m2:v_meta) (cmeta:v_meta) =
 subset (Meta.bps cmeta) (union (Meta.bps m1) (Meta.bps m2))            /\
 ((Meta.cb m1 = Can_b /\ Meta.cb m2 = Can_b) ==> Meta.cb cmeta = Can_b)   /\
 subset (Meta.wps cmeta) (union (Meta.wps m1) (Meta.wps m2))            /\
 ((Meta.cw m1 = Can_w /\ Meta.cw m2 = Can_w) ==> Meta.cw cmeta = Can_w)

val compose_opaque_meta: m1:v_meta -> m2:v_meta -> Tot (r:v_meta{compose_v_meta_inv m1 m2 r})
let compose_opaque_meta m1 m2 =
  let Meta bps1 cb1 wps1 cw1 = m1 in
  let Meta bps2 cb2 wps2 cw2 = m2 in

  let cb = if cb1 = Can_b && cb2 = Can_b then Can_b else Cannot_b in
  let cw = if cw1 = Can_w && cw2 = Can_w then Can_w else Cannot_w in

  Meta (union bps1 bps2) cb (union wps1 wps2) cw
