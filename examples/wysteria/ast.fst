(*--build-config
    options:--admit_fsi OrdSet --admit_fsi OrdMap --split_cases 1;
    variables:LIB=../../lib;
    other-files:$LIB/ordset.fsi $LIB/ordsetproperties.fst $LIB/ordmap.fsi $LIB/list.fst $LIB/constr.fst $LIB/ext.fst
 --*)

module AST

open OrdSet

type other_info = nat

type varname = string

type prin = nat

val p_cmp: prin -> prin -> Tot bool
let p_cmp p1 p2 = p1 <= p2

type prins = ordset prin p_cmp

type const =
  | C_prin : c:prin -> const
  | C_prins: c:prins -> const

  | C_unit : const
  | C_nat  : c:nat -> const
  | C_bool : c:bool -> const

type exp' =
  | E_aspar: ps:exp -> e:exp -> exp'
  | E_unbox: e:exp  -> exp'

  | E_const: c:const -> exp'
  | E_var  : x:varname -> exp'
  | E_let  : x:varname -> e1:exp -> e2:exp -> exp'
  | E_abs  : x:varname -> e:exp -> exp'
  | E_app  : e1:exp -> e2:exp -> exp'

and exp =
  | Exp: e:exp' -> info:option other_info -> exp

and value =
  | V_const  : c:const -> value
  | V_box    : ps:prins -> v:value -> value
  | V_clos   : en:env -> x:varname -> e:exp -> value

  (* bomb value, comes up in target only *)
  | V_emp : value

(* TODO: fix it, option value *)
and env = varname -> Tot value
    
type redex =
  | R_aspar: ps:prins -> v:value -> redex
  | R_box  : ps:prins -> v:value -> redex
  | R_unbox: v:value -> redex
  | R_let  : x:varname -> v:value -> e:exp -> redex
  | R_app  : v1:value -> v2:value -> redex

assume val empty_env: env

val update_env: env -> varname -> value -> Tot env
let update_env en x v = fun y -> if y = x then v else en y

type as_mode =
  | Par

type mode =
  | Mode: m:as_mode -> ps:prins -> mode

type frame' =
  | F_aspar_ps: e:exp -> frame'
  | F_aspar_e : ps:prins -> frame'
  | F_box_e   : ps:prins -> frame'
  | F_unbox   : frame'
  | F_let     : x:varname -> e2:exp -> frame'
  | F_app_e1  : e2:exp -> frame'
  | F_app_e2  : v:value -> frame'
  
type frame =
  | Frame: m:mode -> en:env -> f:frame'-> frame

type stack = list frame

type term =
  | T_exp: e:exp -> term
  | T_red: r:redex -> term
  | T_val: v:value -> term

type level = | Source | Target

type mode_inv (m:mode) (l:level) = is_Target l ==> is_singleton (Mode.ps m)

val stack_source_inv: stack -> mode -> Tot bool
let rec stack_source_inv s m = match s with
  | []                  -> true
  | (Frame m' _ f')::tl ->
    let Mode _ ps = m in
    let Mode _ ps' = m' in
    (not (is_F_box_e f') || (ps = F_box_e.ps f'))  &&
    (ps = ps' || (subset ps ps' && is_F_box_e f')) &&
    stack_source_inv tl m'

val stack_target_inv: stack -> mode -> Tot bool
let rec stack_target_inv s m = match s with
  | []                  -> true
  | (Frame m' _ f')::tl ->
    (Mode.ps m = Mode.ps m' && stack_target_inv tl m)

val stack_inv: stack -> mode -> level -> Tot bool
let rec stack_inv s m l =
  if is_Source l then stack_source_inv s m else stack_target_inv s m

type config =
  | Conf: l:level -> m:mode{mode_inv m l} -> s:stack{stack_inv s m l}
          -> en:env -> t:term -> config

val is_sframe: c:config -> f:(frame' -> Tot bool) -> Tot bool
let is_sframe (Conf _ _ s _ _) f = is_Cons s && f (Frame.f (Cons.hd s))

val is_value: c:config -> Tot bool
let is_value c = is_T_val (Conf.t c)

val is_value_ps: c:config -> Tot bool
let is_value_ps c = match c with
  | Conf _ _ _ _ (T_val (V_const (C_prins _))) -> true
  | _                                        -> false

val c_value: c:config{is_value c} -> Tot value
let c_value (Conf _ _ _ _ (T_val v)) = v

val c_value_ps: c:config{is_value_ps c} -> Tot prins
let c_value_ps c = match c with
  | Conf _ _ _ _ (T_val (V_const (C_prins ps))) -> ps

type is_easpar (c:config) =
  is_T_exp (Conf.t c) /\ is_E_aspar (Exp.e (T_exp.e (Conf.t c)))

type is_eapp (c:config) =
  is_T_exp (Conf.t c) /\ is_E_app (Exp.e (T_exp.e (Conf.t c)))

type is_eabs (c:config) =
  is_T_exp (Conf.t c) /\ is_E_abs (Exp.e (T_exp.e (Conf.t c)))

type is_elet (c:config) =
  is_T_exp (Conf.t c) /\ is_E_let (Exp.e (T_exp.e (Conf.t c)))

type is_evar (c:config) =
  is_T_exp (Conf.t c) /\ is_E_var (Exp.e (T_exp.e (Conf.t c)))

type is_econst (c:config) =
  is_T_exp (Conf.t c) /\ is_E_const (Exp.e (T_exp.e (Conf.t c)))

type is_eunbox (c:config) =
  is_T_exp (Conf.t c) /\ is_E_unbox (Exp.e (T_exp.e (Conf.t c)))

val src: level -> Tot bool
let src = is_Source

(* pre returns comp, for src it's never Skip *)
type comp = | Do | Skip | NA

val step_aspar_e1: c:config{is_easpar c} -> Tot config
let step_aspar_e1 (Conf l m s en (T_exp (Exp (E_aspar e1 e2) _))) =
  Conf l m ((Frame m en (F_aspar_ps e2))::s) en (T_exp e1)
  
val step_unbox_e: c:config{is_eunbox c} -> Tot config
let step_unbox_e (Conf l m s en (T_exp (Exp (E_unbox e) _))) =
  Conf l m ((Frame m en F_unbox)::s) en (T_exp e)

val step_const: c:config{is_econst c} -> Tot config
let step_const (Conf l m s en (T_exp (Exp (E_const c) _))) =
  Conf l m s en (T_val (V_const c))

val step_var: c:config{is_evar c} -> Tot config
let step_var (Conf l m s en (T_exp (Exp (E_var x) _))) =
  Conf l m s en (T_val (en x))

val step_let_e1: c:config{is_elet c} -> Tot config
let step_let_e1 (Conf l m s en (T_exp (Exp (E_let x e1 e2) _))) =
  Conf l m ((Frame m en (F_let x e2))::s) en (T_exp e1)

val step_abs: c:config{is_eabs c} -> Tot config
let step_abs (Conf l m s en (T_exp (Exp (E_abs x e) _))) =
  Conf l m s en (T_val (V_clos en x e))

val step_app_e1: c:config{is_eapp c} -> Tot config
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
  | Conf l (Mode Par ps1) _ _ (T_red (R_box ps2 _)) ->
    if src l then
      if subset ps2 ps1 then Do else NA
    else Do

  | _ -> NA

val step_box: c:config{pre_box c = Do} -> Tot config
let step_box c = match c with
  | Conf l m s en (T_red (R_box ps v)) -> Conf l m s en (T_val (V_box ps v))

val pre_unbox: config -> Tot comp
let pre_unbox c = match c with
  | Conf _ (Mode Par ps1) _ _ (T_red (R_unbox (V_box ps2 _))) ->
    if subset ps1 ps2 then Do else NA
         
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
    c:config{is_easpar c} -> c':config{c' = step_aspar_e1 c}
    -> cstep c c'

  | C_unbox:
    c:config{is_eunbox c} -> c':config{c' = step_unbox_e c}
    -> cstep c c'

  | C_const:
    c:config{is_econst c} -> c':config{c' = step_const c}
    -> cstep c c'

  | C_var:
    c:config{is_evar c} -> c':config{c' = step_var c}
    -> cstep c c'

  | C_let_e1:
    c:config{is_elet c} -> c':config{c' = step_let_e1 c}
    -> cstep c c'

  | C_abs:
    c:config{is_eabs c} -> c':config{c' = step_abs c}
    -> cstep c c'

  | C_app_e1:
    c:config{is_eapp c} -> c':config{c' = step_app_e1 c}
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

assume val preceds_axiom: en:env -> x:varname -> Lemma (ensures (en x << en))

val slice_v : prin -> v:value -> Tot value (decreases %[v])
val slice_en: prin -> en:env -> Tot (varname -> Tot value) (decreases %[en])

let rec slice_v p v =
  match v with
    | V_const _     -> v
    | V_box ps v'   ->
      let v'' = if mem p ps then slice_v p v' else V_emp in
      V_box ps v''
    | V_clos en x e -> V_clos (slice_en p en) x e
    | V_emp         -> v

and slice_en p en =
  let _ = () in
  fun x -> preceds_axiom en x; slice_v p (en x)

assume val slice_emp_en: p:prin
                         -> Lemma (requires (True))
                                  (ensures (slice_en p empty_env = empty_env))
                            [SMTPat (slice_en p empty_env)]

val slice_e: prin -> exp -> Tot exp
let slice_e p e = e

val slice_r: prin -> redex -> Tot redex
let slice_r p r = match r with
  | R_aspar ps v  -> R_aspar ps (slice_v p v)
  | R_box ps v    ->
    let v' = if mem p ps then slice_v p v else V_emp in
    R_box ps v'
  | R_unbox v     -> R_unbox (slice_v p v)
  | R_let x v1 e2 -> R_let x (slice_v p v1) e2
  | R_app v1 v2   -> R_app (slice_v p v1) (slice_v p v2)

val slice_f': p:prin -> frame' -> Tot frame'
let slice_f' p f = match f with
  | F_aspar_ps _ -> f
  | F_aspar_e  _ -> f
  | F_box_e    _ -> f
  | F_unbox      -> f
  | F_let    _ _ -> f
  | F_app_e1   _ -> f
  | F_app_e2   v -> F_app_e2  (slice_v p v)

val slice_f: p:prin -> f:frame{Mode.m (Frame.m f) = Par /\
                               mem p (Mode.ps (Frame.m f))}
                    -> Tot frame
let slice_f p (Frame _ en f) = Frame (Mode Par (singleton p)) (slice_en p en)
                                     (slice_f' p f)

val slice_s: p:prin -> s:stack
             -> Tot (r:stack{stack_target_inv r (Mode Par (singleton p))})
let rec slice_s p s = match s with
  | []     -> []
  | hd::tl ->
    if mem p (Mode.ps (Frame.m hd)) then
      (slice_f p hd)::(slice_s p tl)
    else
      slice_s p tl

val slice_t: p:prin -> t:term -> Tot term
let slice_t p t = match t with
  | T_val v -> T_val (slice_v p v)
  | T_exp e -> t
  | T_red r -> T_red (slice_r p r)

type sconfig = c:config{is_Source (Conf.l c)}
type tconfig = c:config{is_Target (Conf.l c)}

val slice_c: prin -> sconfig -> Tot tconfig
let rec slice_c p (Conf Source (Mode Par ps) s en t) =
  let en', t' =
    if mem p ps then slice_en p en, slice_t p t
    else empty_env, T_val V_emp in
  Conf Target (Mode Par (singleton p)) (slice_s p s) en' t'

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
#set-options "--max_fuel 2 --initial_fuel 2 --initial_ifuel 2 --max_ifuel 2"
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
        ExIntro (update p tc_p' pi_rest') (Conj (PS_tran h2' h1') ())
