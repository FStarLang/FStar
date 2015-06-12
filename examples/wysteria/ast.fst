(*--build-config
    options:--admit_fsi OrdSet;
    variables:LIB=../../lib;
    other-files:$LIB/ordset.fsi $LIB/list.fst $LIB/constr.fst
 --*)

module AST

open OrdSet

type other_info = nat

type varname = string

type prin = nat

val p_cmp: prin -> prin -> Tot bool
let p_cmp p1 p2 = p1 <= p2

type prins = ordset prin p_cmp

(* TODO:FIXME: hack, we don't have s1 = s2 ==> subset s1 s2 yet *)
val subset: prins -> prins -> Tot bool
let subset ps1 ps2 = (ps1 = ps2) || OrdSet.subset p_cmp ps1 ps2

assume val subset_transitive: ps1:prins -> ps2:prins -> ps3:prins
                              -> Lemma (requires (subset ps1 ps2 /\ subset ps2 ps3))
                                       (ensures  (subset ps1 ps3))
                                 [SMTPat (subset ps1 ps2); SMTPat (subset ps2 ps3)]
                                 
val mem: prin -> prins -> Tot bool
let mem = OrdSet.mem p_cmp

assume val mem_subset: p:prin -> ps1:prins -> ps2:prins
                       -> Lemma (requires (mem p ps1 /\ subset ps1 ps2))
                                (ensures  (mem p ps2))
                          [SMTPat (subset ps1 ps2)]

val singleton: prin -> Tot (ps:prins{OrdSet.size p_cmp ps = 1})
let singleton p = OrdSet.singleton p_cmp p

val is_singleton: prins -> Tot bool
let is_singleton ps = (OrdSet.size p_cmp ps = 1)

assume val mem_subset_singleton: p:prin -> ps:prins
                                 -> Lemma (requires (mem p ps))
                                          (ensures  (subset (singleton p) ps))
                                    [SMTPat (subset (singleton p) ps)]

type const =
  | C_prin : c:prin -> const
  | C_prins: c:prins -> const

  | C_unit : const
  | C_nat  : c:nat -> const
  | C_bool : c:bool -> const

type exp' =
  | E_aspar: ps:exp -> e:exp -> exp'
  (*| E_assec: ps:exp -> e:exp -> exp'*)
  | E_unbox: e:exp -> exp'

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

val to_exp: exp' -> Tot exp
let to_exp e = Exp e None

val update_env: env -> varname -> value -> Tot env
let update_env en x v = fun y -> if y = x then v else en y

type as_mode =
  | Par
  (*| Sec*)

type mode =
  | Mode: m:as_mode -> ps:prins -> mode

type frame' =
  | F_aspar_ps   : e:exp -> frame'
  | F_aspar_e    : ps:prins -> frame'
  (*| F_assec_ps   : e:exp -> frame'
  | F_assec_e    : v:value -> frame'*)
  | F_box_e      : ps:prins -> frame'
  | F_unbox      : frame'
  | F_let        : x:varname -> e2:exp -> frame'
  | F_app_e1     : e2:exp -> frame'
  | F_app_e2     : v:value -> frame'
  
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
    let Mode _ ps = m in
    let Mode _ ps' = m' in
    (ps = ps' && stack_target_inv tl m)

val stack_inv: stack -> mode -> level -> Tot bool
let rec stack_inv s m l =
  if is_Source l then stack_source_inv s m else stack_target_inv s m

type config =
  | Conf: l:level -> m:mode{mode_inv m l} -> s:stack{stack_inv s m l}
          -> en:env -> t:term -> config


val s_add: frame -> stack -> Tot stack
let s_add = Cons

val s_replace: frame -> s:stack{is_Cons s} -> Tot stack
let s_replace f s = f::(Cons.tl s)

val s_pop: c:config{is_Cons (Conf.s c)} -> Tot stack
let s_pop c = Cons.tl (Conf.s c)

val is_sframe: c:config -> f:(frame' -> Tot bool) -> Tot bool
let is_sframe (Conf _ _ s _ _) f = is_Cons s && f (Frame.f (Cons.hd s))

val pop_mode: c:config{is_Cons (Conf.s c)} -> Tot mode
let pop_mode (Conf _ _ (fr::_) _ _) = Frame.m fr

val pop_env: c:config{is_Cons (Conf.s c)} -> Tot env
let pop_env (Conf _ _ (fr::_) _ _) = Frame.en fr

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

val is_redex: c:config -> Tot bool
let is_redex c = is_T_red (Conf.t c)

val is_exp: c:config -> Tot bool
let is_exp c = is_T_exp (Conf.t c) 

val pf_aspar_ps: c:config{is_sframe c is_F_aspar_ps} -> Tot exp
let pf_aspar_ps (Conf _ _ ((Frame _ _ (F_aspar_ps e))::_) _ _) = e

(*val pf_assec_ps: c:config{is_sframe c is_F_assec_ps} -> Tot exp
let pf_assec_ps (Conf _ ((Frame _ _ (F_assec_ps e))::_) _ _) = e*)

val pf_let: c:config{is_sframe c is_F_let} -> Tot (varname * exp)
let pf_let (Conf _ _ ((Frame _ _ (F_let x e2))::_) _ _) = x, e2

val pf_app_e1: c:config{is_sframe c is_F_app_e1} -> Tot exp
let pf_app_e1 (Conf _ _ ((Frame _ _ (F_app_e1 e2))::_) _ _) = e2

val pf_aspar_e: c:config{is_sframe c is_F_aspar_e} -> Tot prins
let pf_aspar_e (Conf _ _ ((Frame _ _ (F_aspar_e ps))::_) _ _) = ps

(*val pf_assec_e: c:config{is_sframe c is_F_assec_e} -> Tot value
let pf_assec_e (Conf _ ((Frame _ _ (F_assec_e v))::_) _ _) = v*)

val pf_box_e: c:config{is_sframe c is_F_box_e} -> Tot prins
let pf_box_e (Conf _ _ ((Frame _ _ (F_box_e ps))::_) _ _) = ps

val pf_app_e2: c:config{is_sframe c is_F_app_e2} -> Tot value
let pf_app_e2 (Conf _ _ ((Frame _ _ (F_app_e2 v))::_) _ _) = v

type is_easpar (c:config) =
  is_T_exp (Conf.t c) /\ is_E_aspar (Exp.e (T_exp.e (Conf.t c)))
val pe_aspar: c:config{is_easpar c} -> Tot (exp * exp)
let pe_aspar (Conf _ _ _ _ (T_exp (Exp (E_aspar e1 e2) _))) = e1, e2

(*val pe_assec: c:config{is_E_assec (Exp.e (Conf.e c))} -> Tot (exp * exp)
let pe_assec (Conf _ _ _ (Exp (E_assec e1 e2) _)) = e1, e2*)

type is_eapp (c:config) =
  is_T_exp (Conf.t c) /\ is_E_app (Exp.e (T_exp.e (Conf.t c)))
val pe_app: c:config{is_eapp c} -> Tot (exp * exp)
let pe_app (Conf _ _ _ _ (T_exp (Exp (E_app e1 e2) _))) = (e1, e2)

type is_eabs (c:config) =
  is_T_exp (Conf.t c) /\ is_E_abs (Exp.e (T_exp.e (Conf.t c)))
val pe_abs: c:config{is_eabs c} -> Tot (varname * exp)
let pe_abs (Conf _ _ _ _ (T_exp (Exp (E_abs x e) _))) = (x, e)

type is_elet (c:config) =
  is_T_exp (Conf.t c) /\ is_E_let (Exp.e (T_exp.e (Conf.t c)))
val pe_let: c:config{is_elet c} -> Tot (Tuple3 varname exp exp)
let pe_let (Conf _ _ _ _ (T_exp (Exp (E_let x e1 e2) _))) = MkTuple3 x e1 e2

type is_evar (c:config) =
  is_T_exp (Conf.t c) /\ is_E_var (Exp.e (T_exp.e (Conf.t c)))
val pe_var: c:config{is_evar c} -> Tot varname
let pe_var (Conf _ _ _ _ (T_exp (Exp (E_var x) _))) = x

type is_econst (c:config) =
  is_T_exp (Conf.t c) /\ is_E_const (Exp.e (T_exp.e (Conf.t c)))
val pe_const: c:config{is_econst c} -> Tot const
let pe_const (Conf _ _ _ _ (T_exp (Exp (E_const c) _))) = c

type is_eunbox (c:config) =
  is_T_exp (Conf.t c) /\ is_E_unbox (Exp.e (T_exp.e (Conf.t c)))
val pe_unbox: c:config{is_eunbox c} -> Tot exp
let pe_unbox (Conf _ _ _ _ (T_exp (Exp (E_unbox e) _))) = e

val src: level -> Tot bool
let src = is_Source

val tgt: level -> Tot bool
let tgt = is_Target

(* pre returns comp, for src it's never Skip *)
type comp = | Do | Skip | NA

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
  | Conf l m s _ (T_red (R_aspar ps (V_clos en x e))) ->
    let m'  = if src l then Mode Par ps else m in
    let s'  = s_add (Frame m empty_env (F_box_e ps)) s in
    let en' = update_env en x (V_const C_unit) in
    let t'  =
      if src l then T_exp e
      else (if pre_aspar c = Do then T_exp e else T_val V_emp)
    in
    Conf l m' s' en' t'

(*val pre_assec: c:config -> Tot bool
let pre_assec c = match c with
 | Conf (Mode _ ps1) _ _
        (Exp (E_assec (Exp (E_value (V_const (C_prins ps2))) _)
                      (Exp (E_value (V_clos _ _ _)) _)) _)
        
        -> ps1 = ps2
 
 | _ -> false

val pe_assec_beta: c:config{pre_assec c} -> Tot (Tuple4 prins env varname exp)
let pe_assec_beta c = match c with
 | Conf _ _ _
        (Exp (E_assec (Exp (E_value (V_const (C_prins ps))) _)
                      (Exp (E_value (V_clos en x e)) _)) _)
        
        -> MkTuple4 ps en x e*)

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

(* M; S; E; e --> M'; S'; E'; e' (common steps for source and target) *)
type cstep: config -> config -> Type =

  (* M; S; E; aspar e1 do e2 --> M; (M; E; aspar <> do e2)::S; E; e1*)

  | C_aspar_ps:
    c:config{is_easpar c}
    -> c':config{c' = Conf (Conf.l c) (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_aspar_ps (snd (pe_aspar c))))
                                  (Conf.s c))
                           (Conf.en c) (T_exp(fst (pe_aspar c)))}
    -> cstep c c'

  (* M; S; E; unbox e --> M; (M; E; unbox <>)::S; E; e *)

  | C_unbox:
    c:config{is_eunbox c}
    -> c':config{c' = Conf (Conf.l c)(Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c) F_unbox)
                                  (Conf.s c))
                           (Conf.en c) (T_exp (pe_unbox c))}
    -> cstep c c'

  (* M; S; E; c --> M; S; E; c *)

  | C_const:
    c:config{is_econst c}
    -> c':config{c' = Conf (Conf.l c) (Conf.m c) (Conf.s c) (Conf.en c)
                           (T_val (V_const (pe_const c)))}
    -> cstep c c'

  (* M; S; E; x --> M; S; E; E[x] *)

  | C_var:
    c:config{is_evar c}
    -> c':config{c' = Conf (Conf.l c) (Conf.m c) (Conf.s c) (Conf.en c)
                           (T_val ((Conf.en c) (pe_var c)))}
    -> cstep c c'

  (* M; S; E; let x = e1 in e2 --> M; (M; E; let x = <> in e2)::S; E; e1  *)

  | C_let_e1:
    c:config{is_elet c}
    -> c':config{c' = Conf (Conf.l c) (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_let (MkTuple3._1 (pe_let c))
                                                (MkTuple3._3 (pe_let c))))
                                  (Conf.s c)
                           )
                           (Conf.en c) (T_exp (MkTuple3._2 (pe_let c)))}
    -> cstep c c'

  (* M; S; E; fun x -> e --> M; S; E; clos(E, fun x -> e) *)

  | C_abs:
    c:config{is_eabs c}
    -> c':config{c' = Conf (Conf.l c) (Conf.m c) (Conf.s c) (Conf.en c)
                           (T_val (V_clos (Conf.en c)
                                          (fst (pe_abs c))
                                          (snd (pe_abs c))))}
    -> cstep c c'

  (* M; S; E; e1 e2 --> M; (M; E; <> e2)::s; E; e1 *)

  | C_app_e1:
    c:config{is_eapp c}
    -> c':config{c' = Conf (Conf.l c) (Conf.m c)
                           (s_add  (Frame (Conf.m c) (Conf.en c)
                                          (F_app_e1 (snd (pe_app c))))
                                   (Conf.s c)
                           )
                           (Conf.en c) (T_exp (fst (pe_app c)))}
    -> cstep c c'

  (* M; (M'; E'; aspar <> do e)::S; E; v --> M'; (M'; E'; aspar v do <>)::s; E'; e *)

  | C_aspar_e:
    c:config{is_value_ps c /\ is_sframe c is_F_aspar_ps}
    -> c':config{c' = Conf (Conf.l c) (pop_mode c)
                           (s_replace (Frame (pop_mode c) (pop_env c)
                                             (F_aspar_e (c_value_ps c)))
                                      (Conf.s c))
                           (pop_env c) (T_exp (pf_aspar_ps c))}
    -> cstep c c'

  (* M; (M'; E'; <> e)::S; E; v --> M'; (M'; E'; v <>)::S; E'; e *)

  | C_app_e2:
    c:config{is_value c /\ is_sframe c is_F_app_e1}
    -> c':config{c' = Conf (Conf.l c) (pop_mode c)
                           (s_replace (Frame (pop_mode c) (pop_env c)
                                             (F_app_e2 (c_value c)))
                                      (Conf.s c))
                           (pop_env c) (T_exp (pf_app_e1 c))}
    -> cstep c c'

  (* _; (M'; E'; aspar v1 do <>))::S; _; v2 --> M'; S; E'; aspar v1 do v2  *)  
  
  | C_aspar_rec:
    c:config{is_value c /\ is_sframe c is_F_aspar_e}
    -> c':config{c' = Conf (Conf.l c) (pop_mode c) (s_pop c) (pop_env c)
                           (T_red (R_aspar (pf_aspar_e c) (c_value c)))}
    -> cstep c c'

  (* _; (M'; E'; box v1 <>))::S; _; v2 --> M'; S; E'; box v1 v2  *)
  
  | C_box_rec:
    c:config{is_value c /\ is_sframe c is_F_box_e}
    -> c':config{c' = Conf (Conf.l c) (pop_mode c) (s_pop c) (pop_env c)
                           (T_red (R_box (pf_box_e c) (c_value c)))}
    -> cstep c c'

  (* _; (M; E; unbox <>)::S; _; v --> M; S; E; unbox v*)

  | C_unbox_rec:
    c:config{is_value c /\ is_sframe c is_F_unbox}
    -> c':config{c' = Conf (Conf.l c) (pop_mode c) (s_pop c) (pop_env c)
                           (T_red (R_unbox (c_value c)))}
    -> cstep c c'

  (* _; (M; E; let x = <> in e)::S; _; v --> M; S; E; let x = v in e  *)

  | C_let_rec:
    c:config{is_value c /\ is_sframe c is_F_let}
    -> c':config{c' = Conf (Conf.l c) (pop_mode c) (s_pop c) (pop_env c)
                           (T_red (R_let (fst (pf_let c)) (c_value c)
                                         (snd (pf_let c))))}
    -> cstep c c'

  (* _; (M; E; v1 <>)::S; _; v2 --> M; S; E; v1 v2 *)
  | C_app_rec:
    c:config{is_value c /\ is_sframe c is_F_app_e2}
    -> c':config{c' = Conf (Conf.l c) (pop_mode c) (s_pop c) (pop_env c)
                           (T_red (R_app (pf_app_e2 c) (c_value c)))}
    -> cstep c c'

  (* M; S; E; let x = v1 in e2 --> M; S; E[x -> v]; e2 *)
  
  | C_let_beta:
    c:config{is_let_redex c} -> c':config{c' = step_let c} -> cstep c c'
    
  (* M; S; _; (E, fun x -> e) v --> M; S; E[x -> v]; e *)
  | C_app_beta:
    c:config{is_app_redex c} -> c':config{c' = step_app c} -> cstep c c'

  (* M; S; E; assec e1 do e2 --> M; (M; E; assec <> do e2)::S; E; e1 *)

  (*| S_assec_ps:
    c:config{is_E_assec (Exp.e (Conf.e c)) /\ not (is_reduced c)}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_assec_ps (snd (pe_assec c))))
                                  (Conf.s c))
                           (Conf.en c) (fst (pe_assec c))}
    -> sstep c c'*)

  (* M; (M'; E'; assec <> do e)::S; E; v --> M'; (M'; E'; assec v do <>)::s; E'; e *)

  (*| S_assec_e:
    c:config{is_value c /\ is_sframe c is_F_assec_ps}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_assec_e (pe_value c)))
                                                   (Conf.s c))
                           (pop_env c) (pf_assec_ps c)}
    -> sstep c c'*)

  (* _; (M'; E'; assec v1 do <>))::S; _; v2 --> M'; S; E'; assec v1 do v2  *)
  
  (*| S_assec_rec:
    c:config{is_value c /\ is_sframe c is_F_assec_e}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (e_assec (e_value (pf_assec_e c))
                                    (e_value (pe_value c)))}
    -> sstep c c'*)
    
  (* M; S; _; aspar ps do clos(E, fun x -> e)  (when M is Par(ps1) /\ sub ps ps1
     -->
     Par(ps); (Par(ps); E; Box ps <>)::S; E[x -> ()]; e
  *)
  | C_aspar_beta:
    c:config{not (pre_aspar c = NA)} -> c':config{c' = step_aspar c}
    -> cstep c c'

  (* M; S; _; assec ps do clos(E, fun x -> e)  (when ps = M.ps)
     -->
     Sec(ps); S; E[x -> ()]; e
  *)
  (*| S_assec_beta:
    c:config{pre_assec c}
    -> c':config{c' = Conf (Mode Sec (MkTuple4._1 (pe_assec_beta c))) (Conf.s c)
                           (update_env (MkTuple4._2 (pe_assec_beta c))
                                       (MkTuple4._3 (pe_assec_beta c))
                                       (V_const C_unit))
                           (MkTuple4._4 (pe_assec_beta c))}
    -> sstep c c'*)

  (* M; S; E; box ps v (when is_Par M /\ sub ps M.ps)
     -->
     M; S; E; Box ps v
  *)

  | C_box_beta:
    c:config{pre_box c = Do} -> c':config{c' = step_box c} -> cstep c c'

  (* M; S; E; unbox (Box ps v) (when isPar M ==> sub M.ps ps /\
                                     isSec M ==> sub ps M.ps)
     -->
     M; S; E; v                                   
  *)
  | C_unbox_beta:
    c:config{pre_unbox c = Do} -> c':config{c' = step_unbox c}
    -> cstep c c'

(**********)

assume val preceds_axiom: en:env -> x:varname -> Lemma (ensures (en x << en))

val slice_v : prin -> v:value -> Tot value (decreases %[v])
val slice_en: prin -> en:env -> varname -> Tot value (decreases %[en])

// (fun y -> preceds_axiom en y; slice_v p (en y)) x e
let rec slice_v p v =
  match v with
    | V_box ps v'   ->
      let v'' = if mem p ps then slice_v p v' else V_emp in
      V_box ps v''
    | V_clos en x e -> V_clos (slice_en p en) x e
    | _             -> v

and slice_en p en x = preceds_axiom en x; slice_v p (en x)// fun x -> slice_v p (en x)

assume val slice_emp_en: p:prin
                         -> Lemma (ensures (slice_en p empty_env = empty_env))

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

(* only frame' with values need to be sliced *)
val slice_f': p:prin -> frame' -> Tot frame'
let slice_f' p f = match f with
  | F_app_e2  v -> F_app_e2  (slice_v p v)
  | _           -> f

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

(* TODO: FIXME: this should follow *)
val env_upd_slice_lemma: p:prin -> en:env -> x:varname -> v:value
                         -> Lemma (requires (True))
                                  (ensures (slice_en p (update_env en x v) =
                                            update_env (slice_en p en) x (slice_v p v)))
let env_upd_slice_lemma p en x v = admit ()


val cstep_lemma: #c:sconfig -> #c':sconfig -> h:cstep c c' -> p:prin
                 -> Tot (cor (u:unit{slice_c p c = slice_c p c'})
                             (cstep (slice_c p c) (slice_c p c')))
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
  | C_abs (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      (* bug#259 *)
      let _ = admit () in
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
  | C_aspar_rec (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_aspar_rec (slice_c p c) (slice_c p c'))
  | C_box_rec (Conf _ m s _ _) _ ->
    if mem p (Mode.ps m) then
      IntroR (C_box_rec (slice_c p c) (slice_c p c'))
    else if mem p (Mode.ps (Frame.m (Cons.hd s))) then
      IntroR (C_box_rec (slice_c p c) (slice_c p c'))
    else IntroL ()
  | C_unbox_rec (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_unbox_rec (slice_c p c) (slice_c p c'))
  | C_let_rec (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_let_rec (slice_c p c) (slice_c p c'))
  | C_app_rec (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_app_rec (slice_c p c) (slice_c p c'))
  | C_let_beta (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      let Conf _ _ _ en (T_red (R_let x v _)) = c in
      let _ = env_upd_slice_lemma p en x v in
      IntroR (C_let_beta (slice_c p c) (slice_c p c'))
  | C_app_beta (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      (* bug#259 *)
      let _ = admit () in
      IntroR (C_app_beta (slice_c p c) (slice_c p c'))
  | C_aspar_beta (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      (* bug#259 *)
      let _ = admit () in
      IntroR (C_aspar_beta (slice_c p c) (slice_c p c'))
  | C_box_beta (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      IntroR (C_box_beta (slice_c p c) (slice_c p c'))
  | C_unbox_beta (Conf _ m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      IntroR (C_unbox_beta (slice_c p c) (slice_c p c'))
