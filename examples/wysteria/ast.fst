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

type const =
  | C_prin : c:prin -> const
  | C_prins: c:prins -> const

  | C_unit : const
  | C_nat  : c:nat -> const
  | C_bool : c:bool -> const

type exp' =
  | E_aspar: ps:exp -> e:exp -> exp'
  (*| E_assec: ps:exp -> e:exp -> exp'*)
  | E_box  : ps:exp -> e:exp -> exp'
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
  | R_aspar: ps:value -> v:value -> redex
  | R_box  : ps:value -> v:value -> redex
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
  | F_aspar_e    : v:value -> frame'
  (*| F_assec_ps   : e:exp -> frame'
  | F_assec_e    : v:value -> frame'*)
  | F_box_ps     : e:exp -> frame'
  | F_box_e      : v:value -> frame'
  | F_unbox      : frame'
  | F_let        : x:varname -> e2:exp -> frame'
  | F_app_e1     : e2:exp -> frame'
  | F_app_e2     : v:value -> frame'
  
type frame =
  | Frame: m:mode -> en:env -> f:frame' -> frame

val stack_inv: list frame -> Tot bool
let rec stack_inv = function
  | []        -> true
  | f::[]     -> true
  | f::f'::tl ->
    let (Mode Par ps, Mode Par ps') = Frame.m f, Frame.m f' in
    subset ps ps' && stack_inv (f'::tl)

type stack = l:list frame{stack_inv l}

type CSMode (m:mode) (s:stack) =
  is_Cons s ==> (subset (Mode.ps m) (Mode.ps (Frame.m (Cons.hd s))))

type term =
  | T_exp: e:exp -> term
  | T_red: r:redex -> term
  | T_val: v:value -> term

type config =
  | Conf: m:mode -> s:stack{CSMode m s} -> en:env -> t:term -> config

type AFMode (f:frame) (s:stack) =
  is_Cons s ==> (subset (Mode.ps (Frame.m f)) (Mode.ps (Frame.m (Cons.hd s))))

val s_add: f:frame -> s:stack{AFMode f s} -> Tot stack
let s_add f s = f::s

type RFMode (f:frame) (s:stack) =
  is_Cons s /\ (Mode.ps (Frame.m f) = Mode.ps (Frame.m (Cons.hd s)))
  
val s_replace: f:frame -> s:stack{RFMode f s} -> Tot stack
let s_replace f s = s_add f (Cons.tl s)

val s_pop: c:config{is_Cons (Conf.s c)} -> Tot stack
let s_pop c = Cons.tl (Conf.s c)

val is_sframe: c:config -> f:(frame' -> Tot bool) -> Tot bool
let is_sframe (Conf _ s _ _) f = is_Cons s && f (Frame.f (Cons.hd s))

val pop_mode: c:config{is_Cons (Conf.s c)} -> Tot mode
let pop_mode (Conf _ (fr::_) _ _) = Frame.m fr

val pop_env: c:config{is_Cons (Conf.s c)} -> Tot env
let pop_env (Conf _ (fr::_) _ _) = Frame.en fr

val is_value: c:config -> Tot bool
let is_value c = is_T_val (Conf.t c)

val c_value: c:config{is_value c} -> Tot value
let c_value (Conf _ _ _ (T_val v)) = v

val is_redex: c:config -> Tot bool
let is_redex c = is_T_red (Conf.t c)

val is_exp: c:config -> Tot bool
let is_exp c = is_T_exp (Conf.t c) 

val pf_aspar_ps: c:config{is_sframe c is_F_aspar_ps} -> Tot exp
let pf_aspar_ps (Conf _ ((Frame _ _ (F_aspar_ps e))::_) _ _) = e

(*val pf_assec_ps: c:config{is_sframe c is_F_assec_ps} -> Tot exp
let pf_assec_ps (Conf _ ((Frame _ _ (F_assec_ps e))::_) _ _) = e*)

val pf_let: c:config{is_sframe c is_F_let} -> Tot (varname * exp)
let pf_let (Conf _ ((Frame _ _ (F_let x e2))::_) _ _) = x, e2

val pf_app_e1: c:config{is_sframe c is_F_app_e1} -> Tot exp
let pf_app_e1 (Conf _ ((Frame _ _ (F_app_e1 e2))::_) _ _) = e2

val pf_aspar_e: c:config{is_sframe c is_F_aspar_e} -> Tot value
let pf_aspar_e (Conf _ ((Frame _ _ (F_aspar_e v))::_) _ _) = v

(*val pf_assec_e: c:config{is_sframe c is_F_assec_e} -> Tot value
let pf_assec_e (Conf _ ((Frame _ _ (F_assec_e v))::_) _ _) = v*)

val pf_box_ps: c:config{is_sframe c is_F_box_ps} -> Tot exp
let pf_box_ps (Conf _ ((Frame _ _ (F_box_ps e))::_) _ _) = e

val pf_box_e: c:config{is_sframe c is_F_box_e} -> Tot value
let pf_box_e (Conf _ ((Frame _ _ (F_box_e v))::_) _ _) = v

val pf_app_e2: c:config{is_sframe c is_F_app_e2} -> Tot value
let pf_app_e2 (Conf _ ((Frame _ _ (F_app_e2 v))::_) _ _) = v

type is_easpar (c:config) =
  is_T_exp (Conf.t c) /\ is_E_aspar (Exp.e (T_exp.e (Conf.t c)))
val pe_aspar: c:config{is_easpar c} -> Tot (exp * exp)
let pe_aspar (Conf _ _ _ (T_exp (Exp (E_aspar e1 e2) _))) = e1, e2

(*val pe_assec: c:config{is_E_assec (Exp.e (Conf.e c))} -> Tot (exp * exp)
let pe_assec (Conf _ _ _ (Exp (E_assec e1 e2) _)) = e1, e2*)
type is_ebox (c:config) =
  is_T_exp (Conf.t c) /\ is_E_box (Exp.e (T_exp.e (Conf.t c)))
val pe_box: c:config{is_ebox c} -> Tot (exp * exp)
let pe_box (Conf _ _ _ (T_exp (Exp (E_box e1 e2) _))) = e1, e2

type is_eapp (c:config) =
  is_T_exp (Conf.t c) /\ is_E_app (Exp.e (T_exp.e (Conf.t c)))
val pe_app: c:config{is_eapp c} -> Tot (exp * exp)
let pe_app (Conf _ _ _ (T_exp (Exp (E_app e1 e2) _))) = (e1, e2)

type is_eabs (c:config) =
  is_T_exp (Conf.t c) /\ is_E_abs (Exp.e (T_exp.e (Conf.t c)))
val pe_abs: c:config{is_eabs c} -> Tot (varname * exp)
let pe_abs (Conf _ _ _ (T_exp (Exp (E_abs x e) _))) = (x, e)

type is_elet (c:config) =
  is_T_exp (Conf.t c) /\ is_E_let (Exp.e (T_exp.e (Conf.t c)))
val pe_let: c:config{is_elet c} -> Tot (Tuple3 varname exp exp)
let pe_let (Conf _ _ _ (T_exp (Exp (E_let x e1 e2) _))) = MkTuple3 x e1 e2

type is_evar (c:config) =
  is_T_exp (Conf.t c) /\ is_E_var (Exp.e (T_exp.e (Conf.t c)))
val pe_var: c:config{is_evar c} -> Tot varname
let pe_var (Conf _ _ _ (T_exp (Exp (E_var x) _))) = x

type is_econst (c:config) =
  is_T_exp (Conf.t c) /\ is_E_const (Exp.e (T_exp.e (Conf.t c)))
val pe_const: c:config{is_econst c} -> Tot const
let pe_const (Conf _ _ _ (T_exp (Exp (E_const c) _))) = c

type is_eunbox (c:config) =
  is_T_exp (Conf.t c) /\ is_E_unbox (Exp.e (T_exp.e (Conf.t c)))
val pe_unbox: c:config{is_eunbox c} -> Tot exp
let pe_unbox (Conf _ _ _ (T_exp (Exp (E_unbox e) _))) = e

val e_aspar: exp -> exp -> Tot exp
let e_aspar ps e = Exp (E_aspar ps e) None

(*val e_assec: exp -> exp -> Tot exp
let e_assec ps e = Exp (E_assec ps e) None*)

val e_box: exp -> exp -> Tot exp
let e_box ps e = Exp (E_box ps e) None

val e_unbox: exp -> Tot exp
let e_unbox e = Exp (E_unbox e) None

val e_let: varname -> exp -> exp -> Tot exp
let e_let x e1 e2 = Exp (E_let x e1 e2) None

val e_app: exp -> exp -> Tot exp
let e_app e1 e2 = Exp (E_app e1 e2) None

val v_prins: prins -> Tot value
let v_prins ps = V_const (C_prins ps)

type level = | Src | Tgt

val src: level -> Tot bool
let src = is_Src

val tgt: level -> Tot bool
let tgt = is_Tgt

(* pre returns comp, for src it's never Skip *)
type comp = | Do | Skip | NA

val pre_aspar: config -> l:level -> Tot comp
let pre_aspar c l = match c with
  | Conf (Mode Par ps1) _ _ (T_red (R_aspar (V_const (C_prins ps2))
                                            (V_clos _ _ _))) ->
    if src l then
      if subset ps2 ps1 then Do else NA
    else
      if subset ps1 ps2 then Do else Skip
  
  | _ -> NA

val step_aspar: c:config -> l:level{not (pre_aspar c l = NA)}
                -> Tot config
let step_aspar c l = match c with
  | Conf m s _ (T_red (R_aspar (V_const (C_prins ps)) (V_clos en x e))) ->
    let m'  = if src l then Mode Par ps else m in
    let s'  = s_add (Frame m empty_env (F_box_e (v_prins ps))) s in
    let en' = update_env en x (V_const C_unit) in
    let t'  =
      if src l then T_exp e
      else (if pre_aspar c l = Do then T_exp e else T_val V_emp)
    in
    Conf m' s' en' t'

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

val pre_box: config -> level -> Tot comp
let pre_box c l = match c with
  | Conf (Mode Par ps1) _ _ (T_red (R_box (V_const (C_prins ps2)) _)) ->
    if src l then
      if subset ps2 ps1 then Do else NA
    else Do

  | _ -> NA

val step_box: c:config -> l:level{pre_box c l = Do} -> Tot config
let step_box c l = match c with
  | Conf m s en (T_red (R_box (V_const (C_prins ps)) v)) ->
    Conf m s en (T_val (V_box ps v))

val pre_unbox: config -> level -> Tot comp
let pre_unbox c l = match c with
  | Conf (Mode Par ps1) _ _ (T_red (R_unbox (V_box ps2 _))) ->
    if subset ps1 ps2 then Do else NA
         
  | _ -> NA

val step_unbox: c:config -> l:level{pre_unbox c l = Do} -> Tot config
let step_unbox c l = match c with
  | Conf m s en (T_red (R_unbox (V_box _ v))) -> Conf m s en (T_val v)

val is_let_redex: c:config -> Tot bool
let is_let_redex c = match c with
  | Conf _ _ _ (T_red (R_let _ _ _)) -> true
  | _                                -> false

val step_let: c:config{is_let_redex c} -> Tot config
let step_let c = match c with
  | Conf m s en (T_red (R_let x v1 e2)) -> Conf m s (update_env en x v1) (T_exp e2)

val is_app_redex: c:config -> Tot bool
let is_app_redex c = match c with
  | Conf _ _ _ (T_red (R_app (V_clos _ _ _) _)) -> true

  | _ -> false

val step_app: c:config{is_app_redex c} -> Tot config
let step_app c = match c with
| Conf m s _ (T_red (R_app (V_clos en x e) v)) -> Conf m s (update_env en x v) (T_exp e)

(* M; S; E; e --> M'; S'; E'; e' (common steps for source and target) *)
type cstep: config -> config -> Type =

  (* M; S; E; aspar e1 do e2 --> M; (M; E; aspar <> do e2)::S; E; e1*)

  | C_aspar_ps:
    c:config{is_easpar c}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_aspar_ps (snd (pe_aspar c))))
                                  (Conf.s c))
                           (Conf.en c) (T_exp(fst (pe_aspar c)))}
    -> cstep c c'

  (* M; S; E; box e1 e2 --> M; (M; E; box <> e2)::S; E; e1 *)

  | C_box_ps:
    c:config{is_ebox c}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_box_ps (snd (pe_box c))))
                                  (Conf.s c))
                           (Conf.en c) (T_exp (fst (pe_box c)))}

    -> cstep c c'

  (* M; S; E; unbox e --> M; (M; E; unbox <>)::S; E; e *)

  | C_unbox:
    c:config{is_eunbox c}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c) F_unbox)
                                  (Conf.s c))
                           (Conf.en c) (T_exp (pe_unbox c))}
    -> cstep c c'

  (* M; S; E; c --> M; S; E; c *)

  | C_const:
    c:config{is_econst c}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (T_val (V_const (pe_const c)))}
    -> cstep c c'

  (* M; S; E; x --> M; S; E; E[x] *)

  | C_var:
    c:config{is_evar c}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (T_val ((Conf.en c) (pe_var c)))}
    -> cstep c c'

  (* M; S; E; let x = e1 in e2 --> M; (M; E; let x = <> in e2)::S; E; e1  *)

  | C_let_e1:
    c:config{is_elet c}
    -> c':config{c' = Conf (Conf.m c)
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
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (T_val (V_clos (Conf.en c)
                                          (fst (pe_abs c))
                                          (snd (pe_abs c))))}
    -> cstep c c'

  (* M; S; E; e1 e2 --> M; (M; E; <> e2)::s; E; e1 *)

  | C_app_e1:
    c:config{is_eapp c}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add  (Frame (Conf.m c) (Conf.en c)
                                          (F_app_e1 (snd (pe_app c))))
                                   (Conf.s c)
                           )
                           (Conf.en c) (T_exp (fst (pe_app c)))}
    -> cstep c c'

  (* M; (M'; E'; aspar <> do e)::S; E; v --> M'; (M'; E'; aspar v do <>)::s; E'; e *)

  | C_aspar_e:
    c:config{is_value c /\ is_sframe c is_F_aspar_ps}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_aspar_e (c_value c)))
                                                   (Conf.s c))
                           (pop_env c) (T_exp (pf_aspar_ps c))}
    -> cstep c c'

  (* M; (M'; E'; box <> e)::S; E; v --> M'; (M'; E'; box v <>)::S; E'; e *)
  
  | C_box_e:
    c:config{is_value c /\ is_sframe c is_F_box_ps}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_box_e (c_value c)))
                                                   (Conf.s c))
                           (pop_env c) (T_exp (pf_box_ps c))}
    -> cstep c c'

  (* M; (M'; E'; <> e)::S; E; v --> M'; (M'; E'; v <>)::S; E'; e *)

  | C_app_e2:
    c:config{is_value c /\ is_sframe c is_F_app_e1}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_app_e2 (c_value c)))
                                                   (Conf.s c))
                           (pop_env c) (T_exp (pf_app_e1 c))}
    -> cstep c c'

  (* _; (M'; E'; aspar v1 do <>))::S; _; v2 --> M'; S; E'; aspar v1 do v2  *)  
  
  | C_aspar_rec:
    c:config{is_value c /\ is_sframe c is_F_aspar_e}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (T_red (R_aspar (pf_aspar_e c) (c_value c)))}
    -> cstep c c'

  (* _; (M'; E'; box v1 <>))::S; _; v2 --> M'; S; E'; box v1 v2  *)
  
  | C_box_rec:
    c:config{is_value c /\ is_sframe c is_F_box_e}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (T_red (R_box (pf_box_e c) (c_value c)))}
    -> cstep c c'

  (* _; (M; E; unbox <>)::S; _; v --> M; S; E; unbox v*)

  | C_unbox_rec:
    c:config{is_value c /\ is_sframe c is_F_unbox}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (T_red (R_unbox (c_value c)))}
    -> cstep c c'
    
  (* _; (M; E; let x = <> in e)::S; _; v --> M; S; E; let x = v in e  *)

  | C_let_rec:
    c:config{is_value c /\ is_sframe c is_F_let}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (T_red (R_let (fst (pf_let c)) (c_value c)
                                         (snd (pf_let c))))}
    -> cstep c c'

  (* _; (M; E; v1 <>)::S; _; v2 --> M; S; E; v1 v2 *)
  | C_app_rec:
    c:config{is_value c /\ is_sframe c is_F_app_e2}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (T_red (R_app (pf_app_e2 c) (c_value c)))}
    -> cstep c c'
    
  (* M; S; E; let x = v1 in e2 --> M; S; E[x -> v]; e2 *)
  
  | C_let_beta:
    c:config{is_let_redex c} -> c':config{c' = step_let c} -> cstep c c'
    
  (* M; S; _; (E, fun x -> e) v --> M; S; E[x -> v]; e *)
  | C_app_beta:
    c:config{is_app_redex c} -> c':config{c' = step_app c} -> cstep c c'
  

(* M; S; E; e --> M'; S'; E'; e'  (source configuration beta steps )*)
type sstep: config -> config -> Type =

  | S_cstep: c:config -> c':config -> h:cstep c c' -> sstep c c'

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
  | S_aspar_beta:
    c:config{pre_aspar c Src = Do} -> c':config{c' = step_aspar c Src}
    -> sstep c c'

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

  | S_box_beta:
    c:config{pre_box c Src = Do} -> c':config{c' = step_box c Src} -> sstep c c'

  (* M; S; E; unbox (Box ps v) (when isPar M ==> sub M.ps ps /\
                                     isSec M ==> sub ps M.ps)
     -->
     M; S; E; v                                   
  *)
  | S_unbox_beta:
    c:config{pre_unbox c Src = Do} -> c':config{c' = step_unbox c Src}
    -> sstep c c'


type tconfig = c:config{is_Par (Mode.m (Conf.m c)) /\
                        is_singleton (Mode.ps (Conf.m c))}

(* M; S; E; e --> M'; S'; E'; e'  (target configuration beta steps)*)
type tstep: tconfig -> tconfig -> Type =
  
  (*| T_cstep: #p:prin
    -> c:tconfig p -> c':tconfig p -> h:cstep c c' -> tstep c c'*)
  
  
  (* M; S; _; aspar ps do clos(E, fun x -> e) 
     -->
     (when sub M.ps ps)        M;(M; E; Box ps <>)::S; E[x -> ()]; e
     (when not (sub M.ps ps))  M;(M; E; Box ps <>)::S; E[x -> ()]; V_emp
  *)
  
  | T_aspar_beta:
    c:tconfig{not (pre_aspar c Tgt = NA)} -> c':tconfig{c' = step_aspar c Tgt}
    -> tstep c c'

  (* M; S; E; Box ps v (when sub M.ps ps )
     -->
     M; S; E; V_box ps v
  *)

  | T_box_beta:
    c:tconfig{pre_box c Tgt = Do} -> c':tconfig{c' = step_box c Tgt}
    -> tstep c c'

  (* M; S; E; unbox (Box ps v) (when sub M.ps ps)
     -->
     M; S; E; v
  *)
  
  | T_unbox_beta:
    c:tconfig{pre_unbox c Tgt = Do} -> c':tconfig{c' = step_unbox c Tgt}
    -> tstep c c'

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

(* only expressions with values need to be sliced *)
val slice_e: prin -> exp -> Tot exp
let slice_e p e = e

val slice_r: prin -> redex -> Tot redex
let slice_r p r = match r with
  | R_aspar ps v  -> R_aspar (slice_v p ps) (slice_v p v)
  | R_box ps v    -> R_box (slice_v p ps) (slice_v p v)
  | R_unbox v     -> R_unbox (slice_v p v)
  | R_let x v1 e2 -> R_let x (slice_v p v1) e2
  | R_app v1 v2   -> R_app (slice_v p v1) (slice_v p v2)

(* only frame' with values need to be sliced *)
val slice_f': p:prin -> frame' -> Tot frame'
let slice_f' p f = match f with
  | F_aspar_e v -> F_aspar_e (slice_v p v)
  | F_box_e   v -> F_box_e   (slice_v p v)
  | F_app_e2  v -> F_app_e2  (slice_v p v)
  | _           -> f

val slice_f: p:prin -> f:frame{Mode.m (Frame.m f) = Par /\
                               mem p (Mode.ps (Frame.m f))}
                    -> Tot frame
let slice_f p (Frame _ en f) = Frame (Mode Par (singleton p)) (slice_en p en)
                                     (slice_f' p f)

val slice_s: p:prin -> s:stack -> Tot (s:stack{forall f. List.mem f s ==> (Mode.ps (Frame.m f) = singleton p)}) (decreases s)
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

val slice_c: prin -> config -> Tot tconfig
let rec slice_c p (Conf (Mode Par ps) s en t) =
  let en', t' =
    if mem p ps then slice_en p en, slice_t p t
    else empty_env, T_val V_emp in
  Conf (Mode Par (singleton p)) (slice_s p s) en' t'

(**********)

val slice_add_absent_frame_lem:
    p:prin -> s:stack -> f:frame{AFMode f s}
    -> Lemma (requires (not (mem p (Mode.ps (Frame.m f)))))
             (ensures  (slice_s p s = slice_s p (s_add f s)))
let slice_add_absent_frame_lem p s f = ()

open Constructive

val cstep_lemma: #c:config -> #c':config -> h:cstep c c' -> p:prin
                 -> Tot (cor (u:unit{slice_c p c = slice_c p c'})
                             (cstep (slice_c p c) (slice_c p c')))
let cstep_lemma #c #c' h p = match h with
  | C_aspar_ps (Conf m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_aspar_ps (slice_c p c) (slice_c p c'))
  | C_box_ps (Conf m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_box_ps (slice_c p c) (slice_c p c'))
  | C_unbox (Conf m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_unbox (slice_c p c) (slice_c p c'))
  | C_const (Conf m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_const (slice_c p c) (slice_c p c'))
  | C_var (Conf m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_var (slice_c p c) (slice_c p c'))
  | C_let_e1 (Conf m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_let_e1 (slice_c p c) (slice_c p c'))
  | C_abs (Conf m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else
      (* bug#259 *)
      let _ = admit () in
      IntroR (C_abs (slice_c p c) (slice_c p c'))
  | C_app_e1 (Conf m _ _ _) _ ->
    if not (mem p (Mode.ps m)) then IntroL ()
    else IntroR (C_app_e1 (slice_c p c) (slice_c p c'))

  | _ -> admit ()
