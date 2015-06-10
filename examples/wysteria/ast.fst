(*--build-config
    options:--admit_fsi OrdSet;
    variables:LIB=../../lib;
    other-files:$LIB/ordset.fsi $LIB/list.fst
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
  
  | E_value: v:value -> exp' (* E_value only come up during evaluation *)

and exp =
  | Exp: e:exp' -> info:option other_info -> exp

and value =
  | V_const  : c:const -> value
  | V_box    : ps:prins -> v:value -> value
  | V_clos   : en:env -> x:varname -> e:exp -> value

  (* empty box, comes up in target only *)
  | V_empbox : value

(* TODO: fix it, option value *)
and env = varname -> Tot value

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

(* TODO: FIXME: perhaps build subset of modes in stack order in the list constructor itself (Cons) ?
 * else getting a bit tedious to reason about stack invariant
 *)

type stack = l:list frame{stack_inv l}

type CSMode (m:mode) (s:stack) =
  is_Cons s ==> (subset (Mode.ps m) (Mode.ps (Frame.m (Cons.hd s))))

type config =
  | Conf: m:mode -> s:stack{CSMode m s} -> en:env -> e:exp -> config

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

val is_value_e: exp -> Tot bool
let is_value_e e = is_E_value (Exp.e e)

val is_value: c:config -> Tot bool
let is_value c = is_value_e (Conf.e c)

val is_reduced_e: exp -> Tot bool
let is_reduced_e (Exp e _) =
  match e with
    | E_aspar e1 e2
    (*| E_assec e1 e2*)
    | E_box   e1 e2
    | E_app   e1 e2 -> is_value_e e1 && is_value_e e2
    | E_unbox e
    | E_let _ e _   -> is_value_e e
    | E_value _     -> true
    | _             -> false

val is_reduced: config -> Tot bool
let is_reduced (Conf _ _ _ e) = is_reduced_e e

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

val pe_value: c:config{is_E_value (Exp.e (Conf.e c))} -> Tot value
let pe_value (Conf _ _ _ (Exp (E_value v) _)) = v

val pe_info: c:config -> Tot (option other_info)
let pe_info (Conf _ _ _ (Exp _ inf)) = inf

val pe_aspar: c:config{is_E_aspar (Exp.e (Conf.e c))} -> Tot (exp * exp)
let pe_aspar (Conf _ _ _ (Exp (E_aspar e1 e2) _)) = e1, e2

(*val pe_assec: c:config{is_E_assec (Exp.e (Conf.e c))} -> Tot (exp * exp)
let pe_assec (Conf _ _ _ (Exp (E_assec e1 e2) _)) = e1, e2*)

val pe_box: c:config{is_E_box (Exp.e (Conf.e c))} -> Tot (exp * exp)
let pe_box (Conf _ _ _ (Exp (E_box e1 e2) _)) = e1, e2

val pe_app: c:config{is_E_app (Exp.e (Conf.e c))} -> Tot (exp * exp)
let pe_app (Conf _ _ _ (Exp (E_app e1 e2) _)) = (e1, e2)

val pe_abs: c:config{is_E_abs (Exp.e (Conf.e c))} -> Tot (varname * exp)
let pe_abs (Conf _ _ _ (Exp (E_abs x e) _)) = (x, e)

val pe_let: c:config{is_E_let (Exp.e (Conf.e c))} -> Tot (Tuple3 varname exp exp)
let pe_let (Conf _ _ _ (Exp (E_let x e1 e2) _)) = MkTuple3 x e1 e2

val pe_var: c:config{is_E_var (Exp.e (Conf.e c))} -> Tot varname
let pe_var (Conf _ _ _ (Exp (E_var x) _)) = x

val pe_const: c:config{is_E_const (Exp.e (Conf.e c))} -> Tot const
let pe_const (Conf _ _ _ (Exp (E_const c) _)) = c

val pe_unbox: c:config{is_E_unbox (Exp.e (Conf.e c))} -> Tot exp
let pe_unbox (Conf _ _ _ (Exp (E_unbox e) _)) = e

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

val e_value: value -> Tot exp
let e_value v = Exp (E_value v) None

val v_prins: prins -> Tot value
let v_prins ps = V_const (C_prins ps)

type level = | Src | Tgt

val src: level -> Tot bool
let src = is_Src

val tgt: level -> Tot bool
let tgt = is_Tgt

type comp = | Do | Skip | NA

val pre_aspar: config -> l:level -> Tot comp
let pre_aspar c l = match c with
  | Conf (Mode Par ps1) _ _
         (Exp (E_aspar (Exp (E_value (V_const (C_prins ps2))) _)
                       (Exp (E_value (V_clos _ _ _)) _)) _) ->
    if src l then
      if subset ps2 ps1 then Do else NA
    else
      if subset ps1 ps2 then Do else Skip
  
  | _ -> NA

val step_aspar: c:config -> l:level{pre_aspar c l = Do} -> Tot config
let step_aspar c l = match c with
  | Conf m s _
         (Exp (E_aspar (Exp (E_value (V_const (C_prins ps))) _)
                       (Exp (E_value (V_clos en x e)) _)) _) ->
    let m' = if src l then Mode Par ps else m in
    let s'  = s_add (Frame m' empty_env (F_box_e (v_prins ps))) s in
    let en' = update_env en x (V_const C_unit) in
    Conf m' s' en' e

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
  | Conf (Mode Par ps1) _ _
         (Exp (E_box (Exp (E_value (V_const (C_prins ps2))) _)
                     (Exp (E_value _) _)) _) ->
    if src l then
      if subset ps2 ps1 then Do else NA
    else
      if subset ps1 ps2 then Do else Skip

  | _ -> NA

val step_box: c:config -> l:level{pre_box c l = Do} -> Tot config
let step_box c l = match c with
  | Conf m s en
         (Exp (E_box (Exp (E_value (V_const (C_prins ps))) _)
                     (Exp (E_value v) _)) _) ->
    Conf m s en (e_value (V_box ps v))

val pre_unbox: config -> level -> Tot comp
let pre_unbox c l = match c with
  | Conf (Mode Par ps1) _ _
         (Exp (E_unbox (Exp (E_value (V_box ps2 _)) _)) _) ->
    if subset ps1 ps2 then Do else NA
         
  | _ -> NA

val step_unbox: c:config -> l:level{pre_unbox c l = Do} -> Tot config
let step_unbox c l = match c with
  | Conf m s en (Exp (E_unbox (Exp (E_value (V_box _ v)) _)) _) ->
    Conf m s en (e_value v)

val is_let_redex: c:config -> Tot bool
let is_let_redex c = is_E_let (Exp.e (Conf.e c)) && is_reduced c

val step_let: c:config{is_let_redex c} -> Tot config
let step_let c = match c with
  | Conf m s en (Exp (E_let x (Exp (E_value v) _) e2) _) ->
    Conf m s (update_env en x v) e2

val is_app_redex: c:config -> Tot bool
let is_app_redex c = match c with
  | Conf _ _ _
         (Exp (E_app (Exp (E_value (V_clos _ _ _)) _)
                     (Exp (E_value _) _)) _) ->
    true

  | _ -> false

val step_app: c:config{is_app_redex c} -> Tot config
let step_app c = match c with
| Conf m s _
       (Exp (E_app (Exp (E_value (V_clos en x e)) _)
                   (Exp (E_value v) _)) _) ->
  Conf m s (update_env en x v) e

(* M; S; E; e --> M'; S'; E'; e' (common steps for source and target) *)
type cstep: config -> config -> Type =

  (* M; S; E; aspar e1 do e2 --> M; (M; E; aspar <> do e2)::S; E; e1*)

  | C_aspar_ps:
    c:config{is_E_aspar (Exp.e (Conf.e c)) /\ not (is_reduced c)}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_aspar_ps (snd (pe_aspar c))))
                                  (Conf.s c))
                           (Conf.en c) (fst (pe_aspar c))}
    -> cstep c c'

  (* M; S; E; box e1 e2 --> M; (M; E; box <> e2)::S; E; e1 *)

  | C_box_ps:
    c:config{is_E_box (Exp.e (Conf.e c)) /\ not (is_reduced c)}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_box_ps (snd (pe_box c))))
                                  (Conf.s c))
                           (Conf.en c) (fst (pe_box c))}

    -> cstep c c'

  (* M; S; E; unbox e --> M; (M; E; unbox <>)::S; E; e *)

  | C_unbox:
    c:config{is_E_unbox (Exp.e (Conf.e c)) /\ not (is_reduced c)}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c) F_unbox)
                                  (Conf.s c))
                           (Conf.en c) (pe_unbox c)}
    -> cstep c c'

  (* M; S; E; c --> M; S; E; c *)

  | C_const:
    c:config{is_E_const (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (Exp (E_value (V_const (pe_const c))) (pe_info c))}
    -> cstep c c'

  (* M; S; E; x --> M; S; E; E[x] *)

  | C_var:
    c:config{is_E_var (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (Exp (E_value ((Conf.en c) (pe_var c))) (pe_info c))}
    -> cstep c c'

  (* M; S; E; let x = e1 in e2 --> M; (M; E; let x = <> in e2)::S; E; e1  *)

  | C_let_e1:
    c:config{is_E_let (Exp.e (Conf.e c)) /\ not (is_reduced c)}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_let (MkTuple3._1 (pe_let c))
                                                (MkTuple3._3 (pe_let c))))
                                  (Conf.s c)
                           )
                           (Conf.en c) (MkTuple3._2 (pe_let c))}
    -> cstep c c'

  (* M; S; E; fun x -> e --> M; S; E; clos(E, fun x -> e) *)

  | C_abs:
    c:config{is_E_abs (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (Exp (E_value (V_clos (Conf.en c)
                                                 (fst (pe_abs c))
                                                 (snd (pe_abs c))
                                 )) (Exp.info (Conf.e c)))}
    -> cstep c c'

  (* M; S; E; e1 e2 --> M; (M; E; <> e2)::s; E; e1 *)

  | C_app_e1:
    c:config{is_E_app (Exp.e (Conf.e c)) /\ not (is_reduced c)}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add  (Frame (Conf.m c) (Conf.en c)
                                          (F_app_e1 (snd (pe_app c))))
                                   (Conf.s c)
                           )
                           (Conf.en c) (fst (pe_app c))}
    -> cstep c c'

  (* M; (M'; E'; aspar <> do e)::S; E; v --> M'; (M'; E'; aspar v do <>)::s; E'; e *)

  | C_aspar_e:
    c:config{is_value c /\ is_sframe c is_F_aspar_ps}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_aspar_e (pe_value c)))
                                                   (Conf.s c))
                           (pop_env c) (pf_aspar_ps c)}
    -> cstep c c'
  
  (* M; (M'; E'; box <> e)::S; E; v --> M'; (M'; E'; box v <>)::S; E'; e *)
  
  | C_box_e:
    c:config{is_value c /\ is_sframe c is_F_box_ps}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_box_e (pe_value c)))
                                                   (Conf.s c))
                           (pop_env c) (pf_box_ps c)}
    -> cstep c c'

  (* M; (M'; E'; <> e)::S; E; v --> M'; (M'; E'; v <>)::S; E'; e *)

  | C_app_e2:
    c:config{is_value c /\ is_sframe c is_F_app_e1}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_app_e2 (pe_value c)))
                                                   (Conf.s c))
                           (pop_env c) (pf_app_e1 c)}
    -> cstep c c'
  
  (* _; (M'; E'; aspar v1 do <>))::S; _; v2 --> M'; S; E'; aspar v1 do v2  *)  
  
  | C_aspar_rec:
    c:config{is_value c /\ is_sframe c is_F_aspar_e}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (e_aspar (e_value (pf_aspar_e c))
                                    (e_value (pe_value c)))}
    -> cstep c c'

  (* _; (M'; E'; box v1 <>))::S; _; v2 --> M'; S; E'; box v1 v2  *)
  
  | C_box_rec:
    c:config{is_value c /\ is_sframe c is_F_box_e}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (e_box (e_value (pf_box_e c))
                                  (e_value (pe_value c)))}
    -> cstep c c'

  (* _; (M; E; unbox <>)::S; _; v --> M; S; E; unbox v*)

  | C_unbox_rec:
    c:config{is_value c /\ is_sframe c is_F_unbox}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (e_unbox (e_value (pe_value c)))}
    -> cstep c c'
    
  (* _; (M; E; let x = <> in e)::S; _; v --> M; S; E; let x = v in e  *)

  | C_let_rec:
    c:config{is_value c /\ is_sframe c is_F_let}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (e_let (fst (pf_let c)) (e_value (pe_value c))
                                  (snd (pf_let c)))}
    -> cstep c c'

  (* _; (M; E; v1 <>)::S; _; v2 --> M; S; E; v1 v2 *)
  | C_app_rec:
    c:config{is_value c /\ is_sframe c is_F_app_e2}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (e_app (e_value (pf_app_e2 c))
                                  (e_value (pe_value c)))}
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
  
  
  (* M; S; _; aspar ps do clos(E, fun x -> e) (when sub M.ps ps)
     -->
     M; (M; E; Box ps <>)::S; E[x -> ()]; e
  *)
  
  | T_aspar_do:
    c:tconfig{pre_aspar c Tgt = Do} -> c':tconfig{c' = step_aspar c Tgt}
    -> tstep c c'

  (* M; S; E; aspar ps do _ (when not sub M.ps ps)
     -->
     M; S; E; empty_box
  *)
  
  | T_aspar_dont:
    c:tconfig{pre_aspar c Tgt = Skip}
    -> c':tconfig{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c) (e_value V_empbox)}
    -> tstep c c'

  (* M; S; E; Box ps v (when sub M.ps ps )
     -->
     M; S; E; V_box ps v
  *)

  | T_box_do:
    c:tconfig{pre_box c Tgt = Do} -> c':tconfig{c' = step_box c Tgt}
    -> tstep c c'

  (* M; S; E; Box ps v (when sub M.ps ps )
     -->
     M; S; E; V_box ps v
  *)
    
  | T_box_dont:
    c:tconfig{pre_box c Tgt = Skip}
    -> c':tconfig{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c) (e_value V_empbox)}
    -> tstep c c'

  (* M; S; E; unbox (Box ps v) (when sub M.ps ps)
     -->
     M; S; E; v
  *)
  
  | T_unbox:
    c:tconfig{pre_unbox c Tgt = Do} -> c':tconfig{c' = step_unbox c Tgt}
    -> tstep c c'

(**********)

assume val preceds_axiom: en:env -> x:varname -> Lemma (ensures (en x << en))

val slice_v : prin -> v:value -> Tot value
let rec slice_v p v =
  match v with
    | V_box ps v'   -> if mem p ps then V_box ps (slice_v p v') else V_empbox
    | V_clos en x e -> V_clos (fun y -> preceds_axiom en y; slice_v p (en y)) x e
    | _             -> v

val slice_en: prin -> en:env -> Tot env
let slice_en p en = fun x -> slice_v p (en x)

(* only expressions with values need to be sliced *)
val slice_e: prin -> exp -> Tot exp
let slice_e p e =
  if not (is_reduced_e e) then e
  else
    match Exp.e e with
      | E_aspar (Exp (E_value v1) _) (Exp (E_value v2) _) ->
        e_aspar (e_value (slice_v p v1)) (e_value (slice_v p v2))
      (*| E_assec (Exp (E_value v1) _) (Exp (E_value v2) _) ->
        e_assec (e_value (slice_v p v1)) (e_value (slice_v p v2))*)
      | E_box (Exp (E_value v1) _) (Exp (E_value v2) _) ->
        e_box (e_value (slice_v p v1)) (e_value (slice_v p v2))
      | E_app (Exp (E_value v1) _) (Exp (E_value v2) _) ->
        e_app (e_value (slice_v p v1)) (e_value (slice_v p v2))
      | E_unbox (Exp (E_value v) _) ->
        e_unbox (e_value (slice_v p v))
      | E_let x (Exp (E_value v1) _) e2 ->
        e_let x (e_value (slice_v p v1)) e2
      | E_value v ->
        e_value (slice_v p v)


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

val pop_absent_frames: prin -> stack -> Tot stack
let rec pop_absent_frames p s = match s with
  | []     -> []
  | hd::tl ->
    if mem p (Mode.ps (Frame.m hd)) then s else pop_absent_frames p tl

val pop_absent_frames_lem: p:prin -> s:stack
                           -> Lemma (requires (True))
                                    (ensures  (forall f. List.mem f (pop_absent_frames p s) ==>
                                                         mem p (Mode.ps (Frame.m f))))
let rec pop_absent_frames_lem p s = match s with
  | []        -> ()
  | _::[]     -> ()
  | f::f'::tl ->
    if mem p (Mode.ps (Frame.m f)) then
      let _ = mem_subset p (Mode.ps (Frame.m f)) (Mode.ps (Frame.m f')) in
      pop_absent_frames_lem p (f'::tl)
    else
      pop_absent_frames_lem p (f'::tl)

val slice_s: p:prin -> stack -> Tot (s:stack{forall f. List.mem f s ==> Mode.ps (Frame.m f) = singleton p})
let rec slice_s p s =
  let s':stack = pop_absent_frames p s in
  pop_absent_frames_lem p s;
  match s' with
    | []     -> []
    | hd::tl ->
      let s' = slice_s p tl in
      let _ = assert (forall f. List.mem f s' ==> Mode.ps (Frame.m f) = singleton p) in
      admit ()
      (slice_f p hd)::(slice_s p tl)

val slice_c: prin -> config -> Tot tconfig
let rec slice_c p (Conf (Mode Par ps) s en e) =
  let en', e' =
    if mem p ps then slice_en p en, slice_e p e
    else empty_env, e_value (V_empbox)
  in

  Conf (Mode Par (singleton p)) (slice_s p s) en' e'

(**********)
(*
type z_or_one_tstep: tconfig -> tconfig -> Type =
  | ZT_refl: c:tconfig -> z_or_one_tstep c c
  | ZT_step: c:tconfig -> c':tconfig -> h:tstep c c'
             -> z_or_one_tstep c c'

val cstep_lemma: #c:config -> #c':config -> h:cstep c c' -> p:prin
                 -> Tot (z_or_one_tstep (slice_c p c) (slice_c p c'))
let c_step_lemma #c #c' h = match h with
  | C_aspar_ps c c' ->
    
  | _ -> admit ()*)
