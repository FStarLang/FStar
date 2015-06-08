(*--build-config
    options:--admit_fsi OrdSet;
    variables:LIB=../../lib;
    other-files:$LIB/ordset.fsi
 --*)

module AST

open OrdSet

type other_info = nat

type varname = string

type prin = nat

val p_cmp: prin -> prin -> Tot bool
let p_cmp p1 p2 = p1 <= p2

type prins = ordset prin p_cmp

val subset: prins -> prins -> Tot bool
let subset = OrdSet.subset p_cmp

type const =
  | C_prin : c:prin -> const
  | C_prins: c:prins -> const

  | C_unit : const
  | C_nat  : c:nat -> const
  | C_bool : c:bool -> const

type exp' =
  | E_aspar: ps:exp -> e:exp -> exp'
  | E_assec: ps:exp -> e:exp -> exp'
  | E_unbox: e:exp -> exp'

  | E_const: c:const -> exp'
  | E_var  : x:varname -> exp'
  | E_let  : x:varname -> e1:exp -> e2:exp -> exp'
  | E_abs  : x:varname -> e:exp -> exp'
  | E_app  : e1:exp -> e2:exp -> exp'
    
  | E_value: v:value' -> exp' (* E_value only come up during evaluation *)

and exp =
  | Exp: e:exp' -> info:option other_info -> exp

and value' =
  | V_const: c:const -> value'

  | V_box  : ps:prins -> v:value' -> value'

  | V_clos : en:env -> x:varname -> e:exp -> value'

and value = (* values are created during evaluation, no values in the source *)
  | Mk_value: v:value' -> info:option other_info -> value

and env = varname -> Tot value'

val update_env: env -> varname -> value' -> Tot env
let update_env en x v = fun y -> if y = x then v else en y

type as_mode =
  | Par
  | Sec

type mode =
  | Mode: m:as_mode -> ps:prins -> mode

type frame' =
  | F_aspar_ps: e:exp -> frame'
  | F_aspar_e : v:value' -> frame'
  | F_assec_ps: e:exp -> frame'
  | F_assec_e : v:value' -> frame'
  | F_unbox   : frame'
  | F_let     : x:varname -> e2:exp -> frame'
  | F_app_e1  : e2:exp -> frame'
  | F_app_e2  : v:value' -> frame'
  
  | F_box     : ps:prins -> frame'
  
type frame =
  | Frame: m:mode -> en:env -> f:frame' -> frame
  
type stack = list frame

val s_add: frame -> stack -> Tot stack
let s_add = Cons

val s_replace: frame -> s:stack{is_Cons s} -> Tot stack
let s_replace f s = s_add f (Cons.tl s)

type config =
  | Conf: m:mode -> s:stack -> en:env -> e:exp -> config

val s_pop: c:config{is_Cons (Conf.s c)} -> Tot stack
let s_pop c = Cons.tl (Conf.s c)

val is_sframe: c:config -> f:(frame' -> Tot bool) -> Tot bool
let is_sframe (Conf _ s _ _) f = is_Cons s && f (Frame.f (Cons.hd s))

val pop_mode: c:config{is_Cons (Conf.s c)} -> Tot mode
let pop_mode (Conf _ (fr::_) _ _) = Frame.m fr

val pop_env: c:config{is_Cons (Conf.s c)} -> Tot env
let pop_env (Conf _ (fr::_) _ _) = Frame.en fr

val is_value: c:config -> Tot bool
let is_value c = is_E_value (Exp.e (Conf.e c))

val f_aspar_ps: c:config{is_sframe c is_F_aspar_ps} -> Tot exp
let f_aspar_ps (Conf _ ((Frame _ _ (F_aspar_ps e))::_) _ _) = e

val f_assec_ps: c:config{is_sframe c is_F_assec_ps} -> Tot exp
let f_assec_ps (Conf _ ((Frame _ _ (F_assec_ps e))::_) _ _) = e

val f_let: c:config{is_sframe c is_F_let} -> Tot (varname * exp)
let f_let (Conf _ ((Frame _ _ (F_let x e2))::_) _ _) = x, e2

val f_app_e1: c:config{is_sframe c is_F_app_e1} -> Tot exp
let f_app_e1 (Conf _ ((Frame _ _ (F_app_e1 e2))::_) _ _) = e2

val f_aspar_e: c:config{is_sframe c is_F_aspar_e} -> Tot value'
let f_aspar_e (Conf _ ((Frame _ _ (F_aspar_e v))::_) _ _) = v

val f_assec_e: c:config{is_sframe c is_F_assec_e} -> Tot value'
let f_assec_e (Conf _ ((Frame _ _ (F_assec_e v))::_) _ _) = v

val f_app_e2: c:config{is_sframe c is_F_app_e2} -> Tot value'
let f_app_e2 (Conf _ ((Frame _ _ (F_app_e2 v))::_) _ _) = v

val f_box: c:config{is_sframe c is_F_box} -> Tot prins
let f_box (Conf _ ((Frame _ _ (F_box ps))::_) _ _) = ps

val e_value: c:config{is_E_value (Exp.e (Conf.e c))} -> Tot value'
let e_value (Conf _ _ _ (Exp (E_value v) _)) = v

val e_info: c:config -> Tot (option other_info)
let e_info (Conf _ _ _ (Exp _ inf)) = inf

val e_app: c:config{is_E_app (Exp.e (Conf.e c))} -> Tot (exp * exp)
let e_app (Conf _ _ _ (Exp (E_app e1 e2) _)) = (e1, e2)

val e_abs: c:config{is_E_abs (Exp.e (Conf.e c))} -> Tot (varname * exp)
let e_abs (Conf _ _ _ (Exp (E_abs x e) _)) = (x, e)

val e_let: c:config{is_E_let (Exp.e (Conf.e c))} -> Tot (Tuple3 varname exp exp)
let e_let (Conf _ _ _ (Exp (E_let x e1 e2) _)) = MkTuple3 x e1 e2

val e_var: c:config{is_E_var (Exp.e (Conf.e c))} -> Tot varname
let e_var (Conf _ _ _ (Exp (E_var x) _)) = x

val e_const: c:config{is_E_const (Exp.e (Conf.e c))} -> Tot const
let e_const (Conf _ _ _ (Exp (E_const c) _)) = c

val e_unbox: c:config{is_E_unbox (Exp.e (Conf.e c))} -> Tot exp
let e_unbox (Conf _ _ _ (Exp (E_unbox e) _)) = e

val e_aspar: c:config{is_E_aspar (Exp.e (Conf.e c))} -> Tot (exp * exp)
let e_aspar (Conf _ _ _ (Exp (E_aspar e1 e2) _)) = e1, e2

val e_assec: c:config{is_E_assec (Exp.e (Conf.e c))} -> Tot (exp * exp)
let e_assec (Conf _ _ _ (Exp (E_assec e1 e2) _)) = e1, e2

val v_prin: v:value'{is_V_const v /\ is_C_prin (V_const.c v)} -> Tot prin
let v_prin (V_const (C_prin p)) = p

val v_prins: v:value'{is_V_const v /\ is_C_prins (V_const.c v)} -> Tot prins
let v_prins (V_const (C_prins ps)) = ps

val v_nat: v:value'{is_V_const v /\ is_C_nat (V_const.c v)} -> Tot nat
let v_nat (V_const (C_nat n)) = n

val v_bool: v:value'{is_V_const v /\ is_C_bool (V_const.c v)} -> Tot bool
let v_bool (V_const (C_bool b)) = b

val v_box: v:value'{is_V_box v} -> Tot (prins * value')
let v_box (V_box ps v) = ps, v

val v_clos: v:value'{is_V_clos v} -> Tot (Tuple3 env varname exp)
let v_clos (V_clos en x e) = MkTuple3 en x e

val pre_aspar: c:config -> Tot bool
let pre_aspar c = match c with
  | Conf _ (Cons (Frame (Mode Par ps1) _
                        (F_aspar_e (V_const (C_prins ps2)))) _)
         _ (Exp (E_value (V_clos _ _ _)) _)
         
         -> subset ps2 ps1
  
  | _ -> false

val pre_assec: c:config -> Tot bool
let pre_assec c = match c with
  | Conf _ (Cons (Frame (Mode Par ps1) _
                        (F_assec_e (V_const (C_prins ps2)))) _)
         _ (Exp (E_value (V_clos _ _ _)) _)
         
         -> ps2 = ps1
  
  | _ -> false

val pre_unbox: c:config -> Tot bool
let pre_unbox c = match c with
  | Conf _ (Cons (Frame (Mode as_m ps1) _ F_unbox) _)
         _ (Exp (E_value (V_box ps2 _)) _)
         
         -> if as_m = Par then subset ps1 ps2 else subset ps2 ps1
         
  | _ -> false
  
val pre_app: c:config -> Tot bool
let pre_app c = match c with
  | Conf _ (Cons (Frame _ _ (F_app_e2 (V_clos _ _ _))) _)
         _ (Exp (E_value _) _)
         
         -> true
  
  | _ -> false

(* M; S; E; e --> M'; S'; E'; e' *)
type step: config -> config -> Type =

  (* M; S; E; aspar e1 do e2 --> M; (M; E; aspar <> do e2)::S; E; e1*)
  
  | S_aspar_ps:
    c:config{is_E_aspar (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_aspar_ps (snd (e_aspar c))))
                                  (Conf.s c))
                           (Conf.en c) (fst (e_aspar c))}
    -> step c c'

  (* M; S; E; assec e1 do e2 --> M; (M; E; assec <> do e2)::S; E; e1 *)

  | S_assec_ps:
    c:config{is_E_assec (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_assec_ps (snd (e_assec c))))
                                  (Conf.s c))
                           (Conf.en c) (fst (e_assec c))}
    -> step c c'

  (* M; S; E; unbox e --> M; (M; E; unbox <>)::S; E; e *)

  | S_unbox:
    c:config{is_E_unbox (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c) F_unbox)
                                  (Conf.s c))
                           (Conf.en c) (e_unbox c)}
    -> step c c'

  (* M; S; E; c --> M; S; E; c *)

  | S_const:
    c:config{is_E_const (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (Exp (E_value (V_const (e_const c))) (e_info c))}
    -> step c c'

  (* M; S; E; x --> M; S; E; E[x] *)

  | S_var:
    c:config{is_E_var (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (Exp (E_value ((Conf.en c) (e_var c))) (e_info c))}
    -> step c c'

  (* M; S; E; let x = e1 in e2 --> M; (M; E; let x = <> in e2)::S; E; e1  *)

  | S_let_e1:
    c:config{is_E_let (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_let (MkTuple3._1 (e_let c))
                                                (MkTuple3._3 (e_let c))))
                                  (Conf.s c)
                           )
                           (Conf.en c) (MkTuple3._2 (e_let c))}
    -> step c c'

  (* M; S; E; fun x -> e --> M; S; E; clos(E, fun x -> e) *)

  | S_abs:
    c:config{is_E_abs (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (Exp (E_value (V_clos (Conf.en c)
                                                 (fst (e_abs c))
                                                 (snd (e_abs c))
                                 )) (Exp.info (Conf.e c)))}
    -> step c c'

  (* M; S; E; e1 e2 --> M; (M; E; <> e2)::s; E; e1 *)

  | S_app_e1:
    c:config{is_E_app (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add  (Frame (Conf.m c) (Conf.en c)
                                          (F_app_e1 (snd (e_app c))))
                                   (Conf.s c)
                           )
                           (Conf.en c) (fst (e_app c))}
    -> step c c'

  (* M; (M'; E'; aspar <> do e)::S; E; v --> M'; (M'; E'; aspar v do <>)::s; E'; e *)

  | S_aspar_e:
    c:config{is_value c /\ is_sframe c is_F_aspar_ps}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_aspar_e (e_value c)))
                                                   (Conf.s c))
                           (pop_env c) (f_aspar_ps c)}
    -> step c c'

  (* M; (M'; E'; assec <> do e)::S; E; v --> M'; (M'; E'; assec v do <>)::s; E'; e *)

  | S_assec_e:
    c:config{is_value c /\ is_sframe c is_F_assec_ps}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_assec_e (e_value c)))
                                                   (Conf.s c))
                           (pop_env c) (f_assec_ps c)}
    -> step c c'
  
  (* M; (M'; E'; <> e); E; v --> M'; (M'; E'; v <>)::s; E'; e *)

  | S_app_e2:
    c:config{is_value c /\ is_sframe c is_F_app_e1}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_app_e2 (e_value c)))
                                                   (Conf.s c))
                           (pop_env c) (f_app_e1 c)}
    -> step c c'
  
  (* _; (Par(ps1); _; aspar ps2 do <>)::s; _; (E, fun x -> e)  (when subset ps2 ps1)
    -->
    Par(ps2); (Par(ps2); E; Box ps2 <>)::s; E[x -> ()]; e 
  *)

  | S_aspar_beta:
    c:config{pre_aspar c}
    -> c':config{c' = Conf (Mode Par (v_prins (f_aspar_e c)))
                           (s_replace (Frame (Mode Par (v_prins (f_aspar_e c)))
                                             (MkTuple3._1 (v_clos (e_value c)))
                                             (F_box (v_prins (f_aspar_e c))))
                                      (Conf.s c))
                           (update_env (MkTuple3._1 (v_clos (e_value c)))
                                       (MkTuple3._2 (v_clos (e_value c))) (V_const C_unit))
                           (MkTuple3._3 (v_clos (e_value c)))}
    -> step c c'

  (* _; (Par(ps1); _; assec ps2 do <>)::s; _; (E, fun x -> e)  (when ps2 = ps1)
    -->
    Sec(ps2); s; E[x -> ()]; e 
  *)
    
  | S_assec_beta:
    c:config{pre_assec c}
    -> c':config{c' = Conf (Mode Sec (v_prins (f_assec_e c)))
                           (s_pop c)
                           (update_env (MkTuple3._1 (v_clos (e_value c)))
                                       (MkTuple3._2 (v_clos (e_value c))) (V_const C_unit))
                           (MkTuple3._3 (v_clos (e_value c)))}
    -> step c c'

  (* _; (M; E; unbox <>)::s; _; Box ps v  (when isPar M ==> subset M.ps ps /\
                                                isSec M ==> subset ps M.ps)
     -->
     M; s; E; v                                                    
  *)

  | S_unbox_beta:
    c:config{pre_unbox c}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (Exp (E_value (snd (v_box (e_value c)))) (e_info c))}
    -> step c c'

  (* M; (M'; E'; let x = <> in e2)::s; E; v --> M'; s; E'[x -> v]; e2 *)

  | S_let_beta:
    c:config{is_value c /\ is_sframe c is_F_let}
    -> c':config{c' = Conf (pop_mode c) (s_pop c)
                           (update_env (pop_env c) (fst (f_let c)) (e_value c))
                           (snd (f_let c))}
    -> step c c'

  (* _; (M; _; (E', fun x -> e) <>)::s; _; v --> M; s; E'[x -> v]; e *)

  | S_app_beta:
    c:config{pre_app c}
    -> c':config{c' = Conf (pop_mode c) (s_pop c)
                           (update_env (MkTuple3._1 (v_clos (f_app_e2 c)))
                                       (MkTuple3._2 (v_clos (f_app_e2 c)))
                                       (e_value c))
                           (MkTuple3._3 (v_clos (f_app_e2 c)))}
    -> step c c'
  
  (* _; (M; E; Box ps <>)::s; _; v --> M; s; E; Box ps v *)

  | S_box_beta:
    c:config{is_value c /\ is_sframe c is_F_box}
    -> c':config{c'= Conf (pop_mode c) (s_pop c) (pop_env c)
                          (Exp (E_value (V_box (f_box c) (e_value c)))
                               (e_info c))}
    -> step c c'
