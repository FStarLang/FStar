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
  | V_const: c:const -> value

  | V_box  : ps:prins -> v:value -> value

  | V_clos : en:env -> x:varname -> e:exp -> value

(* TODO: fix it, option value *)
and env = varname -> Tot value

assume val empty_env: env

val to_exp: exp' -> Tot exp
let to_exp e = Exp e None

val update_env: env -> varname -> value -> Tot env
let update_env en x v = fun y -> if y = x then v else en y

type as_mode =
  | Par
  | Sec

type mode =
  | Mode: m:as_mode -> ps:prins -> mode

type frame' =
  | F_aspar_ps   : e:exp -> frame'
  | F_aspar_e    : v:value -> frame'
  | F_assec_ps   : e:exp -> frame'
  | F_assec_e    : v:value -> frame'
  | F_box_ps     : e:exp -> frame'
  | F_box_e      : v:value -> frame'
  | F_unbox      : frame'
  | F_let        : x:varname -> e2:exp -> frame'
  | F_app_e1     : e2:exp -> frame'
  | F_app_e2     : v:value -> frame'
  
type frame =
  | Frame: m:mode -> en:env -> f:frame' -> frame
  
type stack = list frame

type config =
  | Conf: m:mode -> s:stack -> en:env -> e:exp -> config

val s_add: frame -> stack -> Tot stack
let s_add = Cons

val s_replace: frame -> s:stack{is_Cons s} -> Tot stack
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

val is_beta: c:config -> Tot bool
let is_beta (Conf _ _ _ (Exp e _)) =
  match e with
    | E_aspar e1 e2
    | E_assec e1 e2
    | E_box   e1 e2
    | E_app   e1 e2 -> is_value_e e1 && is_value_e e2
    | E_unbox e
    | E_let _ e _   -> is_value_e e
    
    | _             -> false

val pf_aspar_ps: c:config{is_sframe c is_F_aspar_ps} -> Tot exp
let pf_aspar_ps (Conf _ ((Frame _ _ (F_aspar_ps e))::_) _ _) = e

val pf_assec_ps: c:config{is_sframe c is_F_assec_ps} -> Tot exp
let pf_assec_ps (Conf _ ((Frame _ _ (F_assec_ps e))::_) _ _) = e

val pf_let: c:config{is_sframe c is_F_let} -> Tot (varname * exp)
let pf_let (Conf _ ((Frame _ _ (F_let x e2))::_) _ _) = x, e2

val pf_app_e1: c:config{is_sframe c is_F_app_e1} -> Tot exp
let pf_app_e1 (Conf _ ((Frame _ _ (F_app_e1 e2))::_) _ _) = e2

val pf_aspar_e: c:config{is_sframe c is_F_aspar_e} -> Tot value
let pf_aspar_e (Conf _ ((Frame _ _ (F_aspar_e v))::_) _ _) = v

val pf_assec_e: c:config{is_sframe c is_F_assec_e} -> Tot value
let pf_assec_e (Conf _ ((Frame _ _ (F_assec_e v))::_) _ _) = v

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

val pe_assec: c:config{is_E_assec (Exp.e (Conf.e c))} -> Tot (exp * exp)
let pe_assec (Conf _ _ _ (Exp (E_assec e1 e2) _)) = e1, e2

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

val e_assec: exp -> exp -> Tot exp
let e_assec ps e = Exp (E_assec ps e) None

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

val pre_aspar: c:config -> Tot bool
let pre_aspar c = match c with
  | Conf (Mode Par ps1) _ _
         (Exp (E_aspar (Exp (E_value (V_const (C_prins ps2))) _)
                       (Exp (E_value (V_clos _ _ _)) _)) _)
         
         -> subset ps2 ps1
  
  | _ -> false
  
val pe_aspar_beta: c:config{pre_aspar c} -> Tot (Tuple4 prins env varname exp)
let pe_aspar_beta c = match c with
  | Conf _ _ _
         (Exp (E_aspar (Exp (E_value (V_const (C_prins ps))) _)
                       (Exp (E_value (V_clos en x e)) _)) _)
         
         -> MkTuple4 ps en x e

val pre_assec: c:config -> Tot bool
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
        
        -> MkTuple4 ps en x e

val pre_box: c:config -> Tot bool
let pre_box c = match c with
  | Conf (Mode Par ps1) _ _
         (Exp (E_box (Exp (E_value (V_const (C_prins ps2))) _)
                     (Exp (E_value _) _)) _)
                     
         -> subset ps2 ps1
  | _ -> false

val pe_box_beta: c:config{pre_box c} -> Tot (prins * value)
let pe_box_beta c = match c with
  | Conf _ _ _
         (Exp (E_box (Exp (E_value (V_const (C_prins ps))) _)
                     (Exp (E_value v) _)) _)
                     
         -> ps, v

val pre_unbox: c:config -> Tot bool
let pre_unbox c = match c with
  | Conf (Mode as_m ps1) _ _
         (Exp (E_unbox (Exp (E_value (V_box ps2 _)) _)) _)
         
         -> if as_m = Par then subset ps1 ps2 else subset ps2 ps1
         
  | _ -> false

val pe_unbox_beta: c:config{pre_unbox c} -> Tot (prins * value)
let pe_unbox_beta c = match c with
  | Conf _ _ _
         (Exp (E_unbox (Exp (E_value (V_box ps2 v)) _)) _)
         
         -> ps2, v

val pe_let_beta: c:config{is_E_let (Exp.e (Conf.e c)) /\ is_beta c}
                 -> Tot (Tuple3 varname value exp)
let pe_let_beta c = match c with
  | Conf _ _ _
         (Exp (E_let varname (Exp (E_value v1) _) e2) _)
         
         -> MkTuple3 varname v1 e2

val pre_app: c:config -> Tot bool
let pre_app c = match c with
  | Conf _ _ _
         (Exp (E_app (Exp (E_value (V_clos _ _ _)) _)
                     (Exp (E_value _) _)) _)
         -> true
  
  | _ -> false
  
val pe_app_beta: c:config{pre_app c} -> Tot (Tuple4 env varname exp value)
let pe_app_beta c = match c with
| Conf _ _ _
      (Exp (E_app (Exp (E_value (V_clos en x e)) _)
                  (Exp (E_value v) _)) _)
      -> MkTuple4 en x e v

(* M; S; E; e --> M'; S'; E'; e' *)
type step: config -> config -> Type =

  (* M; S; E; aspar e1 do e2 --> M; (M; E; aspar <> do e2)::S; E; e1*)
  
  | S_aspar_ps:
    c:config{is_E_aspar (Exp.e (Conf.e c)) /\ not (is_beta c)}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_aspar_ps (snd (pe_aspar c))))
                                  (Conf.s c))
                           (Conf.en c) (fst (pe_aspar c))}
    -> step c c'

  (* M; S; E; assec e1 do e2 --> M; (M; E; assec <> do e2)::S; E; e1 *)

  | S_assec_ps:
    c:config{is_E_assec (Exp.e (Conf.e c)) /\ not (is_beta c)}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_assec_ps (snd (pe_assec c))))
                                  (Conf.s c))
                           (Conf.en c) (fst (pe_assec c))}
    -> step c c'
    
  (* M; S; E; box e1 e2 --> M; (M; E; box <> e2)::S; E; e1 *)

  | S_box_ps:
    c:config{is_E_box (Exp.e (Conf.e c)) /\ not (is_beta c)}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_box_ps (snd (pe_box c))))
                                  (Conf.s c))
                           (Conf.en c) (fst (pe_box c))}

    -> step c c'

  (* M; S; E; unbox e --> M; (M; E; unbox <>)::S; E; e *)

  | S_unbox:
    c:config{is_E_unbox (Exp.e (Conf.e c)) /\ not (is_beta c)}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c) F_unbox)
                                  (Conf.s c))
                           (Conf.en c) (pe_unbox c)}
    -> step c c'

  (* M; S; E; c --> M; S; E; c *)

  | S_const:
    c:config{is_E_const (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (Exp (E_value (V_const (pe_const c))) (pe_info c))}
    -> step c c'

  (* M; S; E; x --> M; S; E; E[x] *)

  | S_var:
    c:config{is_E_var (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (Exp (E_value ((Conf.en c) (pe_var c))) (pe_info c))}
    -> step c c'

  (* M; S; E; let x = e1 in e2 --> M; (M; E; let x = <> in e2)::S; E; e1  *)

  | S_let_e1:
    c:config{is_E_let (Exp.e (Conf.e c)) /\ not (is_beta c)}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add (Frame (Conf.m c) (Conf.en c)
                                         (F_let (MkTuple3._1 (pe_let c))
                                                (MkTuple3._3 (pe_let c))))
                                  (Conf.s c)
                           )
                           (Conf.en c) (MkTuple3._2 (pe_let c))}
    -> step c c'

  (* M; S; E; fun x -> e --> M; S; E; clos(E, fun x -> e) *)

  | S_abs:
    c:config{is_E_abs (Exp.e (Conf.e c))}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (Exp (E_value (V_clos (Conf.en c)
                                                 (fst (pe_abs c))
                                                 (snd (pe_abs c))
                                 )) (Exp.info (Conf.e c)))}
    -> step c c'

  (* M; S; E; e1 e2 --> M; (M; E; <> e2)::s; E; e1 *)

  | S_app_e1:
    c:config{is_E_app (Exp.e (Conf.e c)) /\ not (is_beta c)}
    -> c':config{c' = Conf (Conf.m c)
                           (s_add  (Frame (Conf.m c) (Conf.en c)
                                          (F_app_e1 (snd (pe_app c))))
                                   (Conf.s c)
                           )
                           (Conf.en c) (fst (pe_app c))}
    -> step c c'

  (* M; (M'; E'; aspar <> do e)::S; E; v --> M'; (M'; E'; aspar v do <>)::s; E'; e *)

  | S_aspar_e:
    c:config{is_value c /\ is_sframe c is_F_aspar_ps}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_aspar_e (pe_value c)))
                                                   (Conf.s c))
                           (pop_env c) (pf_aspar_ps c)}
    -> step c c'

  (* M; (M'; E'; assec <> do e)::S; E; v --> M'; (M'; E'; assec v do <>)::s; E'; e *)

  | S_assec_e:
    c:config{is_value c /\ is_sframe c is_F_assec_ps}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_assec_e (pe_value c)))
                                                   (Conf.s c))
                           (pop_env c) (pf_assec_ps c)}
    -> step c c'

  (* M; (M'; E'; box <> e)::S; E; v --> M'; (M'; E'; box v <>)::S; E'; e *)
  
  | S_box_e:
    c:config{is_value c /\ is_sframe c is_F_box_ps}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_box_e (pe_value c)))
                                                   (Conf.s c))
                           (pop_env c) (pf_box_ps c)}
    -> step c c'

  (* M; (M'; E'; <> e)::S; E; v --> M'; (M'; E'; v <>)::S; E'; e *)

  | S_app_e2:
    c:config{is_value c /\ is_sframe c is_F_app_e1}
    -> c':config{c' = Conf (pop_mode c) (s_replace (Frame (pop_mode c) (pop_env c)
                                                          (F_app_e2 (pe_value c)))
                                                   (Conf.s c))
                           (pop_env c) (pf_app_e1 c)}
    -> step c c'
  
  (* _; (M'; E'; aspar v1 do <>))::S; _; v2 --> M'; S; E'; aspar v1 do v2  *)  
  
  | S_aspar_rec:
    c:config{is_value c /\ is_sframe c is_F_aspar_e}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (e_aspar (e_value (pf_aspar_e c))
                                    (e_value (pe_value c)))}
    -> step c c'

  (* _; (M'; E'; assec v1 do <>))::S; _; v2 --> M'; S; E'; assec v1 do v2  *)
  
  | S_assec_rec:
    c:config{is_value c /\ is_sframe c is_F_assec_e}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (e_assec (e_value (pf_assec_e c))
                                    (e_value (pe_value c)))}
    -> step c c'
    
  (* _; (M'; E'; box v1 <>))::S; _; v2 --> M'; S; E'; box v1 v2  *)
  
  | S_box_rec:
    c:config{is_value c /\ is_sframe c is_F_box_e}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (e_box (e_value (pf_box_e c))
                                  (e_value (pe_value c)))}
    -> step c c'

  (* _; (M; E; unbox <>)::S; _; v --> M; S; E; unbox v*)

  | S_unbox_rec:
    c:config{is_value c /\ is_sframe c is_F_unbox}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (e_unbox (e_value (pe_value c)))}
    -> step c c'
    
  (* _; (M; E; let x = <> in e)::S; _; v --> M; S; E; let x = v in e  *)

  | S_let_rec:
    c:config{is_value c /\ is_sframe c is_F_let}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (e_let (fst (pf_let c)) (e_value (pe_value c))
                                  (snd (pf_let c)))}
    -> step c c'

  (* _; (M; E; v1 <>)::S; _; v2 --> M; S; E; v1 v2 *)
  | S_app_rec:
    c:config{is_value c /\ is_sframe c is_F_app_e2}
    -> c':config{c' = Conf (pop_mode c) (s_pop c) (pop_env c)
                           (e_app (e_value (pf_app_e2 c))
                                  (e_value (pe_value c)))}
    -> step c c'                                

  (* M; S; _; aspar ps do clos(E, fun x -> e)  (when M is Par(ps1) /\ sub ps ps1
     -->
     Par(ps); (Par(ps); E; Box ps <>)::S; E[x -> ()]; e
  *)
  | S_aspar_beta:
    c:config{pre_aspar c}
    -> c':config{c' = Conf (Mode Par (MkTuple4._1 (pe_aspar_beta c)))
                           (s_add (Frame (Mode Par (MkTuple4._1 (pe_aspar_beta c)))
                                         empty_env
                                         (F_box_e (v_prins (MkTuple4._1 (pe_aspar_beta c)))))
                                  (Conf.s c))
                           (update_env (MkTuple4._2 (pe_aspar_beta c))
                                       (MkTuple4._3 (pe_aspar_beta c))
                                       (V_const C_unit))
                           (MkTuple4._4 (pe_aspar_beta c))}
    -> step c c'

  (* M; S; _; assec ps do clos(E, fun x -> e)  (when ps = M.ps)
     -->
     Sec(ps); S; E[x -> ()]; e
  *)
  | S_assec_beta:
    c:config{pre_assec c}
    -> c':config{c' = Conf (Mode Sec (MkTuple4._1 (pe_assec_beta c))) (Conf.s c)
                           (update_env (MkTuple4._2 (pe_assec_beta c))
                                       (MkTuple4._3 (pe_assec_beta c))
                                       (V_const C_unit))
                           (MkTuple4._4 (pe_assec_beta c))}
    -> step c c'

  (* M; S; E; box ps v (when is_Par M /\ sub ps M.ps)
     -->
     M; S; E; Box ps v
  *)

  | S_box_beta:
    c:config{pre_box c}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (e_value (V_box (fst (pe_box_beta c))
                                           (snd (pe_box_beta c))))}
    -> step c c'

  (* M; S; E; unbox (Box ps v) (when isPar M ==> sub M.ps ps /\
                                     isSec M ==> sub ps M.ps)
     -->
     M; S; E; v                                   
  *)
  | S_unbox_beta:
    c:config{pre_unbox c}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c) (Conf.en c)
                           (e_value (snd (pe_unbox_beta c)))}
    -> step c c'

  (* M; S; E; let x = v1 in e2 --> M; S; E[x -> v]; e2 *)
  
  | S_let_beta:
    c:config{is_E_let (Exp.e (Conf.e c)) /\ is_beta c}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c)
                           (update_env (Conf.en c)
                                       (MkTuple3._1 (pe_let_beta c))
                                       (MkTuple3._2 (pe_let_beta c)))
                           (MkTuple3._3 (pe_let_beta c))}
    -> step c c'

  (* M; S; _; (E, fun x -> e) v --> M; S; E[x -> v]; e *)
  | S_app_beta:
    c:config{pre_app c}
    -> c':config{c' = Conf (Conf.m c) (Conf.s c)
                           (update_env (MkTuple4._1 (pe_app_beta c))
                                       (MkTuple4._2 (pe_app_beta c))
                                       (MkTuple4._4 (pe_app_beta c)))
                           (MkTuple4._3 (pe_app_beta c))}
    -> step c c'
