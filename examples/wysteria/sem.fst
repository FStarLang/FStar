(*--build-config
    options:--admit_fsi OrdSet --admit_fsi OrdMap;
    variables:LIB=../../lib;
    other-files:$LIB/ordset.fsi $LIB/ordmap.fsi $LIB/list.fst $LIB/classical.fst ast.fst
 --*)

module Semantics

open OrdMap
open OrdSet

open AST

let pre_easpar (c:config) =
 is_T_exp (Conf.t c) && is_E_aspar (Exp.e (T_exp.e (Conf.t c))) && is_par c

let pre_eapp (c:config) =
 is_T_exp (Conf.t c) && is_E_app (Exp.e (T_exp.e (Conf.t c)))

let pre_eabs (c:config) =
 is_T_exp (Conf.t c) && is_E_abs (Exp.e (T_exp.e (Conf.t c)))
 
let pre_efix (c:config) =
 is_T_exp (Conf.t c) && is_E_fix (Exp.e (T_exp.e (Conf.t c)))

let pre_eempabs (c:config) =
 is_T_exp (Conf.t c) && is_E_empabs (Exp.e (T_exp.e (Conf.t c)))

let pre_elet (c:config) =
 is_T_exp (Conf.t c) && is_E_let (Exp.e (T_exp.e (Conf.t c)))

let pre_evar (c:config) =
 is_T_exp (Conf.t c) && is_E_var (Exp.e (T_exp.e (Conf.t c))) &&
 is_Some ((Conf.en c) (E_var.x (Exp.e (T_exp.e (Conf.t c)))))

let pre_econst (c:config) =
 is_T_exp (Conf.t c) && is_E_const (Exp.e (T_exp.e (Conf.t c)))

let pre_eunbox (c:config) =
 is_T_exp (Conf.t c) && is_E_unbox (Exp.e (T_exp.e (Conf.t c)))
 
let pre_emkwire (c:config) =
 is_T_exp (Conf.t c) && is_E_mkwire (Exp.e (T_exp.e (Conf.t c)))

let pre_eprojwire (c:config) =
 is_T_exp (Conf.t c) && is_E_projwire (Exp.e (T_exp.e (Conf.t c)))
 
let pre_econcatwire (c:config) =
 is_T_exp (Conf.t c) && is_E_concatwire (Exp.e (T_exp.e (Conf.t c)))
 
 let pre_effi (c:config) =
  is_T_exp (Conf.t c) && is_E_ffi (Exp.e (T_exp.e (Conf.t c)))

(* pre returns comp, for src it's never Skip *)
type comp = | Do | Skip | NA

val step_aspar_e1: c:config{pre_easpar c} -> Tot config
let step_aspar_e1 (Conf l m s en (T_exp (Exp (E_aspar e1 e2) _))) =
 Conf l m ((Frame m en (F_aspar_ps e2))::s) en (T_exp e1)

val step_unbox_e: c:config{pre_eunbox c} -> Tot config
let step_unbox_e (Conf l m s en (T_exp (Exp (E_unbox e) _))) =
 Conf l m ((Frame m en F_unbox)::s) en (T_exp e)
 
val step_mkwire_e1: c:config{pre_emkwire c} -> Tot config
let step_mkwire_e1 (Conf l m s en (T_exp (Exp (E_mkwire e1 e2) _))) =
 Conf l m ((Frame m en (F_mkwire_ps e2))::s) en (T_exp e1)

val step_projwire_e1: c:config{pre_eprojwire c} -> Tot config
let step_projwire_e1 (Conf l m s en (T_exp (Exp (E_projwire e1 e2) _))) =
 Conf l m ((Frame m en (F_projwire_p e2))::s) en (T_exp e1)

val step_concatwire_e1: c:config{pre_econcatwire c} -> Tot config
let step_concatwire_e1 (Conf l m s en (T_exp (Exp (E_concatwire e1 e2) _))) =
 Conf l m ((Frame m en (F_concatwire_e1 e2))::s) en (T_exp e1)

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
 
val step_fix: c:config{pre_efix c} -> Tot config
let step_fix (Conf l m s en (T_exp (Exp (E_fix f x e) _))) =
 Conf l m s en (T_val (V_fix_clos en f x e))

val step_empabs: c:config{pre_eempabs c} -> Tot config
let step_empabs (Conf l m s en (T_exp (Exp (E_empabs x e) _))) =
 Conf l m s en (T_val (V_emp_clos x e))

val step_app_e1: c:config{pre_eapp c} -> Tot config
let step_app_e1 (Conf l m s en (T_exp (Exp (E_app e1 e2) _))) =
 Conf l m ((Frame m en (F_app_e1 e2))::s) en (T_exp e1)
 
val step_ffi_e: c:config{pre_effi c} -> Tot config
let step_ffi_e (Conf l m s en (T_exp (Exp (E_ffi fn es) _))) = match es with
  | []    -> Conf l m s en (T_red (R_ffi fn []))
  | e::tl -> Conf l m ((Frame m en (F_ffi fn tl []))::s) en (T_exp e)

val step_aspar_e2: c:config{is_value_ps c /\ is_sframe c is_F_aspar_ps}
                  -> Tot config
let step_aspar_e2 (Conf l _ ((Frame m en (F_aspar_ps e))::s) _
                       (T_val (V_const (C_prins ps)))) =
 Conf l m ((Frame m en (F_aspar_e ps))::s) en (T_exp e)

val step_mkwire_e2: c:config{is_value c /\ is_sframe c is_F_mkwire_ps}
                   -> Tot config
let step_mkwire_e2 (Conf l _ ((Frame m en (F_mkwire_ps e))::s) _
                        (T_val v)) =
 Conf l m ((Frame m en (F_mkwire_e v))::s) en (T_exp e)

val step_projwire_e2: c:config{is_value_p c /\ is_sframe c is_F_projwire_p}
                     -> Tot config
let step_projwire_e2 (Conf l _ ((Frame m en (F_projwire_p e))::s) _
                          (T_val (V_const (C_prin p)))) =
 Conf l m ((Frame m en (F_projwire_e p))::s) en (T_exp e)

val step_concatwire_e2: c:config{is_value c /\ is_sframe c is_F_concatwire_e1}
                       -> Tot config
let step_concatwire_e2 (Conf l _ ((Frame m en (F_concatwire_e1 e))::s) _
                            (T_val v)) =
 Conf l m ((Frame m en (F_concatwire_e2 v))::s) en (T_exp e)

val step_app_e2: c:config{is_value c /\ is_sframe c is_F_app_e1}
                -> Tot config
let step_app_e2 (Conf l _ ((Frame m en (F_app_e1 e2))::s) _ (T_val v)) =
 Conf l m ((Frame m en (F_app_e2 v))::s) en (T_exp e2)

val step_ffi_l: c:config{is_value c /\ is_sframe c is_F_ffi} -> Tot config
let step_ffi_l (Conf l _ ((Frame m en (F_ffi fn es vs))::s) _ (T_val #meta v)) =
  match es with
    | []    -> Conf l m s en (T_red (R_ffi fn ((D_v meta v)::vs)))
    | e::tl -> Conf l m ((Frame m en (F_ffi fn tl ((D_v meta v)::vs)))::s) en (T_exp e) 
  
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

val step_projwire_red: c:config{is_value c /\ is_sframe c is_F_projwire_e}
                      -> Tot config
let step_projwire_red (Conf l _ ((Frame m en (F_projwire_e p))::s) _ (T_val v)) =
 Conf l m s en (T_red (R_projwire p v))

val step_mkwire_red: c:config{is_value c /\ is_sframe c is_F_mkwire_e}
                    -> Tot config
let step_mkwire_red (Conf l _ ((Frame m en (F_mkwire_e v1))::s) _ (T_val v2)) =
 Conf l m s en (T_red (R_mkwire v1 v2))

val step_concatwire_red: c:config{is_value c /\ is_sframe c is_F_concatwire_e2}
                        -> Tot config
let step_concatwire_red (Conf l _ ((Frame m en (F_concatwire_e2 v1))::s) _ (T_val v2)) =
 Conf l m s en (T_red (R_concatwire v1 v2))

val step_let_red: c:config{is_value c /\ is_sframe c is_F_let}
                 -> Tot config
let step_let_red (Conf l _ ((Frame m en (F_let x e2))::s) _ (T_val v)) =
 Conf l m s en (T_red (R_let x v e2))

val step_app_red: c:config{is_value c /\ is_sframe c is_F_app_e2}
                 -> Tot config
let step_app_red (Conf l _ ((Frame m en (F_app_e2 v1))::s) _ (T_val v2)) =
 Conf l m s en (T_red (R_app v1 v2))

val is_clos: #meta:v_meta -> value meta -> Tot bool
let is_clos #meta v = is_V_clos v || is_V_fix_clos v || is_V_emp_clos v

val get_en_b: #meta:v_meta -> v:value meta{is_clos v} -> Tot (env * varname * exp)
let get_en_b #meta v = match v with
 | V_clos en x e       -> en, x, e
 | V_fix_clos en f x e -> update_env #(empty, Cannot_b) en f (V_fix_clos en f x e), x, e
 | V_emp_clos x e      -> empty_env, x, e

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

val pre_mkwire: config -> Tot comp
let pre_mkwire c = match c with
 | Conf l (Mode Par ps) _ _ (T_red (R_mkwire (V_const (C_prins ps'))
                                                      (V_box #mv ps'' _))) ->
   if fst mv = empty && snd mv = Can_b then
     if src l then
       if subset ps' ps && subset ps' ps'' then Do else NA
     else Do
   else NA
 
 | Conf l (Mode Sec ps) _ _ (T_red (R_mkwire #mps #mv (V_const (C_prins ps')) _)) ->
   if fst mv = empty && snd mv = Can_b then
     if subset ps' ps then Do else NA
   else NA
 
 | _ -> NA

val mconst_on:
 eps:eprins -> v:value (empty, Can_b)
 -> Tot (w:v_wire eps{forall p. (mem p eps ==> select p w = Some v)})
let mconst_on eps v = const_on eps v

val step_mkwire: c:config{pre_mkwire c = Do} -> Tot config
let step_mkwire c = match c with
 | Conf l (Mode Par ps) s en (T_red (R_mkwire (V_const (C_prins ps'))
                                                       (V_box _ v))) ->
   let eps, w =
     if src l then ps', mconst_on ps' v
     else
       if subset ps ps' then
         ps, mconst_on ps v
       else empty, OrdMap.empty
   in
   Conf l (Mode Par ps) s en (T_val (V_wire eps w))

 | Conf l (Mode Sec ps) s en (T_red (R_mkwire (V_const (C_prins ps')) v)) ->
   Conf l (Mode Sec ps) s en (T_val (V_wire ps' (mconst_on ps' v)))

val pre_projwire: config -> Tot comp
let pre_projwire c = match c with
 | Conf _ (Mode as_m ps) _ _ (T_red (R_projwire p (V_wire eps _))) ->
   if as_m = Par then
     if ps = singleton p && mem p eps then Do else NA
   else
     if mem p ps && mem p eps then Do else NA
   
 | _ -> NA

val step_projwire: c:config{pre_projwire c = Do} -> Tot config
let step_projwire c = match c with
 | Conf l m s en (T_red (R_projwire p (V_wire _ w))) ->
   Conf l m s en (T_val (Some.v (select p w)))

val pre_concatwire: config -> Tot comp
let pre_concatwire c = match c with
 | Conf _ _ _ _ (T_red (R_concatwire (V_wire eps1 _) (V_wire eps2 _))) ->
   if intersect eps1 eps2 = empty then Do else NA
   
 | _ -> NA

open Classical

val empty_intersection_lemma: eps1:eprins -> eps2:eprins{intersect eps1 eps2 = empty}
                             -> p:prin
                             -> Lemma (requires (True))
                                      (ensures (mem p eps1 ==> not (mem p eps2)))
let empty_intersection_lemma eps1 eps2 p =
 let _ = mem p (intersect eps1 eps2) in
 ()

val empty_intersection_lemma_forall: eps1:eprins -> eps2:eprins{intersect eps1 eps2 = empty}
                                    -> Lemma (requires (True))
                                             (ensures (forall p. mem p eps1 ==> not (mem p eps2)))                                
let empty_intersection_lemma_forall eps1 eps2 =
 forall_intro #prin #(fun p -> mem p eps1 ==> not (mem p eps2)) (empty_intersection_lemma eps1 eps2)
  
opaque val compose_wires:
 #eps1:eprins -> #eps2:eprins{intersect eps1 eps2 = empty}
 -> w1:v_wire eps1 -> w2:v_wire eps2
 -> eps:eprins{subset eps eps1}
 -> Tot (r:v_wire (union eps eps2)
         {forall p. contains p r ==>    ((mem p eps  /\ not (mem p eps2)) \/
                                         (mem p eps2 /\ not (mem p eps)))
                                     /\ (mem p eps  ==> select p r = select p w1)
                                     /\ (mem p eps2 ==> select p r = select p w2)})
    (decreases (size eps))
let rec compose_wires #eps1 #eps2 w1 w2 eps =
 empty_intersection_lemma_forall eps eps2;
 if eps = empty then w2
 else
   let Some p = choose eps in
   let w = compose_wires #eps1 #eps2 w1 w2 (remove p eps) in
   update p (Some.v (select p w1)) w

val step_concatwire: c:config{pre_concatwire c = Do} -> Tot config
let step_concatwire c = match c with
 | Conf l m s en (T_red (R_concatwire (V_wire eps1 w1) (V_wire eps2 w2))) ->
   Conf l m s en (T_val (V_wire (union eps1 eps2) (compose_wires #eps1 #eps2 w1 w2 eps1)))

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

val is_valid_ffi_v: #meta:v_meta -> v:value meta -> Tot bool
let is_valid_ffi_v #meta v = match v with
  | V_const _          -> true
  | V_box _ _          -> false
  | V_wire _ _         -> false
  | V_clos _ _ _       -> false
  | V_fix_clos _ _ _ _ -> false
  | V_emp_clos _ _     -> false
  | V_emp              -> false

val is_valid_ffi_vs: list dvalue -> Tot bool
let rec is_valid_ffi_vs vs = match vs with
  | []            -> true
  | (D_v _ v)::tl -> is_valid_ffi_v v && is_valid_ffi_vs tl

val pre_ffi: config -> Tot comp
let pre_ffi c = match c with
  | Conf _ _ _ _ (T_red (R_ffi _ vs)) ->
    if is_valid_ffi_vs vs then Do else NA
  
  | _ -> NA

assume val exec_ffi: string -> list dvalue -> Tot dvalue

val step_ffi: c:config{pre_ffi c = Do} -> Tot config
let step_ffi (Conf l m s en (T_red (R_ffi fn vs))) =
  let D_v _ v = exec_ffi fn vs in
  Conf l m s en (T_val v)

let pre_eassec (c:config) =
 is_T_exp (Conf.t c) && is_E_assec (Exp.e (T_exp.e (Conf.t c)))

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
   
 | C_mkwire_e1:
   c:config{pre_emkwire c} -> c':config{c' = step_mkwire_e1 c}
   -> sstep c c'

 | C_projwire_p:
   c:config{pre_eprojwire c} -> c':config{c' = step_projwire_e1 c}
   -> sstep c c'
   
 | C_concatwire_e1:
   c:config{pre_econcatwire c} -> c':config{c' = step_concatwire_e1 c}
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
   
 | C_fix:
   c:config{pre_efix c} -> c':config{c' = step_fix c}
   -> sstep c c'

 | C_empabs:
   c:config{pre_eempabs c} -> c':config{c' = step_empabs c}
   -> sstep c c'

 | C_app_e1:
   c:config{pre_eapp c} -> c':config{c' = step_app_e1 c}
   -> sstep c c'
   
 | C_ffi_e:
   c:config{pre_effi c} -> c':config{c' = step_ffi_e c} -> sstep c c'

 | C_aspar_e:
   c:config{is_value_ps c /\ is_sframe c is_F_aspar_ps}
   -> c':config{c' = step_aspar_e2 c}
   -> sstep c c'
   
 | C_mkwire_e2:
   c:config{is_value c /\ is_sframe c is_F_mkwire_ps}
   -> c':config{c' = step_mkwire_e2 c}
   -> sstep c c'
 
 | C_projwire_e:
   c:config{is_value_p c /\ is_sframe c is_F_projwire_p}
   -> c':config{c' = step_projwire_e2 c}
   -> sstep c c'

 | C_concatwire_e2:
   c:config{is_value c /\ is_sframe c is_F_concatwire_e1}
   -> c':config{c' = step_concatwire_e2 c}
   -> sstep c c'

 | C_app_e2:
   c:config{is_value c /\ is_sframe c is_F_app_e1}
   -> c':config{c' = step_app_e2 c}
   -> sstep c c'
   
 | C_ffi_l:
   c:config{is_value c /\ is_sframe c is_F_ffi}
   -> c':config{c' = step_ffi_l c} -> sstep c c'

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
   
 | C_mkwire_red:
   c:config{is_value c /\ is_sframe c is_F_mkwire_e}
   -> c':config{c' = step_mkwire_red c}
   -> sstep c c'
   
 | C_projwire_red:
   c:config{is_value c /\ is_sframe c is_F_projwire_e}
   -> c':config{c' = step_projwire_red c}
   -> sstep c c'

 | C_concatwire_red:
   c:config{is_value c /\ is_sframe c is_F_concatwire_e2}
   -> c':config{c' = step_concatwire_red c}
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
   
 | C_ffi_beta:
   c:config{pre_ffi c = Do} -> c':config{c' = step_ffi c} -> sstep c c'

 | C_aspar_beta:
   c:config{not (pre_aspar c = NA)} -> c':config{c' = step_aspar c}
   -> sstep c c'

 | C_box_beta:
   c:config{pre_box c = Do} -> c':config{c' = step_box c} -> sstep c c'

 | C_unbox_beta:
   c:config{pre_unbox c = Do} -> c':config{c' = step_unbox c}
   -> sstep c c'
   
 | C_mkwire_beta:
   c:config{pre_mkwire c = Do} -> c':config{c' = step_mkwire c}
   -> sstep c c'
   
 | C_projwire_beta:
   c:config{pre_projwire c = Do} -> c':config{c' = step_projwire c}
   -> sstep c c'
   
 | C_concatwire_beta:
   c:config{pre_concatwire c = Do} -> c':config{c' = step_concatwire c}
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
