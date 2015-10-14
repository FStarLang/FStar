(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Prins --admit_fsi Ffibridge;
    other-files:ghost.fst listTot.fst ordset.fsi ordmap.fsi classical.fst prins.fsi ast.fst ffibridge.fsi
 --*)

module Semantics

open FStar.Ghost
open FStar.List.Tot

open FStar.OrdMap
open FStar.OrdSet

open Ffibridge

open Prins
open AST

(* pre returns comp, for src it's never Skip *)
type comp = | Do | Skip | NA

(* TODO: FIXME: workaround for projectors *)
val e_of_t_exp: t:term{is_T_exp t} -> Tot exp
let e_of_t_exp (T_exp e) = e

val concat_traces: erased trace -> erased trace -> Tot (erased trace)
let concat_traces t1 t2 = elift2 append t1 t2

val vals_traces_h_append_lemma:
  tr1:trace{vals_trace_h tr1} -> tr2:trace{vals_trace_h tr2}
  -> Lemma (requires (True)) (ensures (vals_trace_h (append tr1 tr2)))
let rec vals_traces_h_append_lemma tr1 tr2 = match tr1 with
  | []   -> ()
  | _::tl -> vals_traces_h_append_lemma tl tr2

assume val vals_traces_h_append_lemma_forall:
  unit -> Lemma (requires (True)) (ensures (forall tr1 tr2. vals_trace_h tr1 ==>
                                                   vals_trace_h tr2 ==>
						   vals_trace_h (append tr1 tr2)))

val vals_traces_concat_lemma:
  tr1:erased trace{vals_trace tr1}
  -> tr2:erased trace{vals_trace tr2}
  -> Lemma (requires (True)) (ensures (vals_trace (concat_traces tr1 tr2)))
    [SMTPat (vals_trace (concat_traces tr1 tr2))]
let vals_traces_concat_lemma tr1 tr2 =
  vals_traces_h_append_lemma_forall ();
  let _ = assert (vals_trace_h (append (reveal tr1) (reveal tr2))) in
  ()

//----- aspar e1 e2 -----//

let pre_easpar (c:config) =
  is_T_exp (t_of_conf c) && is_E_aspar (e_of_t_exp (t_of_conf c)) && is_par c

val step_aspar_e1: c:config{pre_easpar c} -> Tot config
let step_aspar_e1 (Conf l m s en (T_exp (E_aspar e1 e2)) tr) =
  Conf l m ((Frame m en (F_aspar_ps e2) tr)::s) en (T_exp e1) (hide [])

val step_aspar_e2: c:config{is_value_ps c /\ is_sframe c is_F_aspar_ps}
                  -> Tot config
let step_aspar_e2 (Conf l _ ((Frame m en (F_aspar_ps e) tr)::s) _
                   (T_val (V_prins ps)) tr') =
  Conf l m ((Frame m en (F_aspar_e ps) (concat_traces tr tr'))::s) en (T_exp e) (hide [])

val step_aspar_red: c:config{is_value c /\ is_sframe c is_F_aspar_e}
                   -> Tot config
let step_aspar_red (Conf l _ ((Frame m en (F_aspar_e ps) tr)::s) _ (T_val v) tr') =
  Conf l m s en (T_red (R_aspar ps v)) (concat_traces tr tr')

val pre_aspar: config -> Tot comp
let pre_aspar c = match c with
  | Conf l (Mode Par ps1) _ _ (T_red (R_aspar ps2 v)) _ ->
    if is_clos v then
      if src l then
        if subset ps2 ps1 then Do else NA
     else
        if subset ps1 ps2 then Do else Skip
    else NA

  | _ -> NA

val step_aspar: c:config{not (pre_aspar c = NA)} -> Tot config
let step_aspar c = match c with
  | Conf l m s en' (T_red (R_aspar ps v)) tr ->
    let en, x, e = get_en_b v in
    let m'  = if src l then Mode Par ps else m in
    let s'  = (Frame m en' (F_aspar_ret ps) tr)::s in

    (*
     * for parties not in ps, the choice of empty_env is arbitrary
     * perhaps we should prove the theorem using any env and then
     * implementation can make whatever decision (retain env as in F* semantics)
     *)
    let en', t' =
      if src l then update_env en x V_unit, T_exp e
      else
        if pre_aspar c = Do then update_env en x V_unit, T_exp e
        else empty_env, T_val V_emp
    in

    Conf l m' s' en' t' (hide [])

val pre_aspar_ret: config -> Tot comp
let pre_aspar_ret c = match c with
  | Conf _ _ ((Frame _ _ (F_aspar_ret ps) _)::_) _ (T_val #meta _) _ ->
    if is_meta_boxable ps meta then Do else NA
      (*if src l then
        if subset ps2 ps1 then Do else NA
      else Do
    else NA
*)
  | _ -> NA

val scope_trace: prins -> trace -> Tot trace
let scope_trace ps t = [ Tr_scope ps t ]

val step_aspar_ret: c:config{pre_aspar_ret c = Do} -> Tot config
let step_aspar_ret c = match c with
  | Conf l _ ((Frame m en (F_aspar_ret ps) tr)::s) _ (T_val v) tr' ->
    let tr =
      if l = Source then
	concat_traces tr (elift1 (scope_trace ps) tr')
      else concat_traces tr tr'
    in
	
    Conf l m s en (T_val (V_box ps v)) tr

//----- aspar e1 e2 -----//

// ----- box e1 e2 -----//

let pre_ebox (c:config) =
  is_T_exp (t_of_conf c) && is_E_box (e_of_t_exp (t_of_conf c))

val step_box_e1: c:config{pre_ebox c} -> Tot config
let step_box_e1 (Conf l m s en (T_exp (E_box e1 e2)) tr) =
  Conf l m ((Frame m en (F_box_ps e2) tr)::s) en (T_exp e1) (hide [])

val step_box_e2: c:config{is_value_ps c /\ is_sframe c is_F_box_ps}
                  -> Tot config
let step_box_e2 (Conf l _ ((Frame m en (F_box_ps e) tr)::s) _
                 (T_val (V_prins ps)) tr') =
  Conf l m ((Frame m en (F_box_e ps) (concat_traces tr tr'))::s) en (T_exp e) (hide [])

val step_box_red: c:config{is_value c /\ is_sframe c is_F_box_e}
                   -> Tot config
let step_box_red (Conf l _ ((Frame m en (F_box_e ps) tr)::s) _ (T_val v) tr') =
  Conf l m s en (T_red (R_box ps v)) (concat_traces tr tr')

val pre_box: c:config -> Tot comp
let pre_box c = match c with
  | Conf l (Mode _ ps) _ _ (T_red (R_box #meta ps' v)) _ ->
    if is_meta_boxable ps' meta then
      if src l then
        if subset ps' ps then Do else NA
      else Do
    else NA
  
  | _ -> NA

val step_box: c:config{pre_box c = Do} -> Tot config
let step_box (Conf l m s en (T_red (R_box ps' v)) tr) =
  let Mode as_m ps = m in
  if src l || as_m = Sec then
    Conf l m s en (T_val (V_box ps' v)) tr
  else
    if subset ps ps' then Conf l m s en (T_val (V_box ps' v)) tr
    else Conf l m s en (T_val (V_box ps' V_emp)) tr // TODO: FIXME: V_emp or v ?

//----- box e1 e2 -----//

//----- app e1 e2 -----//

let pre_eapp (c:config) =
  is_T_exp (t_of_conf c) && is_E_app (e_of_t_exp (t_of_conf c))

val step_app_e1: c:config{pre_eapp c} -> Tot config
let step_app_e1 (Conf l m s en (T_exp (E_app e1 e2)) tr) =
  Conf l m ((Frame m en (F_app_e1 e2) tr)::s) en (T_exp e1) (hide [])

val step_app_e2: c:config{is_value c /\ is_sframe c is_F_app_e1}
                -> Tot config
let step_app_e2 (Conf l _ ((Frame m en (F_app_e1 e2) tr)::s) _ (T_val v) tr') =
  Conf l m ((Frame m en (F_app_e2 v) (concat_traces tr tr'))::s) en (T_exp e2) (hide [])

val step_app_red: c:config{is_value c /\ is_sframe c is_F_app_e2}
                 -> Tot config
let step_app_red (Conf l _ ((Frame m en (F_app_e2 v1) tr)::s) _ (T_val v2) tr') =
  Conf l m s en (T_red (R_app v1 v2)) (concat_traces tr tr')

val pre_app: c:config -> Tot bool
let pre_app c = match c with
  | Conf _ _ _ _ (T_red (R_app v _)) _ -> is_clos v

  | _ -> false

val step_app: c:config{pre_app c} -> Tot config
let step_app c = match c with
  | Conf l m s _ (T_red (R_app f v)) tr ->
    let (en, x, e) = get_en_b f in
    Conf l m s (update_env en x v) (T_exp e) tr

//----- app e1 e2 -----//

//----- fun x.e -----//

let pre_eabs (c:config) =
  is_T_exp (t_of_conf c) && is_E_abs (e_of_t_exp (t_of_conf c))

val step_abs: c:config{pre_eabs c} -> Tot config
let step_abs (Conf l m s en (T_exp (E_abs x e)) tr) =
  Conf l m s en (T_val (V_clos en x e)) tr

//----- fun x.e -----//

//----- fix f.fun x.e -----//

let pre_efix (c:config) =
  is_T_exp (t_of_conf c) && is_E_fix (e_of_t_exp (t_of_conf c))

val step_fix: c:config{pre_efix c} -> Tot config
let step_fix (Conf l m s en (T_exp (E_fix f x e)) tr) =
  Conf l m s en (T_val (V_fix_clos en f x e)) tr

//----- fix f.fun x. e -----//

//----- fun x.e (closed) -----//

let pre_eempabs (c:config) =
  is_T_exp (t_of_conf c) && is_E_empabs (e_of_t_exp (t_of_conf c))

val step_empabs: c:config{pre_eempabs c} -> Tot config
let step_empabs (Conf l m s en (T_exp (E_empabs x e)) tr) =
  Conf l m s en (T_val (V_emp_clos x e)) tr

//----- fun x.e (closed) -----// 

//----- let x = e1 in e2 -----//

let pre_elet (c:config) =
  is_T_exp (t_of_conf c) && is_E_let (e_of_t_exp (t_of_conf c))

val step_let_e1: c:config{pre_elet c} -> Tot config
let step_let_e1 (Conf l m s en (T_exp (E_let x e1 e2)) tr) =
  Conf l m ((Frame m en (F_let x e2) tr)::s) en (T_exp e1) (hide [])

val step_let_red: c:config{is_value c /\ is_sframe c is_F_let}
                 -> Tot config
let step_let_red (Conf l _ ((Frame m en (F_let x e2) tr)::s) _ (T_val v) tr') =
  Conf l m s en (T_red (R_let x v e2)) (concat_traces tr tr')

val pre_let: c:config -> Tot bool
let pre_let c = match c with
  | Conf _ _ _ _ (T_red (R_let _ _ _)) _ -> true
  | _                                    -> false

val step_let: c:config{pre_let c} -> Tot config
let step_let c = match c with
  | Conf l m s en (T_red (R_let x v1 e2)) tr ->
    Conf l m s (update_env en x v1) (T_exp e2) tr

//----- let x = e1 in e2 -----//

//----- x -----//

(* TODO: FIXME: workaround for projectors *)
val x_of_e_var: e:exp{is_E_var e} -> Tot varname
let x_of_e_var (E_var x) = x

(* TODO: FIXME: workaround for projectors *)
val is_Some: option 'a -> Tot bool
let is_Some x = match x with
  | Some _ -> true
  | _      -> false

(* TODO: FIXME: workaround for projectors *)
val en_of_conf: config -> Tot env
let en_of_conf (Conf _ _ _ en _ _) = en

let pre_evar (c:config) =
  is_T_exp (t_of_conf c) && is_E_var (e_of_t_exp (t_of_conf c)) &&
  is_Some ((en_of_conf c) (x_of_e_var (e_of_t_exp (t_of_conf c))))

val step_var: c:config{pre_evar c} -> Tot config
let step_var (Conf l m s en (T_exp (E_var x)) tr) =
  let Some (D_v _ v) = en x in
  Conf l m s en (T_val v) tr

//----- x -----//

//----- c -----//

let pre_econst (c:config) =
  is_T_exp (t_of_conf c) && is_E_const (e_of_t_exp (t_of_conf c))

val slice_const: p:prin -> 'a -> Tot 'a
let slice_const p x = x

val compose_const: 'a -> 'a -> Tot 'a
let compose_const x _ = x

val slice_const_sps: ps:prins -> 'a -> Tot 'a
let slice_const_sps ps x = x

val step_const: c:config{pre_econst c} -> Tot config
let step_const (Conf l m s en (T_exp (E_const c)) tr) =
  let meta = Meta empty Can_b empty Can_w in
  let v = match c with
    | C_prin p     -> V_prin p
    | C_eprins eps -> V_eprins eps
    | C_prins ps   -> V_prins ps

    | C_unit _     -> V_unit
    | C_bool b     -> V_bool b

    | C_opaque 'a v -> V_opaque v meta slice_const compose_const slice_const_sps
  in

  Conf l m s en (T_val v) tr

//----- c -----//

//----- unbox e -----//

let pre_eunbox (c:config) =
  is_T_exp (t_of_conf c) && is_E_unbox (e_of_t_exp (t_of_conf c))

val step_unbox_e: c:config{pre_eunbox c} -> Tot config
let step_unbox_e (Conf l m s en (T_exp (E_unbox e)) tr) =
  Conf l m ((Frame m en F_unbox tr)::s) en (T_exp e) (hide [])

val step_unbox_red: c:config{is_value c /\ is_sframe c is_F_unbox}
                   -> Tot config
let step_unbox_red (Conf l _ ((Frame m en F_unbox tr)::s) _ (T_val v) tr') =
  Conf l m s en (T_red (R_unbox v)) (concat_traces tr tr')

val pre_unbox: config -> Tot comp
let pre_unbox c = match c with
  | Conf _ (Mode as_m ps1) _ _ (T_red (R_unbox (V_box ps2 _))) _ ->
    if as_m = Par then
      if subset ps1 ps2 then Do else NA
    else
      if not (intersect ps1 ps2 = empty) then Do else NA

  | _ -> NA

val step_unbox: c:config{pre_unbox c = Do} -> Tot config
let step_unbox c = match c with
  | Conf l m s en (T_red (R_unbox (V_box _ v))) tr -> Conf l m s en (T_val v) tr

//----- unbox e -----//

//----- mkwire e1 e2 -----//

let pre_emkwire (c:config) =
  is_T_exp (t_of_conf c) && is_E_mkwire (e_of_t_exp (t_of_conf c))

val step_mkwire_e1: c:config{pre_emkwire c} -> Tot config
let step_mkwire_e1 (Conf l m s en (T_exp (E_mkwire e1 e2)) tr) =
  Conf l m ((Frame m en (F_mkwire_ps e2) tr)::s) en (T_exp e1) (hide [])

val step_mkwire_e2: c:config{is_value c /\ is_sframe c is_F_mkwire_ps}
                   -> Tot config
let step_mkwire_e2 (Conf l _ ((Frame m en (F_mkwire_ps e) tr)::s) _
                    (T_val v) tr') =
  Conf l m ((Frame m en (F_mkwire_e v) (concat_traces tr tr'))::s) en (T_exp e) (hide [])

val step_mkwire_red: c:config{is_value c /\ is_sframe c is_F_mkwire_e}
                    -> Tot config
let step_mkwire_red (Conf l _ ((Frame m en (F_mkwire_e v1) tr)::s) _ (T_val v2) tr') =
  Conf l m s en (T_red (R_mkwire v1 v2)) (concat_traces tr tr')

val pre_mkwire: config -> Tot comp
let pre_mkwire c = match c with
  | Conf l (Mode Par ps) _ _ (T_red (R_mkwire (V_prins ps')
                                              (V_box #mv ps'' _))) _ ->
    if is_meta_wireable mv then
      if src l then
        if subset ps' ps && subset ps' ps'' then Do else NA
      else Do
    else NA
 
  | Conf l (Mode Sec ps) _ _ (T_red (R_mkwire #mps #mv (V_prins ps') _)) _ ->
    if is_meta_wireable mv then
      if subset ps' ps then Do else NA
    else NA
 
  | _ -> NA

val mconst_on:
 eps:eprins -> v:value (Meta empty Can_b empty Can_w)
 -> Tot (w:v_wire eps{forall p. (mem p eps ==> select p w = Some v)})
let mconst_on eps v = const_on eps v

val step_mkwire: c:config{pre_mkwire c = Do} -> Tot config
let step_mkwire c = match c with
  | Conf l (Mode Par ps) s en (T_red (R_mkwire (V_prins ps')
                                               (V_box _ v))) tr ->
    let eps, w =
      if src l then ps', mconst_on ps' v
      else
        if subset ps ps' then
          ps, mconst_on ps v
        else empty, OrdMap.empty
    in
    Conf l (Mode Par ps) s en (T_val (V_wire eps w)) tr

  | Conf l (Mode Sec ps) s en (T_red (R_mkwire (V_prins ps') v)) tr ->
    Conf l (Mode Sec ps) s en (T_val (V_wire ps' (mconst_on ps' v))) tr

//----- mkwire e1 e2 -----//

//----- projwire e1 e2 -----//

let pre_eprojwire (c:config) =
  is_T_exp (t_of_conf c) && is_E_projwire (e_of_t_exp (t_of_conf c))

val step_projwire_e1: c:config{pre_eprojwire c} -> Tot config
let step_projwire_e1 (Conf l m s en (T_exp (E_projwire e1 e2)) tr) =
  Conf l m ((Frame m en (F_projwire_p e2) tr)::s) en (T_exp e1) (hide [])

val step_projwire_e2: c:config{is_value_p c /\ is_sframe c is_F_projwire_p}
                     -> Tot config
let step_projwire_e2 (Conf l _ ((Frame m en (F_projwire_p e) tr)::s) _
                      (T_val (V_prin p)) tr') =
  Conf l m ((Frame m en (F_projwire_e p) (concat_traces tr tr'))::s) en (T_exp e) (hide [])

val step_projwire_red: c:config{is_value c /\ is_sframe c is_F_projwire_e}
                      -> Tot config
let step_projwire_red (Conf l _ ((Frame m en (F_projwire_e p) tr)::s) _ (T_val v) tr') =
  Conf l m s en (T_red (R_projwire p v)) (concat_traces tr tr')

val pre_projwire: config -> Tot comp
let pre_projwire c = match c with
  | Conf _ (Mode as_m ps) _ _ (T_red (R_projwire p (V_wire eps _))) _ ->
    if as_m = Par then
      if ps = singleton p && mem p eps then Do else NA
    else
      if mem p ps && mem p eps then Do else NA
   
  | _ -> NA

(* TODO: FIXME: workaround for projectors *)
val v_of_some: x:option 'a{is_Some x} -> Tot 'a
let v_of_some (Some x) = x

val step_projwire: c:config{pre_projwire c = Do} -> Tot config
let step_projwire c = match c with
  | Conf l m s en (T_red (R_projwire p (V_wire _ w))) tr ->
    Conf l m s en (T_val (v_of_some (select p w))) tr

//----- projwire e1 e2 -----//

//----- concatwire e1 e2 -----//

let pre_econcatwire (c:config) =
  is_T_exp (t_of_conf c) && is_E_concatwire (e_of_t_exp (t_of_conf c))

val step_concatwire_e1: c:config{pre_econcatwire c} -> Tot config
let step_concatwire_e1 (Conf l m s en (T_exp (E_concatwire e1 e2)) tr) =
  Conf l m ((Frame m en (F_concatwire_e1 e2) tr)::s) en (T_exp e1) (hide [])

val step_concatwire_e2: c:config{is_value c /\ is_sframe c is_F_concatwire_e1}
                       -> Tot config
let step_concatwire_e2 (Conf l _ ((Frame m en (F_concatwire_e1 e) tr)::s) _
                        (T_val v) tr') =
  Conf l m ((Frame m en (F_concatwire_e2 v) (concat_traces tr tr'))::s) en (T_exp e) (hide [])

val step_concatwire_red: c:config{is_value c /\ is_sframe c is_F_concatwire_e2}
                        -> Tot config
let step_concatwire_red (Conf l _ ((Frame m en (F_concatwire_e2 v1) tr)::s) _ (T_val v2) tr') =
  Conf l m s en (T_red (R_concatwire v1 v2)) (concat_traces tr tr')

val pre_concatwire: config -> Tot comp
let pre_concatwire c = match c with
  | Conf _ _ _ _ (T_red (R_concatwire (V_wire eps1 _) (V_wire eps2 _))) tr ->
    if intersect eps1 eps2 = empty then Do else NA
   
  | _ -> NA

open FStar.Classical

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
    update p (v_of_some (select p w1)) w

val step_concatwire: c:config{pre_concatwire c = Do} -> Tot config
let step_concatwire c = match c with
  | Conf l m s en (T_red (R_concatwire (V_wire eps1 w1) (V_wire eps2 w2))) tr ->
    Conf l m s en (T_val (V_wire (union eps1 eps2) (compose_wires #eps1 #eps2 w1 w2 eps1))) tr

//----- concatwire e1 e2 -----//

//----- ffi f l -----//

let pre_effi (c:config) =
  is_T_exp (t_of_conf c) && is_E_ffi (e_of_t_exp (t_of_conf c))

val step_ffi_e: c:config{pre_effi c} -> Tot config
let step_ffi_e (Conf l m s en (T_exp (E_ffi 'a 'b n fn es inj)) tr) = match es with
  | []    -> Conf l m s en (T_red (R_ffi n fn [] inj)) tr
  | e::tl  -> Conf l m ((Frame m en (F_ffi n fn tl [] inj) tr)::s) en (T_exp e) (hide [])

val step_ffi_l: c:config{is_value c /\ is_sframe c is_F_ffi} -> Tot config
let step_ffi_l (Conf l _ ((Frame m en (F_ffi 'a 'b n fn es vs inj) tr)::s) _ (T_val #meta v) tr') =
  match es with
    | []    -> Conf l m s en (T_red (R_ffi n fn ((D_v meta v)::vs) inj)) (concat_traces tr tr')
    | e::tl -> Conf l m ((Frame m en (F_ffi n fn tl ((D_v meta v)::vs) inj) (concat_traces tr tr'))::s) en (T_exp e) (hide [])

val pre_ffi: config -> Tot comp
let pre_ffi c = match c with
  | Conf _ _ _ _ (T_red (R_ffi 'a 'b _ _ vs _)) _ -> Do
  
  | _ -> NA

val step_ffi: c:config{pre_ffi c = Do} -> Tot config
let step_ffi (Conf l m s en (T_red (R_ffi 'a 'b n fn vs inj)) tr) =
  let D_v _ v = exec_ffi n fn vs inj in
  Conf l m s en (T_val v) tr

//----- ffi v l -----//

//----- if e then e1 else e2 -----//

let pre_econd (c:config) =
  is_T_exp (t_of_conf c) && is_E_cond (e_of_t_exp (t_of_conf c))

val step_cond_e: c:config{pre_econd c} -> Tot config
let step_cond_e (Conf l m s en (T_exp (E_cond e e1 e2)) tr) =
  Conf l m ((Frame m en (F_cond e1 e2) tr)::s) en (T_exp e) (hide [])

val step_cond_red: c:config{is_value c /\ is_sframe c is_F_cond} -> Tot config
let step_cond_red (Conf l _ ((Frame m en (F_cond e1 e2) tr)::s) _ (T_val v) tr') =
  Conf l m s en (T_red (R_cond v e1 e2)) (concat_traces tr tr')

val pre_cond: c:config -> Tot bool
let pre_cond c = match c with
  | Conf _ _ _ _ (T_red (R_cond (V_bool _) _ _)) _ -> true
  | _ -> false

val step_cond: c:config{pre_cond c} -> Tot config
let step_cond c = match c with
  | Conf l m s en (T_red (R_cond (V_bool b) e1 e2)) tr ->
    let e = if b then e1 else e2 in
    Conf l m s en (T_exp e) tr

//----- if e then e1 else e2 -----//
  
//----- assec e1 e2 -----//

let pre_eassec (c:config) =
  is_T_exp (t_of_conf c) && is_E_assec (e_of_t_exp (t_of_conf c))

val step_assec_e1: c:config{pre_eassec c} -> Tot config
let step_assec_e1 (Conf l m s en (T_exp (E_assec e1 e2)) tr) =
  Conf l m ((Frame m en (F_assec_ps e2) tr)::s) en (T_exp e1) (hide [])

val step_assec_e2: c:config{is_value_ps c /\ is_sframe c is_F_assec_ps}
                  -> Tot config
let step_assec_e2 (Conf l _ ((Frame m en (F_assec_ps e) tr)::s) _
                   (T_val (V_prins ps)) tr') =
  Conf l m ((Frame m en (F_assec_e ps) (concat_traces tr tr'))::s) en (T_exp e) (hide [])

val step_assec_red: c:config{is_value c /\ is_sframe c is_F_assec_e}
                   -> Tot config
let step_assec_red (Conf l _ ((Frame m en (F_assec_e ps) tr)::s) _ (T_val v) tr') =
  Conf l m s en (T_red (R_assec ps v)) (concat_traces tr tr')

val pre_assec: config -> Tot comp
let pre_assec c = match c with
  | Conf l (Mode as_m ps1) _ _ (T_red (R_assec ps2 v)) _ ->
    if is_clos v then
      if l = Source || as_m = Sec then
        if ps1 = ps2 then Do else NA
      else NA
    else NA

  | _ -> NA

val step_assec: c:config{not (pre_assec c = NA)} -> Tot config
let step_assec c = match c with
  | Conf l m s en' (T_red (R_assec ps v)) tr ->
    let (en, x, e) = get_en_b v in
    Conf l (Mode Sec ps) ((Frame m en' F_assec_ret tr)::s)
           (update_env en x V_unit) (T_exp e) (hide [])

val step_assec_ret: c:config{is_value c /\ is_sframe c is_F_assec_ret}
                   -> Tot config
let step_assec_ret (Conf l _ ((Frame m en F_assec_ret tr)::s) _ t tr') =
  let tr' =
    if m_of_mode m = Par then concat_traces tr (hide [ Tr_val (T_val.v t) ])
    else tr
  in
  Conf l m s en t tr'

//----- assec e1 e2 -----//

type sstep: config -> config -> Type =
  | C_aspar_ps:
    c:config{pre_easpar c} -> c':config{c' = step_aspar_e1 c}
    -> sstep c c'

  | C_aspar_e:
    c:config{is_value_ps c /\ is_sframe c is_F_aspar_ps}
    -> c':config{c' = step_aspar_e2 c}
    -> sstep c c'
    
  | C_aspar_red:
    c:config{is_value c /\ is_sframe c is_F_aspar_e}
    -> c':config{c' = step_aspar_red c}
    -> sstep c c'

  | C_aspar_beta:
    c:config{not (pre_aspar c = NA)} -> c':config{c' = step_aspar c}
    -> sstep c c'

  | C_aspar_ret:
    c:config{is_sframe c is_F_aspar_ret /\ pre_aspar_ret c = Do}
    -> c':config{c' = step_aspar_ret c}
    -> sstep c c'
    
  | C_box_ps:
    c:config{pre_ebox c} -> c':config{c' = step_box_e1 c}
    -> sstep c c'

  | C_box_e:
    c:config{is_value_ps c /\ is_sframe c is_F_box_ps}
    -> c':config{c' = step_box_e2 c}
    -> sstep c c'

  | C_box_red:
    c:config{is_value c /\ is_sframe c is_F_box_e}
    -> c':config{c' = step_box_red c}
    -> sstep c c'

  | C_box_beta:
    c:config{pre_box c = Do} -> c':config{c' = step_box c} -> sstep c c'

  | C_unbox:
    c:config{pre_eunbox c} -> c':config{c' = step_unbox_e c} -> sstep c c'

  | C_unbox_red:
    c:config{is_value c /\ is_sframe c is_F_unbox}
    -> c':config{c' = step_unbox_red c}
    -> sstep c c'

  | C_unbox_beta:
    c:config{pre_unbox c = Do} -> c':config{c' = step_unbox c}
    -> sstep c c'

  | C_mkwire_e1:
    c:config{pre_emkwire c} -> c':config{c' = step_mkwire_e1 c}
    -> sstep c c'

  | C_mkwire_e2:
    c:config{is_value c /\ is_sframe c is_F_mkwire_ps}
    -> c':config{c' = step_mkwire_e2 c}
    -> sstep c c'

  | C_mkwire_red:
    c:config{is_value c /\ is_sframe c is_F_mkwire_e}
    -> c':config{c' = step_mkwire_red c}
    -> sstep c c'

  | C_mkwire_beta:
    c:config{pre_mkwire c = Do} -> c':config{c' = step_mkwire c}
    -> sstep c c'

  | C_projwire_p:
    c:config{pre_eprojwire c} -> c':config{c' = step_projwire_e1 c}
    -> sstep c c'

  | C_projwire_e:
    c:config{is_value_p c /\ is_sframe c is_F_projwire_p}
    -> c':config{c' = step_projwire_e2 c}
    -> sstep c c'

  | C_projwire_red:
    c:config{is_value c /\ is_sframe c is_F_projwire_e}
    -> c':config{c' = step_projwire_red c}
    -> sstep c c'

  | C_projwire_beta:
    c:config{pre_projwire c = Do} -> c':config{c' = step_projwire c}
    -> sstep c c'
   
  | C_concatwire_e1:
    c:config{pre_econcatwire c} -> c':config{c' = step_concatwire_e1 c}
    -> sstep c c'

  | C_concatwire_e2:
    c:config{is_value c /\ is_sframe c is_F_concatwire_e1}
    -> c':config{c' = step_concatwire_e2 c}
    -> sstep c c'

  | C_concatwire_red:
    c:config{is_value c /\ is_sframe c is_F_concatwire_e2}
    -> c':config{c' = step_concatwire_red c}
    -> sstep c c'

  | C_concatwire_beta:
    c:config{pre_concatwire c = Do} -> c':config{c' = step_concatwire c}
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

  | C_let_red:
    c:config{is_value c /\ is_sframe c is_F_let}
    -> c':config{c' = step_let_red c}
    -> sstep c c'

  | C_let_beta:
    c:config{pre_let c} -> c':config{c' = step_let c} -> sstep c c'

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

  | C_app_e2:
    c:config{is_value c /\ is_sframe c is_F_app_e1}
    -> c':config{c' = step_app_e2 c}
    -> sstep c c'

  | C_app_red:
    c:config{is_value c /\ is_sframe c is_F_app_e2}
    -> c':config{c' = step_app_red c}
    -> sstep c c'

  | C_app_beta:
    c:config{pre_app c} -> c':config{c' = step_app c} -> sstep c c'
   
  | C_ffi_e:
    c:config{pre_effi c} -> c':config{c' = step_ffi_e c} -> sstep c c'

  | C_ffi_l:
    c:config{is_value c /\ is_sframe c is_F_ffi}
    -> c':config{c' = step_ffi_l c} -> sstep c c'

  | C_ffi_beta:
    c:config{pre_ffi c = Do} -> c':config{c' = step_ffi c} -> sstep c c'

  | C_cond_e:
    c:config{pre_econd c} -> c':config{c' = step_cond_e c} -> sstep c c'

  | C_cond_red:
    c:config{is_value c /\ is_sframe c is_F_cond}
    -> c':config{c' = step_cond_red c}
    -> sstep c c'

  | C_cond_beta:
    c:config{pre_cond c} -> c':config{c' = step_cond c} -> sstep c c'
   
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

type slice_v_meta_inv (meta:v_meta) (smeta:v_meta) =
  (meta = Meta empty Can_b empty Can_w ==> smeta = meta) /\
  subset (Meta.bps smeta) (Meta.bps meta) /\ (Meta.cb smeta = Meta.cb meta) /\
  subset (Meta.wps smeta) (Meta.wps meta) /\ (Meta.cw smeta = Meta.cw meta)

opaque val slice_wire:
  #eps:eprins -> p:prin -> w:v_wire eps
  -> Tot (r:v_wire (intersect eps (singleton p)){select p r = select p w})
let slice_wire #eps p w =
  if mem p eps then
    update p (Some.v (select p w)) OrdMap.empty
  else OrdMap.empty

val slice_v   : #meta:v_meta -> prin -> v:value meta
                -> Tot (r:dvalue{slice_v_meta_inv meta (D_v.meta r)}) (decreases %[v])
val slice_en  : prin -> en:env -> Tot (varname -> Tot (option dvalue)) (decreases %[en])

let rec slice_v #meta p v =
  let def = D_v meta v in
  let emp = D_v (Meta empty Can_b empty Can_w) V_emp in
  match v with
    | V_prin _                  -> def
    | V_eprins _                -> def
    | V_prins _                 -> def

    | V_unit                    -> def
    | V_bool _                  -> def

    | V_opaque 'a v' m' s c sps  ->
      let Meta bps cb wps cw = m' in
      let v'' = s p v' in
      let m'' = Meta bps cb (intersect wps (singleton p)) cw in
      let _ = admitP (wps = empty ==> intersect wps (singleton p) = empty) in
      D_v m'' (V_opaque v'' m'' s c sps)

    | V_box ps v                ->
      let D_v meta' v' = if mem p ps then slice_v p v else emp in
      D_v (Meta ps Can_b (Meta.wps meta') Cannot_w) (V_box ps v')

    | V_wire eps w              -> D_v (Meta empty Can_b (intersect eps (singleton p)) Cannot_w)
                                      (V_wire (intersect eps (singleton p)) (slice_wire #eps p w))

    | V_clos en x e             -> D_v meta (V_clos (slice_en p en) x e)

    | V_fix_clos en f x e       -> D_v meta (V_fix_clos (slice_en p en) f x e)

    | V_emp_clos _ _            -> def

    | V_emp                     -> emp

and slice_en p en =
  let _ = () in
  fun x -> preceds_axiom en x;
           if en x = None then None
           else
             Some (slice_v p (D_v.v (Some.v (en x))))

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

(* TODO: FIXME: discriminators are not generated properly, they don't have index argument *)
val is_v_emp: #meta:v_meta -> v:value meta -> Tot bool
let is_v_emp #meta v = match v with
  | V_emp -> true
  | _     -> false

val is_v_prin: #meta:v_meta -> v:value meta -> Tot bool
let is_v_prin #meta v = match v with
  | V_prin _ -> true
  | _        -> false

val is_v_eprins: #meta:v_meta -> v:value meta -> Tot bool
let is_v_eprins #meta v = match v with
  | V_eprins _ -> true
  | _          -> false

val is_v_prins: #meta:v_meta -> v:value meta -> Tot bool
let is_v_prins #meta v = match v with
  | V_prins _ -> true
  | _         -> false

val is_v_unit: #meta:v_meta -> v:value meta -> Tot bool
let is_v_unit #meta v = match v with
  | V_unit   -> true
  | _        -> false

val is_v_bool: #meta:v_meta -> v:value meta -> Tot bool
let is_v_bool #meta v = match v with
  | V_bool _ -> true
  | _        -> false

val is_v_opaque: #meta:v_meta -> v:value meta -> Tot bool
let is_v_opaque #meta v = match v with
  | V_opaque 'a _ _ _ _ _ -> true
  | _                    -> false

val is_v_box: #meta:v_meta -> v:value meta -> Tot bool
let is_v_box #meta v = match v with
  | V_box _ _ -> true
  | _         -> false

val is_v_wire: #meta:v_meta -> v:value meta -> Tot bool
let is_v_wire #meta v = match v with
  | V_wire _ _ -> true
  | _          -> false

val is_v_clos: #meta:v_meta -> v:value meta -> Tot bool
let is_v_clos #meta v = match v with
  | V_clos _ _ _ -> true
  | _            -> false

val is_v_fix_clos: #meta:v_meta -> v:value meta -> Tot bool
let is_v_fix_clos #meta v = match v with
  | V_fix_clos _ _ _ _ -> true
  | _                  -> false

val is_v_emp_clos: #meta:v_meta -> v:value meta -> Tot bool
let is_v_emp_clos #meta v = match v with
  | V_emp_clos _ _ -> true
  | _              -> false

type compose_fn_wrapper =
  | Mk_c_w: ('a -> 'a -> Tot 'a) -> compose_fn_wrapper

val compose_vals: #m1:v_meta -> #m2:v_meta -> v1:value m1 -> v2:value m2
                 -> Tot (r:dvalue{compose_v_meta_inv m1 m2 (D_v.meta r)})
                    (decreases %[v1])
val compose_envs: en:env -> env -> Tot (varname -> Tot (option dvalue)) (decreases %[en])

let rec compose_vals #m1 #m2 v1 v2 =
 if is_v_emp v1 then D_v m2 v2
 else if is_v_emp v2 then D_v m1 v1
 else
   let emp = D_v (Meta empty Can_b empty Can_w) V_emp in
   match v1 with
     | V_prin _
     | V_eprins _
     | V_prins _
     | V_unit
     | V_bool _ -> D_v m1 v1

     | V_opaque 'a v1 m1 s1 c1 sps1 ->
       if is_v_opaque v2 then
	 let V_opaque 'b v2 m2 s2 c2 sps2 = v2 in
	 let c1' = Mk_c_w c1 in
	 let c2' = Mk_c_w c2 in
	 if verified_eq c1' c2' then
	   let v' = c1 v1 v2 in
	   let m' = compose_opaque_meta m1 m2 in
	   D_v m' (V_opaque v' m' s1 c1 sps1)
	 else emp
       else emp

     | V_box ps1 v1 ->
       if is_v_box v2 then
         let V_box ps2 v2 = v2 in
         if ps1 = ps2 then
           let D_v meta v = compose_vals v1 v2 in
           D_v (Meta ps1 Can_b (Meta.wps meta) Cannot_w) (V_box ps1 v)
         else emp
       else emp

     | V_wire eps1 w1 ->
       if is_v_wire v2 then
         let V_wire eps2 w2 = v2 in
         if intersect eps1 eps2 = empty then
           D_v (Meta empty Can_b (union eps1 eps2) Cannot_w)
               (V_wire (union eps1 eps2) (compose_wires #eps1 #eps2 w1 w2 eps1))
         else emp
       else emp

     | V_clos en1 x1 e1 ->
       if is_v_clos v2 then
         let V_clos en2 x2 e2 = v2 in
         (*if x1 = x2 && e1 = e2 then*)
           D_v m1 (V_clos (compose_envs en1 en2) x1 e1)
         (*else emp*)
       else emp

     | V_fix_clos en1 f1 x1 e1 ->
       if is_v_fix_clos v2 then
         let V_fix_clos en2 f2 x2 e2 = v2 in
         (*if f1 = f2 && x1 = x2 && e1 = e2 then*)
           D_v m1 (V_fix_clos (compose_envs en1 en2) f1 x1 e1)
         (*else emp*)
       else emp

     | V_emp_clos x1 e1 ->
       if is_v_emp_clos v2 then
         let V_emp_clos x2 e2 = v2 in
         (*if x1 = x2 && e1 = e2 then*)
           D_v m1 (V_emp_clos x1 e1)
         (*else emp*)
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

opaque val slice_wire_sps:
  #eps:eprins -> ps:prins -> w:v_wire eps
  -> Tot (r:v_wire (intersect eps ps)
            {forall p. contains p r ==>
                       Some.v (select p r) = (Some.v (select p w))})
     (decreases (size ps))
let rec slice_wire_sps #eps ps w =
  let Some p = choose ps in
  let ps_rest = remove p ps in
  if ps_rest = empty then
    if mem p eps then
      update p (Some.v (select p w)) OrdMap.empty
    else OrdMap.empty
  else
    let w' = slice_wire_sps #eps ps_rest w in
    if mem p eps then
      update p (Some.v (select p w)) w'
    else w'

val slice_v_sps : #meta:v_meta -> prins -> v:value meta
                  -> Tot (r:dvalue{slice_v_meta_inv meta (D_v.meta r)})
                     (decreases %[v])
val slice_en_sps: prins -> en:env
                  -> Tot (varname -> Tot (option dvalue))
                     (decreases %[en])
let rec slice_v_sps #meta ps v =
  let def = D_v meta v in
  let emp = D_v (Meta empty Can_b empty Can_w) V_emp in
  match v with
   | V_prin _            -> def
   | V_eprins _          -> def
   | V_prins _           -> def

   | V_unit              -> def
   | V_bool _            -> def

   | V_opaque 'a v' m' s c sps  ->
     let Meta bps cb wps cw = m' in
     let v'' = sps ps v' in
     let m'' = Meta bps cb (intersect wps ps) cw in
     let _ = admitP (wps = empty ==> intersect wps ps = empty) in
     D_v m'' (V_opaque v'' m'' s c sps)

   | V_box ps' v         ->
     let D_v meta' v' =
       if intersect ps' ps = empty then emp
       else slice_v_sps ps v
     in
     D_v (Meta ps' Can_b (Meta.wps meta') Cannot_w) (V_box ps' v')
     
   | V_wire eps m        -> D_v (Meta empty Can_b (intersect eps ps) Cannot_w)
                                (V_wire (intersect eps ps) (slice_wire_sps #eps ps m))

   | V_clos en x e       -> D_v meta (V_clos (slice_en_sps ps en) x e)

   | V_fix_clos en f x e -> D_v meta (V_fix_clos (slice_en_sps ps en) f x e)

   | V_emp_clos _ _      -> def

   | V_emp               -> emp

and slice_en_sps ps en =
 let _ = () in
 fun x -> preceds_axiom en x;
          if en x = None then None
          else
            Some (slice_v_sps ps (D_v.v (Some.v (en x))))

(*
 * TODO: we should update proofs to use these functions instead
 *)
val slice_v_ffi: prin -> dvalue -> Tot dvalue
let slice_v_ffi p dv =
  let D_v meta v = dv in
  slice_v #meta p v

val compose_vals_ffi: dvalue -> dvalue -> Tot dvalue
let compose_vals_ffi dv1 dv2 =
  let D_v meta1 v1 = dv1 in
  let D_v meta2 v2 = dv2 in
  compose_vals #meta1 #meta2 v1 v2

val slice_v_sps_ffi: prins -> dvalue -> Tot dvalue
let slice_v_sps_ffi ps dv =
  let D_v meta v = dv in
  slice_v_sps #meta ps v
