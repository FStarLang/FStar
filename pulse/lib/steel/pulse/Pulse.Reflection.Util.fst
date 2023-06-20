module Pulse.Reflection.Util

module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
module RU = Pulse.RuntimeUtils
open FStar.List.Tot

let tun = R.pack_ln R.Tv_Unknown
let unit_lid = R.unit_lid
let bool_lid = R.bool_lid
let erased_lid = ["FStar"; "Ghost"; "erased"]
let hide_lid = ["FStar"; "Ghost"; "hide"]
let reveal_lid = ["FStar"; "Ghost"; "reveal"]
let vprop_lid = ["Steel"; "Effect"; "Common"; "vprop"]
let vprop_fv = R.pack_fv vprop_lid
let vprop_tm = R.pack_ln (R.Tv_FVar vprop_fv)
let unit_fv = R.pack_fv unit_lid
let unit_tm = R.pack_ln (R.Tv_FVar unit_fv)
let bool_fv = R.pack_fv bool_lid
let bool_tm = R.pack_ln (R.Tv_FVar bool_fv)

let tuple2_lid = ["FStar"; "Pervasives"; "Native"; "tuple2"]
let fst_lid = ["FStar"; "Pervasives"; "Native"; "fst"]
let snd_lid = ["FStar"; "Pervasives"; "Native"; "snd"]

let mk_tuple2 (u1 u2:R.universe) (a1 a2:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv tuple2_lid) [u1; u2]) in
  let t = pack_ln (Tv_App t (a1, Q_Explicit)) in
  pack_ln (Tv_App t (a2, Q_Explicit))

let mk_fst (u1 u2:R.universe) (a1 a2 e:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv fst_lid) [u1; u2]) in
  let t = pack_ln (Tv_App t (a1, Q_Implicit)) in
  let t = pack_ln (Tv_App t (a2, Q_Implicit)) in
  pack_ln (Tv_App t (e, Q_Explicit))
  
let mk_snd (u1 u2:R.universe) (a1 a2 e:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv snd_lid) [u1; u2]) in
  let t = pack_ln (Tv_App t (a1, Q_Implicit)) in
  let t = pack_ln (Tv_App t (a2, Q_Implicit)) in
  pack_ln (Tv_App t (e, Q_Explicit))

let true_tm = R.pack_ln (R.Tv_Const (R.C_True))
let false_tm = R.pack_ln (R.Tv_Const (R.C_False))

let emp_lid = ["Steel"; "Effect"; "Common"; "emp"]
let inames_lid = ["Steel"; "Memory"; "inames"]

let star_lid = ["Steel"; "Effect"; "Common"; "star"]

let mk_star (l r:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv star_lid)) in
  let t = pack_ln (Tv_App t (l, Q_Explicit)) in
  pack_ln (Tv_App t (r, Q_Explicit))

let pure_lid = ["Steel"; "ST"; "Util"; "pure"]
let exists_lid = ["Steel"; "ST"; "Util"; "exists_"]
let forall_lid = ["Steel"; "ST"; "Util"; "forall_"]
let args_of (tms:list R.term) =
  List.Tot.map (fun x -> x, R.Q_Explicit) tms

let mk_pure (p:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv pure_lid)) in
  pack_ln (Tv_App t (p, Q_Explicit))

let uzero = R.pack_universe (R.Uv_Zero)

let steel_wrapper = ["Pulse"; "Steel"; "Wrapper"]
let mk_steel_wrapper_lid s = steel_wrapper@[s]

let mk_squash (u:R.universe) (ty:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv R.squash_qn) [u]) in
  pack_ln (Tv_App t (ty, Q_Explicit))

let mk_eq2 (u:R.universe) (ty e1 e2:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv (mk_steel_wrapper_lid "eq2_prop")) [u]) in
  let t = pack_ln (Tv_App t (ty, Q_Implicit)) in
  let t = pack_ln (Tv_App t (e1, Q_Explicit)) in
  pack_ln (Tv_App t (e2, Q_Explicit))

let stt_admit_lid = mk_steel_wrapper_lid "stt_admit"
let mk_stt_admit (u:R.universe) (t pre post:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv stt_admit_lid) [u]) in
  let t = pack_ln (Tv_App t (t, Q_Explicit)) in
  let t = pack_ln (Tv_App t (pre, Q_Explicit)) in
  pack_ln (Tv_App t (post, Q_Explicit))

let stt_atomic_admit_lid = mk_steel_wrapper_lid "stt_atomic_admit"
let mk_stt_atomic_admit (u:R.universe) (t pre post:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv stt_atomic_admit_lid) [u]) in
  let t = pack_ln (Tv_App t (t, Q_Explicit)) in
  let t = pack_ln (Tv_App t (pre, Q_Explicit)) in
  pack_ln (Tv_App t (post, Q_Explicit))

let stt_ghost_admit_lid = mk_steel_wrapper_lid "stt_ghost_admit"
let mk_stt_ghost_admit (u:R.universe) (t pre post:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv stt_ghost_admit_lid) [u]) in
  let t = pack_ln (Tv_App t (t, Q_Explicit)) in
  let t = pack_ln (Tv_App t (pre, Q_Explicit)) in
  pack_ln (Tv_App t (post, Q_Explicit))

let emp_inames_lid = mk_steel_wrapper_lid "emp_inames"
let elim_pure_lid = mk_steel_wrapper_lid "elim_pure"

 //the thunked, value-type counterpart of the effect STT
let stt_lid = mk_steel_wrapper_lid "stt"
let stt_fv = R.pack_fv stt_lid
let stt_tm = R.pack_ln (R.Tv_FVar stt_fv)
let mk_stt_comp (u:R.universe) (res pre post:R.term) : Tot R.term =
  let t = R.pack_ln (R.Tv_UInst stt_fv [u]) in
  let t = R.pack_ln (R.Tv_App t (res, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (pre, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let stt_atomic_lid = mk_steel_wrapper_lid "stt_atomic"
let stt_atomic_fv = R.pack_fv stt_atomic_lid
let stt_atomic_tm = R.pack_ln (R.Tv_FVar stt_atomic_fv)
let mk_stt_atomic_comp (u:R.universe) (a inames pre post:R.term) =
  let t = R.pack_ln (R.Tv_UInst stt_atomic_fv [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (inames, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (pre, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let stt_ghost_lid = mk_steel_wrapper_lid "stt_ghost"
let stt_ghost_fv = R.pack_fv stt_ghost_lid
let stt_ghost_tm = R.pack_ln (R.Tv_FVar stt_ghost_fv)
let mk_stt_ghost_comp (u:R.universe) (a inames pre post:R.term) =
  let t = R.pack_ln (R.Tv_UInst stt_ghost_fv [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (inames, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (pre, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_stt_ghost_comp_post_equiv (g:R.env) (u:R.universe) (a inames pre post1 post2:R.term)
  (posts_equiv:RT.equiv g post1 post2)
  : RT.equiv g (mk_stt_ghost_comp u a inames pre post1)
               (mk_stt_ghost_comp u a inames pre post2) =
  let open R in
  let open RT in
  let t = R.pack_ln (R.Tv_UInst stt_ghost_fv [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (inames, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (pre, R.Q_Explicit)) in
  EQ_Ctxt g post1 post2
    (Ctxt_app_arg t Q_Explicit Ctxt_hole)
    posts_equiv

let mk_total t = R.C_Total t
let binder_of_t_q t q = RT.binder_of_t_q t q
let binder_of_t_q_s (t:R.term) (q:R.aqualv) (s:RT.pp_name_t) = RT.mk_binder s t q
let bound_var i : R.term = RT.bound_var i
let mk_name i : R.term = R.pack_ln (R.Tv_Var (R.pack_namedv (RT.make_namedv i)))

let arrow_dom = (R.term & R.aqualv)
let mk_arrow (f:arrow_dom) (out:R.term) : R.term =
  let ty, q = f in
  R.pack_ln (R.Tv_Arrow (binder_of_t_q ty q) (R.pack_comp (mk_total out)))
let mk_arrow_with_name (s:RT.pp_name_t) (f:arrow_dom) (out:R.term) : R.term =
  let ty, q = f in
  R.pack_ln (R.Tv_Arrow (binder_of_t_q_s ty q s) (R.pack_comp (mk_total out)))
let mk_abs ty qual t : R.term = RT.mk_abs ty qual t
let mk_abs_with_name s ty qual t : R.term =  R.pack_ln (R.Tv_Abs (binder_of_t_q_s ty qual s) t)
let mk_abs_with_name_and_range s r ty qual t : R.term = 
  let b = (binder_of_t_q_s ty qual s) in
  let b = RU.binder_set_range b r in
  R.pack_ln (R.Tv_Abs b t)
  
let mk_erased (u:R.universe) (t:R.term) : R.term =
  let hd = R.pack_ln (R.Tv_UInst (R.pack_fv erased_lid) [u]) in
  R.pack_ln (R.Tv_App hd (t, R.Q_Explicit))

let mk_reveal (u:R.universe) (t:R.term) (e:R.term) : R.term =
  let hd = R.pack_ln (R.Tv_UInst (R.pack_fv reveal_lid) [u]) in
  let hd = R.pack_ln (R.Tv_App hd (t, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App hd (e, R.Q_Explicit))

let elim_exists_lid = mk_steel_wrapper_lid "elim_exists"
let intro_exists_lid = mk_steel_wrapper_lid "intro_exists"
let intro_exists_erased_lid = mk_steel_wrapper_lid "intro_exists_erased"

let mk_exists (u:R.universe) (a p:R.term) =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv exists_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App t (p, R.Q_Explicit))

let mk_forall (u:R.universe) (a p:R.term) =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv forall_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App t (p, R.Q_Explicit))

let mk_elim_exists (u:R.universe) (a p:R.term) : R.term =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv elim_exists_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App t (p, R.Q_Explicit))

let mk_intro_exists (u:R.universe) (a p:R.term) (e:R.term) : R.term =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv intro_exists_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (p, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (e, R.Q_Explicit))

let mk_intro_exists_erased (u:R.universe) (a p:R.term) (e:R.term) : R.term =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv intro_exists_erased_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (p, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (e, R.Q_Explicit))

let while_lid = mk_steel_wrapper_lid "while_loop"

let mk_while (inv cond body:R.term) : R.term =
  let t = R.pack_ln (R.Tv_FVar (R.pack_fv while_lid)) in
  let t = R.pack_ln (R.Tv_App t (inv, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (cond, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (body, R.Q_Explicit))

let vprop_eq_tm t1 t2 =
  let open R in
  let u2 =
    pack_universe (Uv_Succ (pack_universe (Uv_Succ (pack_universe Uv_Zero)))) in
  let t = pack_ln (Tv_UInst (pack_fv eq2_qn) [u2]) in
  let t = pack_ln (Tv_App t (pack_ln (Tv_FVar (pack_fv vprop_lid)), Q_Implicit)) in
  let t = pack_ln (Tv_App t (t1, Q_Explicit)) in
  let t = pack_ln (Tv_App t (t2, Q_Explicit)) in
  t

let emp_inames_tm : R.term = R.pack_ln (R.Tv_FVar (R.pack_fv emp_inames_lid))

let non_informative_witness_lid = mk_steel_wrapper_lid "non_informative_witness"
let non_informative_witness_rt (u:R.universe) (a:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv non_informative_witness_lid) [u]) in
  let t = pack_ln (Tv_App t (a, Q_Explicit)) in
  t


let stt_vprop_equiv_fv =
  R.pack_fv (mk_steel_wrapper_lid "vprop_equiv")
let stt_vprop_equiv_tm =
  R.pack_ln (R.Tv_FVar stt_vprop_equiv_fv)
let stt_vprop_equiv (t1 t2:R.term) =
  let open R in
		let t = pack_ln (Tv_App stt_vprop_equiv_tm (t1, Q_Explicit)) in
		pack_ln (Tv_App t (t2, Q_Explicit))

let return_stt_lid = mk_steel_wrapper_lid "return_stt"
let return_stt_noeq_lid = mk_steel_wrapper_lid "return"
let return_stt_atomic_lid = mk_steel_wrapper_lid "return_stt_atomic"
let return_stt_atomic_noeq_lid = mk_steel_wrapper_lid "return_stt_atomic_noeq"
let return_stt_ghost_lid = mk_steel_wrapper_lid "return_stt_ghost"
let return_stt_ghost_noeq_lid = mk_steel_wrapper_lid "return_stt_ghost_noeq"

let mk_stt_return (u:R.universe) (ty:R.term) (t:R.term) (post:R.term)
  : R.term =
  
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv return_stt_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (ty, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (t, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_stt_return_noeq (u:R.universe) (ty:R.term) (t:R.term) (post:R.term)
  : R.term =
  
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv return_stt_noeq_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (ty, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (t, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_stt_atomic_return (u:R.universe) (ty:R.term) (t:R.term) (post:R.term)
  : R.term =
  
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv return_stt_atomic_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (ty, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (t, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_stt_atomic_return_noeq (u:R.universe) (ty:R.term) (t:R.term) (post:R.term)
  : R.term =
  
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv return_stt_atomic_noeq_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (ty, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (t, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_stt_ghost_return (u:R.universe) (ty:R.term) (t:R.term) (post:R.term)
  : R.term =
  
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv return_stt_ghost_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (ty, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (t, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_stt_ghost_return_noeq (u:R.universe) (ty:R.term) (t:R.term) (post:R.term)
  : R.term =
  
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv return_stt_ghost_noeq_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (ty, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (t, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

// Wrapper.lift_stt_atomic<u> #a #pre #post e
let mk_lift_atomic_stt (u:R.universe) (a pre post e:R.term)  =
  let open R in
  let lid = mk_steel_wrapper_lid "lift_stt_atomic" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

// Wrapper.lift_stt_ghost<u> #a #opened #pre #post e reveal_a
let mk_lift_ghost_atomic (u:R.universe) (a opened pre post e reveal_a:R.term) =
  let open R in
  let lid = mk_steel_wrapper_lid "lift_stt_ghost" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (e, Q_Explicit)) in
  pack_ln (R.Tv_App t (reveal_a, Q_Explicit))

// Wrapper.bind_stt<u1, u2> #a #b #pre1 #post1 #post2 e1 e2
let mk_bind_stt
  (u1 u2:R.universe)
  (ty1 ty2:R.term)
  (pre1 post1: R.term)
  (post2: R.term)
  (t1 t2:R.term) 
  : R.term
  = let bind_lid = mk_steel_wrapper_lid "bind_stt" in
    let head = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid) [u1;u2]) in
    R.mk_app
      (R.mk_app
        (R.mk_app
          (R.mk_app 
            (R.mk_app 
              (R.mk_app 
                (R.mk_app head
                          [(ty1, R.Q_Implicit)])
                [(ty2, R.Q_Implicit)])
              [(pre1, R.Q_Implicit)])
            [(post1, R.Q_Implicit)])
          [(post2, R.Q_Implicit)])
        [(t1, R.Q_Explicit)])
      [(t2, R.Q_Explicit)]

// Wrapper.bind_sttg<u1, u2> #a #b #opened #pre1 #post1 #post2 e1 e2
let mk_bind_ghost
  (u1 u2:R.universe)
  (a b opened pre1 post1 post2 e1 e2:R.term) =
  let open R in
  let bind_lid = mk_steel_wrapper_lid "bind_sttg" in
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid) [u1;u2]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (b, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (e1, Q_Explicit)) in
  pack_ln (R.Tv_App t (e2, Q_Explicit))

// Wrapper.bind_stt_ghost_atomic<u1, u2> #a #b #opened #pre1 #post1 #post2 e1 e2 reveal_a
let mk_bind_ghost_atomic
  (u1 u2:R.universe)
  (a b opened pre1 post1 post2 e1 e2 reveal_a:R.term) =
  let open R in
  let bind_lid = mk_steel_wrapper_lid "bind_stt_ghost_atomic" in
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid) [u1;u2]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (b, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (e1, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (e2, Q_Explicit)) in
  pack_ln (R.Tv_App t (reveal_a, Q_Explicit))

// Wrapper.bind_stt_atomic_ghost<u1, u2> #a #b #opened #pre1 #post1 #post2 e1 e2 reveal_b
let mk_bind_atomic_ghost
  (u1 u2:R.universe)
  (a b opened pre1 post1 post2 e1 e2 reveal_b:R.term) =
  let open R in
  let bind_lid = mk_steel_wrapper_lid "bind_stt_atomic_ghost" in
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid) [u1;u2]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (b, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (e1, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (e2, Q_Explicit)) in
  pack_ln (R.Tv_App t (reveal_b, Q_Explicit))

// Wrapper.frame_stt<u> #ty #pre #post frame t
let mk_frame_stt
  (u:R.universe)
  (ty:R.term)
  (pre: R.term)
  (post: R.term)
  (frame: R.term)
  (t:R.term) 
  : R.term
  = let frame_lid = mk_steel_wrapper_lid "frame_stt" in
    let frame_fv = R.pack_fv frame_lid in
    let frame_univ_inst u = R.pack_ln (R.Tv_UInst (R.pack_fv frame_lid) [u]) in
    let head = frame_univ_inst u in
    R.mk_app
      (R.mk_app
        (R.mk_app
          (R.mk_app
            (R.mk_app head [(ty, R.Q_Implicit)])
            [(pre, R.Q_Implicit)])
          [(post, R.Q_Implicit)])
        [(frame, R.Q_Explicit)])
      [(t, R.Q_Explicit)]

// Wrapper.frame_stt_atomic<u> #a #opened #pre #post frame e
let mk_frame_stt_atomic (u:R.universe) (a opened pre post frame e:R.term)  =
  let open R in
  let lid = mk_steel_wrapper_lid "frame_stt_atomic" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (frame, Q_Explicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

// Wrapper.frame_stt_ghost<u> #a #opened #pre #post frame e
let mk_frame_stt_ghost (u:R.universe) (a opened pre post frame e:R.term)  =
  let open R in
  let lid = mk_steel_wrapper_lid "frame_stt_ghost" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (frame, Q_Explicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

// Wrapper.sub_stt<u> #ty #pre1 pre2 #post1 post2 () () e
let mk_sub_stt
  (u:R.universe)
  (ty:R.term)
  (pre1 pre2: R.term)
  (post1 post2: R.term)
  (t:R.term) 
  : R.term
  = let subsumption_lid = mk_steel_wrapper_lid "sub_stt" in
    let subsumption_fv = R.pack_fv subsumption_lid in
    let subsumption_univ_inst u = R.pack_ln (R.Tv_UInst subsumption_fv [u]) in
    let head = subsumption_univ_inst u in
    R.mk_app
     (R.mk_app 
      (R.mk_app
        (R.mk_app
          (R.mk_app
            (R.mk_app
              (R.mk_app 
                 (R.mk_app head [(ty, R.Q_Implicit)])
                 [(pre1, R.Q_Implicit)])
              [(pre2, R.Q_Explicit)])
            [(post1, R.Q_Implicit)])
          [(post2, R.Q_Explicit)])
        [(`(), R.Q_Explicit)])
      [(`(), R.Q_Explicit)])
     [(t, R.Q_Explicit)]

// Wrapper.sub_stt_atomic<u> #a #opened #pre1 pre2 #post1 post2 () () e
let mk_sub_stt_atomic (u:R.universe) (a opened pre1 pre2 post1 post2 e:R.term)  =
  let open R in
  let lid = mk_steel_wrapper_lid "sub_stt_atomic" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre2, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (`(), Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (`(), Q_Explicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

// Wrapper.sub_stt_ghost<u> #a #opened #pre1 pre2 #post1 post2 () () e
let mk_sub_stt_ghost (u:R.universe) (a opened pre1 pre2 post1 post2 e:R.term)  =
  let open R in
  let lid = mk_steel_wrapper_lid "sub_stt_ghost" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre2, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (`(), Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (`(), Q_Explicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

let mk_par (u:R.universe) (aL aR preL postL preR postR eL eR:R.term) =
  let open R in
  let lid = mk_steel_wrapper_lid "stt_par" in
  let t = pack_ln (Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (Tv_App t (aL, Q_Implicit)) in
  let t = pack_ln (Tv_App t (aR, Q_Implicit)) in
  let t = pack_ln (Tv_App t (preL, Q_Implicit)) in
  let t = pack_ln (Tv_App t (postL, Q_Implicit)) in
  let t = pack_ln (Tv_App t (preR, Q_Implicit)) in
  let t = pack_ln (Tv_App t (postR, Q_Implicit)) in
  let t = pack_ln (Tv_App t (eL, Q_Explicit)) in
  pack_ln (Tv_App t (eR, Q_Explicit))

let mk_rewrite (p q:R.term) =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv (mk_steel_wrapper_lid "rewrite"))) in
  let t = pack_ln (Tv_App t (p, Q_Explicit)) in
  let t = pack_ln (Tv_App t (q, Q_Explicit)) in
  pack_ln (Tv_App t (`(), Q_Explicit))


let mk_withlocal (ret_u:R.universe) (a init pre ret_t post body:R.term) =
  let open R in
  let lid = mk_steel_wrapper_lid "with_local" in
  let t = pack_ln (Tv_UInst (R.pack_fv lid) [ret_u]) in
  let t = pack_ln (Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (Tv_App t (init, Q_Explicit)) in
  let t = pack_ln (Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (Tv_App t (ret_t, Q_Implicit)) in
  let t = pack_ln (Tv_App t (post, Q_Implicit)) in
  pack_ln (Tv_App t (body, Q_Explicit))

///// Utils to derive equiv for common constructs /////
let mk_star_equiv (g:R.env) (t1 t2 t3 t4:R.term)
  (eq1:RT.equiv g t1 t3)
  (eq2:RT.equiv g t2 t4)
  : RT.equiv g (mk_star t1 t2) (mk_star t3 t4) =
  
  admit ()

let mk_stt_comp_equiv (g:R.env) (u:R.universe) (res pre1 post1 pre2 post2:R.term)
  (pre_eq:RT.equiv g pre1 pre2)
  (post_eq:RT.equiv g post1 post2)
  : RT.equiv g (mk_stt_comp u res pre1 post1)
               (mk_stt_comp u res pre2 post2)
  = admit ()

let mk_stt_atomic_comp_equiv (g:R.env) (u:R.universe) (res inames pre1 post1 pre2 post2:R.term)
  (pre_eq:RT.equiv g pre1 pre2)
  (post_eq:RT.equiv g post1 post2)
  : RT.equiv g (mk_stt_atomic_comp u res inames pre1 post1)
               (mk_stt_atomic_comp u res inames pre2 post2)
  = admit ()

let mk_stt_ghost_comp_equiv (g:R.env) (u:R.universe) (res inames pre1 post1 pre2 post2:R.term)
  (pre_eq:RT.equiv g pre1 pre2)
  (post_eq:RT.equiv g post1 post2)
  : RT.equiv g (mk_stt_ghost_comp u res inames pre1 post1)
               (mk_stt_ghost_comp u res inames pre2 post2)
  = admit ()

let ref_lid = ["Steel"; "ST"; "Reference"; "ref"]
let pts_to_lid = ["Steel"; "ST"; "Reference"; "pts_to"]
let full_perm_lid = ["Steel"; "FractionalPermission"; "full_perm"]

let mk_ref (a:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv ref_lid)) in
  pack_ln (Tv_App t (a, Q_Explicit))

let mk_pts_to (a:R.term) (r:R.term) (perm:R.term) (v:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv pts_to_lid)) in
  let t = pack_ln (Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (Tv_App t (r, Q_Explicit)) in
  let t = pack_ln (Tv_App t (perm, Q_Explicit)) in
  pack_ln (Tv_App t (v, Q_Explicit))

let full_perm_tm : R.term =
  let open R in
  pack_ln (Tv_FVar (pack_fv full_perm_lid))
