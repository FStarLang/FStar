open Prims
type ('g, 'gu, 'ss) well_typed_ss = unit
let (psubst_env :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      unit Pulse_Prover_Substs.t -> Pulse_Typing_Env.env)
  =
  fun g0 ->
    fun g ->
      fun ss ->
        Pulse_Typing_Metatheory.subst_env g
          (Pulse_Prover_Substs.as_subst g0 ss)
type ('g1, 'g2) subenv = unit
let rec (filter_ss :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      unit Pulse_Prover_Substs.t -> Pulse_Typing_Env.env)
  =
  fun g0 ->
    fun g ->
      fun ss ->
        match Pulse_Typing_Env.bindings g with
        | [] -> Pulse_Typing_Env.mk_env (Pulse_Typing_Env.fstar_env g)
        | uu___ ->
            let uu___1 = Pulse_Typing_Env.remove_latest_binding g in
            (match uu___1 with
             | (x, t, g1) ->
                 let g2 = filter_ss g0 g1 ss in
                 if FStar_Set.mem x (Pulse_Prover_Substs.dom g0 ss)
                 then g2
                 else
                   Pulse_Typing_Env.push_binding g2 x
                     Pulse_Syntax_Base.ppname_default t)
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
let rec (apply_partial_psubs_aux :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        Pulse_Typing_Env.env ->
          unit Pulse_Prover_Substs.t ->
            unit Pulse_Prover_Substs.t ->
              unit Pulse_Prover_Substs.t ->
                Pulse_Typing_Env.env ->
                  Pulse_Typing_Env.env ->
                    Pulse_Typing_Env.env ->
                      (unit, unit, unit) Pulse_Typing.st_typing ->
                        (Pulse_Typing_Env.env,
                          (unit, unit, unit) Pulse_Typing.st_typing)
                          Prims.dtuple2)
  =
  fun g0 ->
    fun t ->
      fun c ->
        fun uvs ->
          fun ss ->
            fun ss_consumed ->
              fun ss_remaining ->
                fun uvs_seen ->
                  fun uvs_remaining ->
                    fun uvs_unresolved ->
                      fun t_typing ->
                        match Pulse_Typing_Env.bindings uvs_remaining with
                        | [] -> Prims.Mkdtuple2 (uvs_unresolved, t_typing)
                        | uu___ ->
                            let uu___1 =
                              Pulse_Typing_Env.remove_binding uvs_remaining in
                            (match uu___1 with
                             | (x, ty, uvs_remaining_new) ->
                                 let g_x_t =
                                   Pulse_Typing_Env.push_binding_def
                                     (Pulse_Typing_Env.mk_env
                                        (Pulse_Typing_Env.fstar_env
                                           uvs_remaining)) x ty in
                                 let uvs_seen_new =
                                   Pulse_Typing_Env.push_binding_def uvs_seen
                                     x ty in
                                 if
                                   Prims.op_Negation
                                     (FStar_Set.mem x
                                        (Pulse_Prover_Substs.dom g0
                                           ss_remaining))
                                 then
                                   let uvs_unresolved_new =
                                     Pulse_Typing_Env.push_binding_def
                                       uvs_unresolved x ty in
                                   let t_typing1 = coerce_eq t_typing () in
                                   apply_partial_psubs_aux g0 t c uvs ss
                                     ss_consumed ss_remaining uvs_seen_new
                                     uvs_remaining_new uvs_unresolved_new
                                     t_typing1
                                 else
                                   (let e =
                                      Pulse_Prover_Substs.lookup g0
                                        ss_remaining x in
                                    let g_x_ss_t =
                                      Pulse_Typing_Env.push_binding_def
                                        (Pulse_Typing_Env.mk_env
                                           (Pulse_Typing_Env.fstar_env
                                              uvs_remaining)) x
                                        (Pulse_Prover_Substs.subst_term g0
                                           ss_consumed ty) in
                                    let s_x_e =
                                      Pulse_Prover_Substs.singleton g0 x e in
                                    let t_typing1 =
                                      Pulse_Typing_Metatheory.st_typing_subst
                                        (Pulse_Typing_Env.push_env g0
                                           (psubst_env g0 uvs_unresolved
                                              ss_consumed)) x
                                        (Pulse_Prover_Substs.subst_term g0
                                           ss_consumed ty)
                                        (psubst_env g0 uvs_remaining_new
                                           ss_consumed) e ()
                                        (Pulse_Prover_Substs.subst_st_term g0
                                           ss_consumed t)
                                        (Pulse_Prover_Substs.subst_comp g0
                                           ss_consumed c)
                                        (coerce_eq t_typing ()) in
                                    let ss_consumed_new =
                                      Pulse_Prover_Substs.push g0 ss_consumed
                                        s_x_e in
                                    let t_typing2 = coerce_eq t_typing1 () in
                                    let t_typing3 = coerce_eq t_typing2 () in
                                    let ss_remaining_new =
                                      Pulse_Prover_Substs.diff g0
                                        ss_remaining s_x_e in
                                    apply_partial_psubs_aux g0 t c uvs ss
                                      ss_consumed_new ss_remaining_new
                                      uvs_seen_new uvs_remaining_new
                                      uvs_unresolved t_typing3))
let (apply_partial_subs :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        Pulse_Typing_Env.env ->
          unit Pulse_Prover_Substs.t ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              (Pulse_Typing_Env.env,
                (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2)
  =
  fun g0 ->
    fun t ->
      fun c ->
        fun uvs ->
          fun ss ->
            fun t_typing ->
              let ss_consumed = Pulse_Prover_Substs.empty g0 in
              let ss_remaining = ss in
              let uvs_seen =
                Pulse_Typing_Env.mk_env (Pulse_Typing_Env.fstar_env uvs) in
              let uvs_remaining = uvs in
              let uvs_unresolved =
                Pulse_Typing_Env.mk_env (Pulse_Typing_Env.fstar_env uvs) in
              apply_partial_psubs_aux g0 t c uvs ss ss_consumed ss_remaining
                uvs_seen uvs_remaining uvs_unresolved t_typing
let (apply_partial_subs_veq :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Typing_Env.env ->
          unit Pulse_Prover_Substs.t ->
            unit -> (Pulse_Typing_Env.env, unit) Prims.dtuple2)
  =
  fun g0 ->
    fun p1 -> fun p2 -> fun uvs -> fun ss -> fun veq -> Prims.admit ()
let (ghost_comp :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.vprop -> Pulse_Syntax_Base.comp_st)
  =
  fun pre ->
    fun post ->
      Pulse_Syntax_Base.C_STGhost
        (Pulse_Syntax_Base.tm_emp_inames,
          {
            Pulse_Syntax_Base.u = Pulse_Syntax_Pure.u_zero;
            Pulse_Syntax_Base.res = Pulse_Typing.tm_unit;
            Pulse_Syntax_Base.pre = pre;
            Pulse_Syntax_Base.post = post
          })
let (idem_steps :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      (Pulse_Syntax_Base.st_term, (unit, unit, unit) Pulse_Typing.st_typing)
        Prims.dtuple2)
  = fun g -> fun ctxt -> Prims.admit ()