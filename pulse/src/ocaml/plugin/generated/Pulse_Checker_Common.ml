open Prims
let (mk_abs :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun t ->
      FStar_Reflection_Typing.mk_abs (Pulse_Elaborate_Pure.elab_term ty)
        FStar_Reflection_Data.Q_Explicit (Pulse_Elaborate_Pure.elab_term t)
let (mk_arrow :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term -> FStar_Reflection_Types.term)
  =
  fun ty ->
    fun t ->
      FStar_Reflection_Typing.mk_arrow (Pulse_Elaborate_Pure.elab_term ty)
        FStar_Reflection_Data.Q_Explicit (Pulse_Elaborate_Pure.elab_term t)
type post_hint_t =
  {
  g: Pulse_Typing.env ;
  ret_ty: Pulse_Syntax_Base.term ;
  u: Pulse_Syntax_Base.universe ;
  ty_typing: unit ;
  post: Pulse_Syntax_Base.term ;
  post_typing: unit }
let (__proj__Mkpost_hint_t__item__g : post_hint_t -> Pulse_Typing.env) =
  fun projectee ->
    match projectee with
    | { g; ret_ty; u; ty_typing; post; post_typing;_} -> g
let (__proj__Mkpost_hint_t__item__ret_ty :
  post_hint_t -> Pulse_Syntax_Base.term) =
  fun projectee ->
    match projectee with
    | { g; ret_ty; u; ty_typing; post; post_typing;_} -> ret_ty
let (__proj__Mkpost_hint_t__item__u :
  post_hint_t -> Pulse_Syntax_Base.universe) =
  fun projectee ->
    match projectee with
    | { g; ret_ty; u; ty_typing; post; post_typing;_} -> u

let (__proj__Mkpost_hint_t__item__post :
  post_hint_t -> Pulse_Syntax_Base.term) =
  fun projectee ->
    match projectee with
    | { g; ret_ty; u; ty_typing; post; post_typing;_} -> post
type ('gu, 'g) env_extends = unit
type ('g, 'p) post_hint_for_env_p = unit
type 'g post_hint_for_env = post_hint_t
type 'g post_hint_opt = post_hint_t FStar_Pervasives_Native.option
type ('g, 'p, 'x) post_hint_typing_t =
  {
  ty_typing1: unit ;
  post_typing1: unit }


let (post_hint_typing :
  Pulse_Typing.env ->
    unit post_hint_for_env ->
      Pulse_Syntax_Base.var -> (unit, unit, unit) post_hint_typing_t)
  = fun g -> fun p -> fun x -> { ty_typing1 = (); post_typing1 = () }
let (intro_post_hint :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
      Pulse_Syntax_Base.term ->
        (unit post_hint_for_env, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ret_ty_opt ->
      fun post ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Common.fst"
             (Prims.of_int (17)) (Prims.of_int (10)) (Prims.of_int (17))
             (Prims.of_int (17)))
          (FStar_Range.mk_range "Pulse.Checker.Common.fst"
             (Prims.of_int (17)) (Prims.of_int (20)) (Prims.of_int (30))
             (Prims.of_int (109)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> Pulse_Typing.fresh g))
          (fun uu___ ->
             (fun x ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                        (Prims.of_int (19)) (Prims.of_int (6))
                        (Prims.of_int (21)) (Prims.of_int (19)))
                     (FStar_Range.mk_range "Pulse.Checker.Common.fst"
                        (Prims.of_int (22)) (Prims.of_int (4))
                        (Prims.of_int (30)) (Prims.of_int (109)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           match ret_ty_opt with
                           | FStar_Pervasives_Native.None ->
                               Pulse_Syntax_Base.Tm_FStar
                                 (FStar_Reflection_Typing.unit_ty,
                                   FStar_Range.range_0)
                           | FStar_Pervasives_Native.Some t -> t))
                     (fun uu___ ->
                        (fun ret_ty ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Common.fst"
                                   (Prims.of_int (23)) (Prims.of_int (18))
                                   (Prims.of_int (23)) (Prims.of_int (55)))
                                (FStar_Range.mk_range
                                   "Pulse.Checker.Common.fst"
                                   (Prims.of_int (22)) (Prims.of_int (4))
                                   (Prims.of_int (30)) (Prims.of_int (109)))
                                (Obj.magic
                                   (Pulse_Checker_Pure.instantiate_term_implicits
                                      g ret_ty))
                                (fun uu___ ->
                                   (fun uu___ ->
                                      match uu___ with
                                      | (ret_ty1, uu___1) ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Common.fst"
                                                  (Prims.of_int (24))
                                                  (Prims.of_int (27))
                                                  (Prims.of_int (24))
                                                  (Prims.of_int (52)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Common.fst"
                                                  (Prims.of_int (23))
                                                  (Prims.of_int (58))
                                                  (Prims.of_int (30))
                                                  (Prims.of_int (109)))
                                               (Obj.magic
                                                  (Pulse_Checker_Pure.check_universe
                                                     g ret_ty1))
                                               (fun uu___2 ->
                                                  (fun uu___2 ->
                                                     match uu___2 with
                                                     | Prims.Mkdtuple2
                                                         (u, ty_typing) ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Common.fst"
                                                                 (Prims.of_int (25))
                                                                 (Prims.of_int (32))
                                                                 (Prims.of_int (25))
                                                                 (Prims.of_int (103)))
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Checker.Common.fst"
                                                                 (Prims.of_int (24))
                                                                 (Prims.of_int (55))
                                                                 (Prims.of_int (30))
                                                                 (Prims.of_int (109)))
                                                              (Obj.magic
                                                                 (Pulse_Checker_Pure.check_vprop
                                                                    (
                                                                    Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    ret_ty1)
                                                                    g)
                                                                    (
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    post
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    x))))
                                                              (fun uu___3 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (post1,
                                                                    post_typing)
                                                                    ->
                                                                    {
                                                                    g;
                                                                    ret_ty =
                                                                    ret_ty1;
                                                                    u;
                                                                    ty_typing
                                                                    = ();
                                                                    post =
                                                                    (Pulse_Syntax_Naming.close_term
                                                                    post1 x);
                                                                    post_typing
                                                                    = ()
                                                                    }))))
                                                    uu___2))) uu___))) uu___)))
               uu___)
let (post_hint_from_comp_typing :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) Pulse_Typing_Metatheory.comp_typing_u ->
        unit post_hint_for_env)
  =
  fun g ->
    fun c ->
      fun ct ->
        let st_comp_typing =
          Pulse_Typing_Metatheory.comp_typing_inversion g c ct in
        let uu___ =
          Pulse_Typing_Metatheory.st_comp_typing_inversion g
            (Pulse_Syntax_Base.st_comp_of_comp c) st_comp_typing in
        match uu___ with
        | FStar_Pervasives.Mkdtuple4 (ty_typing, pre_typing, x, post_typing)
            ->
            let p =
              {
                g;
                ret_ty = (Pulse_Syntax_Base.comp_res c);
                u = (Pulse_Syntax_Base.comp_u c);
                ty_typing = ();
                post = (Pulse_Syntax_Base.comp_post c);
                post_typing = ()
              } in
            p
type check_t =
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit post_hint_opt ->
            ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
               (unit, unit, unit) Pulse_Typing.st_typing)
               FStar_Pervasives.dtuple3,
              unit) FStar_Tactics_Effect.tac_repr