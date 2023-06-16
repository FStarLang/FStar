open Prims
type ('g, 'c) comp_typing_u = (unit, unit, unit) Pulse_Typing.comp_typing
let (admit_st_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_comp -> (unit, unit) Pulse_Typing.st_comp_typing)
  =
  fun g ->
    fun st ->
      Pulse_Typing.STC (g, st, (Pulse_Typing_Env.fresh g), (), (), ())
let (admit_comp_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st -> (unit, unit) comp_typing_u)
  =
  fun g ->
    fun c ->
      match c with
      | Pulse_Syntax_Base.C_ST st ->
          Pulse_Typing.CT_ST (g, st, (admit_st_comp_typing g st))
      | Pulse_Syntax_Base.C_STAtomic (inames, st) ->
          Pulse_Typing.CT_STAtomic
            (g, inames, st, (), (admit_st_comp_typing g st))
      | Pulse_Syntax_Base.C_STGhost (inames, st) ->
          Pulse_Typing.CT_STGhost
            (g, inames, st, (), (admit_st_comp_typing g st))
let (st_typing_correctness :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (unit, unit) comp_typing_u)
  = fun g -> fun t -> fun c -> fun uu___ -> admit_comp_typing g c
let (add_frame_well_typed :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) comp_typing_u ->
        Pulse_Syntax_Base.term -> unit -> (unit, unit) comp_typing_u)
  =
  fun g ->
    fun c ->
      fun ct ->
        fun f -> fun ft -> admit_comp_typing g (Pulse_Typing.add_frame c f)
let (comp_typing_inversion :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.comp_st ->
      (unit, unit) comp_typing_u -> (unit, unit) Pulse_Typing.st_comp_typing)
  =
  fun g ->
    fun c ->
      fun ct ->
        match ct with
        | Pulse_Typing.CT_ST (uu___, uu___1, st) -> st
        | Pulse_Typing.CT_STAtomic (uu___, uu___1, uu___2, uu___3, st) -> st
        | Pulse_Typing.CT_STGhost (uu___, uu___1, uu___2, uu___3, st) -> st
type ('x, 'g, 'vars) fresh_wrt = unit
let (st_comp_typing_inversion_cofinite :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_comp ->
      (unit, unit) Pulse_Typing.st_comp_typing -> (unit * unit * unit))
  = fun g -> fun st -> fun ct -> ((), (), ())
let (st_comp_typing_inversion :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_comp ->
      (unit, unit) Pulse_Typing.st_comp_typing ->
        (unit, unit, Pulse_Syntax_Base.var, unit) FStar_Pervasives.dtuple4)
  =
  fun g ->
    fun st ->
      fun ct ->
        let uu___ = ct in
        match uu___ with
        | Pulse_Typing.STC (g1, st1, x, ty, pre, post) ->
            FStar_Pervasives.Mkdtuple4 ((), (), x, ())
let (tm_exists_inversion :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          unit -> Pulse_Syntax_Base.var -> (unit * unit))
  = fun g -> fun u -> fun ty -> fun p -> fun uu___ -> fun x -> ((), ())


let (comp_st_with_post :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp_st)
  =
  fun c ->
    fun post ->
      match c with
      | Pulse_Syntax_Base.C_ST st ->
          Pulse_Syntax_Base.C_ST
            {
              Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
              Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
              Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
              Pulse_Syntax_Base.post = post
            }
      | Pulse_Syntax_Base.C_STGhost (i, st) ->
          Pulse_Syntax_Base.C_STGhost
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
                Pulse_Syntax_Base.post = post
              })
      | Pulse_Syntax_Base.C_STAtomic (i, st) ->
          Pulse_Syntax_Base.C_STAtomic
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
                Pulse_Syntax_Base.post = post
              })
let (comp_st_with_pre :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp_st)
  =
  fun c ->
    fun pre ->
      match c with
      | Pulse_Syntax_Base.C_ST st ->
          Pulse_Syntax_Base.C_ST
            {
              Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
              Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
              Pulse_Syntax_Base.pre = pre;
              Pulse_Syntax_Base.post = (st.Pulse_Syntax_Base.post)
            }
      | Pulse_Syntax_Base.C_STGhost (i, st) ->
          Pulse_Syntax_Base.C_STGhost
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = pre;
                Pulse_Syntax_Base.post = (st.Pulse_Syntax_Base.post)
              })
      | Pulse_Syntax_Base.C_STAtomic (i, st) ->
          Pulse_Syntax_Base.C_STAtomic
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = pre;
                Pulse_Syntax_Base.post = (st.Pulse_Syntax_Base.post)
              })
type ('g, 't, 'p1, 'p2) vprop_equiv_x = unit
let (st_typing_equiv_post :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term ->
            unit -> (unit, unit, unit) Pulse_Typing.st_typing)
  = fun g -> fun t -> fun c -> fun d -> fun post -> fun veq -> Prims.admit ()
let (st_typing_equiv_pre :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term ->
            unit -> (unit, unit, unit) Pulse_Typing.st_typing)
  = fun g -> fun t -> fun c -> fun d -> fun pre -> fun veq -> Prims.admit ()
let map_opt :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun x ->
      match x with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x1 ->
          FStar_Pervasives_Native.Some (f x1)
let (subst_flip :
  Pulse_Syntax_Naming.subst ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  = fun ss -> fun t -> Pulse_Syntax_Naming.subst_term t ss
let (subst_env :
  Pulse_Typing_Env.env -> Pulse_Syntax_Naming.subst -> Pulse_Typing_Env.env)
  = fun en -> fun ss -> Prims.admit ()
type nt_subst = Pulse_Syntax_Naming.subst
type ('g, 'gu, 'guu) pairwise_disjoint = unit
let rec (lookup_nt_subst :
  nt_subst ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun ss ->
    fun x ->
      match ss with
      | [] -> FStar_Pervasives_Native.None
      | (Pulse_Syntax_Naming.NT (y, t))::ss1 ->
          if x = y
          then FStar_Pervasives_Native.Some t
          else lookup_nt_subst ss1 x
type ('g, 'gu, 'ss) well_typed_ss = unit
type ('ss, 'gu) ss_covers_g' = unit

let rec (st_typing_subst :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Typing_Env.env ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              nt_subst -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun g' ->
      fun g'' ->
        fun e1 ->
          fun c1 ->
            fun e1_typing ->
              fun ss ->
                match e1_typing with
                | Pulse_Typing.T_Abs
                    (uu___, x, q, b, u, body, c, b_ty_typing, body_typing) ->
                    let g1 =
                      Pulse_Typing_Env.push_binding
                        (Pulse_Typing_Env.push_env g
                           (Pulse_Typing_Env.push_env g' g'')) x
                        Pulse_Syntax_Base.ppname_default
                        (Pulse_Syntax_Naming.subst_term
                           b.Pulse_Syntax_Base.binder_ty ss) in
                    let g2 =
                      Pulse_Typing_Env.push_env g
                        (Pulse_Typing_Env.push_env g'
                           (Pulse_Typing_Env.push_binding g'' x
                              Pulse_Syntax_Base.ppname_default
                              (Pulse_Syntax_Naming.subst_term
                                 b.Pulse_Syntax_Base.binder_ty ss))) in
                    let body_typing1 =
                      st_typing_subst g g'
                        (Pulse_Typing_Env.push_binding g'' x
                           Pulse_Syntax_Base.ppname_default
                           (Pulse_Syntax_Naming.subst_term
                              b.Pulse_Syntax_Base.binder_ty ss))
                        (Pulse_Syntax_Naming.open_st_term_nv body
                           ((b.Pulse_Syntax_Base.binder_ppname), x)) c
                        body_typing ss in
                    Pulse_Typing.T_Abs
                      ((Pulse_Typing_Env.push_env g g'), x, q,
                        (Pulse_Syntax_Naming.subst_binder b ss), u,
                        (Pulse_Syntax_Naming.subst_st_term body ss),
                        (Pulse_Syntax_Naming.subst_comp c ss), (),
                        body_typing1)
                | Pulse_Typing.T_STApp
                    (uu___, head, ty, q, res, arg, head_typing, arg_typing)
                    ->
                    Pulse_Typing.T_STApp
                      ((Pulse_Typing_Env.push_env g g''),
                        (Pulse_Syntax_Naming.subst_term head ss),
                        (Pulse_Syntax_Naming.subst_term ty ss), q,
                        (Pulse_Syntax_Naming.subst_comp res ss),
                        (Pulse_Syntax_Naming.subst_term arg ss), (), ())
                | uu___ -> Prims.admit ()