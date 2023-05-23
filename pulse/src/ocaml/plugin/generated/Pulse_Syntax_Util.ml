open Prims
let op_let_Question :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      ('a -> 'b FStar_Pervasives_Native.option) ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun g ->
      match f with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x -> g x
let (is_var :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.nm FStar_Pervasives_Native.option)
  =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_FStar (host_term, r) ->
        (match FStar_Reflection_Builtins.inspect_ln host_term with
         | FStar_Reflection_Data.Tv_Var bv ->
             let bv_view = FStar_Reflection_Builtins.inspect_bv bv in
             FStar_Pervasives_Native.Some
               {
                 Pulse_Syntax_Base.nm_index =
                   (bv_view.FStar_Reflection_Data.bv_index);
                 Pulse_Syntax_Base.nm_ppname =
                   (bv_view.FStar_Reflection_Data.bv_ppname);
                 Pulse_Syntax_Base.nm_range = r
               }
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (is_fvar :
  Pulse_Syntax_Base.term ->
    (FStar_Reflection_Types.name * Pulse_Syntax_Base.universe Prims.list)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_FStar (host_term, uu___) ->
        (match FStar_Reflection_Builtins.inspect_ln host_term with
         | FStar_Reflection_Data.Tv_FVar fv ->
             FStar_Pervasives_Native.Some
               ((FStar_Reflection_Builtins.inspect_fv fv), [])
         | FStar_Reflection_Data.Tv_UInst (fv, us) ->
             FStar_Pervasives_Native.Some
               ((FStar_Reflection_Builtins.inspect_fv fv), us)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (is_fvar_app :
  Pulse_Syntax_Base.term ->
    (FStar_Reflection_Types.name * Pulse_Syntax_Base.universe Prims.list *
      Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option *
      Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match is_fvar t with
    | FStar_Pervasives_Native.Some (l, us) ->
        FStar_Pervasives_Native.Some
          (l, us, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
    | FStar_Pervasives_Native.None ->
        (match t with
         | Pulse_Syntax_Base.Tm_PureApp (head, q, arg) ->
             (match is_fvar head with
              | FStar_Pervasives_Native.Some (l, us) ->
                  FStar_Pervasives_Native.Some
                    (l, us, q, (FStar_Pervasives_Native.Some arg))
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
         | uu___ -> FStar_Pervasives_Native.None)
let (is_arrow :
  Pulse_Syntax_Base.term ->
    (Pulse_Syntax_Base.binder * Pulse_Syntax_Base.qualifier
      FStar_Pervasives_Native.option * Pulse_Syntax_Base.comp)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_FStar (host_term, uu___) ->
        (match FStar_Reflection_Builtins.inspect_ln host_term with
         | FStar_Reflection_Data.Tv_Arrow (b, c) ->
             let uu___1 = FStar_Reflection_Builtins.inspect_binder b in
             (match uu___1 with
              | { FStar_Reflection_Data.binder_bv = binder_bv;
                  FStar_Reflection_Data.binder_qual = binder_qual;
                  FStar_Reflection_Data.binder_attrs = uu___2;
                  FStar_Reflection_Data.binder_sort = binder_sort;_} ->
                  (match binder_qual with
                   | FStar_Reflection_Data.Q_Meta uu___3 ->
                       FStar_Pervasives_Native.None
                   | uu___3 ->
                       let q = Pulse_Readback.readback_qual binder_qual in
                       let bv_view =
                         FStar_Reflection_Builtins.inspect_bv binder_bv in
                       let c_view = FStar_Reflection_Builtins.inspect_comp c in
                       (match c_view with
                        | FStar_Reflection_Data.C_Total c_t ->
                            op_let_Question
                              (Pulse_Readback.readback_ty binder_sort)
                              (fun binder_ty ->
                                 op_let_Question
                                   (match Pulse_Readback.readback_comp c_t
                                    with
                                    | FStar_Pervasives_Native.Some c1 ->
                                        FStar_Pervasives_Native.Some c1
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Pervasives_Native.None)
                                   (fun c1 ->
                                      FStar_Pervasives_Native.Some
                                        ({
                                           Pulse_Syntax_Base.binder_ty =
                                             binder_ty;
                                           Pulse_Syntax_Base.binder_ppname =
                                             (bv_view.FStar_Reflection_Data.bv_ppname)
                                         }, q, c1)))
                        | uu___4 -> FStar_Pervasives_Native.None)))
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None