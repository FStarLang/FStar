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
let (is_pure_app :
  Pulse_Syntax_Base.term ->
    (Pulse_Syntax_Base.term * Pulse_Syntax_Base.qualifier
      FStar_Pervasives_Native.option * Pulse_Syntax_Base.term)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_FStar (host_term, uu___) ->
        (match FStar_Reflection_Builtins.inspect_ln host_term with
         | FStar_Reflection_Data.Tv_App (hd, (arg, q)) ->
             op_let_Question
               (match Pulse_Readback.readback_ty hd with
                | FStar_Pervasives_Native.Some hd1 ->
                    FStar_Pervasives_Native.Some hd1
                | uu___1 -> FStar_Pervasives_Native.None)
               (fun hd1 ->
                  let q1 = Pulse_Readback.readback_qual q in
                  op_let_Question
                    (match Pulse_Readback.readback_ty arg with
                     | FStar_Pervasives_Native.Some arg1 ->
                         FStar_Pervasives_Native.Some arg1
                     | uu___1 -> FStar_Pervasives_Native.None)
                    (fun arg1 -> FStar_Pervasives_Native.Some (hd1, q1, arg1)))
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (leftmost_head :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_FStar (host_term, uu___) ->
        let uu___1 = FStar_Reflection_Derived.collect_app_ln host_term in
        (match uu___1 with
         | (hd, uu___2) ->
             (match Pulse_Readback.readback_ty hd with
              | FStar_Pervasives_Native.Some t1 ->
                  FStar_Pervasives_Native.Some t1
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
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
        (match is_pure_app t with
         | FStar_Pervasives_Native.Some (head, q, arg) ->
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
let (is_embedded_uvar :
  Pulse_Syntax_Base.term -> Prims.nat FStar_Pervasives_Native.option) =
  fun t ->
    match is_fvar t with
    | FStar_Pervasives_Native.Some (l, u::[]) ->
        if l = Pulse_Elaborate_Pure.embedded_uvar_lid
        then
          (match FStar_Reflection_Builtins.inspect_universe u with
           | FStar_Reflection_Data.Uv_BVar n ->
               FStar_Pervasives_Native.Some n
           | uu___ -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None
let (is_eq2 :
  Pulse_Syntax_Base.term ->
    (Pulse_Syntax_Base.term * Pulse_Syntax_Base.term)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    match is_pure_app t with
    | FStar_Pervasives_Native.Some (head, FStar_Pervasives_Native.None, a2)
        ->
        (match is_pure_app head with
         | FStar_Pervasives_Native.Some
             (head1, FStar_Pervasives_Native.None, a1) ->
             (match is_pure_app head1 with
              | FStar_Pervasives_Native.Some
                  (head2, FStar_Pervasives_Native.Some
                   (Pulse_Syntax_Base.Implicit), uu___)
                  ->
                  (match is_fvar head2 with
                   | FStar_Pervasives_Native.Some (l, uu___1) ->
                       if l = ["Pulse"; "Steel"; "Wrapper"; "eq2_prop"]
                       then FStar_Pervasives_Native.Some (a1, a2)
                       else FStar_Pervasives_Native.None
                   | uu___1 -> FStar_Pervasives_Native.None)
              | uu___ -> FStar_Pervasives_Native.None)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (unreveal :
  Pulse_Syntax_Base.term ->
    Pulse_Syntax_Base.term FStar_Pervasives_Native.option)
  =
  fun t ->
    match is_pure_app t with
    | FStar_Pervasives_Native.Some (head, FStar_Pervasives_Native.None, arg)
        ->
        (match is_pure_app head with
         | FStar_Pervasives_Native.Some
             (head1, FStar_Pervasives_Native.Some
              (Pulse_Syntax_Base.Implicit), uu___)
             ->
             (match is_fvar head1 with
              | FStar_Pervasives_Native.Some (l, []) ->
                  if l = ["FStar"; "Ghost"; "reveal"]
                  then FStar_Pervasives_Native.Some arg
                  else FStar_Pervasives_Native.None
              | uu___1 -> FStar_Pervasives_Native.None)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None