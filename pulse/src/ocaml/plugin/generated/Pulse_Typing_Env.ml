open Prims
type binding = (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ)
type env_bindings = binding Prims.list
type bmap = (Pulse_Syntax_Base.var, Pulse_Syntax_Base.typ) FStar_Map.t
type ('bs, 'm) related = unit
type env =
  {
  f: FStar_Reflection_Typing.fstar_top_env ;
  bs: (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ) Prims.list ;
  names: Pulse_Syntax_Base.ppname Prims.list ;
  m: bmap ;
  ctxt: Pulse_RuntimeUtils.context }
let (__proj__Mkenv__item__f : env -> FStar_Reflection_Typing.fstar_top_env) =
  fun projectee -> match projectee with | { f; bs; names; m; ctxt;_} -> f
let (__proj__Mkenv__item__bs :
  env -> (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ) Prims.list) =
  fun projectee -> match projectee with | { f; bs; names; m; ctxt;_} -> bs
let (__proj__Mkenv__item__names : env -> Pulse_Syntax_Base.ppname Prims.list)
  =
  fun projectee -> match projectee with | { f; bs; names; m; ctxt;_} -> names
let (__proj__Mkenv__item__m : env -> bmap) =
  fun projectee -> match projectee with | { f; bs; names; m; ctxt;_} -> m
let (__proj__Mkenv__item__ctxt : env -> Pulse_RuntimeUtils.context) =
  fun projectee -> match projectee with | { f; bs; names; m; ctxt;_} -> ctxt
let (fstar_env : env -> FStar_Reflection_Typing.fstar_top_env) = fun g -> g.f
let (bindings : env -> env_bindings) = fun g -> g.bs
let (as_map :
  env -> (Pulse_Syntax_Base.var, Pulse_Syntax_Base.typ) FStar_Map.t) =
  fun g -> g.m
type ('bs, 'm) is_related_to = unit
let (dom : env -> Pulse_Syntax_Base.var FStar_Set.set) =
  fun g -> FStar_Map.domain (as_map g)
type ('g1, 'g2) equal = unit
let (empty_bmap : bmap) =
  FStar_Map.const_on (FStar_Set.empty ()) Pulse_Syntax_Base.tm_unknown
let (default_context : Pulse_RuntimeUtils.context) = FStar_Sealed.seal []
let (mk_env : FStar_Reflection_Typing.fstar_top_env -> env) =
  fun f -> { f; bs = []; names = []; m = empty_bmap; ctxt = default_context }
let (push_binding :
  env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.ppname -> Pulse_Syntax_Base.typ -> env)
  =
  fun g ->
    fun x ->
      fun p ->
        fun t ->
          {
            f = (g.f);
            bs = ((x, t) :: (g.bs));
            names = (p :: (g.names));
            m = (FStar_Map.upd g.m x t);
            ctxt = (g.ctxt)
          }
let (singleton_env :
  FStar_Reflection_Typing.fstar_top_env ->
    Pulse_Syntax_Base.var -> Pulse_Syntax_Base.typ -> env)
  =
  fun f ->
    fun x ->
      fun t -> push_binding (mk_env f) x Pulse_Syntax_Base.ppname_default t
let (push_binding_def :
  env -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.typ -> env) =
  fun g ->
    fun x -> fun t -> push_binding g x Pulse_Syntax_Base.ppname_default t
let (lookup :
  env ->
    Pulse_Syntax_Base.var ->
      Pulse_Syntax_Base.typ FStar_Pervasives_Native.option)
  =
  fun g ->
    fun x ->
      let m = as_map g in
      if FStar_Map.contains m x
      then FStar_Pervasives_Native.Some (FStar_Map.sel m x)
      else FStar_Pervasives_Native.None
let rec (max :
  (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ) Prims.list ->
    Pulse_Syntax_Base.var -> Pulse_Syntax_Base.var)
  =
  fun bs ->
    fun current ->
      match bs with
      | [] -> current
      | (x, t)::rest ->
          let current1 = if x < current then current else x in
          max rest current1
let (fresh : env -> Pulse_Syntax_Base.var) =
  fun g ->
    match g.bs with
    | [] -> Prims.int_one
    | (x, uu___)::bs_rest -> let max1 = max bs_rest x in max1 + Prims.int_one
let (contains : env -> Pulse_Syntax_Base.var -> Prims.bool) =
  fun g -> fun x -> FStar_Map.contains (as_map g) x
type ('g1, 'g2) disjoint = unit
type ('g, 'gu, 'guu) pairwise_disjoint = unit
let (push_env : env -> env -> env) =
  fun g1 ->
    fun g2 ->
      {
        f = (g1.f);
        bs = (FStar_List_Tot_Base.op_At g2.bs g1.bs);
        names = (FStar_List_Tot_Base.op_At g2.names g1.names);
        m = (FStar_Map.concat g2.m g1.m);
        ctxt = (g1.ctxt)
      }
let (check_disjoint :
  env -> Pulse_Syntax_Base.var FStar_Set.set -> Prims.bool) =
  fun g ->
    fun s ->
      Prims.op_Negation
        (FStar_List_Tot_Base.existsb
           (fun uu___ -> match uu___ with | (x, uu___1) -> FStar_Set.mem x s)
           g.bs)
let rec (remove_binding_aux :
  env ->
    (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ) Prims.list ->
      Pulse_Syntax_Base.ppname Prims.list ->
        (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ) Prims.list ->
          Pulse_Syntax_Base.ppname Prims.list ->
            (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ * env))
  =
  fun g ->
    fun prefix ->
      fun prefix_names ->
        fun suffix ->
          fun suffix_names ->
            match (suffix, suffix_names) with
            | ((x, t)::[], uu___) ->
                let m =
                  FStar_Map.restrict
                    (FStar_Set.complement (FStar_Set.singleton x))
                    (FStar_Map.upd g.m x Pulse_Syntax_Base.tm_unknown) in
                let g' =
                  {
                    f = (g.f);
                    bs = prefix;
                    names = prefix_names;
                    m;
                    ctxt = (g.ctxt)
                  } in
                (x, t, g')
            | ((x, t)::suffix_rest, n::suffix_names_rest) ->
                remove_binding_aux g
                  (FStar_List_Tot_Base.op_At prefix [(x, t)])
                  (FStar_List_Tot_Base.op_At prefix_names [n]) suffix_rest
                  suffix_names_rest
let (remove_binding :
  env -> (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ * env)) =
  fun g -> remove_binding_aux g [] [] g.bs g.names
let (remove_latest_binding :
  env -> (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ * env)) =
  fun g ->
    match g.bs with
    | (x, t)::rest ->
        let m =
          FStar_Map.restrict (FStar_Set.complement (FStar_Set.singleton x))
            (FStar_Map.upd g.m x Pulse_Syntax_Base.tm_unknown) in
        let g' =
          {
            f = (g.f);
            bs = rest;
            names = (FStar_List_Tot_Base.tl g.names);
            m;
            ctxt = (g.ctxt)
          } in
        (x, t, g')
type ('g1, 'g2, 'g3) extends_with = unit
type ('g1, 'g2) env_extends = unit
let rec diff_witness :
  'a . 'a Prims.list -> 'a Prims.list -> unit -> 'a Prims.list =
  fun l1 ->
    fun l2 ->
      fun l3 ->
        match (l1, l2) with
        | ([], uu___) -> []
        | (uu___, []) -> l1
        | (hd1::tl1, hd2::tl2) -> diff_witness tl1 tl2 ()
let rec (create_m :
  (Pulse_Syntax_Base.var * Pulse_Syntax_Base.typ) Prims.list -> bmap) =
  fun bs ->
    match bs with
    | [] -> empty_bmap
    | (x, t)::tl -> FStar_Map.upd (create_m tl) x t
let rec diff_names : 'a . 'a Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | ([], uu___) -> []
      | (uu___, []) -> l1
      | (uu___::tl1, uu___1::tl2) -> diff_names tl1 tl2
let (diff : env -> env -> env) =
  fun g1 ->
    fun g2 ->
      let g1_bs_rev = FStar_List_Tot_Base.rev g1.bs in
      let g2_bs_rev = FStar_List_Tot_Base.rev g2.bs in
      let rev_bs3 = diff_witness g1_bs_rev g2_bs_rev () in
      let bs3 = FStar_List_Tot_Base.rev rev_bs3 in
      let names3 =
        FStar_List_Tot_Base.rev
          (diff_names (FStar_List_Tot_Base.rev g1.names)
             (FStar_List_Tot_Base.rev g2.names)) in
      let m3 = create_m bs3 in
      let g31 =
        { f = (g1.f); bs = bs3; names = names3; m = m3; ctxt = (g1.ctxt) } in
      g31
let rec (subst_env : env -> Pulse_Syntax_Naming.subst -> env) =
  fun en ->
    fun ss ->
      match bindings en with
      | [] -> en
      | uu___ ->
          let uu___1 = remove_latest_binding en in
          (match uu___1 with
           | (x, t, en1) ->
               push_binding (subst_env en1 ss) x
                 Pulse_Syntax_Base.ppname_default
                 (Pulse_Syntax_Naming.subst_term t ss))
let (push_context : env -> Prims.string -> Pulse_Syntax_Base.range -> env) =
  fun g ->
    fun ctx ->
      fun r ->
        {
          f = (g.f);
          bs = (g.bs);
          names = (g.names);
          m = (g.m);
          ctxt =
            (Pulse_RuntimeUtils.extend_context ctx
               (FStar_Pervasives_Native.Some r) g.ctxt)
        }
let (push_context_no_range : env -> Prims.string -> env) =
  fun g ->
    fun ctx ->
      {
        f = (g.f);
        bs = (g.bs);
        names = (g.names);
        m = (g.m);
        ctxt =
          (Pulse_RuntimeUtils.extend_context ctx FStar_Pervasives_Native.None
             g.ctxt)
      }
let (get_context : env -> Pulse_RuntimeUtils.context) = fun g -> g.ctxt
let (range_of_env :
  env -> (Pulse_Syntax_Base.range, unit) FStar_Tactics_Effect.tac_repr) =
  fun g ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Typing.Env.fst" (Prims.of_int (282))
               (Prims.of_int (14)) (Prims.of_int (282)) (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Typing.Env.fst" (Prims.of_int (283))
               (Prims.of_int (4)) (Prims.of_int (291)) (Prims.of_int (30)))))
      (Obj.magic (FStar_Tactics_Unseal.unseal g.ctxt))
      (fun uu___ ->
         (fun ctx ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                          (Prims.of_int (284)) (Prims.of_int (6))
                          (Prims.of_int (289)) (Prims.of_int (66)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                          (Prims.of_int (283)) (Prims.of_int (4))
                          (Prims.of_int (291)) (Prims.of_int (30)))))
                 (Obj.magic
                    (FStar_Tactics_Util.tryPick
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     match uu___ with
                                     | (uu___2, r) ->
                                         (match r with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some r1
                                              ->
                                              if
                                                Prims.op_Negation
                                                  (Pulse_RuntimeUtils.is_range_zero
                                                     r1)
                                              then
                                                FStar_Pervasives_Native.Some
                                                  r1
                                              else
                                                FStar_Pervasives_Native.None))))
                            uu___) ctx))
                 (fun uu___ ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 ->
                         match uu___ with
                         | FStar_Pervasives_Native.Some r -> r
                         | uu___2 -> FStar_Range.range_0)))) uu___)
let (ctxt_elt_to_string :
  (Prims.string * Pulse_Syntax_Base.range FStar_Pervasives_Native.option) ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun c ->
       match FStar_Pervasives_Native.snd c with
       | FStar_Pervasives_Native.None ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pervasives_Native.fst c)))
       | FStar_Pervasives_Native.Some r ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                            (Prims.of_int (298)) (Prims.of_int (49))
                            (Prims.of_int (298)) (Prims.of_int (70)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic (FStar_Tactics_V2_Builtins.range_to_string r))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           Prims.strcat
                             (Prims.strcat ""
                                (Prims.strcat (FStar_Pervasives_Native.fst c)
                                   " @ ")) (Prims.strcat uu___ "")))))) uu___
let (ctx_to_string :
  (Prims.string * Pulse_Syntax_Base.range FStar_Pervasives_Native.option)
    Prims.list -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun c ->
       match c with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                            (Prims.of_int (304)) (Prims.of_int (42))
                            (Prims.of_int (304)) (Prims.of_int (93)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                  (Prims.of_int (304)) (Prims.of_int (64))
                                  (Prims.of_int (304)) (Prims.of_int (92)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                  (Prims.of_int (304)) (Prims.of_int (42))
                                  (Prims.of_int (304)) (Prims.of_int (93)))))
                         (Obj.magic
                            (FStar_Tactics_Util.map ctxt_elt_to_string c))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 FStar_String.concat "\n\t" uu___1))))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat "\n\tContext:\n\t"
                             (Prims.strcat uu___1 "")))))) uu___
let (ctxt_to_list :
  env -> (Prims.string Prims.list, unit) FStar_Tactics_Effect.tac_repr) =
  fun g ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Typing.Env.fst" (Prims.of_int (307))
               (Prims.of_int (12)) (Prims.of_int (307)) (Prims.of_int (27)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Typing.Env.fst" (Prims.of_int (308))
               (Prims.of_int (2)) (Prims.of_int (308)) (Prims.of_int (30)))))
      (Obj.magic (FStar_Tactics_Unseal.unseal g.ctxt))
      (fun uu___ ->
         (fun ctx ->
            Obj.magic (FStar_Tactics_Util.map ctxt_elt_to_string ctx)) uu___)
let (print_context :
  env -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun g ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Typing.Env.fst" (Prims.of_int (311))
               (Prims.of_int (12)) (Prims.of_int (311)) (Prims.of_int (27)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Typing.Env.fst" (Prims.of_int (312))
               (Prims.of_int (2)) (Prims.of_int (315)) (Prims.of_int (79)))))
      (Obj.magic (FStar_Tactics_Unseal.unseal g.ctxt))
      (fun uu___ ->
         (fun ctx ->
            match ctx with
            | [] ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
            | uu___ ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                 (Prims.of_int (315)) (Prims.of_int (40))
                                 (Prims.of_int (315)) (Prims.of_int (79)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "prims.fst"
                                 (Prims.of_int (590)) (Prims.of_int (19))
                                 (Prims.of_int (590)) (Prims.of_int (31)))))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Env.fst"
                                       (Prims.of_int (315))
                                       (Prims.of_int (62))
                                       (Prims.of_int (315))
                                       (Prims.of_int (78)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Env.fst"
                                       (Prims.of_int (315))
                                       (Prims.of_int (40))
                                       (Prims.of_int (315))
                                       (Prims.of_int (79)))))
                              (Obj.magic (ctxt_to_list g))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      FStar_String.concat "\n\t" uu___1))))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 ->
                                Prims.strcat "\n\tContext:\n\t"
                                  (Prims.strcat uu___1 "")))))) uu___)
let (print_issue :
  env ->
    FStar_Issue.issue -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun i ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                 (Prims.of_int (319)) (Prims.of_int (30))
                 (Prims.of_int (321)) (Prims.of_int (37)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                 (Prims.of_int (323)) (Prims.of_int (4)) (Prims.of_int (327))
                 (Prims.of_int (101)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              fun uu___ ->
                (fun uu___ ->
                   fun uu___1 ->
                     match uu___1 with
                     | FStar_Pervasives_Native.None ->
                         Obj.magic
                           (Obj.repr
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 -> "Unknown range")))
                     | FStar_Pervasives_Native.Some r ->
                         Obj.magic
                           (Obj.repr
                              (FStar_Tactics_V2_Builtins.range_to_string r)))
                  uu___1 uu___))
        (fun uu___ ->
           (fun range_opt_to_string ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                            (Prims.of_int (327)) (Prims.of_int (7))
                            (Prims.of_int (327)) (Prims.of_int (101)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                            (Prims.of_int (323)) (Prims.of_int (4))
                            (Prims.of_int (327)) (Prims.of_int (101)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                  (Prims.of_int (327)) (Prims.of_int (22))
                                  (Prims.of_int (327)) (Prims.of_int (100)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                  (Prims.of_int (327)) (Prims.of_int (7))
                                  (Prims.of_int (327)) (Prims.of_int (101)))))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Env.fst"
                                        (Prims.of_int (327))
                                        (Prims.of_int (23))
                                        (Prims.of_int (327))
                                        (Prims.of_int (47)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Env.fst"
                                        (Prims.of_int (327))
                                        (Prims.of_int (22))
                                        (Prims.of_int (327))
                                        (Prims.of_int (100)))))
                               (Obj.magic
                                  (FStar_Tactics_Unseal.unseal
                                     (get_context g)))
                               (fun uu___ ->
                                  (fun uu___ ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Typing.Env.fst"
                                                   (Prims.of_int (327))
                                                   (Prims.of_int (50))
                                                   (Prims.of_int (327))
                                                   (Prims.of_int (99)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Typing.Env.fst"
                                                   (Prims.of_int (327))
                                                   (Prims.of_int (22))
                                                   (Prims.of_int (327))
                                                   (Prims.of_int (100)))))
                                          (Obj.magic
                                             (FStar_Tactics_Util.map
                                                (fun uu___1 ->
                                                   (fun i1 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___1 ->
                                                              (i1,
                                                                FStar_Pervasives_Native.None))))
                                                     uu___1)
                                                (FStar_Issue.context_of_issue
                                                   i)))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  FStar_List_Tot_Base.op_At
                                                    uu___ uu___1)))) uu___)))
                         (fun uu___ ->
                            (fun uu___ -> Obj.magic (ctx_to_string uu___))
                              uu___)))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Env.fst"
                                       (Prims.of_int (323))
                                       (Prims.of_int (4))
                                       (Prims.of_int (327))
                                       (Prims.of_int (101)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Typing.Env.fst"
                                       (Prims.of_int (323))
                                       (Prims.of_int (4))
                                       (Prims.of_int (327))
                                       (Prims.of_int (101)))))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Typing.Env.fst"
                                             (Prims.of_int (323))
                                             (Prims.of_int (4))
                                             (Prims.of_int (327))
                                             (Prims.of_int (101)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Typing.Env.fst"
                                             (Prims.of_int (323))
                                             (Prims.of_int (4))
                                             (Prims.of_int (327))
                                             (Prims.of_int (101)))))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Typing.Env.fst"
                                                   (Prims.of_int (323))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (327))
                                                   (Prims.of_int (101)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Typing.Env.fst"
                                                   (Prims.of_int (323))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (327))
                                                   (Prims.of_int (101)))))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Typing.Env.fst"
                                                         (Prims.of_int (324))
                                                         (Prims.of_int (7))
                                                         (Prims.of_int (324))
                                                         (Prims.of_int (47)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Printf.fst"
                                                         (Prims.of_int (121))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (123))
                                                         (Prims.of_int (44)))))
                                                (Obj.magic
                                                   (range_opt_to_string
                                                      (FStar_Issue.range_of_issue
                                                         i)))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        fun x ->
                                                          fun x1 ->
                                                            fun x2 ->
                                                              Prims.strcat
                                                                (Prims.strcat
                                                                   (Prims.strcat
                                                                    (Prims.strcat
                                                                    ""
                                                                    (Prims.strcat
                                                                    uu___1
                                                                    " ("))
                                                                    (Prims.strcat
                                                                    x "): "))
                                                                   (Prims.strcat
                                                                    x1 ""))
                                                                (Prims.strcat
                                                                   x2 "")))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  uu___1
                                                    (FStar_Issue.level_of_issue
                                                       i)))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            uu___1
                                              (FStar_Issue.render_issue i)))))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> uu___1 uu___)))) uu___)))
             uu___)
let (print_issues :
  env ->
    FStar_Issue.issue Prims.list ->
      (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun i ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                 (Prims.of_int (331)) (Prims.of_int (24))
                 (Prims.of_int (331)) (Prims.of_int (49)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                 (Prims.of_int (331)) (Prims.of_int (5)) (Prims.of_int (331))
                 (Prims.of_int (49)))))
        (Obj.magic (FStar_Tactics_Util.map (print_issue g) i))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStar_String.concat "\n" uu___))
let (env_to_string :
  env -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun e ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Typing.Env.fst" (Prims.of_int (334))
               (Prims.of_int (11)) (Prims.of_int (336)) (Prims.of_int (24)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Typing.Env.fst" (Prims.of_int (337))
               (Prims.of_int (2)) (Prims.of_int (337)) (Prims.of_int (25)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                     (Prims.of_int (336)) (Prims.of_int (4))
                     (Prims.of_int (336)) (Prims.of_int (24)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                     (Prims.of_int (334)) (Prims.of_int (11))
                     (Prims.of_int (336)) (Prims.of_int (24)))))
            (Obj.magic (FStar_Tactics_Util.zip e.bs e.names))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Util.map
                       (fun uu___1 ->
                          match uu___1 with
                          | ((n, t), x) ->
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Typing.Env.fst"
                                         (Prims.of_int (335))
                                         (Prims.of_int (72))
                                         (Prims.of_int (335))
                                         (Prims.of_int (111)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Typing.Env.fst"
                                         (Prims.of_int (335))
                                         (Prims.of_int (24))
                                         (Prims.of_int (335))
                                         (Prims.of_int (111)))))
                                (Obj.magic
                                   (Pulse_Syntax_Printer.term_to_string t))
                                (fun uu___2 ->
                                   (fun uu___2 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Env.fst"
                                                    (Prims.of_int (335))
                                                    (Prims.of_int (24))
                                                    (Prims.of_int (335))
                                                    (Prims.of_int (111)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Env.fst"
                                                    (Prims.of_int (335))
                                                    (Prims.of_int (24))
                                                    (Prims.of_int (335))
                                                    (Prims.of_int (111)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Typing.Env.fst"
                                                          (Prims.of_int (335))
                                                          (Prims.of_int (24))
                                                          (Prims.of_int (335))
                                                          (Prims.of_int (111)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Typing.Env.fst"
                                                          (Prims.of_int (335))
                                                          (Prims.of_int (24))
                                                          (Prims.of_int (335))
                                                          (Prims.of_int (111)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Typing.Env.fst"
                                                                (Prims.of_int (335))
                                                                (Prims.of_int (52))
                                                                (Prims.of_int (335))
                                                                (Prims.of_int (69)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Printf.fst"
                                                                (Prims.of_int (121))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (123))
                                                                (Prims.of_int (44)))))
                                                       (Obj.magic
                                                          (FStar_Tactics_Unseal.unseal
                                                             x.Pulse_Syntax_Base.name))
                                                       (fun uu___3 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               fun x1 ->
                                                                 fun x2 ->
                                                                   Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    ""
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    "#"))
                                                                    (Prims.strcat
                                                                    (Prims.string_of_int
                                                                    x1) " : "))
                                                                    (Prims.strcat
                                                                    x2 "")))))
                                                 (fun uu___3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 -> uu___3 n))))
                                           (fun uu___3 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___4 -> uu___3 uu___2))))
                                     uu___2)) uu___)) uu___)))
      (fun bs ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> FStar_String.concat "\n  " bs))
let rec separate_map :
  'a .
    FStar_Pprint.document ->
      ('a -> (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr) ->
        'a Prims.list ->
          (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun sep ->
           fun f ->
             fun l ->
               match l with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> FStar_Pprint.empty)))
               | x::[] -> Obj.magic (Obj.repr (f x))
               | x::xs ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                    (Prims.of_int (348)) (Prims.of_int (13))
                                    (Prims.of_int (348)) (Prims.of_int (16)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                    (Prims.of_int (348)) (Prims.of_int (13))
                                    (Prims.of_int (348)) (Prims.of_int (49)))))
                           (Obj.magic (f x))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Typing.Env.fst"
                                               (Prims.of_int (348))
                                               (Prims.of_int (20))
                                               (Prims.of_int (348))
                                               (Prims.of_int (49)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Typing.Env.fst"
                                               (Prims.of_int (348))
                                               (Prims.of_int (13))
                                               (Prims.of_int (348))
                                               (Prims.of_int (49)))))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Typing.Env.fst"
                                                     (Prims.of_int (348))
                                                     (Prims.of_int (28))
                                                     (Prims.of_int (348))
                                                     (Prims.of_int (49)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Typing.Env.fst"
                                                     (Prims.of_int (348))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (348))
                                                     (Prims.of_int (49)))))
                                            (Obj.magic
                                               (separate_map sep f xs))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                      sep uu___1))))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              FStar_Pprint.op_Hat_Hat uu___
                                                uu___1)))) uu___)))) uu___2
          uu___1 uu___
let (env_to_doc :
  env -> (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr) =
  fun e ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Typing.Env.fst" (Prims.of_int (352))
               (Prims.of_int (4)) (Prims.of_int (354)) (Prims.of_int (45)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Typing.Env.fst" (Prims.of_int (356))
               (Prims.of_int (2)) (Prims.of_int (356)) (Prims.of_int (56)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            fun uu___1 ->
              match uu___1 with
              | ((n, t), x) ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                             (Prims.of_int (353)) (Prims.of_int (6))
                             (Prims.of_int (353)) (Prims.of_int (37)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                             (Prims.of_int (353)) (Prims.of_int (6))
                             (Prims.of_int (354)) (Prims.of_int (45)))))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                   (Prims.of_int (353)) (Prims.of_int (20))
                                   (Prims.of_int (353)) (Prims.of_int (37)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                   (Prims.of_int (353)) (Prims.of_int (6))
                                   (Prims.of_int (353)) (Prims.of_int (37)))))
                          (Obj.magic
                             (FStar_Tactics_Unseal.unseal
                                x.Pulse_Syntax_Base.name))
                          (fun uu___2 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 ->
                                  FStar_Pprint.doc_of_string uu___2))))
                    (fun uu___2 ->
                       (fun uu___2 ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Env.fst"
                                        (Prims.of_int (353))
                                        (Prims.of_int (41))
                                        (Prims.of_int (354))
                                        (Prims.of_int (45)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Typing.Env.fst"
                                        (Prims.of_int (353))
                                        (Prims.of_int (6))
                                        (Prims.of_int (354))
                                        (Prims.of_int (45)))))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Typing.Env.fst"
                                              (Prims.of_int (353))
                                              (Prims.of_int (62))
                                              (Prims.of_int (354))
                                              (Prims.of_int (45)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Typing.Env.fst"
                                              (Prims.of_int (353))
                                              (Prims.of_int (41))
                                              (Prims.of_int (354))
                                              (Prims.of_int (45)))))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Env.fst"
                                                    (Prims.of_int (354))
                                                    (Prims.of_int (11))
                                                    (Prims.of_int (354))
                                                    (Prims.of_int (45)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Env.fst"
                                                    (Prims.of_int (353))
                                                    (Prims.of_int (62))
                                                    (Prims.of_int (354))
                                                    (Prims.of_int (45)))))
                                           (Obj.magic
                                              (Pulse_Syntax_Printer.term_to_doc
                                                 t))
                                           (fun uu___3 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___4 ->
                                                   FStar_Pprint.op_Hat_Hat
                                                     (FStar_Pprint.doc_of_string
                                                        (Prims.string_of_int
                                                           n)) uu___3))))
                                     (fun uu___3 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 ->
                                             FStar_Pprint.op_Hat_Hat
                                               (FStar_Pprint.doc_of_string
                                                  "#") uu___3))))
                               (fun uu___3 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___4 ->
                                       FStar_Pprint.op_Hat_Hat uu___2 uu___3))))
                         uu___2)))
      (fun uu___ ->
         (fun pp1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                          (Prims.of_int (356)) (Prims.of_int (11))
                          (Prims.of_int (356)) (Prims.of_int (56)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                          (Prims.of_int (356)) (Prims.of_int (2))
                          (Prims.of_int (356)) (Prims.of_int (56)))))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                (Prims.of_int (356)) (Prims.of_int (35))
                                (Prims.of_int (356)) (Prims.of_int (55)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                (Prims.of_int (356)) (Prims.of_int (11))
                                (Prims.of_int (356)) (Prims.of_int (56)))))
                       (Obj.magic (FStar_Tactics_Util.zip e.bs e.names))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (separate_map FStar_Pprint.comma pp1 uu___))
                            uu___)))
                 (fun uu___ ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 -> FStar_Pprint.brackets uu___)))) uu___)
let (get_range :
  env ->
    Pulse_Syntax_Base.range FStar_Pervasives_Native.option ->
      (Pulse_Syntax_Base.range, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun r ->
      match r with
      | FStar_Pervasives_Native.None -> range_of_env g
      | FStar_Pervasives_Native.Some r1 ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                     (Prims.of_int (362)) (Prims.of_int (9))
                     (Prims.of_int (362)) (Prims.of_int (27)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                     (Prims.of_int (362)) (Prims.of_int (6))
                     (Prims.of_int (364)) (Prims.of_int (12)))))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> Pulse_RuntimeUtils.is_range_zero r1))
            (fun uu___ ->
               (fun uu___ ->
                  if uu___
                  then Obj.magic (Obj.repr (range_of_env g))
                  else
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> r1)))) uu___)
let fail_doc :
  'a .
    env ->
      Pulse_Syntax_Base.range FStar_Pervasives_Native.option ->
        FStar_Pprint.document Prims.list ->
          ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun g ->
    fun r ->
      fun msg ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                   (Prims.of_int (367)) (Prims.of_int (10))
                   (Prims.of_int (367)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                   (Prims.of_int (367)) (Prims.of_int (26))
                   (Prims.of_int (375)) (Prims.of_int (31)))))
          (Obj.magic (get_range g r))
          (fun uu___ ->
             (fun r1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                              (Prims.of_int (369)) (Prims.of_int (4))
                              (Prims.of_int (371)) (Prims.of_int (12)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                              (Prims.of_int (372)) (Prims.of_int (4))
                              (Prims.of_int (375)) (Prims.of_int (31)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                    (Prims.of_int (369)) (Prims.of_int (7))
                                    (Prims.of_int (369)) (Prims.of_int (43)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                    (Prims.of_int (369)) (Prims.of_int (4))
                                    (Prims.of_int (371)) (Prims.of_int (12)))))
                           (Obj.magic (Pulse_Config.debug_flag "env_on_err"))
                           (fun uu___ ->
                              (fun uu___ ->
                                 if uu___
                                 then
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Env.fst"
                                                    (Prims.of_int (370))
                                                    (Prims.of_int (15))
                                                    (Prims.of_int (370))
                                                    (Prims.of_int (64)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Env.fst"
                                                    (Prims.of_int (370))
                                                    (Prims.of_int (9))
                                                    (Prims.of_int (370))
                                                    (Prims.of_int (64)))))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Typing.Env.fst"
                                                          (Prims.of_int (370))
                                                          (Prims.of_int (16))
                                                          (Prims.of_int (370))
                                                          (Prims.of_int (63)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Typing.Env.fst"
                                                          (Prims.of_int (370))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (370))
                                                          (Prims.of_int (64)))))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Typing.Env.fst"
                                                                (Prims.of_int (370))
                                                                (Prims.of_int (51))
                                                                (Prims.of_int (370))
                                                                (Prims.of_int (63)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Typing.Env.fst"
                                                                (Prims.of_int (370))
                                                                (Prims.of_int (16))
                                                                (Prims.of_int (370))
                                                                (Prims.of_int (63)))))
                                                       (Obj.magic
                                                          (env_to_doc g))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               FStar_Pprint.op_Hat_Slash_Hat
                                                                 (FStar_Pprint.doc_of_string
                                                                    "In environment")
                                                                 uu___1))))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 -> [uu___1]))))
                                           (fun uu___1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_List_Tot_Base.op_At
                                                     msg uu___1))))
                                 else
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 -> msg)))) uu___)))
                     (fun uu___ ->
                        (fun msg1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Typing.Env.fst"
                                         (Prims.of_int (373))
                                         (Prims.of_int (14))
                                         (Prims.of_int (373))
                                         (Prims.of_int (81)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Typing.Env.fst"
                                         (Prims.of_int (374))
                                         (Prims.of_int (2))
                                         (Prims.of_int (375))
                                         (Prims.of_int (31)))))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Typing.Env.fst"
                                               (Prims.of_int (373))
                                               (Prims.of_int (65))
                                               (Prims.of_int (373))
                                               (Prims.of_int (81)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Typing.Env.fst"
                                               (Prims.of_int (373))
                                               (Prims.of_int (14))
                                               (Prims.of_int (373))
                                               (Prims.of_int (81)))))
                                      (Obj.magic (ctxt_to_list g))
                                      (fun uu___ ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              FStar_Issue.mk_issue_doc
                                                "Error" msg1
                                                (FStar_Pervasives_Native.Some
                                                   r1)
                                                FStar_Pervasives_Native.None
                                                uu___))))
                                (fun uu___ ->
                                   (fun issue ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Env.fst"
                                                    (Prims.of_int (374))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (374))
                                                    (Prims.of_int (22)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Typing.Env.fst"
                                                    (Prims.of_int (375))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (375))
                                                    (Prims.of_int (31)))))
                                           (Obj.magic
                                              (FStar_Tactics_V2_Builtins.log_issues
                                                 [issue]))
                                           (fun uu___ ->
                                              FStar_Tactics_V2_Derived.fail
                                                "Pulse checker failed")))
                                     uu___))) uu___))) uu___)
let (warn_doc :
  env ->
    Pulse_Syntax_Base.range FStar_Pervasives_Native.option ->
      FStar_Pprint.document Prims.list ->
        (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun r ->
      fun msg ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                   (Prims.of_int (378)) (Prims.of_int (10))
                   (Prims.of_int (378)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                   (Prims.of_int (378)) (Prims.of_int (26))
                   (Prims.of_int (380)) (Prims.of_int (22)))))
          (Obj.magic (get_range g r))
          (fun uu___ ->
             (fun r1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                              (Prims.of_int (379)) (Prims.of_int (14))
                              (Prims.of_int (379)) (Prims.of_int (83)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                              (Prims.of_int (380)) (Prims.of_int (2))
                              (Prims.of_int (380)) (Prims.of_int (22)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                    (Prims.of_int (379)) (Prims.of_int (67))
                                    (Prims.of_int (379)) (Prims.of_int (83)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                    (Prims.of_int (379)) (Prims.of_int (14))
                                    (Prims.of_int (379)) (Prims.of_int (83)))))
                           (Obj.magic (ctxt_to_list g))
                           (fun uu___ ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   FStar_Issue.mk_issue_doc "Warning" msg
                                     (FStar_Pervasives_Native.Some r1)
                                     FStar_Pervasives_Native.None uu___))))
                     (fun uu___ ->
                        (fun issue ->
                           Obj.magic
                             (FStar_Tactics_V2_Builtins.log_issues [issue]))
                          uu___))) uu___)
let (info_doc :
  env ->
    Pulse_Syntax_Base.range FStar_Pervasives_Native.option ->
      FStar_Pprint.document Prims.list ->
        (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun r ->
      fun msg ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                   (Prims.of_int (383)) (Prims.of_int (10))
                   (Prims.of_int (383)) (Prims.of_int (23)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                   (Prims.of_int (383)) (Prims.of_int (26))
                   (Prims.of_int (385)) (Prims.of_int (22)))))
          (Obj.magic (get_range g r))
          (fun uu___ ->
             (fun r1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                              (Prims.of_int (384)) (Prims.of_int (14))
                              (Prims.of_int (384)) (Prims.of_int (80)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                              (Prims.of_int (385)) (Prims.of_int (2))
                              (Prims.of_int (385)) (Prims.of_int (22)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                    (Prims.of_int (384)) (Prims.of_int (64))
                                    (Prims.of_int (384)) (Prims.of_int (80)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Typing.Env.fst"
                                    (Prims.of_int (384)) (Prims.of_int (14))
                                    (Prims.of_int (384)) (Prims.of_int (80)))))
                           (Obj.magic (ctxt_to_list g))
                           (fun uu___ ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   FStar_Issue.mk_issue_doc "Info" msg
                                     (FStar_Pervasives_Native.Some r1)
                                     FStar_Pervasives_Native.None uu___))))
                     (fun uu___ ->
                        (fun issue ->
                           Obj.magic
                             (FStar_Tactics_V2_Builtins.log_issues [issue]))
                          uu___))) uu___)
let fail :
  'a .
    env ->
      Pulse_Syntax_Base.range FStar_Pervasives_Native.option ->
        Prims.string -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun g ->
    fun r -> fun msg -> fail_doc g r [FStar_Pprint.arbitrary_string msg]
let (warn :
  env ->
    Pulse_Syntax_Base.range FStar_Pervasives_Native.option ->
      Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun r -> fun msg -> warn_doc g r [FStar_Pprint.arbitrary_string msg]
let (info :
  env ->
    Pulse_Syntax_Base.range FStar_Pervasives_Native.option ->
      Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun r -> fun msg -> info_doc g r [FStar_Pprint.arbitrary_string msg]