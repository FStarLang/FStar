open Prims
exception Splitlast_empty 
let (uu___is_Splitlast_empty : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Splitlast_empty -> true | uu___ -> false
let rec splitlast :
  'a .
    'a Prims.list ->
      (('a Prims.list * 'a), unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___ ->
    (fun l ->
       match l with
       | [] ->
           Obj.magic (Obj.repr (FStar_Tactics_Effect.raise Splitlast_empty))
       | x::[] ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ([], x))))
       | x::xs ->
           Obj.magic
             (Obj.repr
                (let uu___ = splitlast xs in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Recursion.fst"
                            (Prims.of_int (37)) (Prims.of_int (21))
                            (Prims.of_int (37)) (Prims.of_int (33)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Recursion.fst"
                            (Prims.of_int (36)) (Prims.of_int (12))
                            (Prims.of_int (38)) (Prims.of_int (17)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           match uu___1 with
                           | (init, last) -> ((x :: init), last)))))) uu___
exception Map2_length_mismatch 
let (uu___is_Map2_length_mismatch : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Map2_length_mismatch -> true | uu___ -> false
let rec map2 :
  'a 'b 'c .
    ('a -> 'b -> ('c, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list ->
        'b Prims.list -> ('c Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun f ->
           fun xs ->
             fun ys ->
               match (xs, ys) with
               | ([], []) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
               | (x::xx, y::yy) ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = f x y in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Recursion.fst"
                                    (Prims.of_int (45)) (Prims.of_int (20))
                                    (Prims.of_int (45)) (Prims.of_int (25)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Recursion.fst"
                                    (Prims.of_int (45)) (Prims.of_int (20))
                                    (Prims.of_int (45)) (Prims.of_int (41)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 let uu___2 = map2 f xx yy in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Recursion.fst"
                                               (Prims.of_int (45))
                                               (Prims.of_int (29))
                                               (Prims.of_int (45))
                                               (Prims.of_int (41)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Recursion.fst"
                                               (Prims.of_int (45))
                                               (Prims.of_int (20))
                                               (Prims.of_int (45))
                                               (Prims.of_int (41)))))
                                      (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 -> uu___1 :: uu___3))))
                                uu___1)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.raise Map2_length_mismatch)))
          uu___2 uu___1 uu___
let (debug_main :
  Pulse_Typing_Env.env ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun s ->
           if
             Pulse_RuntimeUtils.debug_at_level (Pulse_Typing_Env.fstar_env g)
               "pulse.main"
           then
             Obj.magic
               (Obj.repr
                  (let uu___ = s () in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Recursion.fst"
                              (Prims.of_int (50)) (Prims.of_int (13))
                              (Prims.of_int (50)) (Prims.of_int (19)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Recursion.fst"
                              (Prims.of_int (50)) (Prims.of_int (7))
                              (Prims.of_int (50)) (Prims.of_int (19)))))
                     (Obj.magic uu___)
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic (FStar_Tactics_V2_Builtins.print uu___1))
                          uu___1)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let (string_as_term : Prims.string -> FStar_Reflection_Types.term) =
  fun s ->
    FStar_Reflection_V2_Builtins.pack_ln
      (FStar_Reflection_V2_Data.Tv_Const
         (FStar_Reflection_V2_Data.C_String s))
let (freshen_binder :
  FStar_Tactics_NamedView.binder -> FStar_Tactics_NamedView.binder) =
  fun b ->
    {
      FStar_Tactics_NamedView.uniq =
        ((Prims.of_int (10000)) + b.FStar_Tactics_NamedView.uniq);
      FStar_Tactics_NamedView.ppname =
        (FStar_Sealed.map_seal b.FStar_Tactics_NamedView.ppname
           (fun s -> Prims.strcat s "'"));
      FStar_Tactics_NamedView.sort = (b.FStar_Tactics_NamedView.sort);
      FStar_Tactics_NamedView.qual = (b.FStar_Tactics_NamedView.qual);
      FStar_Tactics_NamedView.attrs = (b.FStar_Tactics_NamedView.attrs)
    }
let (subst_binder_typ :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Tactics_NamedView.binder -> FStar_Tactics_NamedView.binder)
  =
  fun s ->
    fun b ->
      {
        FStar_Tactics_NamedView.uniq = (b.FStar_Tactics_NamedView.uniq);
        FStar_Tactics_NamedView.ppname = (b.FStar_Tactics_NamedView.ppname);
        FStar_Tactics_NamedView.sort =
          (FStar_Reflection_V2_Builtins.subst_term s
             b.FStar_Tactics_NamedView.sort);
        FStar_Tactics_NamedView.qual = (b.FStar_Tactics_NamedView.qual);
        FStar_Tactics_NamedView.attrs = (b.FStar_Tactics_NamedView.attrs)
      }
let rec (freshen_binders :
  FStar_Tactics_NamedView.binders -> FStar_Tactics_NamedView.binders) =
  fun bs ->
    match bs with
    | [] -> []
    | b::bs1 ->
        let b' = freshen_binder b in
        let bs2 =
          FStar_List_Tot_Base.map
            (subst_binder_typ
               [FStar_Syntax_Syntax.NT
                  ((FStar_Reflection_V2_Builtins.pack_namedv
                      (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv b)),
                    (FStar_Tactics_V2_SyntaxCoercions.binder_to_term b'))])
            bs1 in
        b' :: (freshen_binders bs2)
let (elab_b :
  (Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option *
    Pulse_Syntax_Base.binder * Pulse_Syntax_Base.bv) ->
    FStar_Tactics_NamedView.binder)
  =
  fun qbv ->
    let uu___ = qbv in
    match uu___ with
    | (q, b, bv) ->
        {
          FStar_Tactics_NamedView.uniq = (bv.Pulse_Syntax_Base.bv_index);
          FStar_Tactics_NamedView.ppname =
            ((b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name);
          FStar_Tactics_NamedView.sort = (b.Pulse_Syntax_Base.binder_ty);
          FStar_Tactics_NamedView.qual = (Pulse_Elaborate_Pure.elab_qual q);
          FStar_Tactics_NamedView.attrs = []
        }
let (add_knot :
  Pulse_Typing_Env.env ->
    FStar_Range.range ->
      Pulse_Syntax_Base.decl ->
        (Pulse_Syntax_Base.decl, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun rng ->
      fun d ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> d.Pulse_Syntax_Base.d)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Recursion.fst"
                   (Prims.of_int (86)) (Prims.of_int (51))
                   (Prims.of_int (86)) (Prims.of_int (54)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Recursion.fst"
                   (Prims.of_int (85)) Prims.int_one (Prims.of_int (204))
                   (Prims.of_int (3))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | Pulse_Syntax_Base.FnDefn
                    { Pulse_Syntax_Base.id = id;
                      Pulse_Syntax_Base.isrec = isrec;
                      Pulse_Syntax_Base.bs = bs;
                      Pulse_Syntax_Base.comp = comp;
                      Pulse_Syntax_Base.meas = meas;
                      Pulse_Syntax_Base.body7 = body;_}
                    ->
                    let uu___2 =
                      if Prims.uu___is_Nil bs
                      then
                        Obj.magic
                          (Obj.repr
                             (Pulse_Typing_Env.fail g
                                (FStar_Pervasives_Native.Some
                                   (d.Pulse_Syntax_Base.range2))
                                "main: FnDefn does not have binders"))
                      else
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___4 -> ()))) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Recursion.fst"
                                  (Prims.of_int (87)) (Prims.of_int (2))
                                  (Prims.of_int (88)) (Prims.of_int (62)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Pulse.Recursion.fst"
                                  (Prims.of_int (88)) (Prims.of_int (63))
                                  (Prims.of_int (204)) (Prims.of_int (3)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun uu___3 ->
                               let uu___4 =
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 ->
                                         Pulse_Elaborate_Pure.elab_comp comp)) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Recursion.fst"
                                             (Prims.of_int (90))
                                             (Prims.of_int (14))
                                             (Prims.of_int (90))
                                             (Prims.of_int (28)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Recursion.fst"
                                             (Prims.of_int (91))
                                             (Prims.of_int (2))
                                             (Prims.of_int (204))
                                             (Prims.of_int (3)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun r_res ->
                                          let uu___5 =
                                            debug_main g
                                              (fun uu___6 ->
                                                 let uu___7 =
                                                   FStar_Tactics_Util.string_of_list
                                                     (fun uu___8 ->
                                                        match uu___8 with
                                                        | (uu___9, b,
                                                           uu___10) ->
                                                            Pulse_Syntax_Printer.binder_to_string
                                                              b) bs in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Recursion.fst"
                                                            (Prims.of_int (93))
                                                            (Prims.of_int (14))
                                                            (Prims.of_int (93))
                                                            (Prims.of_int (72)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "prims.fst"
                                                            (Prims.of_int (611))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (611))
                                                            (Prims.of_int (31)))))
                                                   (Obj.magic uu___7)
                                                   (fun uu___8 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___9 ->
                                                           Prims.strcat
                                                             "add_knot: bs = "
                                                             (Prims.strcat
                                                                uu___8 "\n")))) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Recursion.fst"
                                                        (Prims.of_int (91))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (93))
                                                        (Prims.of_int (73)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Recursion.fst"
                                                        (Prims.of_int (93))
                                                        (Prims.of_int (74))
                                                        (Prims.of_int (204))
                                                        (Prims.of_int (3)))))
                                               (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  (fun uu___6 ->
                                                     let uu___7 =
                                                       splitlast bs in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Recursion.fst"
                                                                   (Prims.of_int (127))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (127))
                                                                   (Prims.of_int (31)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Recursion.fst"
                                                                   (Prims.of_int (93))
                                                                   (Prims.of_int (74))
                                                                   (Prims.of_int (204))
                                                                   (Prims.of_int (3)))))
                                                          (Obj.magic uu___7)
                                                          (fun uu___8 ->
                                                             (fun uu___8 ->
                                                                match uu___8
                                                                with
                                                                | (bs1,
                                                                   b_knot) ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_List_Tot_Base.map
                                                                    elab_b
                                                                    bs1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    r_bs0 ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    freshen_binders
                                                                    r_bs0)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun r_bs
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    fun b ->
                                                                    FStar_Reflection_V2_Builtins.pack_namedv
                                                                    {
                                                                    FStar_Reflection_V2_Data.uniq
                                                                    =
                                                                    (b.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Reflection_V2_Data.sort
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    b.FStar_Tactics_NamedView.sort);
                                                                    FStar_Reflection_V2_Data.ppname
                                                                    =
                                                                    (b.FStar_Tactics_NamedView.ppname)
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    binder_to_r_namedv
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    map2
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    fun
                                                                    uu___13
                                                                    ->
                                                                    (fun b1
                                                                    ->
                                                                    fun b2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    ((binder_to_r_namedv
                                                                    b1),
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binder_to_term
                                                                    b2)))))
                                                                    uu___14
                                                                    uu___13)
                                                                    r_bs0
                                                                    r_bs in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    prime_subst
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    if
                                                                    (Pulse_Syntax_Base.uu___is_C_STAtomic
                                                                    comp) ||
                                                                    (Pulse_Syntax_Base.uu___is_C_STGhost
                                                                    comp)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___14
                                                                    =
                                                                    if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    meas
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail_doc
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (d.Pulse_Syntax_Base.range2))
                                                                    [
                                                                    Pulse_PP.text
                                                                    "'ghost' and 'atomic' recursive functions require a 'decreases' clause"]))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    -> ()))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    splitlast
                                                                    r_bs in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    (init,
                                                                    last) ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    init
                                                                    [
                                                                    {
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.ppname);
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Refine
                                                                    ({
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.ppname);
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.sort);
                                                                    FStar_Tactics_NamedView.qual
                                                                    =
                                                                    FStar_Reflection_V2_Data.Q_Explicit;
                                                                    FStar_Tactics_NamedView.attrs
                                                                    = []
                                                                    },
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Range";
                                                                    "labeled"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Range";
                                                                    "range_0"]))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    (FStar_Reflection_V2_Data.C_String
                                                                    "Could not prove termination"))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "precedes"]))),
                                                                    ((FStar_Reflection_V2_Builtins.subst_term
                                                                    prime_subst
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    meas)),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStar_Pervasives_Native.__proj__Some__item__v
                                                                    meas),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))))));
                                                                    FStar_Tactics_NamedView.qual
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.qual);
                                                                    FStar_Tactics_NamedView.attrs
                                                                    =
                                                                    (last.FStar_Tactics_NamedView.attrs)
                                                                    }]))))
                                                                    uu___15)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    -> r_bs))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    r_bs1 ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.subst_term
                                                                    prime_subst
                                                                    r_res)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    r_res1 ->
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                                    r_bs1
                                                                    r_res1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (204))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun r_ty
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    if
                                                                    FStar_Reflection_V2_Data.uu___is_Tv_Unknown
                                                                    (FStar_Reflection_V2_Builtins.inspect_ln
                                                                    r_ty)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (d.Pulse_Syntax_Base.range2))
                                                                    "error: r_ty is Tv_unknown in add_knot?"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Recursion.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    {
                                                                    Pulse_Syntax_Base.d
                                                                    =
                                                                    (Pulse_Syntax_Base.FnDefn
                                                                    {
                                                                    Pulse_Syntax_Base.id
                                                                    =
                                                                    (match 
                                                                    FStar_Reflection_V2_Builtins.inspect_ident
                                                                    id
                                                                    with
                                                                    | 
                                                                    (s, rng1)
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.pack_ident
                                                                    ((Prims.strcat
                                                                    "__recaux_"
                                                                    s), rng1));
                                                                    Pulse_Syntax_Base.isrec
                                                                    = false;
                                                                    Pulse_Syntax_Base.bs
                                                                    =
                                                                    (FStar_List_Tot_Base.op_At
                                                                    bs1
                                                                    [(
                                                                    match 
                                                                    FStar_Reflection_V2_Builtins.inspect_ident
                                                                    id
                                                                    with
                                                                    | 
                                                                    (s, rng1)
                                                                    ->
                                                                    (FStar_Pervasives_Native.None,
                                                                    (Pulse_Syntax_Base.mk_binder
                                                                    s rng1
                                                                    (Pulse_Syntax_Pure.wr
                                                                    r_ty rng1)),
                                                                    {
                                                                    Pulse_Syntax_Base.bv_index
                                                                    =
                                                                    ((FStar_Pervasives_Native.__proj__Mktuple3__item___3
                                                                    b_knot).Pulse_Syntax_Base.bv_index);
                                                                    Pulse_Syntax_Base.bv_ppname
                                                                    =
                                                                    {
                                                                    Pulse_Syntax_Base.name
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    s);
                                                                    Pulse_Syntax_Base.range
                                                                    = rng1
                                                                    }
                                                                    }))]);
                                                                    Pulse_Syntax_Base.comp
                                                                    = comp;
                                                                    Pulse_Syntax_Base.meas
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    Pulse_Syntax_Base.body7
                                                                    = body
                                                                    });
                                                                    Pulse_Syntax_Base.range2
                                                                    =
                                                                    (d.Pulse_Syntax_Base.range2)
                                                                    }))))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                               uu___8)))
                                                    uu___6))) uu___5)))
                              uu___3))) uu___1)
let (tie_knot :
  Pulse_Typing_Env.env ->
    FStar_Range.range ->
      Prims.string ->
        Prims.string ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Typing.blob ->
              ((Prims.bool * FStar_Reflection_Types.sigelt *
                 FStar_Reflection_Typing.blob FStar_Pervasives_Native.option),
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun rng ->
      fun nm_orig ->
        fun nm_aux ->
          fun r_typ ->
            fun blob ->
              let uu___ =
                let uu___1 =
                  FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs r_typ in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Recursion.fst"
                           (Prims.of_int (215)) (Prims.of_int (16))
                           (Prims.of_int (215)) (Prims.of_int (36)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Recursion.fst"
                           (Prims.of_int (212)) (Prims.of_int (18))
                           (Prims.of_int (219)) (Prims.of_int (15)))))
                  (Obj.magic uu___1)
                  (fun uu___2 ->
                     (fun uu___2 ->
                        match uu___2 with
                        | (bs, c) ->
                            let uu___3 =
                              if Prims.uu___is_Nil bs
                              then
                                Obj.magic
                                  (Obj.repr
                                     (Pulse_Typing_Env.fail g
                                        (FStar_Pervasives_Native.Some rng)
                                        "tie_knot: impossible (1)"))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 -> ()))) in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Recursion.fst"
                                          (Prims.of_int (216))
                                          (Prims.of_int (4))
                                          (Prims.of_int (216))
                                          (Prims.of_int (64)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Recursion.fst"
                                          (Prims.of_int (216))
                                          (Prims.of_int (65))
                                          (Prims.of_int (219))
                                          (Prims.of_int (15)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    (fun uu___4 ->
                                       let uu___5 =
                                         Obj.magic
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___6 ->
                                                 FStar_List_Tot_Base.init bs)) in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Recursion.fst"
                                                     (Prims.of_int (217))
                                                     (Prims.of_int (13))
                                                     (Prims.of_int (217))
                                                     (Prims.of_int (20)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Recursion.fst"
                                                     (Prims.of_int (218))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (219))
                                                     (Prims.of_int (15)))))
                                            (Obj.magic uu___5)
                                            (fun uu___6 ->
                                               (fun bs1 ->
                                                  let uu___6 =
                                                    if Prims.uu___is_Nil bs1
                                                    then
                                                      Obj.magic
                                                        (Obj.repr
                                                           (Pulse_Typing_Env.fail
                                                              g
                                                              (FStar_Pervasives_Native.Some
                                                                 rng)
                                                              "tie_knot: impossible (2)"))
                                                    else
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___8 ->
                                                                 ()))) in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Recursion.fst"
                                                                (Prims.of_int (218))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (218))
                                                                (Prims.of_int (64)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Recursion.fst"
                                                                (Prims.of_int (219))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (219))
                                                                (Prims.of_int (15)))))
                                                       (Obj.magic uu___6)
                                                       (fun uu___7 ->
                                                          (fun uu___7 ->
                                                             Obj.magic
                                                               (FStar_Tactics_V2_SyntaxHelpers.mk_arr
                                                                  bs1 c))
                                                            uu___7))) uu___6)))
                                      uu___4))) uu___2) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Recursion.fst"
                         (Prims.of_int (212)) (Prims.of_int (18))
                         (Prims.of_int (219)) (Prims.of_int (15)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Recursion.fst"
                         (Prims.of_int (220)) (Prims.of_int (4))
                         (Prims.of_int (226)) (Prims.of_int (22)))))
                (Obj.magic uu___)
                (fun uu___1 ->
                   (fun knot_r_typ ->
                      let uu___1 =
                        let uu___2 = FStar_Tactics_V2_Derived.cur_module () in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Recursion.fst"
                                   (Prims.of_int (223)) (Prims.of_int (55))
                                   (Prims.of_int (223)) (Prims.of_int (72)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Pulse.Recursion.fst"
                                   (Prims.of_int (223)) (Prims.of_int (21))
                                   (Prims.of_int (223)) (Prims.of_int (104)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 ->
                                  FStar_Reflection_Typing.mk_unchecked_let
                                    (Pulse_Typing_Env.fstar_env g) uu___3
                                    nm_orig
                                    (FStar_Reflection_V2_Builtins.pack_ln
                                       (FStar_Reflection_V2_Data.Tv_App
                                          ((FStar_Reflection_V2_Builtins.pack_ln
                                              (FStar_Reflection_V2_Data.Tv_FVar
                                                 (FStar_Reflection_V2_Builtins.pack_fv
                                                    ["Prims"; "magic"]))),
                                            ((FStar_Reflection_V2_Builtins.pack_ln
                                                (FStar_Reflection_V2_Data.Tv_Const
                                                   FStar_Reflection_V2_Data.C_Unit)),
                                              FStar_Reflection_V2_Data.Q_Explicit))))
                                    knot_r_typ)) in
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Recursion.fst"
                                    (Prims.of_int (223)) (Prims.of_int (21))
                                    (Prims.of_int (223)) (Prims.of_int (104)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Recursion.fst"
                                    (Prims.of_int (220)) (Prims.of_int (4))
                                    (Prims.of_int (226)) (Prims.of_int (22)))))
                           (Obj.magic uu___1)
                           (fun uu___2 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 ->
                                   match uu___2 with
                                   | (flag, sig1, uu___4) ->
                                       (flag,
                                         (Pulse_RuntimeUtils.add_attribute
                                            sig1
                                            (FStar_Reflection_V2_Builtins.pack_ln
                                               (FStar_Reflection_V2_Data.Tv_App
                                                  ((FStar_Reflection_V2_Builtins.pack_ln
                                                      (FStar_Reflection_V2_Data.Tv_App
                                                         ((FStar_Reflection_V2_Builtins.pack_ln
                                                             (FStar_Reflection_V2_Data.Tv_FVar
                                                                (FStar_Reflection_V2_Builtins.pack_fv
                                                                   ["FStar";
                                                                   "Pervasives";
                                                                   "Native";
                                                                   "Mktuple2"]))),
                                                           ((FStar_Reflection_V2_Builtins.pack_ln
                                                               (FStar_Reflection_V2_Data.Tv_Const
                                                                  (FStar_Reflection_V2_Data.C_String
                                                                    "pulse.recursive.knot"))),
                                                             FStar_Reflection_V2_Data.Q_Explicit)))),
                                                    ((string_as_term nm_aux),
                                                      FStar_Reflection_V2_Data.Q_Explicit))))),
                                         (FStar_Pervasives_Native.Some blob))))))
                     uu___1)