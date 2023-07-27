open Prims
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
type 'l no_repeats = Obj.t
type ss_dom = Pulse_Syntax_Base.var Prims.list
type ss_map = (Pulse_Syntax_Base.var, Pulse_Syntax_Base.term) FStar_Map.t
let (remove_map :
  ss_map ->
    Pulse_Syntax_Base.var ->
      (Pulse_Syntax_Base.var, Pulse_Syntax_Base.term) FStar_Map.t)
  =
  fun m ->
    fun x ->
      FStar_Map.restrict (FStar_Set.complement (FStar_Set.singleton x))
        (FStar_Map.upd m x Pulse_Syntax_Base.tm_unknown)
type ('l, 'm) is_dom = Obj.t
type ss_t = {
  l: ss_dom ;
  m: ss_map }
let (__proj__Mkss_t__item__l : ss_t -> ss_dom) =
  fun projectee -> match projectee with | { l; m;_} -> l
let (__proj__Mkss_t__item__m : ss_t -> ss_map) =
  fun projectee -> match projectee with | { l; m;_} -> m
let (as_map :
  ss_t -> (Pulse_Syntax_Base.var, Pulse_Syntax_Base.term) FStar_Map.t) =
  fun ss -> ss.m
let (dom : ss_t -> Pulse_Syntax_Base.var FStar_Set.set) =
  fun ss -> FStar_Map.domain (as_map ss)
let (contains : ss_t -> Pulse_Syntax_Base.var -> Prims.bool) =
  fun ss -> fun x -> FStar_Map.contains (as_map ss) x
let (sel : ss_t -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term) =
  fun ss -> fun x -> FStar_Map.sel (as_map ss) x
let (empty : ss_t) =
  {
    l = [];
    m =
      (FStar_Map.const_on (FStar_Set.empty ()) Pulse_Syntax_Base.tm_unknown)
  }
let (push : ss_t -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term -> ss_t)
  =
  fun ss ->
    fun x -> fun t -> { l = (x :: (ss.l)); m = (FStar_Map.upd ss.m x t) }
let (tail : ss_t -> ss_t) =
  fun ss ->
    {
      l = (FStar_List_Tot_Base.tl ss.l);
      m = (remove_map ss.m (FStar_List_Tot_Base.hd ss.l))
    }
let rec (push_ss : ss_t -> ss_t -> ss_t) =
  fun ss1 ->
    fun ss2 ->
      match ss2.l with
      | [] -> ss1
      | x::tl -> push_ss (push ss1 x (FStar_Map.sel ss2.m x)) (tail ss2)
let (check_disjoint : ss_t -> ss_t -> Prims.bool) =
  fun ss1 ->
    fun ss2 ->
      Prims.op_Negation
        (FStar_List_Tot_Base.existsb
           (fun v1 -> FStar_List_Tot_Base.mem v1 ss2.l) ss1.l)
let rec (remove_l : ss_dom -> Pulse_Syntax_Base.var -> ss_dom) =
  fun l ->
    fun x ->
      match l with
      | [] -> []
      | y::tl -> if y = x then tl else y :: (remove_l tl x)
let rec (ss_term : Pulse_Syntax_Base.term -> ss_t -> Pulse_Syntax_Base.term)
  =
  fun t ->
    fun ss ->
      match ss.l with
      | [] -> t
      | y::tl ->
          let t1 =
            Pulse_Syntax_Naming.subst_term t
              [Pulse_Syntax_Naming.NT (y, (FStar_Map.sel ss.m y))] in
          ss_term t1 (tail ss)
let rec (ss_st_term :
  Pulse_Syntax_Base.st_term -> ss_t -> Pulse_Syntax_Base.st_term) =
  fun t ->
    fun ss ->
      match ss.l with
      | [] -> t
      | y::tl ->
          let t1 =
            Pulse_Syntax_Naming.subst_st_term t
              [Pulse_Syntax_Naming.NT (y, (FStar_Map.sel ss.m y))] in
          ss_st_term t1 (tail ss)
let rec (ss_st_comp :
  Pulse_Syntax_Base.st_comp -> ss_t -> Pulse_Syntax_Base.st_comp) =
  fun s ->
    fun ss ->
      match ss.l with
      | [] -> s
      | y::tl ->
          let s1 =
            Pulse_Syntax_Naming.subst_st_comp s
              [Pulse_Syntax_Naming.NT (y, (FStar_Map.sel ss.m y))] in
          ss_st_comp s1 (tail ss)
let rec (ss_comp : Pulse_Syntax_Base.comp -> ss_t -> Pulse_Syntax_Base.comp)
  =
  fun c ->
    fun ss ->
      match ss.l with
      | [] -> c
      | y::tl ->
          let c1 =
            Pulse_Syntax_Naming.subst_comp c
              [Pulse_Syntax_Naming.NT (y, (FStar_Map.sel ss.m y))] in
          ss_comp c1 (tail ss)
let rec (ss_binder :
  Pulse_Syntax_Base.binder -> ss_t -> Pulse_Syntax_Base.binder) =
  fun b ->
    fun ss ->
      match ss.l with
      | [] -> b
      | y::tl ->
          let b1 =
            Pulse_Syntax_Naming.subst_binder b
              [Pulse_Syntax_Naming.NT (y, (FStar_Map.sel ss.m y))] in
          ss_binder b1 (tail ss)
let rec (ss_env : Pulse_Typing_Env.env -> ss_t -> Pulse_Typing_Env.env) =
  fun g ->
    fun ss ->
      match ss.l with
      | [] -> g
      | y::tl ->
          ss_env
            (Pulse_Typing_Env.subst_env g
               [Pulse_Syntax_Naming.NT (y, (FStar_Map.sel ss.m y))])
            (tail ss)
type nt_substs = Pulse_Syntax_Naming.subst_elt Prims.list
let (nt_subst_term :
  Pulse_Syntax_Base.term -> nt_substs -> Pulse_Syntax_Base.term) =
  fun t ->
    fun ss ->
      FStar_List_Tot_Base.fold_left
        (fun t1 -> fun elt -> Pulse_Syntax_Naming.subst_term t1 [elt]) t ss
let (nt_subst_binder :
  Pulse_Syntax_Base.binder -> nt_substs -> Pulse_Syntax_Base.binder) =
  fun b ->
    fun ss ->
      FStar_List_Tot_Base.fold_left
        (fun b1 -> fun elt -> Pulse_Syntax_Naming.subst_binder b1 [elt]) b ss
let (nt_subst_st_term :
  Pulse_Syntax_Base.st_term -> nt_substs -> Pulse_Syntax_Base.st_term) =
  fun t ->
    fun ss ->
      FStar_List_Tot_Base.fold_left
        (fun t1 -> fun elt -> Pulse_Syntax_Naming.subst_st_term t1 [elt]) t
        ss
let (nt_subst_st_comp :
  Pulse_Syntax_Base.st_comp -> nt_substs -> Pulse_Syntax_Base.st_comp) =
  fun s ->
    fun ss ->
      FStar_List_Tot_Base.fold_left
        (fun s1 -> fun elt -> Pulse_Syntax_Naming.subst_st_comp s1 [elt]) s
        ss
let (nt_subst_comp :
  Pulse_Syntax_Base.comp -> nt_substs -> Pulse_Syntax_Base.comp) =
  fun c ->
    fun ss ->
      FStar_List_Tot_Base.fold_left
        (fun c1 -> fun elt -> Pulse_Syntax_Naming.subst_comp c1 [elt]) c ss
let (nt_subst_env :
  Pulse_Typing_Env.env -> nt_substs -> Pulse_Typing_Env.env) =
  fun g ->
    fun ss ->
      let g' =
        FStar_List_Tot_Base.fold_left
          (fun g1 -> fun elt -> Pulse_Typing_Env.subst_env g1 [elt]) g ss in
      g'
type ('g, 'uvs, 'nts) well_typed_nt_substs = Obj.t
type ('nts, 'ss) is_permutation = Obj.t
let rec (ss_to_nt_substs :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      ss_t ->
        ((nt_substs, Prims.string) FStar_Pervasives.either, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun uvs ->
      fun ss ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.Substs.fst"
                   (Prims.of_int (249)) (Prims.of_int (10))
                   (Prims.of_int (249)) (Prims.of_int (59)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Checker.Prover.Substs.fst"
                   (Prims.of_int (250)) (Prims.of_int (2))
                   (Prims.of_int (277)) (Prims.of_int (66)))))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.Substs.fst"
                         (Prims.of_int (249)) (Prims.of_int (43))
                         (Prims.of_int (249)) (Prims.of_int (59)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.Prover.Substs.fst"
                         (Prims.of_int (249)) (Prims.of_int (10))
                         (Prims.of_int (249)) (Prims.of_int (59)))))
                (Obj.magic (Pulse_Typing_Env.range_of_env g))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        Pulse_Typing_Env.push_context g "ss_to_nt_substs"
                          uu___))))
          (fun uu___ ->
             (fun g1 ->
                match Pulse_Typing_Env.bindings uvs with
                | [] ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ ->
                               match ss.l with
                               | [] -> FStar_Pervasives.Inl []
                               | x::uu___1 ->
                                   FStar_Pervasives.Inr
                                     (Prims.strcat
                                        "extra uvars in the substitutions collected by the prover, e.g._#"
                                        (Prims.strcat (Prims.string_of_int x)
                                           "")))))
                | uu___ ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Prover.Substs.fst"
                                     (Prims.of_int (257)) (Prims.of_int (26))
                                     (Prims.of_int (257)) (Prims.of_int (44)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Prover.Substs.fst"
                                     (Prims.of_int (256)) (Prims.of_int (8))
                                     (Prims.of_int (277)) (Prims.of_int (66)))))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 ->
                                  Pulse_Typing_Env.remove_binding uvs))
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  match uu___1 with
                                  | (x, ty, rest_uvs) ->
                                      if FStar_Map.contains ss.m x
                                      then
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.Substs.fst"
                                                         (Prims.of_int (259))
                                                         (Prims.of_int (17))
                                                         (Prims.of_int (259))
                                                         (Prims.of_int (31)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Prover.Substs.fst"
                                                         (Prims.of_int (259))
                                                         (Prims.of_int (34))
                                                         (Prims.of_int (276))
                                                         (Prims.of_int (18)))))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      FStar_Map.sel ss.m x))
                                                (fun uu___2 ->
                                                   (fun t ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Substs.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (45)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Substs.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (18)))))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 ()))
                                                           (fun uu___2 ->
                                                              (fun d ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Substs.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Prover.Substs.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    (ss_to_nt_substs
                                                                    g1
                                                                    (Pulse_Typing_Env.subst_env
                                                                    rest_uvs
                                                                    [
                                                                    Pulse_Syntax_Naming.NT
                                                                    (x, t)])
                                                                    {
                                                                    l =
                                                                    (remove_l
                                                                    ss.l x);
                                                                    m =
                                                                    (remove_map
                                                                    ss.m x)
                                                                    }))
                                                                    (fun
                                                                    nts_opt
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match nts_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Inr
                                                                    e ->
                                                                    FStar_Pervasives.Inr
                                                                    e
                                                                    | 
                                                                    FStar_Pervasives.Inl
                                                                    nts ->
                                                                    FStar_Pervasives.Inl
                                                                    ((Pulse_Syntax_Naming.NT
                                                                    (x, t))
                                                                    :: nts)))))
                                                                uu___2)))
                                                     uu___2)))
                                      else
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___3 ->
                                                   FStar_Pervasives.Inr
                                                     (Prims.strcat
                                                        "prover could not prove uvar _#"
                                                        (Prims.strcat
                                                           (Prims.string_of_int
                                                              x) ""))))))
                                 uu___1)))) uu___)
let rec (well_typed_nt_substs_prefix :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env -> nt_substs -> Pulse_Typing_Env.env -> nt_substs)
  =
  fun g ->
    fun uvs ->
      fun nts ->
        fun uvs1 ->
          match ((Pulse_Typing_Env.bindings uvs1),
                  (Pulse_Typing_Env.bindings uvs))
          with
          | ([], uu___) -> []
          | (uu___::uu___1, uu___2::uu___3) ->
              let uu___4 = Pulse_Typing_Env.remove_binding uvs1 in
              (match uu___4 with
               | (x1, ty1, rest_uvs1) ->
                   let uu___5 = Pulse_Typing_Env.remove_binding uvs in
                   (match uu___5 with
                    | (x, ty, rest_uvs) ->
                        let uu___6 = nts in
                        (match uu___6 with
                         | (Pulse_Syntax_Naming.NT (y, e))::nts_rest ->
                             (Pulse_Syntax_Naming.NT (y, e)) ::
                             (well_typed_nt_substs_prefix g
                                (Pulse_Typing_Env.subst_env rest_uvs
                                   [Pulse_Syntax_Naming.NT (y, e)]) nts_rest
                                (Pulse_Typing_Env.subst_env rest_uvs1
                                   [Pulse_Syntax_Naming.NT (y, e)])))))
let rec (st_typing_nt_substs :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Typing_Env.env ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              nt_substs -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun uvs ->
      fun g' ->
        fun t ->
          fun c ->
            fun t_typing ->
              fun nts ->
                match Pulse_Typing_Env.bindings uvs with
                | [] -> t_typing
                | uu___ ->
                    let uu___1 = Pulse_Typing_Env.remove_binding uvs in
                    (match uu___1 with
                     | (x, ty, uvs_rest) ->
                         let uu___2 = nts in
                         (match uu___2 with
                          | (Pulse_Syntax_Naming.NT (uu___3, e))::nts_rest ->
                              let t_typing1 = coerce_eq t_typing () in
                              let t_typing2 =
                                Pulse_Typing_Metatheory_Base.st_typing_subst
                                  g x ty
                                  (Pulse_Typing_Env.push_env uvs_rest g') e
                                  () t c t_typing1 in
                              st_typing_nt_substs g
                                (Pulse_Typing_Env.subst_env uvs_rest
                                   [Pulse_Syntax_Naming.NT (x, e)])
                                (Pulse_Typing_Env.subst_env g'
                                   [Pulse_Syntax_Naming.NT (x, e)])
                                (Pulse_Syntax_Naming.subst_st_term t
                                   [Pulse_Syntax_Naming.NT (x, e)])
                                (Pulse_Syntax_Naming.subst_comp c
                                   [Pulse_Syntax_Naming.NT (x, e)]) t_typing2
                                nts_rest))
let (st_typing_nt_substs_derived :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp_st ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            nt_substs -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun uvs ->
      fun t ->
        fun c ->
          fun t_typing ->
            fun ss ->
              let g' = Pulse_Typing_Env.mk_env (Pulse_Typing_Env.fstar_env g) in
              let d =
                st_typing_nt_substs g uvs g' t c (coerce_eq t_typing ()) ss in
              d