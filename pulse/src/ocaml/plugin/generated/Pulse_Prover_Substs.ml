open Prims
type nt_substs = Pulse_Syntax_Naming.subst_elt Prims.list
let (compose_nt_substs : nt_substs -> nt_substs -> nt_substs) =
  fun ss1 -> fun ss2 -> FStar_List_Tot_Base.op_At ss1 ss2
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
      FStar_List_Tot_Base.fold_left
        (fun g1 -> fun elt -> Pulse_Typing_Metatheory.subst_env g1 [elt]) g
        ss
type ('g, 'uvs, 'ss) well_typed_ss = Obj.t
let coerce_eq : 'a 'b . 'a -> unit -> 'b =
  fun uu___1 -> fun uu___ -> (fun x -> fun uu___ -> Obj.magic x) uu___1 uu___
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
              fun ss ->
                match Pulse_Typing_Env.bindings uvs with
                | [] -> t_typing
                | uu___ ->
                    let uu___1 = Pulse_Typing_Env.remove_binding uvs in
                    (match uu___1 with
                     | (x, ty, uvs') ->
                         let uu___2 = ss in
                         (match uu___2 with
                          | (Pulse_Syntax_Naming.NT (y, e))::ss' ->
                              let t_typing1 = coerce_eq t_typing () in
                              let t_typing2 =
                                Pulse_Typing_Metatheory.st_typing_subst g x
                                  ty (Pulse_Typing_Env.push_env uvs' g') e ()
                                  t c t_typing1 in
                              st_typing_nt_substs g
                                (Pulse_Typing_Metatheory.subst_env uvs'
                                   [Pulse_Syntax_Naming.NT (y, e)])
                                (Pulse_Typing_Metatheory.subst_env g'
                                   [Pulse_Syntax_Naming.NT (y, e)])
                                (Pulse_Syntax_Naming.subst_st_term t
                                   [Pulse_Syntax_Naming.NT (y, e)])
                                (Pulse_Syntax_Naming.subst_comp c
                                   [Pulse_Syntax_Naming.NT (y, e)]) t_typing2
                                ss'))
type map = (Pulse_Syntax_Base.var, Pulse_Syntax_Base.term) FStar_Map.t
type ('l, 'm) related = unit
type t =
  {
  l: (Pulse_Syntax_Base.var * Pulse_Syntax_Base.term) Prims.list ;
  m: map }
let (__proj__Mkt__item__l :
  t -> (Pulse_Syntax_Base.var * Pulse_Syntax_Base.term) Prims.list) =
  fun projectee -> match projectee with | { l; m;_} -> l
let (__proj__Mkt__item__m : t -> map) =
  fun projectee -> match projectee with | { l; m;_} -> m
let rec (as_nt_substs_aux :
  (Pulse_Syntax_Base.var * Pulse_Syntax_Base.term) Prims.list -> nt_substs) =
  fun l ->
    match l with
    | [] -> []
    | (x, t1)::tl -> (Pulse_Syntax_Naming.NT (x, t1)) ::
        (as_nt_substs_aux tl)
let (as_nt_substs : t -> nt_substs) = fun s -> as_nt_substs_aux s.l
let (as_map :
  t -> (Pulse_Syntax_Base.var, Pulse_Syntax_Base.term) FStar_Map.t) =
  fun s -> s.m
let (sel : t -> Pulse_Syntax_Base.var -> Pulse_Syntax_Base.term) =
  fun s -> fun x -> FStar_Map.sel (as_map s) x
let (contains : t -> Pulse_Syntax_Base.var -> Prims.bool) =
  fun s -> fun x -> FStar_Map.contains (as_map s) x
let (dom : t -> Pulse_Syntax_Base.var FStar_Set.set) =
  fun s -> FStar_Map.domain (as_map s)
let (subst_term : Pulse_Syntax_Base.term -> t -> Pulse_Syntax_Base.term) =
  fun e -> fun s -> nt_subst_term e (as_nt_substs s)
let (subst_st_term :
  Pulse_Syntax_Base.st_term -> t -> Pulse_Syntax_Base.st_term) =
  fun e -> fun s -> nt_subst_st_term e (as_nt_substs s)
let (subst_comp : Pulse_Syntax_Base.comp -> t -> Pulse_Syntax_Base.comp) =
  fun c -> fun s -> nt_subst_comp c (as_nt_substs s)
let (subst_st_comp :
  Pulse_Syntax_Base.st_comp -> t -> Pulse_Syntax_Base.st_comp) =
  fun c -> fun s -> nt_subst_st_comp c (as_nt_substs s)
let (empty : t) =
  {
    l = [];
    m =
      (FStar_Map.const_on (FStar_Set.empty ()) Pulse_Syntax_Base.tm_unknown)
  }
let (push : t -> t -> t) =
  fun s1 ->
    fun s2 ->
      {
        l = (FStar_List_Tot_Base.op_At s1.l s2.l);
        m = (FStar_Map.concat s1.m s2.m)
      }
let (check_well_typedness :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      t -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun uvs ->
             fun ss ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> true)))
          uu___2 uu___1 uu___