open Prims
exception LengthMismatch 
let (uu___is_LengthMismatch : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | LengthMismatch -> true | uu___ -> false
let (print : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun s -> Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ())))
      uu___
type pattern__Pat_Constant__payload = {
  c: FStar_Reflection_Data.vconst }
and pattern__Pat_Cons__payload =
  {
  head: FStar_Reflection_Types.fv ;
  univs: FStar_Reflection_Data.universes FStar_Pervasives_Native.option ;
  subpats: (pattern * Prims.bool) Prims.list }
and pattern__Pat_Var__payload =
  {
  v: FStar_Reflection_Types.namedv ;
  sort: FStar_Reflection_Types.typ FStar_Sealed.sealed }
and pattern__Pat_Dot_Term__payload =
  {
  t: FStar_Reflection_Types.term FStar_Pervasives_Native.option }
and pattern =
  | Pat_Constant of pattern__Pat_Constant__payload 
  | Pat_Cons of pattern__Pat_Cons__payload 
  | Pat_Var of pattern__Pat_Var__payload 
  | Pat_Dot_Term of pattern__Pat_Dot_Term__payload 
let (__proj__Mkpattern__Pat_Constant__payload__item__c :
  pattern__Pat_Constant__payload -> FStar_Reflection_Data.vconst) =
  fun projectee -> match projectee with | { c;_} -> c
let (__proj__Mkpattern__Pat_Cons__payload__item__head :
  pattern__Pat_Cons__payload -> FStar_Reflection_Types.fv) =
  fun projectee -> match projectee with | { head; univs; subpats;_} -> head
let (__proj__Mkpattern__Pat_Cons__payload__item__univs :
  pattern__Pat_Cons__payload ->
    FStar_Reflection_Data.universes FStar_Pervasives_Native.option)
  =
  fun projectee -> match projectee with | { head; univs; subpats;_} -> univs
let (__proj__Mkpattern__Pat_Cons__payload__item__subpats :
  pattern__Pat_Cons__payload -> (pattern * Prims.bool) Prims.list) =
  fun projectee ->
    match projectee with | { head; univs; subpats;_} -> subpats
let (__proj__Mkpattern__Pat_Var__payload__item__v :
  pattern__Pat_Var__payload -> FStar_Reflection_Types.namedv) =
  fun projectee -> match projectee with | { v; sort;_} -> v
let (__proj__Mkpattern__Pat_Var__payload__item__sort :
  pattern__Pat_Var__payload -> FStar_Reflection_Types.typ FStar_Sealed.sealed)
  = fun projectee -> match projectee with | { v; sort;_} -> sort
let (__proj__Mkpattern__Pat_Dot_Term__payload__item__t :
  pattern__Pat_Dot_Term__payload ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option)
  = fun projectee -> match projectee with | { t;_} -> t
let (uu___is_Pat_Constant : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_Constant _0 -> true | uu___ -> false
let (__proj__Pat_Constant__item___0 :
  pattern -> pattern__Pat_Constant__payload) =
  fun projectee -> match projectee with | Pat_Constant _0 -> _0
let (uu___is_Pat_Cons : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_Cons _0 -> true | uu___ -> false
let (__proj__Pat_Cons__item___0 : pattern -> pattern__Pat_Cons__payload) =
  fun projectee -> match projectee with | Pat_Cons _0 -> _0
let (uu___is_Pat_Var : pattern -> Prims.bool) =
  fun projectee -> match projectee with | Pat_Var _0 -> true | uu___ -> false
let (__proj__Pat_Var__item___0 : pattern -> pattern__Pat_Var__payload) =
  fun projectee -> match projectee with | Pat_Var _0 -> _0
let (uu___is_Pat_Dot_Term : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_Dot_Term _0 -> true | uu___ -> false
let (__proj__Pat_Dot_Term__item___0 :
  pattern -> pattern__Pat_Dot_Term__payload) =
  fun projectee -> match projectee with | Pat_Dot_Term _0 -> _0
type branch = (pattern * FStar_Reflection_Types.term)
type binder =
  {
  uniq: Prims.nat ;
  ppname: FStar_Reflection_Data.ppname_t ;
  sort1: FStar_Reflection_Types.typ ;
  qual: FStar_Reflection_Data.aqualv ;
  attrs: FStar_Reflection_Types.term Prims.list }
let (__proj__Mkbinder__item__uniq : binder -> Prims.nat) =
  fun projectee ->
    match projectee with
    | { uniq; ppname; sort1 = sort; qual; attrs;_} -> uniq
let (__proj__Mkbinder__item__ppname :
  binder -> FStar_Reflection_Data.ppname_t) =
  fun projectee ->
    match projectee with
    | { uniq; ppname; sort1 = sort; qual; attrs;_} -> ppname
let (__proj__Mkbinder__item__sort : binder -> FStar_Reflection_Types.typ) =
  fun projectee ->
    match projectee with
    | { uniq; ppname; sort1 = sort; qual; attrs;_} -> sort
let (__proj__Mkbinder__item__qual : binder -> FStar_Reflection_Data.aqualv) =
  fun projectee ->
    match projectee with
    | { uniq; ppname; sort1 = sort; qual; attrs;_} -> qual
let (__proj__Mkbinder__item__attrs :
  binder -> FStar_Reflection_Types.term Prims.list) =
  fun projectee ->
    match projectee with
    | { uniq; ppname; sort1 = sort; qual; attrs;_} -> attrs
let (rbinder_to_string :
  FStar_Reflection_Types.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst" (Prims.of_int (77))
         (Prims.of_int (11)) (Prims.of_int (77)) (Prims.of_int (27)))
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst" (Prims.of_int (78))
         (Prims.of_int (2)) (Prims.of_int (78)) (Prims.of_int (57)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_Builtins.inspect_binder b))
      (fun uu___ ->
         (fun bv ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                    (Prims.of_int (78)) (Prims.of_int (2))
                    (Prims.of_int (78)) (Prims.of_int (18)))
                 (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                    (Prims.of_int (78)) (Prims.of_int (2))
                    (Prims.of_int (78)) (Prims.of_int (57)))
                 (Obj.magic
                    (FStar_Tactics_Builtins.unseal
                       bv.FStar_Reflection_Data.ppname2))
                 (fun uu___ ->
                    (fun uu___ ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range
                               "FStar.Tactics.NamedView.fst"
                               (Prims.of_int (78)) (Prims.of_int (21))
                               (Prims.of_int (78)) (Prims.of_int (57)))
                            (FStar_Range.mk_range "prims.fst"
                               (Prims.of_int (590)) (Prims.of_int (19))
                               (Prims.of_int (590)) (Prims.of_int (31)))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.NamedView.fst"
                                     (Prims.of_int (78)) (Prims.of_int (29))
                                     (Prims.of_int (78)) (Prims.of_int (57)))
                                  (FStar_Range.mk_range "prims.fst"
                                     (Prims.of_int (590)) (Prims.of_int (19))
                                     (Prims.of_int (590)) (Prims.of_int (31)))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.NamedView.fst"
                                           (Prims.of_int (78))
                                           (Prims.of_int (29))
                                           (Prims.of_int (78))
                                           (Prims.of_int (51)))
                                        (FStar_Range.mk_range "prims.fst"
                                           (Prims.of_int (590))
                                           (Prims.of_int (19))
                                           (Prims.of_int (590))
                                           (Prims.of_int (31)))
                                        (Obj.magic
                                           (FStar_Tactics_Builtins.term_to_string
                                              bv.FStar_Reflection_Data.sort2))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                Prims.strcat uu___1 ")"))))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          Prims.strcat "::(" uu___1))))
                            (fun uu___1 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 -> Prims.strcat uu___ uu___1))))
                      uu___))) uu___)
let (binder_to_string :
  binder -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst" (Prims.of_int (82))
         (Prims.of_int (2)) (Prims.of_int (82)) (Prims.of_int (17)))
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst" (Prims.of_int (82))
         (Prims.of_int (2)) (Prims.of_int (82)) (Prims.of_int (85)))
      (Obj.magic (FStar_Tactics_Builtins.unseal b.ppname))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                    (Prims.of_int (82)) (Prims.of_int (20))
                    (Prims.of_int (82)) (Prims.of_int (85)))
                 (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                    (Prims.of_int (19)) (Prims.of_int (590))
                    (Prims.of_int (31)))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (82)) (Prims.of_int (27))
                          (Prims.of_int (82)) (Prims.of_int (85)))
                       (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                          (Prims.of_int (19)) (Prims.of_int (590))
                          (Prims.of_int (31)))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "FStar.Tactics.NamedView.fst"
                                (Prims.of_int (82)) (Prims.of_int (50))
                                (Prims.of_int (82)) (Prims.of_int (85)))
                             (FStar_Range.mk_range "prims.fst"
                                (Prims.of_int (590)) (Prims.of_int (19))
                                (Prims.of_int (590)) (Prims.of_int (31)))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.NamedView.fst"
                                      (Prims.of_int (82)) (Prims.of_int (58))
                                      (Prims.of_int (82)) (Prims.of_int (85)))
                                   (FStar_Range.mk_range "prims.fst"
                                      (Prims.of_int (590))
                                      (Prims.of_int (19))
                                      (Prims.of_int (590))
                                      (Prims.of_int (31)))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.NamedView.fst"
                                            (Prims.of_int (82))
                                            (Prims.of_int (58))
                                            (Prims.of_int (82))
                                            (Prims.of_int (79)))
                                         (FStar_Range.mk_range "prims.fst"
                                            (Prims.of_int (590))
                                            (Prims.of_int (19))
                                            (Prims.of_int (590))
                                            (Prims.of_int (31)))
                                         (Obj.magic
                                            (FStar_Tactics_Builtins.term_to_string
                                               b.sort1))
                                         (fun uu___1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 Prims.strcat uu___1 ")"))))
                                   (fun uu___1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           Prims.strcat "::(" uu___1))))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     Prims.strcat
                                       (Prims.string_of_int b.uniq) uu___1))))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> Prims.strcat "@@" uu___1))))
                 (fun uu___1 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 -> Prims.strcat uu___ uu___1)))) uu___)
type binders = binder Prims.list
type 'b is_simple_binder = unit
type simple_binder = binder
type named_term_view =
  | Tv_Var of FStar_Reflection_Types.namedv 
  | Tv_BVar of FStar_Reflection_Types.bv 
  | Tv_FVar of FStar_Reflection_Types.fv 
  | Tv_UInst of FStar_Reflection_Types.fv * FStar_Reflection_Data.universes 
  | Tv_App of FStar_Reflection_Types.term * FStar_Reflection_Data.argv 
  | Tv_Abs of binder * FStar_Reflection_Types.term 
  | Tv_Arrow of binder * FStar_Reflection_Types.comp 
  | Tv_Type of FStar_Reflection_Types.universe 
  | Tv_Refine of simple_binder * FStar_Reflection_Types.term 
  | Tv_Const of FStar_Reflection_Data.vconst 
  | Tv_Uvar of Prims.nat * FStar_Reflection_Types.ctx_uvar_and_subst 
  | Tv_Let of Prims.bool * FStar_Reflection_Types.term Prims.list *
  simple_binder * FStar_Reflection_Types.term * FStar_Reflection_Types.term 
  | Tv_Match of FStar_Reflection_Types.term *
  FStar_Reflection_Types.match_returns_ascription
  FStar_Pervasives_Native.option * branch Prims.list 
  | Tv_AscribedT of FStar_Reflection_Types.term * FStar_Reflection_Types.term
  * FStar_Reflection_Types.term FStar_Pervasives_Native.option * Prims.bool 
  | Tv_AscribedC of FStar_Reflection_Types.term * FStar_Reflection_Types.comp
  * FStar_Reflection_Types.term FStar_Pervasives_Native.option * Prims.bool 
  | Tv_Unknown 
  | Tv_Unsupp 
let (uu___is_Tv_Var : named_term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Var v -> true | uu___ -> false
let (__proj__Tv_Var__item__v :
  named_term_view -> FStar_Reflection_Types.namedv) =
  fun projectee -> match projectee with | Tv_Var v -> v
let (uu___is_Tv_BVar : named_term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_BVar v -> true | uu___ -> false
let (__proj__Tv_BVar__item__v : named_term_view -> FStar_Reflection_Types.bv)
  = fun projectee -> match projectee with | Tv_BVar v -> v
let (uu___is_Tv_FVar : named_term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_FVar v -> true | uu___ -> false
let (__proj__Tv_FVar__item__v : named_term_view -> FStar_Reflection_Types.fv)
  = fun projectee -> match projectee with | Tv_FVar v -> v
let (uu___is_Tv_UInst : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_UInst (v, us) -> true | uu___ -> false
let (__proj__Tv_UInst__item__v :
  named_term_view -> FStar_Reflection_Types.fv) =
  fun projectee -> match projectee with | Tv_UInst (v, us) -> v
let (__proj__Tv_UInst__item__us :
  named_term_view -> FStar_Reflection_Data.universes) =
  fun projectee -> match projectee with | Tv_UInst (v, us) -> us
let (uu___is_Tv_App : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_App (hd, a) -> true | uu___ -> false
let (__proj__Tv_App__item__hd :
  named_term_view -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Tv_App (hd, a) -> hd
let (__proj__Tv_App__item__a : named_term_view -> FStar_Reflection_Data.argv)
  = fun projectee -> match projectee with | Tv_App (hd, a) -> a
let (uu___is_Tv_Abs : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Abs (bv, body) -> true | uu___ -> false
let (__proj__Tv_Abs__item__bv : named_term_view -> binder) =
  fun projectee -> match projectee with | Tv_Abs (bv, body) -> bv
let (__proj__Tv_Abs__item__body :
  named_term_view -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Tv_Abs (bv, body) -> body
let (uu___is_Tv_Arrow : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Arrow (bv, c) -> true | uu___ -> false
let (__proj__Tv_Arrow__item__bv : named_term_view -> binder) =
  fun projectee -> match projectee with | Tv_Arrow (bv, c) -> bv
let (__proj__Tv_Arrow__item__c :
  named_term_view -> FStar_Reflection_Types.comp) =
  fun projectee -> match projectee with | Tv_Arrow (bv, c) -> c
let (uu___is_Tv_Type : named_term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Type _0 -> true | uu___ -> false
let (__proj__Tv_Type__item___0 :
  named_term_view -> FStar_Reflection_Types.universe) =
  fun projectee -> match projectee with | Tv_Type _0 -> _0
let (uu___is_Tv_Refine : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Refine (b, ref) -> true | uu___ -> false
let (__proj__Tv_Refine__item__b : named_term_view -> simple_binder) =
  fun projectee -> match projectee with | Tv_Refine (b, ref) -> b
let (__proj__Tv_Refine__item__ref :
  named_term_view -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Tv_Refine (b, ref) -> ref
let (uu___is_Tv_Const : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Const _0 -> true | uu___ -> false
let (__proj__Tv_Const__item___0 :
  named_term_view -> FStar_Reflection_Data.vconst) =
  fun projectee -> match projectee with | Tv_Const _0 -> _0
let (uu___is_Tv_Uvar : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Uvar (_0, _1) -> true | uu___ -> false
let (__proj__Tv_Uvar__item___0 : named_term_view -> Prims.nat) =
  fun projectee -> match projectee with | Tv_Uvar (_0, _1) -> _0
let (__proj__Tv_Uvar__item___1 :
  named_term_view -> FStar_Reflection_Types.ctx_uvar_and_subst) =
  fun projectee -> match projectee with | Tv_Uvar (_0, _1) -> _1
let (uu___is_Tv_Let : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Tv_Let (recf, attrs, b, def, body) -> true
    | uu___ -> false
let (__proj__Tv_Let__item__recf : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Let (recf, attrs, b, def, body) -> recf
let (__proj__Tv_Let__item__attrs :
  named_term_view -> FStar_Reflection_Types.term Prims.list) =
  fun projectee ->
    match projectee with | Tv_Let (recf, attrs, b, def, body) -> attrs
let (__proj__Tv_Let__item__b : named_term_view -> simple_binder) =
  fun projectee ->
    match projectee with | Tv_Let (recf, attrs, b, def, body) -> b
let (__proj__Tv_Let__item__def :
  named_term_view -> FStar_Reflection_Types.term) =
  fun projectee ->
    match projectee with | Tv_Let (recf, attrs, b, def, body) -> def
let (__proj__Tv_Let__item__body :
  named_term_view -> FStar_Reflection_Types.term) =
  fun projectee ->
    match projectee with | Tv_Let (recf, attrs, b, def, body) -> body
let (uu___is_Tv_Match : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Tv_Match (scrutinee, ret, brs) -> true
    | uu___ -> false
let (__proj__Tv_Match__item__scrutinee :
  named_term_view -> FStar_Reflection_Types.term) =
  fun projectee ->
    match projectee with | Tv_Match (scrutinee, ret, brs) -> scrutinee
let (__proj__Tv_Match__item__ret :
  named_term_view ->
    FStar_Reflection_Types.match_returns_ascription
      FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with | Tv_Match (scrutinee, ret, brs) -> ret
let (__proj__Tv_Match__item__brs : named_term_view -> branch Prims.list) =
  fun projectee ->
    match projectee with | Tv_Match (scrutinee, ret, brs) -> brs
let (uu___is_Tv_AscribedT : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Tv_AscribedT (e, t, tac, use_eq) -> true
    | uu___ -> false
let (__proj__Tv_AscribedT__item__e :
  named_term_view -> FStar_Reflection_Types.term) =
  fun projectee ->
    match projectee with | Tv_AscribedT (e, t, tac, use_eq) -> e
let (__proj__Tv_AscribedT__item__t :
  named_term_view -> FStar_Reflection_Types.term) =
  fun projectee ->
    match projectee with | Tv_AscribedT (e, t, tac, use_eq) -> t
let (__proj__Tv_AscribedT__item__tac :
  named_term_view ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with | Tv_AscribedT (e, t, tac, use_eq) -> tac
let (__proj__Tv_AscribedT__item__use_eq : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_AscribedT (e, t, tac, use_eq) -> use_eq
let (uu___is_Tv_AscribedC : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Tv_AscribedC (e, c, tac, use_eq) -> true
    | uu___ -> false
let (__proj__Tv_AscribedC__item__e :
  named_term_view -> FStar_Reflection_Types.term) =
  fun projectee ->
    match projectee with | Tv_AscribedC (e, c, tac, use_eq) -> e
let (__proj__Tv_AscribedC__item__c :
  named_term_view -> FStar_Reflection_Types.comp) =
  fun projectee ->
    match projectee with | Tv_AscribedC (e, c, tac, use_eq) -> c
let (__proj__Tv_AscribedC__item__tac :
  named_term_view ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with | Tv_AscribedC (e, c, tac, use_eq) -> tac
let (__proj__Tv_AscribedC__item__use_eq : named_term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_AscribedC (e, c, tac, use_eq) -> use_eq
let (uu___is_Tv_Unknown : named_term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Unknown -> true | uu___ -> false
let (uu___is_Tv_Unsupp : named_term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Unsupp -> true | uu___ -> false
let (__binding_to_binder :
  FStar_Reflection_Data.binding -> FStar_Reflection_Types.binder -> binder) =
  fun bnd ->
    fun b ->
      {
        uniq = (bnd.FStar_Reflection_Data.uniq1);
        ppname = (bnd.FStar_Reflection_Data.ppname3);
        sort1 = (bnd.FStar_Reflection_Data.sort3);
        qual =
          ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.qual);
        attrs =
          ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.attrs)
      }
let (binding_to_binder : FStar_Reflection_Data.binding -> binder) =
  fun bnd ->
    {
      uniq = (bnd.FStar_Reflection_Data.uniq1);
      ppname = (bnd.FStar_Reflection_Data.ppname3);
      sort1 = (bnd.FStar_Reflection_Data.sort3);
      qual = FStar_Reflection_Data.Q_Explicit;
      attrs = []
    }
let (binder_to_binding : binder -> FStar_Reflection_Data.binding) =
  fun b ->
    {
      FStar_Reflection_Data.uniq1 = (b.uniq);
      FStar_Reflection_Data.sort3 = (b.sort1);
      FStar_Reflection_Data.ppname3 = (b.ppname)
    }
let (binder_to_namedv : binder -> FStar_Reflection_Types.namedv) =
  fun b ->
    FStar_Reflection_Builtins.pack_namedv
      {
        FStar_Reflection_Data.uniq = (b.uniq);
        FStar_Reflection_Data.sort = (FStar_Sealed.seal b.sort1);
        FStar_Reflection_Data.ppname = (b.ppname)
      }
let (namedv_to_binder :
  FStar_Reflection_Types.namedv -> FStar_Reflection_Types.term -> binder) =
  fun nv ->
    fun sort ->
      let nvv = FStar_Reflection_Builtins.inspect_namedv nv in
      {
        uniq = (nvv.FStar_Reflection_Data.uniq);
        ppname = (nvv.FStar_Reflection_Data.ppname);
        sort1 = sort;
        qual = FStar_Reflection_Data.Q_Explicit;
        attrs = []
      }
let (binding_to_simple_binder :
  FStar_Reflection_Data.binding -> simple_binder) =
  fun b ->
    {
      uniq = (b.FStar_Reflection_Data.uniq1);
      ppname = (b.FStar_Reflection_Data.ppname3);
      sort1 = (b.FStar_Reflection_Data.sort3);
      qual = FStar_Reflection_Data.Q_Explicit;
      attrs = []
    }
let (simple_binder_to_binding :
  simple_binder -> FStar_Reflection_Data.binding) =
  fun b ->
    {
      FStar_Reflection_Data.uniq1 = (b.uniq);
      FStar_Reflection_Data.sort3 = (b.sort1);
      FStar_Reflection_Data.ppname3 = (b.ppname)
    }
let (open_term_with :
  FStar_Reflection_Types.binder ->
    binder ->
      FStar_Reflection_Types.term ->
        (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun b ->
           fun nb ->
             fun t ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       FStar_Reflection_Builtins.subst_term
                         [FStar_Syntax_Syntax.DB
                            (Prims.int_zero,
                              (FStar_Reflection_Builtins.pack_namedv
                                 {
                                   FStar_Reflection_Data.uniq = (nb.uniq);
                                   FStar_Reflection_Data.sort =
                                     (FStar_Sealed.seal nb.sort1);
                                   FStar_Reflection_Data.ppname = (nb.ppname)
                                 }))] t))) uu___2 uu___1 uu___
let (open_term :
  FStar_Reflection_Types.binder ->
    FStar_Reflection_Types.term ->
      ((binder * FStar_Reflection_Types.term), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
           (Prims.of_int (178)) (Prims.of_int (10)) (Prims.of_int (178))
           (Prims.of_int (18)))
        (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
           (Prims.of_int (178)) (Prims.of_int (21)) (Prims.of_int (188))
           (Prims.of_int (33))) (Obj.magic (FStar_Tactics_Builtins.fresh ()))
        (fun uu___ ->
           (fun n ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (179)) (Prims.of_int (11))
                      (Prims.of_int (179)) (Prims.of_int (27)))
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (179)) (Prims.of_int (30))
                      (Prims.of_int (188)) (Prims.of_int (33)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         FStar_Reflection_Builtins.inspect_binder b))
                   (fun uu___ ->
                      (fun bv ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.Tactics.NamedView.fst"
                                 (Prims.of_int (181)) (Prims.of_int (4))
                                 (Prims.of_int (185)) (Prims.of_int (22)))
                              (FStar_Range.mk_range
                                 "FStar.Tactics.NamedView.fst"
                                 (Prims.of_int (188)) (Prims.of_int (2))
                                 (Prims.of_int (188)) (Prims.of_int (33)))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ ->
                                    {
                                      uniq = n;
                                      ppname =
                                        (bv.FStar_Reflection_Data.ppname2);
                                      sort1 =
                                        (bv.FStar_Reflection_Data.sort2);
                                      qual = (bv.FStar_Reflection_Data.qual);
                                      attrs =
                                        (bv.FStar_Reflection_Data.attrs)
                                    }))
                              (fun uu___ ->
                                 (fun bndr ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.NamedView.fst"
                                            (Prims.of_int (188))
                                            (Prims.of_int (9))
                                            (Prims.of_int (188))
                                            (Prims.of_int (32)))
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.NamedView.fst"
                                            (Prims.of_int (188))
                                            (Prims.of_int (2))
                                            (Prims.of_int (188))
                                            (Prims.of_int (33)))
                                         (Obj.magic (open_term_with b bndr t))
                                         (fun uu___ ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 -> (bndr, uu___)))))
                                   uu___))) uu___))) uu___)
let (open_comp :
  FStar_Reflection_Types.binder ->
    FStar_Reflection_Types.comp ->
      ((binder * FStar_Reflection_Types.comp), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
           (Prims.of_int (191)) (Prims.of_int (10)) (Prims.of_int (191))
           (Prims.of_int (18)))
        (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
           (Prims.of_int (191)) (Prims.of_int (21)) (Prims.of_int (208))
           (Prims.of_int (12))) (Obj.magic (FStar_Tactics_Builtins.fresh ()))
        (fun n ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                ({
                   uniq = n;
                   ppname =
                     ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.ppname2);
                   sort1 =
                     ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.sort2);
                   qual =
                     ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.qual);
                   attrs =
                     ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.attrs)
                 },
                  (FStar_Reflection_Builtins.subst_comp
                     [FStar_Syntax_Syntax.DB
                        (Prims.int_zero,
                          (FStar_Reflection_Builtins.pack_namedv
                             {
                               FStar_Reflection_Data.uniq = n;
                               FStar_Reflection_Data.sort =
                                 (FStar_Sealed.seal
                                    (FStar_Reflection_Builtins.inspect_binder
                                       b).FStar_Reflection_Data.sort2);
                               FStar_Reflection_Data.ppname =
                                 ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.ppname2)
                             }))] t))))
let (open_term_simple :
  FStar_Reflection_Data.simple_binder ->
    FStar_Reflection_Types.term ->
      ((simple_binder * FStar_Reflection_Types.term), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
           (Prims.of_int (213)) (Prims.of_int (10)) (Prims.of_int (213))
           (Prims.of_int (18)))
        (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
           (Prims.of_int (213)) (Prims.of_int (21)) (Prims.of_int (230))
           (Prims.of_int (12))) (Obj.magic (FStar_Tactics_Builtins.fresh ()))
        (fun n ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                ({
                   uniq = n;
                   ppname =
                     ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.ppname2);
                   sort1 =
                     ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.sort2);
                   qual =
                     ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.qual);
                   attrs =
                     ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.attrs)
                 },
                  (FStar_Reflection_Builtins.subst_term
                     [FStar_Syntax_Syntax.DB
                        (Prims.int_zero,
                          (FStar_Reflection_Builtins.pack_namedv
                             {
                               FStar_Reflection_Data.uniq = n;
                               FStar_Reflection_Data.sort =
                                 (FStar_Sealed.seal
                                    (FStar_Reflection_Builtins.inspect_binder
                                       b).FStar_Reflection_Data.sort2);
                               FStar_Reflection_Data.ppname =
                                 ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.ppname2)
                             }))] t))))
let (open_comp_simple :
  FStar_Reflection_Data.simple_binder ->
    FStar_Reflection_Types.comp ->
      ((simple_binder * FStar_Reflection_Types.comp), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
           (Prims.of_int (233)) (Prims.of_int (10)) (Prims.of_int (233))
           (Prims.of_int (18)))
        (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
           (Prims.of_int (233)) (Prims.of_int (21)) (Prims.of_int (250))
           (Prims.of_int (12))) (Obj.magic (FStar_Tactics_Builtins.fresh ()))
        (fun n ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                ({
                   uniq = n;
                   ppname =
                     ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.ppname2);
                   sort1 =
                     ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.sort2);
                   qual =
                     ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.qual);
                   attrs =
                     ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.attrs)
                 },
                  (FStar_Reflection_Builtins.subst_comp
                     [FStar_Syntax_Syntax.DB
                        (Prims.int_zero,
                          (FStar_Reflection_Builtins.pack_namedv
                             {
                               FStar_Reflection_Data.uniq = n;
                               FStar_Reflection_Data.sort =
                                 (FStar_Sealed.seal
                                    (FStar_Reflection_Builtins.inspect_binder
                                       b).FStar_Reflection_Data.sort2);
                               FStar_Reflection_Data.ppname =
                                 ((FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.ppname2)
                             }))] t))))
let (close_term :
  binder ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.binder * FStar_Reflection_Types.term))
  =
  fun b ->
    fun t ->
      let nv = binder_to_namedv b in
      let t' =
        FStar_Reflection_Builtins.subst_term
          [FStar_Syntax_Syntax.NM (nv, Prims.int_zero)] t in
      let b1 =
        FStar_Reflection_Builtins.pack_binder
          {
            FStar_Reflection_Data.sort2 = (b.sort1);
            FStar_Reflection_Data.qual = (b.qual);
            FStar_Reflection_Data.attrs = (b.attrs);
            FStar_Reflection_Data.ppname2 = (b.ppname)
          } in
      (b1, t')
let (close_comp :
  binder ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Types.binder * FStar_Reflection_Types.comp))
  =
  fun b ->
    fun t ->
      let nv = binder_to_namedv b in
      let t' =
        FStar_Reflection_Builtins.subst_comp
          [FStar_Syntax_Syntax.NM (nv, Prims.int_zero)] t in
      let b1 =
        FStar_Reflection_Builtins.pack_binder
          {
            FStar_Reflection_Data.sort2 = (b.sort1);
            FStar_Reflection_Data.qual = (b.qual);
            FStar_Reflection_Data.attrs = (b.attrs);
            FStar_Reflection_Data.ppname2 = (b.ppname)
          } in
      (b1, t')
let (close_term_simple :
  simple_binder ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Data.simple_binder * FStar_Reflection_Types.term))
  =
  fun b ->
    fun t ->
      let nv = binder_to_namedv b in
      let t' =
        FStar_Reflection_Builtins.subst_term
          [FStar_Syntax_Syntax.NM (nv, Prims.int_zero)] t in
      let bv =
        {
          FStar_Reflection_Data.sort2 = (b.sort1);
          FStar_Reflection_Data.qual = (b.qual);
          FStar_Reflection_Data.attrs = (b.attrs);
          FStar_Reflection_Data.ppname2 = (b.ppname)
        } in
      let b1 = FStar_Reflection_Builtins.pack_binder bv in (b1, t')
let (close_comp_simple :
  simple_binder ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Data.simple_binder * FStar_Reflection_Types.comp))
  =
  fun b ->
    fun t ->
      let nv = binder_to_namedv b in
      let t' =
        FStar_Reflection_Builtins.subst_comp
          [FStar_Syntax_Syntax.NM (nv, Prims.int_zero)] t in
      let bv =
        {
          FStar_Reflection_Data.sort2 = (b.sort1);
          FStar_Reflection_Data.qual = (b.qual);
          FStar_Reflection_Data.attrs = (b.attrs);
          FStar_Reflection_Data.ppname2 = (b.ppname)
        } in
      let b1 = FStar_Reflection_Builtins.pack_binder bv in (b1, t')
let rec (open_term_n :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      ((binder Prims.list * FStar_Reflection_Types.term), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun t ->
           match bs with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ([], t))))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (283)) (Prims.of_int (18))
                          (Prims.of_int (283)) (Prims.of_int (34)))
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (282)) (Prims.of_int (12))
                          (Prims.of_int (285)) (Prims.of_int (18)))
                       (Obj.magic (open_term_n bs1 t))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | (bs', t') ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.NamedView.fst"
                                         (Prims.of_int (284))
                                         (Prims.of_int (18))
                                         (Prims.of_int (284))
                                         (Prims.of_int (32)))
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.NamedView.fst"
                                         (Prims.of_int (283))
                                         (Prims.of_int (37))
                                         (Prims.of_int (285))
                                         (Prims.of_int (18)))
                                      (Obj.magic (open_term b t'))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              match uu___1 with
                                              | (b', t'') ->
                                                  ((b' :: bs'), t'')))))
                            uu___)))) uu___1 uu___
let rec (open_term_n_with :
  FStar_Reflection_Types.binder Prims.list ->
    binder Prims.list ->
      FStar_Reflection_Types.term ->
        (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun bs ->
           fun nbs ->
             fun t ->
               match (bs, nbs) with
               | ([], []) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
               | (b::bs1, nb::nbs1) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "FStar.Tactics.NamedView.fst"
                              (Prims.of_int (291)) (Prims.of_int (13))
                              (Prims.of_int (291)) (Prims.of_int (38)))
                           (FStar_Range.mk_range
                              "FStar.Tactics.NamedView.fst"
                              (Prims.of_int (291)) (Prims.of_int (41))
                              (Prims.of_int (293)) (Prims.of_int (7)))
                           (Obj.magic (open_term_n_with bs1 nbs1 t))
                           (fun uu___ ->
                              (fun t' ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.NamedView.fst"
                                         (Prims.of_int (292))
                                         (Prims.of_int (14))
                                         (Prims.of_int (292))
                                         (Prims.of_int (36)))
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.NamedView.fst"
                                         (Prims.of_int (292))
                                         (Prims.of_int (8))
                                         (Prims.of_int (292))
                                         (Prims.of_int (11)))
                                      (Obj.magic (open_term_with b nb t'))
                                      (fun t'' ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___ -> t'')))) uu___)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr (FStar_Tactics_Effect.raise LengthMismatch)))
          uu___2 uu___1 uu___
let rec (close_term_n :
  binder Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.binder Prims.list *
        FStar_Reflection_Types.term))
  =
  fun bs ->
    fun t ->
      match bs with
      | [] -> ([], t)
      | b::bs1 ->
          let uu___ = close_term_n bs1 t in
          (match uu___ with
           | (bs', t') ->
               let uu___1 = close_term b t' in
               (match uu___1 with | (b', t'') -> ((b' :: bs'), t'')))
let rec (open_term_n_simple :
  FStar_Reflection_Data.simple_binder Prims.list ->
    FStar_Reflection_Types.term ->
      ((simple_binder Prims.list * FStar_Reflection_Types.term), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun t ->
           match bs with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ([], t))))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (308)) (Prims.of_int (18))
                          (Prims.of_int (308)) (Prims.of_int (41)))
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (307)) (Prims.of_int (12))
                          (Prims.of_int (310)) (Prims.of_int (18)))
                       (Obj.magic (open_term_n_simple bs1 t))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | (bs', t') ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.NamedView.fst"
                                         (Prims.of_int (309))
                                         (Prims.of_int (18))
                                         (Prims.of_int (309))
                                         (Prims.of_int (39)))
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.NamedView.fst"
                                         (Prims.of_int (308))
                                         (Prims.of_int (44))
                                         (Prims.of_int (310))
                                         (Prims.of_int (18)))
                                      (Obj.magic (open_term_simple b t'))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              match uu___1 with
                                              | (b', t'') ->
                                                  ((b' :: bs'), t'')))))
                            uu___)))) uu___1 uu___
let rec (close_term_n_simple :
  simple_binder Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Data.simple_binder Prims.list *
        FStar_Reflection_Types.term))
  =
  fun bs ->
    fun t ->
      match bs with
      | [] -> ([], t)
      | b::bs1 ->
          let uu___ = close_term_n_simple bs1 t in
          (match uu___ with
           | (bs', t') ->
               let uu___1 = close_term_simple b t' in
               (match uu___1 with | (b', t'') -> ((b' :: bs'), t'')))
let (open_univ_s :
  FStar_Reflection_Types.univ_name Prims.list ->
    ((FStar_Reflection_Types.univ_name Prims.list *
       FStar_Syntax_Syntax.subst_t),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun us ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
         (Prims.of_int (321)) (Prims.of_int (10)) (Prims.of_int (321))
         (Prims.of_int (28)))
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
         (Prims.of_int (321)) (Prims.of_int (31)) (Prims.of_int (323))
         (Prims.of_int (7)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_List_Tot_Base.length us))
      (fun uu___ ->
         (fun n ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                    (Prims.of_int (322)) (Prims.of_int (10))
                    (Prims.of_int (322)) (Prims.of_int (69)))
                 (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                    (Prims.of_int (323)) (Prims.of_int (2))
                    (Prims.of_int (323)) (Prims.of_int (7)))
                 (Obj.magic
                    (FStar_Tactics_Util.mapi
                       (fun uu___1 ->
                          fun uu___ ->
                            (fun i ->
                               fun u ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ ->
                                         FStar_Syntax_Syntax.UN
                                           (((n - Prims.int_one) - i),
                                             (FStar_Reflection_Builtins.pack_universe
                                                (FStar_Reflection_Data.Uv_Name
                                                   u)))))) uu___1 uu___) us))
                 (fun s ->
                    FStar_Tactics_Effect.lift_div_tac (fun uu___ -> (us, s)))))
           uu___)
let (close_univ_s :
  FStar_Reflection_Types.univ_name Prims.list ->
    (FStar_Reflection_Types.univ_name Prims.list *
      FStar_Syntax_Syntax.subst_t))
  =
  fun us ->
    let n = FStar_List_Tot_Base.length us in
    let s =
      FStar_List_Tot_Base.mapi
        (fun i ->
           fun u ->
             FStar_Syntax_Syntax.UD
               ((FStar_Reflection_Builtins.pack_ident u),
                 ((n - i) - Prims.int_one))) us in
    (us, s)
let (subst_binder_sort :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Reflection_Types.binder -> FStar_Reflection_Types.binder)
  =
  fun s ->
    fun b ->
      let v = FStar_Reflection_Builtins.inspect_binder b in
      let v1 =
        {
          FStar_Reflection_Data.sort2 =
            (FStar_Reflection_Builtins.subst_term s
               v.FStar_Reflection_Data.sort2);
          FStar_Reflection_Data.qual = (v.FStar_Reflection_Data.qual);
          FStar_Reflection_Data.attrs = (v.FStar_Reflection_Data.attrs);
          FStar_Reflection_Data.ppname2 = (v.FStar_Reflection_Data.ppname2)
        } in
      FStar_Reflection_Builtins.pack_binder v1
let rec (open_pat :
  FStar_Reflection_Data.pattern ->
    FStar_Syntax_Syntax.subst_t ->
      ((pattern * FStar_Syntax_Syntax.subst_t), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun p ->
         fun s ->
           match p with
           | FStar_Reflection_Data.Pat_Constant c ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> ((Pat_Constant { c }), s))))
           | FStar_Reflection_Data.Pat_Var (ssort, n) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (341)) (Prims.of_int (15))
                          (Prims.of_int (341)) (Prims.of_int (27)))
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (341)) (Prims.of_int (30))
                          (Prims.of_int (349)) (Prims.of_int (64)))
                       (Obj.magic (FStar_Tactics_Builtins.unseal ssort))
                       (fun uu___ ->
                          (fun sort ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.NamedView.fst"
                                     (Prims.of_int (342)) (Prims.of_int (15))
                                     (Prims.of_int (342)) (Prims.of_int (32)))
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.NamedView.fst"
                                     (Prims.of_int (342)) (Prims.of_int (35))
                                     (Prims.of_int (349)) (Prims.of_int (64)))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ ->
                                        FStar_Reflection_Builtins.subst_term
                                          s sort))
                                  (fun uu___ ->
                                     (fun sort1 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.NamedView.fst"
                                                (Prims.of_int (343))
                                                (Prims.of_int (22))
                                                (Prims.of_int (347))
                                                (Prims.of_int (5)))
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.NamedView.fst"
                                                (Prims.of_int (349))
                                                (Prims.of_int (4))
                                                (Prims.of_int (349))
                                                (Prims.of_int (64)))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.NamedView.fst"
                                                      (Prims.of_int (344))
                                                      (Prims.of_int (6))
                                                      (Prims.of_int (346))
                                                      (Prims.of_int (17)))
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.NamedView.fst"
                                                      (Prims.of_int (343))
                                                      (Prims.of_int (22))
                                                      (Prims.of_int (347))
                                                      (Prims.of_int (5)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.NamedView.fst"
                                                            (Prims.of_int (344))
                                                            (Prims.of_int (13))
                                                            (Prims.of_int (344))
                                                            (Prims.of_int (20)))
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.NamedView.fst"
                                                            (Prims.of_int (344))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (346))
                                                            (Prims.of_int (17)))
                                                         (Obj.magic
                                                            (FStar_Tactics_Builtins.fresh
                                                               ()))
                                                         (fun uu___ ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___1 ->
                                                                 {
                                                                   FStar_Reflection_Data.uniq
                                                                    = uu___;
                                                                   FStar_Reflection_Data.sort
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    sort1);
                                                                   FStar_Reflection_Data.ppname
                                                                    = n
                                                                 }))))
                                                   (fun uu___ ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           FStar_Reflection_Builtins.pack_namedv
                                                             uu___))))
                                             (fun nv ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___ ->
                                                     ((Pat_Var
                                                         {
                                                           v = nv;
                                                           sort =
                                                             (FStar_Sealed.seal
                                                                sort1)
                                                         }),
                                                       ((FStar_Syntax_Syntax.DB
                                                           (Prims.int_zero,
                                                             nv)) ::
                                                       (FStar_Reflection_Derived.shift_subst
                                                          Prims.int_one s)))))))
                                       uu___))) uu___)))
           | FStar_Reflection_Data.Pat_Cons (head, univs, subpats) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (352)) (Prims.of_int (21))
                          (Prims.of_int (355)) (Prims.of_int (38)))
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (351)) (Prims.of_int (36))
                          (Prims.of_int (358)) (Prims.of_int (57)))
                       (Obj.magic
                          (FStar_Tactics_Util.fold_left
                             (fun uu___ ->
                                fun uu___1 ->
                                  match (uu___, uu___1) with
                                  | ((pats, s1), (pat, b)) ->
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.NamedView.fst"
                                           (Prims.of_int (353))
                                           (Prims.of_int (38))
                                           (Prims.of_int (353))
                                           (Prims.of_int (52)))
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.NamedView.fst"
                                           (Prims.of_int (352))
                                           (Prims.of_int (55))
                                           (Prims.of_int (354))
                                           (Prims.of_int (43)))
                                        (Obj.magic (open_pat pat s1))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                match uu___2 with
                                                | (pat1, s') ->
                                                    (((pat1, b) :: pats), s'))))
                             ([], s) subpats))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               match uu___ with
                               | (subpats1, s1) ->
                                   ((Pat_Cons
                                       {
                                         head;
                                         univs;
                                         subpats =
                                           (FStar_List_Tot_Base.rev subpats1)
                                       }), s1)))))
           | FStar_Reflection_Data.Pat_Dot_Term
               (FStar_Pervasives_Native.None) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          ((Pat_Dot_Term { t = FStar_Pervasives_Native.None }),
                            s))))
           | FStar_Reflection_Data.Pat_Dot_Term (FStar_Pervasives_Native.Some
               t) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          ((Pat_Dot_Term
                              {
                                t =
                                  (FStar_Pervasives_Native.Some
                                     (FStar_Reflection_Builtins.subst_term s
                                        t))
                              }), s))))) uu___1 uu___
let (open_branch :
  FStar_Reflection_Data.branch ->
    (branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
         (Prims.of_int (368)) (Prims.of_int (17)) (Prims.of_int (368))
         (Prims.of_int (18)))
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
         (Prims.of_int (367)) (Prims.of_int (45)) (Prims.of_int (371))
         (Prims.of_int (11)))
      (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> b))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (pat, t) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                        (Prims.of_int (369)) (Prims.of_int (15))
                        (Prims.of_int (369)) (Prims.of_int (30)))
                     (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                        (Prims.of_int (368)) (Prims.of_int (21))
                        (Prims.of_int (371)) (Prims.of_int (11)))
                     (Obj.magic (open_pat pat []))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             match uu___1 with
                             | (pat1, s) ->
                                 (pat1,
                                   (FStar_Reflection_Builtins.subst_term s t))))))
           uu___)
let rec (close_pat :
  pattern ->
    FStar_Syntax_Syntax.subst_t ->
      (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.subst_t))
  =
  fun p ->
    fun s ->
      match p with
      | Pat_Constant { c;_} -> ((FStar_Reflection_Data.Pat_Constant c), s)
      | Pat_Var { v; sort;_} ->
          let s1 = (FStar_Syntax_Syntax.NM (v, Prims.int_zero)) ::
            (FStar_Reflection_Derived.shift_subst Prims.int_one s) in
          ((FStar_Reflection_Data.Pat_Var
              (sort,
                ((FStar_Reflection_Builtins.inspect_namedv v).FStar_Reflection_Data.ppname))),
            s1)
      | Pat_Cons { head; univs; subpats;_} ->
          let uu___ =
            FStar_List_Tot_Base.fold_left
              (fun uu___1 ->
                 fun uu___2 ->
                   match (uu___1, uu___2) with
                   | ((pats, s1), (pat, b)) ->
                       let uu___3 = close_pat pat s1 in
                       (match uu___3 with
                        | (pat1, s') -> (((pat1, b) :: pats), s'))) ([], s)
              subpats in
          (match uu___ with
           | (subpats1, s1) ->
               let subpats2 = FStar_List_Tot_Base.rev subpats1 in
               ((FStar_Reflection_Data.Pat_Cons (head, univs, subpats2)), s1))
      | Pat_Dot_Term { t = FStar_Pervasives_Native.None;_} ->
          ((FStar_Reflection_Data.Pat_Dot_Term FStar_Pervasives_Native.None),
            s)
      | Pat_Dot_Term { t = FStar_Pervasives_Native.Some t;_} ->
          let t1 = FStar_Reflection_Builtins.subst_term s t in
          ((FStar_Reflection_Data.Pat_Dot_Term
              (FStar_Pervasives_Native.Some t1)), s)
let (close_branch : branch -> FStar_Reflection_Data.branch) =
  fun b ->
    let uu___ = b in
    match uu___ with
    | (pat, t) ->
        let uu___1 = close_pat pat [] in
        (match uu___1 with
         | (pat1, s) ->
             let t' = FStar_Reflection_Builtins.subst_term s t in (pat1, t'))
let (open_view :
  FStar_Reflection_Data.term_view ->
    (named_term_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun tv ->
       match tv with
       | FStar_Reflection_Data.Tv_Var v ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Tv_Var v)))
       | FStar_Reflection_Data.Tv_BVar v ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Tv_BVar v)))
       | FStar_Reflection_Data.Tv_FVar v ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Tv_FVar v)))
       | FStar_Reflection_Data.Tv_UInst (v, us) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Tv_UInst (v, us))))
       | FStar_Reflection_Data.Tv_App (hd, a) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Tv_App (hd, a))))
       | FStar_Reflection_Data.Tv_Type u ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Tv_Type u)))
       | FStar_Reflection_Data.Tv_Const c ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Tv_Const c)))
       | FStar_Reflection_Data.Tv_Uvar (n, ctx_uvar_and_subst) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Tv_Uvar (n, ctx_uvar_and_subst))))
       | FStar_Reflection_Data.Tv_AscribedT (e, t, tac, use_eq) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Tv_AscribedT (e, t, tac, use_eq))))
       | FStar_Reflection_Data.Tv_AscribedC (e, c, tac, use_eq) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Tv_AscribedC (e, c, tac, use_eq))))
       | FStar_Reflection_Data.Tv_Unknown ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Tv_Unknown)))
       | FStar_Reflection_Data.Tv_Unsupp ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Tv_Unsupp)))
       | FStar_Reflection_Data.Tv_Abs (b, body) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (430)) (Prims.of_int (19))
                      (Prims.of_int (430)) (Prims.of_int (35)))
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (429)) (Prims.of_int (23))
                      (Prims.of_int (431)) (Prims.of_int (18)))
                   (Obj.magic (open_term b body))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           match uu___ with
                           | (nb, body1) -> Tv_Abs (nb, body1)))))
       | FStar_Reflection_Data.Tv_Arrow (b, c) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (434)) (Prims.of_int (16))
                      (Prims.of_int (434)) (Prims.of_int (29)))
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (433)) (Prims.of_int (22))
                      (Prims.of_int (435)) (Prims.of_int (17)))
                   (Obj.magic (open_comp b c))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           match uu___ with | (nb, c1) -> Tv_Arrow (nb, c1)))))
       | FStar_Reflection_Data.Tv_Refine (b, ref) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (438)) (Prims.of_int (18))
                      (Prims.of_int (438)) (Prims.of_int (40)))
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (437)) (Prims.of_int (25))
                      (Prims.of_int (439)) (Prims.of_int (20)))
                   (Obj.magic (open_term_simple b ref))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           match uu___ with
                           | (nb, ref1) -> Tv_Refine (nb, ref1)))))
       | FStar_Reflection_Data.Tv_Let (recf, attrs, b, def, body) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (442)) (Prims.of_int (19))
                      (Prims.of_int (442)) (Prims.of_int (42)))
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (441)) (Prims.of_int (38))
                      (Prims.of_int (448)) (Prims.of_int (33)))
                   (Obj.magic (open_term_simple b body))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           match uu___ with
                           | (nb, body1) ->
                               Tv_Let
                                 (recf, attrs, nb,
                                   (if recf
                                    then
                                      FStar_Reflection_Builtins.subst_term
                                        [FStar_Syntax_Syntax.DB
                                           (Prims.int_zero,
                                             (binder_to_namedv nb))] def
                                    else def), body1)))))
       | FStar_Reflection_Data.Tv_Match (scrutinee, ret, brs) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (451)) (Prims.of_int (14))
                      (Prims.of_int (451)) (Prims.of_int (33)))
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (452)) (Prims.of_int (4))
                      (Prims.of_int (452)) (Prims.of_int (30)))
                   (Obj.magic (FStar_Tactics_Util.map open_branch brs))
                   (fun brs1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> Tv_Match (scrutinee, ret, brs1))))))
      uu___
let (close_view : named_term_view -> FStar_Reflection_Data.term_view) =
  fun tv ->
    match tv with
    | Tv_Var v -> FStar_Reflection_Data.Tv_Var v
    | Tv_BVar v -> FStar_Reflection_Data.Tv_BVar v
    | Tv_FVar v -> FStar_Reflection_Data.Tv_FVar v
    | Tv_UInst (v, us) -> FStar_Reflection_Data.Tv_UInst (v, us)
    | Tv_App (hd, a) -> FStar_Reflection_Data.Tv_App (hd, a)
    | Tv_Type u -> FStar_Reflection_Data.Tv_Type u
    | Tv_Const c -> FStar_Reflection_Data.Tv_Const c
    | Tv_Uvar (n, ctx_uvar_and_subst) ->
        FStar_Reflection_Data.Tv_Uvar (n, ctx_uvar_and_subst)
    | Tv_AscribedT (e, t, tac, use_eq) ->
        FStar_Reflection_Data.Tv_AscribedT (e, t, tac, use_eq)
    | Tv_AscribedC (e, c, tac, use_eq) ->
        FStar_Reflection_Data.Tv_AscribedC (e, c, tac, use_eq)
    | Tv_Unknown -> FStar_Reflection_Data.Tv_Unknown
    | Tv_Unsupp -> FStar_Reflection_Data.Tv_Unsupp
    | Tv_Abs (nb, body) ->
        let uu___ = close_term nb body in
        (match uu___ with
         | (b, body1) -> FStar_Reflection_Data.Tv_Abs (b, body1))
    | Tv_Arrow (nb, c) ->
        let uu___ = close_comp nb c in
        (match uu___ with | (b, c1) -> FStar_Reflection_Data.Tv_Arrow (b, c1))
    | Tv_Refine (nb, ref) ->
        let uu___ = close_term_simple nb ref in
        (match uu___ with
         | (b, ref1) -> FStar_Reflection_Data.Tv_Refine (b, ref1))
    | Tv_Let (recf, attrs, nb, def, body) ->
        let def1 =
          if recf
          then
            FStar_Reflection_Builtins.subst_term
              [FStar_Syntax_Syntax.NM ((binder_to_namedv nb), Prims.int_zero)]
              def
          else def in
        let uu___ = close_term_simple nb body in
        (match uu___ with
         | (b, body1) ->
             FStar_Reflection_Data.Tv_Let (recf, attrs, b, def1, body1))
    | Tv_Match (scrutinee, ret, brs) ->
        let brs1 = FStar_List_Tot_Base.map close_branch brs in
        FStar_Reflection_Data.Tv_Match (scrutinee, ret, brs1)
let (inspect :
  FStar_Reflection_Types.term ->
    (named_term_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
         (Prims.of_int (499)) (Prims.of_int (11)) (Prims.of_int (499))
         (Prims.of_int (23)))
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
         (Prims.of_int (500)) (Prims.of_int (2)) (Prims.of_int (500))
         (Prims.of_int (14)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_Builtins.inspect_ln t))
      (fun uu___ -> (fun tv -> Obj.magic (open_view tv)) uu___)
let (pack : named_term_view -> FStar_Reflection_Types.term) =
  fun tv -> let tv1 = close_view tv in FStar_Reflection_Builtins.pack_ln tv1
let (notAscription : named_term_view -> Prims.bool) =
  fun tv ->
    (Prims.op_Negation (uu___is_Tv_AscribedT tv)) &&
      (Prims.op_Negation (uu___is_Tv_AscribedC tv))
type letbinding =
  {
  lb_fv: FStar_Reflection_Types.fv ;
  lb_us: FStar_Reflection_Types.univ_name Prims.list ;
  lb_typ: FStar_Reflection_Types.typ ;
  lb_def: FStar_Reflection_Types.term }
let (__proj__Mkletbinding__item__lb_fv :
  letbinding -> FStar_Reflection_Types.fv) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_fv
let (__proj__Mkletbinding__item__lb_us :
  letbinding -> FStar_Reflection_Types.univ_name Prims.list) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_us
let (__proj__Mkletbinding__item__lb_typ :
  letbinding -> FStar_Reflection_Types.typ) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_typ
let (__proj__Mkletbinding__item__lb_def :
  letbinding -> FStar_Reflection_Types.term) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_def
type named_sigelt_view__Sg_Let__payload =
  {
  isrec: Prims.bool ;
  lbs: letbinding Prims.list }
and named_sigelt_view__Sg_Inductive__payload =
  {
  nm: FStar_Reflection_Types.name ;
  univs1: FStar_Reflection_Types.univ_name Prims.list ;
  params: binders ;
  typ: FStar_Reflection_Types.typ ;
  ctors: FStar_Reflection_Data.ctor Prims.list }
and named_sigelt_view__Sg_Val__payload =
  {
  nm1: FStar_Reflection_Types.name ;
  univs2: FStar_Reflection_Types.univ_name Prims.list ;
  typ1: FStar_Reflection_Types.typ }
and named_sigelt_view =
  | Sg_Let of named_sigelt_view__Sg_Let__payload 
  | Sg_Inductive of named_sigelt_view__Sg_Inductive__payload 
  | Sg_Val of named_sigelt_view__Sg_Val__payload 
  | Unk 
let (__proj__Mknamed_sigelt_view__Sg_Let__payload__item__isrec :
  named_sigelt_view__Sg_Let__payload -> Prims.bool) =
  fun projectee -> match projectee with | { isrec; lbs;_} -> isrec
let (__proj__Mknamed_sigelt_view__Sg_Let__payload__item__lbs :
  named_sigelt_view__Sg_Let__payload -> letbinding Prims.list) =
  fun projectee -> match projectee with | { isrec; lbs;_} -> lbs
let (__proj__Mknamed_sigelt_view__Sg_Inductive__payload__item__nm :
  named_sigelt_view__Sg_Inductive__payload -> FStar_Reflection_Types.name) =
  fun projectee ->
    match projectee with | { nm; univs1 = univs; params; typ; ctors;_} -> nm
let (__proj__Mknamed_sigelt_view__Sg_Inductive__payload__item__univs :
  named_sigelt_view__Sg_Inductive__payload ->
    FStar_Reflection_Types.univ_name Prims.list)
  =
  fun projectee ->
    match projectee with
    | { nm; univs1 = univs; params; typ; ctors;_} -> univs
let (__proj__Mknamed_sigelt_view__Sg_Inductive__payload__item__params :
  named_sigelt_view__Sg_Inductive__payload -> binders) =
  fun projectee ->
    match projectee with
    | { nm; univs1 = univs; params; typ; ctors;_} -> params
let (__proj__Mknamed_sigelt_view__Sg_Inductive__payload__item__typ :
  named_sigelt_view__Sg_Inductive__payload -> FStar_Reflection_Types.typ) =
  fun projectee ->
    match projectee with | { nm; univs1 = univs; params; typ; ctors;_} -> typ
let (__proj__Mknamed_sigelt_view__Sg_Inductive__payload__item__ctors :
  named_sigelt_view__Sg_Inductive__payload ->
    FStar_Reflection_Data.ctor Prims.list)
  =
  fun projectee ->
    match projectee with
    | { nm; univs1 = univs; params; typ; ctors;_} -> ctors
let (__proj__Mknamed_sigelt_view__Sg_Val__payload__item__nm :
  named_sigelt_view__Sg_Val__payload -> FStar_Reflection_Types.name) =
  fun projectee ->
    match projectee with | { nm1 = nm; univs2 = univs; typ1 = typ;_} -> nm
let (__proj__Mknamed_sigelt_view__Sg_Val__payload__item__univs :
  named_sigelt_view__Sg_Val__payload ->
    FStar_Reflection_Types.univ_name Prims.list)
  =
  fun projectee ->
    match projectee with | { nm1 = nm; univs2 = univs; typ1 = typ;_} -> univs
let (__proj__Mknamed_sigelt_view__Sg_Val__payload__item__typ :
  named_sigelt_view__Sg_Val__payload -> FStar_Reflection_Types.typ) =
  fun projectee ->
    match projectee with | { nm1 = nm; univs2 = univs; typ1 = typ;_} -> typ
let (uu___is_Sg_Let : named_sigelt_view -> Prims.bool) =
  fun projectee -> match projectee with | Sg_Let _0 -> true | uu___ -> false
let (__proj__Sg_Let__item___0 :
  named_sigelt_view -> named_sigelt_view__Sg_Let__payload) =
  fun projectee -> match projectee with | Sg_Let _0 -> _0
let (uu___is_Sg_Inductive : named_sigelt_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Sg_Inductive _0 -> true | uu___ -> false
let (__proj__Sg_Inductive__item___0 :
  named_sigelt_view -> named_sigelt_view__Sg_Inductive__payload) =
  fun projectee -> match projectee with | Sg_Inductive _0 -> _0
let (uu___is_Sg_Val : named_sigelt_view -> Prims.bool) =
  fun projectee -> match projectee with | Sg_Val _0 -> true | uu___ -> false
let (__proj__Sg_Val__item___0 :
  named_sigelt_view -> named_sigelt_view__Sg_Val__payload) =
  fun projectee -> match projectee with | Sg_Val _0 -> _0
let (uu___is_Unk : named_sigelt_view -> Prims.bool) =
  fun projectee -> match projectee with | Unk -> true | uu___ -> false
let (open_lb :
  FStar_Reflection_Types.letbinding ->
    (letbinding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun lb ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
         (Prims.of_int (546)) (Prims.of_int (39)) (Prims.of_int (546))
         (Prims.of_int (52)))
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
         (Prims.of_int (545)) (Prims.of_int (50)) (Prims.of_int (550))
         (Prims.of_int (34)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_Builtins.inspect_lb lb))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | { FStar_Reflection_Data.lb_fv = lb_fv;
                FStar_Reflection_Data.lb_us = lb_us;
                FStar_Reflection_Data.lb_typ = lb_typ;
                FStar_Reflection_Data.lb_def = lb_def;_} ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                        (Prims.of_int (547)) (Prims.of_int (17))
                        (Prims.of_int (547)) (Prims.of_int (34)))
                     (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                        (Prims.of_int (546)) (Prims.of_int (55))
                        (Prims.of_int (550)) (Prims.of_int (34)))
                     (Obj.magic (open_univ_s lb_us))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             match uu___1 with
                             | (lb_us1, s) ->
                                 {
                                   lb_fv;
                                   lb_us = lb_us1;
                                   lb_typ =
                                     (FStar_Reflection_Builtins.subst_term s
                                        lb_typ);
                                   lb_def =
                                     (FStar_Reflection_Builtins.subst_term s
                                        lb_def)
                                 })))) uu___)
let (close_lb : letbinding -> FStar_Reflection_Types.letbinding) =
  fun lb ->
    let uu___ = lb in
    match uu___ with
    | { lb_fv; lb_us; lb_typ; lb_def;_} ->
        let uu___1 = close_univ_s lb_us in
        (match uu___1 with
         | (lb_us1, s) ->
             let lb_typ1 = FStar_Reflection_Builtins.subst_term s lb_typ in
             let lb_def1 = FStar_Reflection_Builtins.subst_term s lb_def in
             FStar_Reflection_Builtins.pack_lb
               {
                 FStar_Reflection_Data.lb_fv = lb_fv;
                 FStar_Reflection_Data.lb_us = lb_us1;
                 FStar_Reflection_Data.lb_typ = lb_typ1;
                 FStar_Reflection_Data.lb_def = lb_def1
               })
exception NotEnoughBinders 
let (uu___is_NotEnoughBinders : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | NotEnoughBinders -> true | uu___ -> false
exception NotTot 
let (uu___is_NotTot : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | NotTot -> true | uu___ -> false
let rec (open_n_binders_from_arrow :
  binders ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun t ->
           match bs with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (566)) (Prims.of_int (4))
                          (Prims.of_int (566)) (Prims.of_int (37)))
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (567)) (Prims.of_int (4))
                          (Prims.of_int (579)) (Prims.of_int (33)))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "FStar.Tactics.NamedView.fst"
                                (Prims.of_int (566)) (Prims.of_int (10))
                                (Prims.of_int (566)) (Prims.of_int (37)))
                             (FStar_Range.mk_range
                                "FStar.Tactics.NamedView.fst"
                                (Prims.of_int (566)) (Prims.of_int (4))
                                (Prims.of_int (566)) (Prims.of_int (37)))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.NamedView.fst"
                                      (Prims.of_int (566))
                                      (Prims.of_int (20))
                                      (Prims.of_int (566))
                                      (Prims.of_int (36)))
                                   (FStar_Range.mk_range "prims.fst"
                                      (Prims.of_int (590))
                                      (Prims.of_int (19))
                                      (Prims.of_int (590))
                                      (Prims.of_int (31)))
                                   (Obj.magic
                                      (FStar_Tactics_Builtins.term_to_string
                                         t))
                                   (fun uu___ ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 ->
                                           Prims.strcat "t = " uu___))))
                             (fun uu___ ->
                                (fun uu___ -> Obj.magic (print uu___)) uu___)))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.NamedView.fst"
                                     (Prims.of_int (567)) (Prims.of_int (10))
                                     (Prims.of_int (567)) (Prims.of_int (19)))
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.NamedView.fst"
                                     (Prims.of_int (567)) (Prims.of_int (4))
                                     (Prims.of_int (579)) (Prims.of_int (33)))
                                  (Obj.magic (inspect t))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
                                        match uu___1 with
                                        | Tv_Arrow (b', c) ->
                                            Obj.magic
                                              (Obj.repr
                                                 (match FStar_Reflection_Builtins.inspect_comp
                                                          c
                                                  with
                                                  | FStar_Reflection_Data.C_Total
                                                      t' ->
                                                      Obj.repr
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.NamedView.fst"
                                                              (Prims.of_int (571))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (571))
                                                              (Prims.of_int (42)))
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.NamedView.fst"
                                                              (Prims.of_int (572))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (576))
                                                              (Prims.of_int (39)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (42)))
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (42)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    t))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "t' = "
                                                                    uu___2))))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (print
                                                                    uu___2))
                                                                    uu___2)))
                                                           (fun uu___2 ->
                                                              (fun uu___2 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (75)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (75)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (75)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (74)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (74)))
                                                                    (Obj.magic
                                                                    (binder_to_string
                                                                    b'))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (74)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (74)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (binder_to_string
                                                                    b))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    " for "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    uu___3
                                                                    uu___4))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "sub "
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (print
                                                                    uu___3))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (51)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    t'))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "substituting "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (print
                                                                    uu___4))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (94)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Reflection_Builtins.subst_term
                                                                    [
                                                                    FStar_Syntax_Syntax.NT
                                                                    ((binder_to_namedv
                                                                    b'),
                                                                    (pack
                                                                    (Tv_Var
                                                                    (binder_to_namedv
                                                                    b))))] t'))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun t'1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    t'1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "got "
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (print
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (open_n_binders_from_arrow
                                                                    bs1 t'1))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                uu___2))
                                                  | uu___2 ->
                                                      Obj.repr
                                                        (FStar_Tactics_Effect.raise
                                                           NotTot)))
                                        | uu___2 ->
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.raise
                                                    NotEnoughBinders)))
                                       uu___1))) uu___)))) uu___1 uu___
let (open_sigelt_view :
  FStar_Reflection_Data.sigelt_view ->
    (named_sigelt_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun sv ->
       match sv with
       | FStar_Reflection_Data.Sg_Let (isrec, lbs) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (584)) (Prims.of_int (14))
                      (Prims.of_int (584)) (Prims.of_int (29)))
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (586)) (Prims.of_int (4))
                      (Prims.of_int (586)) (Prims.of_int (25)))
                   (Obj.magic (FStar_Tactics_Util.map open_lb lbs))
                   (fun lbs1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> Sg_Let { isrec; lbs = lbs1 }))))
       | FStar_Reflection_Data.Sg_Inductive (nm, univs, params, typ, ctors)
           ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (589)) (Prims.of_int (18))
                      (Prims.of_int (589)) (Prims.of_int (40)))
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (589)) (Prims.of_int (43))
                      (Prims.of_int (613)) (Prims.of_int (48)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> FStar_List_Tot_Base.length params))
                   (fun uu___ ->
                      (fun nparams ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.Tactics.NamedView.fst"
                                 (Prims.of_int (592)) (Prims.of_int (16))
                                 (Prims.of_int (592)) (Prims.of_int (33)))
                              (FStar_Range.mk_range
                                 "FStar.Tactics.NamedView.fst"
                                 (Prims.of_int (589)) (Prims.of_int (43))
                                 (Prims.of_int (613)) (Prims.of_int (48)))
                              (Obj.magic (open_univ_s univs))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    match uu___ with
                                    | (us, s) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.NamedView.fst"
                                                (Prims.of_int (593))
                                                (Prims.of_int (17))
                                                (Prims.of_int (593))
                                                (Prims.of_int (58)))
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.NamedView.fst"
                                                (Prims.of_int (593))
                                                (Prims.of_int (61))
                                                (Prims.of_int (613))
                                                (Prims.of_int (48)))
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   FStar_List_Tot_Base.map
                                                     (subst_binder_sort s)
                                                     params))
                                             (fun uu___1 ->
                                                (fun params1 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.NamedView.fst"
                                                           (Prims.of_int (594))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (594))
                                                           (Prims.of_int (30)))
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.NamedView.fst"
                                                           (Prims.of_int (594))
                                                           (Prims.of_int (33))
                                                           (Prims.of_int (613))
                                                           (Prims.of_int (48)))
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___1 ->
                                                              FStar_Reflection_Builtins.subst_term
                                                                s typ))
                                                        (fun uu___1 ->
                                                           (fun typ1 ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (63)))
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (48)))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    (nm1, ty)
                                                                    ->
                                                                    (nm1,
                                                                    (FStar_Reflection_Builtins.subst_term
                                                                    s ty)))))
                                                                    uu___1)
                                                                    ctors))
                                                                   (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    ctors1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (598))
                                                                    (Prims.of_int (44)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (595))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (open_term_n
                                                                    params1
                                                                    typ1))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    (params2,
                                                                    typ2) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (609))
                                                                    (Prims.of_int (13)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (nm1, ty)
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (607))
                                                                    (Prims.of_int (54)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (608))
                                                                    (Prims.of_int (17)))
                                                                    (Obj.magic
                                                                    (open_n_binders_from_arrow
                                                                    params2
                                                                    ty))
                                                                    (fun ty'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (nm1,
                                                                    ty'))))
                                                                    ctors1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    ctors2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (89)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (89)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (89)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (88)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.string_of_list
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (nm1,
                                                                    cty) ->
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    cty)
                                                                    ctors2))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "ctors typs2 = "
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (print
                                                                    uu___2))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Sg_Inductive
                                                                    {
                                                                    nm;
                                                                    univs1 =
                                                                    univs;
                                                                    params =
                                                                    params2;
                                                                    typ =
                                                                    typ2;
                                                                    ctors =
                                                                    ctors2
                                                                    }))))
                                                                    uu___2)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                             uu___1))) uu___1)))
                                   uu___))) uu___)))
       | FStar_Reflection_Data.Sg_Val (nm, univs, typ) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (616)) (Prims.of_int (19))
                      (Prims.of_int (616)) (Prims.of_int (36)))
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (615)) (Prims.of_int (29))
                      (Prims.of_int (618)) (Prims.of_int (27)))
                   (Obj.magic (open_univ_s univs))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           match uu___ with
                           | (univs1, s) ->
                               Sg_Val
                                 {
                                   nm1 = nm;
                                   univs2 = univs1;
                                   typ1 =
                                     (FStar_Reflection_Builtins.subst_term s
                                        typ)
                                 }))))
       | FStar_Reflection_Data.Unk ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Unk))))
      uu___
let rec (mk_abs :
  binder Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun args ->
         fun t ->
           match args with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
           | a::args' ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (628)) (Prims.of_int (13))
                          (Prims.of_int (628)) (Prims.of_int (27)))
                       (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                          (Prims.of_int (629)) (Prims.of_int (4))
                          (Prims.of_int (629)) (Prims.of_int (22)))
                       (Obj.magic (mk_abs args' t))
                       (fun t' ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> pack (Tv_Abs (a, t'))))))) uu___1
        uu___
let (close_sigelt_view :
  named_sigelt_view ->
    (FStar_Reflection_Data.sigelt_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun sv ->
       match sv with
       | Sg_Let { isrec; lbs;_} ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      FStar_Reflection_Data.Sg_Let
                        (isrec, (FStar_List_Tot_Base.map close_lb lbs)))))
       | Sg_Inductive { nm; univs1 = univs; params; typ; ctors;_} ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (640)) (Prims.of_int (16))
                      (Prims.of_int (640)) (Prims.of_int (64)))
                   (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
                      (Prims.of_int (640)) (Prims.of_int (67))
                      (Prims.of_int (651)) (Prims.of_int (45)))
                   (Obj.magic
                      (FStar_Tactics_Util.map
                         (fun uu___ ->
                            match uu___ with
                            | (nm1, ty) ->
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.NamedView.fst"
                                     (Prims.of_int (640)) (Prims.of_int (41))
                                     (Prims.of_int (640)) (Prims.of_int (57)))
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.NamedView.fst"
                                     (Prims.of_int (640)) (Prims.of_int (37))
                                     (Prims.of_int (640)) (Prims.of_int (57)))
                                  (Obj.magic (mk_abs params ty))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> (nm1, uu___1)))) ctors))
                   (fun uu___ ->
                      (fun ctors1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.Tactics.NamedView.fst"
                                 (Prims.of_int (643)) (Prims.of_int (22))
                                 (Prims.of_int (643)) (Prims.of_int (45)))
                              (FStar_Range.mk_range
                                 "FStar.Tactics.NamedView.fst"
                                 (Prims.of_int (640)) (Prims.of_int (67))
                                 (Prims.of_int (651)) (Prims.of_int (45)))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ -> close_term_n params typ))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    match uu___ with
                                    | (params1, typ1) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.NamedView.fst"
                                                (Prims.of_int (646))
                                                (Prims.of_int (16))
                                                (Prims.of_int (646))
                                                (Prims.of_int (34)))
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.NamedView.fst"
                                                (Prims.of_int (643))
                                                (Prims.of_int (48))
                                                (Prims.of_int (651))
                                                (Prims.of_int (45)))
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   close_univ_s univs))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   match uu___1 with
                                                   | (us, s) ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.NamedView.fst"
                                                               (Prims.of_int (647))
                                                               (Prims.of_int (17))
                                                               (Prims.of_int (647))
                                                               (Prims.of_int (58)))
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.NamedView.fst"
                                                               (Prims.of_int (647))
                                                               (Prims.of_int (61))
                                                               (Prims.of_int (651))
                                                               (Prims.of_int (45)))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  FStar_List_Tot_Base.map
                                                                    (
                                                                    subst_binder_sort
                                                                    s)
                                                                    params1))
                                                            (fun uu___2 ->
                                                               (fun params2
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (648))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (648))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (648))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (45)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Reflection_Builtins.subst_term
                                                                    s typ1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun typ2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.NamedView.fst"
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (45)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (nm1, ty)
                                                                    ->
                                                                    (nm1,
                                                                    (FStar_Reflection_Builtins.subst_term
                                                                    s ty)))))
                                                                    uu___2)
                                                                    ctors1))
                                                                    (fun
                                                                    ctors2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Reflection_Data.Sg_Inductive
                                                                    (nm,
                                                                    univs,
                                                                    params2,
                                                                    typ2,
                                                                    ctors2)))))
                                                                    uu___2)))
                                                                 uu___2)))
                                                  uu___1))) uu___))) uu___)))
       | Sg_Val { nm1 = nm; univs2 = univs; typ1 = typ;_} ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      match close_univ_s univs with
                      | (univs1, s) ->
                          FStar_Reflection_Data.Sg_Val
                            (nm, univs1,
                              (FStar_Reflection_Builtins.subst_term s typ))))))
      uu___
let (inspect_sigelt :
  FStar_Reflection_Types.sigelt ->
    (named_sigelt_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
         (Prims.of_int (659)) (Prims.of_int (11)) (Prims.of_int (659))
         (Prims.of_int (29)))
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
         (Prims.of_int (661)) (Prims.of_int (2)) (Prims.of_int (661))
         (Prims.of_int (21)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_Builtins.inspect_sigelt s))
      (fun uu___ -> (fun sv -> Obj.magic (open_sigelt_view sv)) uu___)
let (pack_sigelt :
  named_sigelt_view ->
    (FStar_Reflection_Types.sigelt, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun sv ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
         (Prims.of_int (664)) (Prims.of_int (11)) (Prims.of_int (664))
         (Prims.of_int (31)))
      (FStar_Range.mk_range "FStar.Tactics.NamedView.fst"
         (Prims.of_int (665)) (Prims.of_int (2)) (Prims.of_int (665))
         (Prims.of_int (18))) (Obj.magic (close_sigelt_view sv))
      (fun sv1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> FStar_Reflection_Builtins.pack_sigelt sv1))
type term_view = named_term_view
type sigelt_view = named_sigelt_view