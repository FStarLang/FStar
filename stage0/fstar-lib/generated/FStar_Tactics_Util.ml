open Prims
let rec map :
  'a 'b .
    ('a -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun x ->
           match x with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
           | a1::tl ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = f a1 in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (25)) (Prims.of_int (13))
                                (Prims.of_int (25)) (Prims.of_int (16)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (25)) (Prims.of_int (13))
                                (Prims.of_int (25)) (Prims.of_int (26)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___2 = map f tl in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Util.fst"
                                           (Prims.of_int (25))
                                           (Prims.of_int (18))
                                           (Prims.of_int (25))
                                           (Prims.of_int (26)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Util.fst"
                                           (Prims.of_int (25))
                                           (Prims.of_int (13))
                                           (Prims.of_int (25))
                                           (Prims.of_int (26)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 -> uu___1 :: uu___3))))
                            uu___1)))) uu___1 uu___
let rec concatMap :
  'a 'b .
    ('a -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun l ->
           match l with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
           | x::xs ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = f x in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (30)) (Prims.of_int (13))
                                (Prims.of_int (30)) (Prims.of_int (16)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (30)) (Prims.of_int (13))
                                (Prims.of_int (30)) (Prims.of_int (33)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___2 = concatMap f xs in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Util.fst"
                                           (Prims.of_int (30))
                                           (Prims.of_int (19))
                                           (Prims.of_int (30))
                                           (Prims.of_int (33)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Util.fst"
                                           (Prims.of_int (30))
                                           (Prims.of_int (13))
                                           (Prims.of_int (30))
                                           (Prims.of_int (33)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 ->
                                          FStar_List_Tot_Base.op_At uu___1
                                            uu___3)))) uu___1)))) uu___1
        uu___
let rec __mapi :
  'a 'b .
    Prims.nat ->
      (Prims.nat -> 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
        'a Prims.list -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun i ->
           fun f ->
             fun x ->
               match x with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
               | a1::tl ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = f i a1 in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Util.fst"
                                    (Prims.of_int (35)) (Prims.of_int (13))
                                    (Prims.of_int (35)) (Prims.of_int (18)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Util.fst"
                                    (Prims.of_int (35)) (Prims.of_int (13))
                                    (Prims.of_int (35)) (Prims.of_int (37)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 let uu___2 = __mapi (i + Prims.int_one) f tl in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Util.fst"
                                               (Prims.of_int (35))
                                               (Prims.of_int (20))
                                               (Prims.of_int (35))
                                               (Prims.of_int (37)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Util.fst"
                                               (Prims.of_int (35))
                                               (Prims.of_int (13))
                                               (Prims.of_int (35))
                                               (Prims.of_int (37)))))
                                      (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 -> uu___1 :: uu___3))))
                                uu___1)))) uu___2 uu___1 uu___
let mapi :
  'a 'b .
    (Prims.nat -> 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr
  = fun f -> fun l -> __mapi Prims.int_zero f l
let rec iter :
  'a .
    ('a -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun x ->
           match x with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ())))
           | a1::tl ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = f a1 in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (43)) (Prims.of_int (13))
                                (Prims.of_int (43)) (Prims.of_int (16)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (43)) (Prims.of_int (18))
                                (Prims.of_int (43)) (Prims.of_int (27)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 -> Obj.magic (iter f tl)) uu___1))))
        uu___1 uu___
let rec iteri_aux :
  'a .
    Prims.int ->
      (Prims.int -> 'a -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
        'a Prims.list -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun i ->
           fun f ->
             fun x ->
               match x with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ())))
               | a1::tl ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = f i a1 in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Util.fst"
                                    (Prims.of_int (48)) (Prims.of_int (13))
                                    (Prims.of_int (48)) (Prims.of_int (18)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Util.fst"
                                    (Prims.of_int (48)) (Prims.of_int (20))
                                    (Prims.of_int (48)) (Prims.of_int (40)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (iteri_aux (i + Prims.int_one) f tl))
                                uu___1)))) uu___2 uu___1 uu___
let iteri :
  'a .
    (Prims.int -> 'a -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (unit, unit) FStar_Tactics_Effect.tac_repr
  = fun f -> fun x -> iteri_aux Prims.int_zero f x
let rec fold_left :
  'a 'b .
    ('a -> 'b -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      'a -> 'b Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun f ->
           fun x ->
             fun l ->
               match l with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x)))
               | hd::tl ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = f x hd in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Util.fst"
                                    (Prims.of_int (56)) (Prims.of_int (26))
                                    (Prims.of_int (56)) (Prims.of_int (34)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Util.fst"
                                    (Prims.of_int (56)) (Prims.of_int (14))
                                    (Prims.of_int (56)) (Prims.of_int (37)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic (fold_left f uu___1 tl)) uu___1))))
          uu___2 uu___1 uu___
let rec fold_right :
  'a 'b .
    ('a -> 'b -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> 'b -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun f ->
           fun l ->
             fun x ->
               match l with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x)))
               | hd::tl ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = fold_right f tl x in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Util.fst"
                                    (Prims.of_int (61)) (Prims.of_int (19))
                                    (Prims.of_int (61)) (Prims.of_int (38)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Util.fst"
                                    (Prims.of_int (61)) (Prims.of_int (14))
                                    (Prims.of_int (61)) (Prims.of_int (38)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 -> Obj.magic (f hd uu___1)) uu___1))))
          uu___2 uu___1 uu___
let rec zip :
  'a 'b .
    'a Prims.list ->
      'b Prims.list ->
        (('a * 'b) Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun l1 ->
         fun l2 ->
           match (l1, l2) with
           | (x::xs, y::ys) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = zip xs ys in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (66)) (Prims.of_int (31))
                                (Prims.of_int (66)) (Prims.of_int (42)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (66)) (Prims.of_int (22))
                                (Prims.of_int (66)) (Prims.of_int (42)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> (x, y) :: uu___1))))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> []))))
        uu___1 uu___
let rec filter :
  'a .
    ('a -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun uu___ ->
           match uu___ with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> [])))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (let uu___1 = f hd in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (72)) (Prims.of_int (17))
                                (Prims.of_int (72)) (Prims.of_int (21)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (72)) (Prims.of_int (14))
                                (Prims.of_int (72)) (Prims.of_int (61)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun uu___2 ->
                             if uu___2
                             then
                               let uu___3 = filter f tl in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Util.fst"
                                             (Prims.of_int (72))
                                             (Prims.of_int (31))
                                             (Prims.of_int (72))
                                             (Prims.of_int (44)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Util.fst"
                                             (Prims.of_int (72))
                                             (Prims.of_int (27))
                                             (Prims.of_int (72))
                                             (Prims.of_int (44)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___5 -> hd :: uu___4)))
                             else Obj.magic (filter f tl)) uu___2)))) uu___1
        uu___
let rec filter_map_acc :
  'a 'b .
    ('a ->
       ('b FStar_Pervasives_Native.option, unit)
         FStar_Tactics_Effect.tac_repr)
      ->
      'b Prims.list ->
        'a Prims.list -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun f ->
           fun acc ->
             fun l ->
               match l with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> FStar_List_Tot_Base.rev acc)))
               | hd::tl ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = f hd in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Util.fst"
                                    (Prims.of_int (80)) (Prims.of_int (12))
                                    (Prims.of_int (80)) (Prims.of_int (16)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Util.fst"
                                    (Prims.of_int (80)) (Prims.of_int (6))
                                    (Prims.of_int (84)) (Prims.of_int (33)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 match uu___1 with
                                 | FStar_Pervasives_Native.Some hd1 ->
                                     Obj.magic
                                       (filter_map_acc f (hd1 :: acc) tl)
                                 | FStar_Pervasives_Native.None ->
                                     Obj.magic (filter_map_acc f acc tl))
                                uu___1)))) uu___2 uu___1 uu___
let filter_map :
  'a 'b .
    ('a ->
       ('b FStar_Pervasives_Native.option, unit)
         FStar_Tactics_Effect.tac_repr)
      -> 'a Prims.list -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr
  = fun f -> fun l -> filter_map_acc f [] l
let rec tryPick :
  'a 'b .
    ('a ->
       ('b FStar_Pervasives_Native.option, unit)
         FStar_Tactics_Effect.tac_repr)
      ->
      'a Prims.list ->
        ('b FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun l ->
           match l with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives_Native.None)))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = f hd in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (93)) (Prims.of_int (13))
                                (Prims.of_int (93)) (Prims.of_int (17)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (93)) (Prims.of_int (7))
                                (Prims.of_int (95)) (Prims.of_int (31)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | FStar_Pervasives_Native.Some x ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            FStar_Pervasives_Native.Some x)))
                             | FStar_Pervasives_Native.None ->
                                 Obj.magic (Obj.repr (tryPick f tl))) uu___1))))
        uu___1 uu___
let map_opt :
  'a 'b .
    ('a -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
      'a FStar_Pervasives_Native.option ->
        ('b FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun x ->
           match x with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives_Native.None)))
           | FStar_Pervasives_Native.Some x1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = f x1 in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (100)) (Prims.of_int (19))
                                (Prims.of_int (100)) (Prims.of_int (24)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (100)) (Prims.of_int (14))
                                (Prims.of_int (100)) (Prims.of_int (24)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStar_Pervasives_Native.Some uu___1)))))
        uu___1 uu___
let rec repeatn :
  'a .
    Prims.int ->
      (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun n ->
         fun t ->
           if n <= Prims.int_zero
           then
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
           else
             Obj.magic
               (Obj.repr
                  (let uu___1 = t () in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                              (Prims.of_int (106)) (Prims.of_int (9))
                              (Prims.of_int (106)) (Prims.of_int (13)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                              (Prims.of_int (106)) (Prims.of_int (9))
                              (Prims.of_int (106)) (Prims.of_int (34)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 = repeatn (n - Prims.int_one) t in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Util.fst"
                                         (Prims.of_int (106))
                                         (Prims.of_int (17))
                                         (Prims.of_int (106))
                                         (Prims.of_int (34)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Util.fst"
                                         (Prims.of_int (106))
                                         (Prims.of_int (9))
                                         (Prims.of_int (106))
                                         (Prims.of_int (34)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 -> uu___2 :: uu___4))))
                          uu___2)))) uu___1 uu___
let rec tryFind :
  'a .
    ('a -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun l ->
           match l with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> false)))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = f hd in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (112)) (Prims.of_int (7))
                                (Prims.of_int (112)) (Prims.of_int (11)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (112)) (Prims.of_int (4))
                                (Prims.of_int (113)) (Prims.of_int (21)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             if uu___1
                             then
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> true)))
                             else Obj.magic (Obj.repr (tryFind f tl))) uu___1))))
        uu___1 uu___
let rec fold_left2 :
  'a 'b 'c .
    ('a -> 'b -> 'c -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      'a ->
        'b Prims.list ->
          'c Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun f ->
             fun x ->
               fun l1 ->
                 fun l2 ->
                   match (l1, l2) with
                   | ([], []) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> x)))
                   | (hd1::tl1, hd2::tl2) ->
                       Obj.magic
                         (Obj.repr
                            (let uu___ = f x hd1 hd2 in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.Util.fst"
                                        (Prims.of_int (122))
                                        (Prims.of_int (17))
                                        (Prims.of_int (122))
                                        (Prims.of_int (30)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.Util.fst"
                                        (Prims.of_int (122))
                                        (Prims.of_int (4))
                                        (Prims.of_int (122))
                                        (Prims.of_int (38)))))
                               (Obj.magic uu___)
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     Obj.magic (fold_left2 f uu___1 tl1 tl2))
                                    uu___1)))) uu___3 uu___2 uu___1 uu___
let rec string_of_list :
  'a .
    ('a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun l ->
           match l with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
           | x::xs ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = f x in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (127)) (Prims.of_int (13))
                                (Prims.of_int (127)) (Prims.of_int (16)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (127)) (Prims.of_int (13))
                                (Prims.of_int (127)) (Prims.of_int (44)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___2 =
                               let uu___3 = string_of_list f xs in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Util.fst"
                                          (Prims.of_int (127))
                                          (Prims.of_int (25))
                                          (Prims.of_int (127))
                                          (Prims.of_int (44)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 -> Prims.strcat ";" uu___4)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Util.fst"
                                           (Prims.of_int (127))
                                           (Prims.of_int (19))
                                           (Prims.of_int (127))
                                           (Prims.of_int (44)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Prims.fst"
                                           (Prims.of_int (611))
                                           (Prims.of_int (19))
                                           (Prims.of_int (611))
                                           (Prims.of_int (31)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 ->
                                          Prims.strcat uu___1 uu___3))))
                            uu___1)))) uu___1 uu___
let string_of_option :
  'a .
    ('a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      'a FStar_Pervasives_Native.option ->
        (Prims.string, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun o ->
           match o with
           | FStar_Pervasives_Native.Some x ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = f x in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Util.fst"
                                (Prims.of_int (131)) (Prims.of_int (24))
                                (Prims.of_int (131)) (Prims.of_int (27)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (611)) (Prims.of_int (19))
                                (Prims.of_int (611)) (Prims.of_int (31)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> Prims.strcat "Some " uu___1))))
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "None"))))
        uu___1 uu___