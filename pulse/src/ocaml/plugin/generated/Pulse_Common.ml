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
let rec for_all_dec :
  'a 'b . 'a -> 'b Prims.list -> ('b -> Prims.bool) -> Prims.bool =
  fun top ->
    fun l ->
      fun f ->
        match l with | [] -> true | x::xs -> (f x) && (for_all_dec top xs f)
let rec map_dec :
  'a 'b 'c . 'a -> 'b Prims.list -> ('b -> 'c) -> 'c Prims.list =
  fun top ->
    fun l ->
      fun f -> match l with | [] -> [] | x::xs -> (f x) :: (map_dec top xs f)
let rec zipWith :
  'a 'b 'c .
    ('a -> 'b -> ('c, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list ->
        'b Prims.list -> ('c Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun f ->
           fun l ->
             fun m ->
               match (l, m) with
               | ([], []) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
               | (x::xs, y::ys) ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Common.fst"
                                    (Prims.of_int (38)) (Prims.of_int (20))
                                    (Prims.of_int (38)) (Prims.of_int (25)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Pulse.Common.fst"
                                    (Prims.of_int (38)) (Prims.of_int (20))
                                    (Prims.of_int (38)) (Prims.of_int (44)))))
                           (Obj.magic (f x y))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Common.fst"
                                               (Prims.of_int (38))
                                               (Prims.of_int (29))
                                               (Prims.of_int (38))
                                               (Prims.of_int (44)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Common.fst"
                                               (Prims.of_int (38))
                                               (Prims.of_int (20))
                                               (Prims.of_int (38))
                                               (Prims.of_int (44)))))
                                      (Obj.magic (zipWith f xs ys))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 -> uu___ :: uu___1))))
                                uu___)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_V1_Derived.fail
                           "zipWith: length mismatch"))) uu___2 uu___1 uu___
let rec zip : 'a 'b . 'a Prims.list -> 'b Prims.list -> ('a * 'b) Prims.list
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | (x::xs, y::ys) -> (x, y) :: (zip xs ys)
      | uu___ -> []
let rec map_opt :
  'uuuuu 'uuuuu1 .
    ('uuuuu -> 'uuuuu1 FStar_Pervasives_Native.option) ->
      'uuuuu Prims.list -> 'uuuuu1 Prims.list FStar_Pervasives_Native.option
  =
  fun f ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives_Native.Some []
      | x::xs ->
          op_let_Question (f x)
            (fun y ->
               op_let_Question (map_opt f xs)
                 (fun ys -> FStar_Pervasives_Native.Some (y :: ys)))
let rec map_opt_dec :
  'a 'b 'z .
    'z ->
      ('a -> 'b FStar_Pervasives_Native.option) ->
        'a Prims.list -> 'b Prims.list FStar_Pervasives_Native.option
  =
  fun top ->
    fun f ->
      fun l ->
        match l with
        | [] -> FStar_Pervasives_Native.Some []
        | x::xs ->
            op_let_Question (f x)
              (fun y ->
                 op_let_Question (map_opt_dec top f xs)
                   (fun ys -> FStar_Pervasives_Native.Some (y :: ys)))
let rec concat_map_opt :
  'a 'b .
    ('a -> 'b Prims.list FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list FStar_Pervasives_Native.option
  =
  fun f ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives_Native.Some []
      | x::xs ->
          op_let_Question (f x)
            (fun y ->
               op_let_Question (concat_map_opt f xs)
                 (fun ys ->
                    FStar_Pervasives_Native.Some
                      (FStar_List_Tot_Base.append y ys)))