open Fstarcompiler
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
           | [] -> Obj.magic (Obj.repr (fun uu___ -> []))
           | a1::tl ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x1 = f a1 ps in let x2 = map f tl ps in x1 :: x2)))
        uu___1 uu___
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
           | [] -> Obj.magic (Obj.repr (fun uu___ -> []))
           | x::xs ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x1 = f x ps in
                       let x2 = concatMap f xs ps in
                       FStar_List_Tot_Base.op_At x1 x2))) uu___1 uu___
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
               | [] -> Obj.magic (Obj.repr (fun uu___ -> []))
               | a1::tl ->
                   Obj.magic
                     (Obj.repr
                        (fun ps ->
                           let x1 = f i a1 ps in
                           let x2 = __mapi (i + Prims.int_one) f tl ps in x1
                             :: x2))) uu___2 uu___1 uu___
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
           | [] -> Obj.magic (Obj.repr (fun uu___ -> ()))
           | a1::tl -> Obj.magic (Obj.repr (fun ps -> f a1 ps; iter f tl ps)))
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
               | [] -> Obj.magic (Obj.repr (fun uu___ -> ()))
               | a1::tl ->
                   Obj.magic
                     (Obj.repr
                        (fun ps ->
                           f i a1 ps; iteri_aux (i + Prims.int_one) f tl ps)))
          uu___2 uu___1 uu___
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
               | [] -> Obj.magic (Obj.repr (fun uu___ -> x))
               | hd::tl ->
                   Obj.magic
                     (Obj.repr
                        (fun ps -> let x1 = f x hd ps in fold_left f x1 tl ps)))
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
               | [] -> Obj.magic (Obj.repr (fun uu___ -> x))
               | hd::tl ->
                   Obj.magic
                     (Obj.repr
                        (fun ps ->
                           let x1 = fold_right f tl x ps in f hd x1 ps)))
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
                 (Obj.repr (fun ps -> let x1 = zip xs ys ps in (x, y) :: x1))
           | uu___ -> Obj.magic (Obj.repr (fun uu___1 -> []))) uu___1 uu___
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
           | [] -> Obj.magic (Obj.repr (fun uu___1 -> []))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x = f hd ps in
                       if x
                       then let x1 = filter f tl ps in hd :: x1
                       else filter f tl ps))) uu___1 uu___
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
                     (Obj.repr (fun uu___ -> FStar_List_Tot_Base.rev acc))
               | hd::tl ->
                   Obj.magic
                     (Obj.repr
                        (fun ps ->
                           let x = f hd ps in
                           match x with
                           | FStar_Pervasives_Native.Some hd1 ->
                               filter_map_acc f (hd1 :: acc) tl ps
                           | FStar_Pervasives_Native.None ->
                               filter_map_acc f acc tl ps))) uu___2 uu___1
          uu___
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
                 (Obj.repr (fun uu___ -> FStar_Pervasives_Native.None))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x = f hd ps in
                       match x with
                       | FStar_Pervasives_Native.Some x1 ->
                           FStar_Pervasives_Native.Some x1
                       | FStar_Pervasives_Native.None -> tryPick f tl ps)))
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
                 (Obj.repr (fun uu___ -> FStar_Pervasives_Native.None))
           | FStar_Pervasives_Native.Some x1 ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x2 = f x1 ps in FStar_Pervasives_Native.Some x2)))
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
           then Obj.magic (Obj.repr (fun uu___ -> []))
           else
             Obj.magic
               (Obj.repr
                  (fun ps ->
                     let x = t () ps in
                     let x1 = repeatn (n - Prims.int_one) t ps in x :: x1)))
        uu___1 uu___
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
           | [] -> Obj.magic (Obj.repr (fun uu___ -> false))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x = f hd ps in if x then true else tryFind f tl ps)))
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
                   | ([], []) -> Obj.magic (Obj.repr (fun uu___ -> x))
                   | (hd1::tl1, hd2::tl2) ->
                       Obj.magic
                         (Obj.repr
                            (fun ps ->
                               let x1 = f x hd1 hd2 ps in
                               fold_left2 f x1 tl1 tl2 ps))) uu___3 uu___2
            uu___1 uu___
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
           | [] -> Obj.magic (Obj.repr (fun uu___ -> ""))
           | x::xs ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x1 = f x ps in
                       let x2 =
                         let x3 = string_of_list f xs ps in
                         Prims.strcat ";" x3 in
                       Prims.strcat x1 x2))) uu___1 uu___
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
                    (fun ps -> let x1 = f x ps in Prims.strcat "Some " x1))
           | FStar_Pervasives_Native.None ->
               Obj.magic (Obj.repr (fun uu___ -> "None"))) uu___1 uu___
let rec existsb :
  'a .
    ('a -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun l ->
           match l with
           | [] -> Obj.magic (Obj.repr (fun uu___ -> false))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (fun ps ->
                       let x = f hd ps in if x then true else existsb f tl ps)))
        uu___1 uu___
