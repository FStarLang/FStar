open Fstarcompiler
open Prims
let rec map :
  'a 'b .
    ('a -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 uu___ ->
    (fun f x ->
       match x with
       | [] -> Obj.magic (Obj.repr (fun uu___ -> []))
       | a1::tl ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f a1))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (fun ps -> let x1 = map f tl ps in uu___ :: x1))
                        uu___)))) uu___1 uu___
let rec concatMap :
  'a 'b .
    ('a -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 uu___ ->
    (fun f l ->
       match l with
       | [] -> Obj.magic (Obj.repr (fun uu___ -> []))
       | x::xs ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f x))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (fun ps ->
                              let x1 = concatMap f xs ps in
                              FStar_List_Tot_Base.op_At uu___ x1)) uu___))))
      uu___1 uu___
let rec __mapi :
  'a 'b .
    Prims.nat ->
      (Prims.nat -> 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
        'a Prims.list -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 uu___1 uu___ ->
    (fun i f x ->
       match x with
       | [] -> Obj.magic (Obj.repr (fun uu___ -> []))
       | a1::tl ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f i a1))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (fun ps ->
                              let x1 = __mapi (i + Prims.int_one) f tl ps in
                              uu___ :: x1)) uu___)))) uu___2 uu___1 uu___
let mapi (f : Prims.nat -> 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr)
  (l : 'a Prims.list) : ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr=
  __mapi Prims.int_zero f l
let rec iter :
  'a .
    ('a -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 uu___ ->
    (fun f x ->
       match x with
       | [] -> Obj.magic (Obj.repr (fun uu___ -> ()))
       | a1::tl ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f a1))
                   (fun uu___ -> (fun uu___ -> Obj.magic (iter f tl)) uu___))))
      uu___1 uu___
let rec iteri_aux :
  'a .
    Prims.int ->
      (Prims.int -> 'a -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
        'a Prims.list -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 uu___1 uu___ ->
    (fun i f x ->
       match x with
       | [] -> Obj.magic (Obj.repr (fun uu___ -> ()))
       | a1::tl ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f i a1))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic (iteri_aux (i + Prims.int_one) f tl))
                        uu___)))) uu___2 uu___1 uu___
let iteri (f : Prims.int -> 'a -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  (x : 'a Prims.list) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  iteri_aux Prims.int_zero f x
let rec fold_left :
  'a 'b .
    ('a -> 'b -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      'a -> 'b Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 uu___1 uu___ ->
    (fun f x l ->
       match l with
       | [] -> Obj.magic (Obj.repr (fun uu___ -> x))
       | hd::tl ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f x hd))
                   (fun uu___ ->
                      (fun uu___ -> Obj.magic (fold_left f uu___ tl)) uu___))))
      uu___2 uu___1 uu___
let rec fold_right :
  'a 'b .
    ('a -> 'b -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> 'b -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 uu___1 uu___ ->
    (fun f l x ->
       match l with
       | [] -> Obj.magic (Obj.repr (fun uu___ -> x))
       | hd::tl ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Obj.magic (fold_right f tl x))
                   (fun uu___ -> (fun uu___ -> Obj.magic (f hd uu___)) uu___))))
      uu___2 uu___1 uu___
let rec zip :
  'a 'b .
    'a Prims.list ->
      'b Prims.list ->
        (('a * 'b) Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 uu___ ->
    (fun l1 l2 ->
       match (l1, l2) with
       | (x::xs, y::ys) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (zip xs ys))
                   (fun uu___ uu___1 -> (x, y) :: uu___)))
       | uu___ ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> []))))
      uu___1 uu___
let rec filter :
  'a .
    ('a -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 uu___ ->
    (fun f uu___ ->
       match uu___ with
       | [] -> Obj.magic (Obj.repr (fun uu___1 -> []))
       | hd::tl ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f hd))
                   (fun uu___1 ->
                      (fun uu___1 ->
                         if uu___1
                         then
                           Obj.magic
                             (fun ps -> let x = filter f tl ps in hd :: x)
                         else Obj.magic (filter f tl)) uu___1)))) uu___1
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
  fun uu___2 uu___1 uu___ ->
    (fun f acc l ->
       match l with
       | [] ->
           Obj.magic (Obj.repr (fun uu___ -> FStar_List_Tot_Base.rev acc))
       | hd::tl ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f hd))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | FStar_Pervasives_Native.Some hd1 ->
                             Obj.magic (filter_map_acc f (hd1 :: acc) tl)
                         | FStar_Pervasives_Native.None ->
                             Obj.magic (filter_map_acc f acc tl)) uu___))))
      uu___2 uu___1 uu___
let filter_map
  (f :
    'a ->
      ('b FStar_Pervasives_Native.option, unit) FStar_Tactics_Effect.tac_repr)
  (l : 'a Prims.list) : ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr=
  filter_map_acc f [] l
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
  fun uu___1 uu___ ->
    (fun f l ->
       match l with
       | [] ->
           Obj.magic (Obj.repr (fun uu___ -> FStar_Pervasives_Native.None))
       | hd::tl ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f hd))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | FStar_Pervasives_Native.Some x ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        FStar_Pervasives_Native.Some x)))
                         | FStar_Pervasives_Native.None ->
                             Obj.magic (Obj.repr (tryPick f tl))) uu___))))
      uu___1 uu___
let map_opt (uu___1 : 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr)
  (uu___ : 'a FStar_Pervasives_Native.option) :
  ('b FStar_Pervasives_Native.option, unit) FStar_Tactics_Effect.tac_repr=
  (fun f x ->
     match x with
     | FStar_Pervasives_Native.None ->
         Obj.magic (Obj.repr (fun uu___ -> FStar_Pervasives_Native.None))
     | FStar_Pervasives_Native.Some x1 ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind (Obj.magic (f x1))
                 (fun uu___ uu___1 -> FStar_Pervasives_Native.Some uu___))))
    uu___1 uu___
let rec repeatn :
  'a .
    Prims.int ->
      (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 uu___ ->
    (fun n t ->
       if n <= Prims.int_zero
       then Obj.magic (Obj.repr (fun uu___ -> []))
       else
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind (Obj.magic (t ()))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       Obj.magic
                         (fun ps ->
                            let x = repeatn (n - Prims.int_one) t ps in
                            uu___1 :: x)) uu___1)))) uu___1 uu___
let rec tryFind :
  'a .
    ('a -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 uu___ ->
    (fun f l ->
       match l with
       | [] -> Obj.magic (Obj.repr (fun uu___ -> false))
       | hd::tl ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f hd))
                   (fun uu___ ->
                      (fun uu___ ->
                         if uu___
                         then Obj.magic (Obj.repr (fun uu___1 -> true))
                         else Obj.magic (Obj.repr (tryFind f tl))) uu___))))
      uu___1 uu___
let rec fold_left2 :
  'a 'b 'c .
    ('a -> 'b -> 'c -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      'a ->
        'b Prims.list ->
          'c Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___3 uu___2 uu___1 uu___ ->
    (fun f x l1 l2 ->
       match (l1, l2) with
       | ([], []) -> Obj.magic (Obj.repr (fun uu___ -> x))
       | (hd1::tl1, hd2::tl2) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f x hd1 hd2))
                   (fun uu___ ->
                      (fun uu___ -> Obj.magic (fold_left2 f uu___ tl1 tl2))
                        uu___)))) uu___3 uu___2 uu___1 uu___
let rec string_of_list :
  'a .
    ('a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 uu___ ->
    (fun f l ->
       match l with
       | [] -> Obj.magic (Obj.repr (fun uu___ -> ""))
       | x::xs ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f x))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (fun ps ->
                              let x1 =
                                let x2 = string_of_list f xs ps in
                                Prims.strcat ";" x2 in
                              Prims.strcat uu___ x1)) uu___)))) uu___1 uu___
let string_of_option
  (uu___1 : 'a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  (uu___ : 'a FStar_Pervasives_Native.option) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  (fun f o ->
     match o with
     | FStar_Pervasives_Native.Some x ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind (Obj.magic (f x))
                 (fun uu___ uu___1 -> Prims.strcat "Some " uu___)))
     | FStar_Pervasives_Native.None ->
         Obj.magic (Obj.repr (fun uu___ -> "None"))) uu___1 uu___
let rec existsb :
  'a .
    ('a -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 uu___ ->
    (fun f l ->
       match l with
       | [] -> Obj.magic (Obj.repr (fun uu___ -> false))
       | hd::tl ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind (Obj.magic (f hd))
                   (fun uu___ ->
                      (fun uu___ ->
                         if uu___
                         then Obj.magic (Obj.repr (fun uu___1 -> true))
                         else Obj.magic (Obj.repr (existsb f tl))) uu___))))
      uu___1 uu___
