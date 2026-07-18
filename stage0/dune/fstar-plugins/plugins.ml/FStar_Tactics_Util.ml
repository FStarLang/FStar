open Fstarcompiler
open Prims
let rec map :
  'a 'b .
    ('a -> ('b, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('b Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f x ->
    match x with
    | [] -> (fun uu___ -> [])
    | a1::tl ->
        FStar_Tactics_Effect.tac_bind () () (f a1)
          (fun uu___ ps -> let x1 = map f tl ps in uu___ :: x1)
let rec concatMap :
  'a 'b .
    ('a -> ('b Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('b Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f l ->
    match l with
    | [] -> (fun uu___ -> [])
    | x::xs ->
        FStar_Tactics_Effect.tac_bind () () (f x)
          (fun uu___ ps ->
             let x1 = concatMap f xs ps in FStar_List_Tot_Base.op_At uu___ x1)
let rec __mapi :
  'a 'b .
    Prims.nat ->
      (Prims.nat -> 'a -> ('b, Obj.t) FStar_Tactics_Effect.tac_repr) ->
        'a Prims.list -> ('b Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun i f x ->
    match x with
    | [] -> (fun uu___ -> [])
    | a1::tl ->
        FStar_Tactics_Effect.tac_bind () () (f i a1)
          (fun uu___ ps ->
             let x1 = __mapi (i + Prims.int_one) f tl ps in uu___ :: x1)
let mapi (f : Prims.nat -> 'a -> ('b, Obj.t) FStar_Tactics_Effect.tac_repr)
  (l : 'a Prims.list) : ('b Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr=
  __mapi Prims.int_zero f l
let rec iter :
  'a .
    ('a -> (unit, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (unit, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f x ->
    match x with
    | [] -> (fun uu___ -> ())
    | a1::tl ->
        FStar_Tactics_Effect.tac_bind () () (f a1) (fun uu___ -> iter f tl)
let rec iteri_aux :
  'a .
    Prims.int ->
      (Prims.int -> 'a -> (unit, Obj.t) FStar_Tactics_Effect.tac_repr) ->
        'a Prims.list -> (unit, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun i f x ->
    match x with
    | [] -> (fun uu___ -> ())
    | a1::tl ->
        FStar_Tactics_Effect.tac_bind () () (f i a1)
          (fun uu___ -> iteri_aux (i + Prims.int_one) f tl)
let iteri
  (f : Prims.int -> 'a -> (unit, Obj.t) FStar_Tactics_Effect.tac_repr)
  (x : 'a Prims.list) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  iteri_aux Prims.int_zero f x
let rec fold_left :
  'a 'b .
    ('a -> 'b -> ('a, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a -> 'b Prims.list -> ('a, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f x l ->
    match l with
    | [] -> (fun uu___ -> x)
    | hd::tl ->
        FStar_Tactics_Effect.tac_bind () () (f x hd)
          (fun uu___ -> fold_left f uu___ tl)
let rec fold_right :
  'a 'b .
    ('a -> 'b -> ('b, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> 'b -> ('b, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f l x ->
    match l with
    | [] -> (fun uu___ -> x)
    | hd::tl ->
        FStar_Tactics_Effect.tac_bind () () (fold_right f tl x)
          (fun uu___ -> f hd uu___)
let rec zip :
  'a 'b .
    'a Prims.list ->
      'b Prims.list ->
        (('a * 'b) Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun l1 l2 ->
    match (l1, l2) with
    | (x::xs, y::ys) ->
        FStar_Tactics_Effect.tac_bind () () (zip xs ys)
          (fun uu___ uu___1 -> (x, y) :: uu___)
    | uu___ -> FStar_Tactics_Effect.lift_div_tac () (fun uu___1 -> [])
let rec filter :
  'a .
    ('a -> (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('a Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f uu___ ->
    match uu___ with
    | [] -> (fun uu___1 -> [])
    | hd::tl ->
        FStar_Tactics_Effect.tac_bind () () (f hd)
          (fun uu___1 ->
             if uu___1
             then fun ps -> let x = filter f tl ps in hd :: x
             else filter f tl)
let rec filter_map_acc :
  'a 'b .
    ('a ->
       ('b FStar_Pervasives_Native.option, Obj.t)
         FStar_Tactics_Effect.tac_repr)
      ->
      'b Prims.list ->
        'a Prims.list -> ('b Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f acc l ->
    match l with
    | [] -> (fun uu___ -> FStar_List_Tot_Base.rev acc)
    | hd::tl ->
        FStar_Tactics_Effect.tac_bind () () (f hd)
          (fun uu___ ->
             match uu___ with
             | FStar_Pervasives_Native.Some hd1 ->
                 filter_map_acc f (hd1 :: acc) tl
             | FStar_Pervasives_Native.None -> filter_map_acc f acc tl)
let filter_map
  (f :
    'a ->
      ('b FStar_Pervasives_Native.option, Obj.t)
        FStar_Tactics_Effect.tac_repr)
  (l : 'a Prims.list) : ('b Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr=
  filter_map_acc f [] l
let rec tryPick :
  'a 'b .
    ('a ->
       ('b FStar_Pervasives_Native.option, Obj.t)
         FStar_Tactics_Effect.tac_repr)
      ->
      'a Prims.list ->
        ('b FStar_Pervasives_Native.option, Obj.t)
          FStar_Tactics_Effect.tac_repr
  =
  fun f l ->
    match l with
    | [] -> (fun uu___ -> FStar_Pervasives_Native.None)
    | hd::tl ->
        FStar_Tactics_Effect.tac_bind () () (f hd)
          (fun uu___ ->
             match uu___ with
             | FStar_Pervasives_Native.Some x ->
                 FStar_Tactics_Effect.lift_div_tac ()
                   (fun uu___1 -> FStar_Pervasives_Native.Some x)
             | FStar_Pervasives_Native.None -> tryPick f tl)
let map_opt (f : 'a -> ('b, Obj.t) FStar_Tactics_Effect.tac_repr)
  (x : 'a FStar_Pervasives_Native.option) :
  ('b FStar_Pervasives_Native.option, Obj.t) FStar_Tactics_Effect.tac_repr=
  match x with
  | FStar_Pervasives_Native.None ->
      (fun uu___ -> FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.Some x1 ->
      FStar_Tactics_Effect.tac_bind () () (f x1)
        (fun uu___ uu___1 -> FStar_Pervasives_Native.Some uu___)
let rec repeatn :
  'a .
    Prims.int ->
      (unit -> ('a, Obj.t) FStar_Tactics_Effect.tac_repr) ->
        ('a Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun n t ->
    if n <= Prims.int_zero
    then fun uu___ -> []
    else
      FStar_Tactics_Effect.tac_bind () () (t ())
        (fun uu___1 ps ->
           let x = repeatn (n - Prims.int_one) t ps in uu___1 :: x)
let rec tryFind :
  'a .
    ('a -> (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f l ->
    match l with
    | [] -> (fun uu___ -> false)
    | hd::tl ->
        FStar_Tactics_Effect.tac_bind () () (f hd)
          (fun uu___ -> if uu___ then fun uu___1 -> true else tryFind f tl)
let rec fold_left2 :
  'a 'b 'c .
    ('a -> 'b -> 'c -> ('a, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a ->
        'b Prims.list ->
          'c Prims.list -> ('a, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f x l1 l2 ->
    match (l1, l2) with
    | ([], []) -> (fun uu___ -> x)
    | (hd1::tl1, hd2::tl2) ->
        FStar_Tactics_Effect.tac_bind () () (f x hd1 hd2)
          (fun uu___ -> fold_left2 f uu___ tl1 tl2)
let rec string_of_list :
  'a .
    ('a -> (Prims.string, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.string, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f l ->
    match l with
    | [] -> (fun uu___ -> "")
    | x::xs ->
        FStar_Tactics_Effect.tac_bind () () (f x)
          (fun uu___ ps ->
             let x1 = let x2 = string_of_list f xs ps in Prims.strcat ";" x2 in
             Prims.strcat uu___ x1)
let string_of_option
  (f : 'a -> (Prims.string, Obj.t) FStar_Tactics_Effect.tac_repr)
  (o : 'a FStar_Pervasives_Native.option) :
  (Prims.string, Obj.t) FStar_Tactics_Effect.tac_repr=
  match o with
  | FStar_Pervasives_Native.Some x ->
      FStar_Tactics_Effect.tac_bind () () (f x)
        (fun uu___ uu___1 -> Prims.strcat "Some " uu___)
  | FStar_Pervasives_Native.None -> (fun uu___ -> "None")
let rec existsb :
  'a .
    ('a -> (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f l ->
    match l with
    | [] -> (fun uu___ -> false)
    | hd::tl ->
        FStar_Tactics_Effect.tac_bind () () (f hd)
          (fun uu___ -> if uu___ then fun uu___1 -> true else existsb f tl)
