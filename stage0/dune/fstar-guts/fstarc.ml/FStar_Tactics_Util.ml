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
        (fun ps -> let x1 = f a1 ps in let x2 = map f tl ps in x1 :: x2)
let rec concatMap :
  'a 'b .
    ('a -> ('b Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('b Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f l ->
    match l with
    | [] -> (fun uu___ -> [])
    | x::xs ->
        (fun ps ->
           let x1 = f x ps in
           let x2 = concatMap f xs ps in FStar_List_Tot_Base.op_At x1 x2)
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
        (fun ps ->
           let x1 = f i a1 ps in
           let x2 = __mapi (i + Prims.int_one) f tl ps in x1 :: x2)
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
    | a1::tl -> (fun ps -> f a1 ps; iter f tl ps)
let rec iteri_aux :
  'a .
    Prims.int ->
      (Prims.int -> 'a -> (unit, Obj.t) FStar_Tactics_Effect.tac_repr) ->
        'a Prims.list -> (unit, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun i f x ->
    match x with
    | [] -> (fun uu___ -> ())
    | a1::tl -> (fun ps -> f i a1 ps; iteri_aux (i + Prims.int_one) f tl ps)
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
    | hd::tl -> (fun ps -> let x1 = f x hd ps in fold_left f x1 tl ps)
let rec fold_right :
  'a 'b .
    ('a -> 'b -> ('b, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> 'b -> ('b, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f l x ->
    match l with
    | [] -> (fun uu___ -> x)
    | hd::tl -> (fun ps -> let x1 = fold_right f tl x ps in f hd x1 ps)
let rec zip :
  'a 'b .
    'a Prims.list ->
      'b Prims.list ->
        (('a * 'b) Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun l1 l2 ->
    match (l1, l2) with
    | (x::xs, y::ys) -> (fun ps -> let x1 = zip xs ys ps in (x, y) :: x1)
    | uu___ -> (fun uu___1 -> [])
let rec filter :
  'a .
    ('a -> (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('a Prims.list, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f uu___ ->
    match uu___ with
    | [] -> (fun uu___1 -> [])
    | hd::tl ->
        (fun ps ->
           let x = f hd ps in
           if x then let x1 = filter f tl ps in hd :: x1 else filter f tl ps)
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
        (fun ps ->
           let x = f hd ps in
           match x with
           | FStar_Pervasives_Native.Some hd1 ->
               filter_map_acc f (hd1 :: acc) tl ps
           | FStar_Pervasives_Native.None -> filter_map_acc f acc tl ps)
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
        (fun ps ->
           let x = f hd ps in
           match x with
           | FStar_Pervasives_Native.Some x1 ->
               FStar_Pervasives_Native.Some x1
           | FStar_Pervasives_Native.None -> tryPick f tl ps)
let map_opt (f : 'a -> ('b, Obj.t) FStar_Tactics_Effect.tac_repr)
  (x : 'a FStar_Pervasives_Native.option) :
  ('b FStar_Pervasives_Native.option, Obj.t) FStar_Tactics_Effect.tac_repr=
  match x with
  | FStar_Pervasives_Native.None ->
      (fun uu___ -> FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.Some x1 ->
      (fun ps -> let x2 = f x1 ps in FStar_Pervasives_Native.Some x2)
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
      (fun ps ->
         let x = t () ps in
         let x1 = repeatn (n - Prims.int_one) t ps in x :: x1)
let rec tryFind :
  'a .
    ('a -> (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f l ->
    match l with
    | [] -> (fun uu___ -> false)
    | hd::tl ->
        (fun ps -> let x = f hd ps in if x then true else tryFind f tl ps)
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
        (fun ps -> let x1 = f x hd1 hd2 ps in fold_left2 f x1 tl1 tl2 ps)
let rec string_of_list :
  'a .
    ('a -> (Prims.string, Obj.t) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.string, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun f l ->
    match l with
    | [] -> (fun uu___ -> "")
    | x::xs ->
        (fun ps ->
           let x1 = f x ps in
           let x2 = let x3 = string_of_list f xs ps in Prims.strcat ";" x3 in
           Prims.strcat x1 x2)
let string_of_option
  (f : 'a -> (Prims.string, Obj.t) FStar_Tactics_Effect.tac_repr)
  (o : 'a FStar_Pervasives_Native.option) :
  (Prims.string, Obj.t) FStar_Tactics_Effect.tac_repr=
  match o with
  | FStar_Pervasives_Native.Some x ->
      (fun ps -> let x1 = f x ps in Prims.strcat "Some " x1)
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
        (fun ps -> let x = f hd ps in if x then true else existsb f tl ps)
