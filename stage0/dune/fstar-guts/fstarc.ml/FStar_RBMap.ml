open Prims
type color =
  | R 
  | B 
let uu___is_R (projectee : color) : Prims.bool=
  match projectee with | R -> true | uu___ -> false
let uu___is_B (projectee : color) : Prims.bool=
  match projectee with | B -> true | uu___ -> false
type ('a, 'b) t =
  | L 
  | N of (color * ('a, 'b) t * 'a * 'b * ('a, 'b) t) 
let uu___is_L (projectee : ('a, 'b) t) : Prims.bool=
  match projectee with | L -> true | uu___ -> false
let uu___is_N (projectee : ('a, 'b) t) : Prims.bool=
  match projectee with | N _0 -> true | uu___ -> false
let __proj__N__item___0 (projectee : ('a, 'b) t) :
  (color * ('a, 'b) t * 'a * 'b * ('a, 'b) t)=
  match projectee with | N _0 -> _0
let empty (uu___ : unit) : ('a, 'b) t= L
let singleton (x : 'a) (y : 'b) : ('a, 'b) t= N (R, L, x, y, L)
let is_empty : ('a, 'b) t -> Prims.bool= uu___is_L
let balance (c : color) (l : ('uuuuu, 'uuuuu1) t) (x : 'uuuuu) (vx : 'uuuuu1)
  (r : ('uuuuu, 'uuuuu1) t) : ('uuuuu, 'uuuuu1) t=
  match (c, l, x, vx, r) with
  | (B, N (R, N (R, a, x1, vx1, b), y, vy, c1), z, vz, d) ->
      N (R, (N (B, a, x1, vx1, b)), y, vy, (N (B, c1, z, vz, d)))
  | (B, a, x1, vx1, N (R, N (R, b, y, vy, c1), z, vz, d)) ->
      N (R, (N (B, a, x1, vx1, b)), y, vy, (N (B, c1, z, vz, d)))
  | (B, N (R, a, x1, vx1, N (R, b, y, vy, c1)), z, vz, d) ->
      N (R, (N (B, a, x1, vx1, b)), y, vy, (N (B, c1, z, vz, d)))
  | (B, a, x1, vx1, N (R, b, y, vy, N (R, c1, z, vz, d))) ->
      N (R, (N (B, a, x1, vx1, b)), y, vy, (N (B, c1, z, vz, d)))
  | (c1, l1, x1, vx1, r1) -> N (c1, l1, x1, vx1, r1)
let blackroot (m : ('a, 'b) t) : ('a, 'b) t=
  let uu___ = m in
  match uu___ with | N (uu___1, l, x, vx, r) -> N (B, l, x, vx, r)
let add (uu___ : 'a FStar_Class_Ord_Raw.ord) (x : 'a) (vx : 'b)
  (s : ('a, 'b) t) : ('a, 'b) t=
  let rec add' s1 =
    match s1 with
    | L -> N (R, L, x, vx, L)
    | N (c, a1, y, vy, b1) ->
        if FStar_Class_Ord_Raw.op_Less_Question uu___ x y
        then balance c (add' a1) y vy b1
        else
          if FStar_Class_Ord_Raw.op_Greater_Question uu___ x y
          then balance c a1 y vy (add' b1)
          else s1 in
  blackroot (add' s)
let filter (uu___ : 'a FStar_Class_Ord_Raw.ord)
  (predicate : 'a -> 'b -> Prims.bool) (set : ('a, 'b) t) : ('a, 'b) t=
  let rec aux acc m =
    match m with
    | L -> acc
    | N (uu___1, l, v, vy, r) ->
        aux (aux (if predicate v vy then add uu___ v vy acc else acc) l) r in
  aux (empty ()) set
let rec extract_min :
  'a 'b .
    'a FStar_Class_Ord_Raw.ord -> ('a, 'b) t -> (('a, 'b) t * ('a * 'b))
  =
  fun uu___ m ->
    match m with
    | N (uu___1, L, x, vx, r) -> (r, (x, vx))
    | N (c, a1, x, vx, b1) ->
        let uu___1 = extract_min uu___ a1 in
        (match uu___1 with | (a', y) -> ((balance c a' x vx b1), y))
let rec remove :
  'a 'b . 'a FStar_Class_Ord_Raw.ord -> 'a -> ('a, 'b) t -> ('a, 'b) t =
  fun uu___ x m ->
    match m with
    | L -> L
    | N (c, l, y, vy, r) ->
        if FStar_Class_Ord_Raw.op_Less_Question uu___ x y
        then balance c (remove uu___ x l) y vy r
        else
          if FStar_Class_Ord_Raw.op_Greater_Question uu___ x y
          then balance c l y vy (remove uu___ x r)
          else
            if uu___is_L r
            then l
            else
              (let uu___1 = extract_min uu___ r in
               match uu___1 with | (r', (y', vy')) -> balance c l y' vy' r')
let rec mem :
  'a 'b . 'a FStar_Class_Ord_Raw.ord -> 'a -> ('a, 'b) t -> Prims.bool =
  fun uu___ x m ->
    match m with
    | L -> false
    | N (uu___1, a1, y, uu___2, b1) ->
        if FStar_Class_Ord_Raw.op_Less_Question uu___ x y
        then mem uu___ x a1
        else
          if FStar_Class_Ord_Raw.op_Greater_Question uu___ x y
          then mem uu___ x b1
          else true
let rec lookup :
  'a 'b .
    'a FStar_Class_Ord_Raw.ord ->
      'a -> ('a, 'b) t -> 'b FStar_Pervasives_Native.option
  =
  fun uu___ x m ->
    match m with
    | L -> FStar_Pervasives_Native.None
    | N (uu___1, a1, y, vy, b1) ->
        if FStar_Class_Ord_Raw.op_Less_Question uu___ x y
        then lookup uu___ x a1
        else
          if FStar_Class_Ord_Raw.op_Greater_Question uu___ x y
          then lookup uu___ x b1
          else FStar_Pervasives_Native.Some vy
let rec keys : 'a 'b . ('a, 'b) t -> 'a Prims.list =
  fun s ->
    match s with
    | L -> []
    | N (uu___, a1, x, uu___1, b1) ->
        FStar_List_Tot_Base.op_At (keys a1)
          (FStar_List_Tot_Base.op_At [x] (keys b1))
let rec to_list : 'a 'b . ('a, 'b) t -> ('a * 'b) Prims.list =
  fun s ->
    match s with
    | L -> []
    | N (uu___, a1, x, vx, b1) ->
        FStar_List_Tot_Base.op_At (to_list a1)
          (FStar_List_Tot_Base.op_At [(x, vx)] (to_list b1))
let equal (uu___ : 'a FStar_Class_Ord_Raw.ord)
  (uu___1 : 'b FStar_Class_Eq_Raw.deq) (s1 : ('a, 'b) t) (s2 : ('a, 'b) t) :
  Prims.bool=
  FStar_Class_Eq_Raw.op_Equals
    (FStar_Class_Eq_Raw.eq_list
       (FStar_Class_Eq_Raw.eq_pair (FStar_Class_Ord_Raw.ord_eq uu___) uu___1))
    (to_list s1) (to_list s2)
let rec union :
  'a 'b .
    'a FStar_Class_Ord_Raw.ord -> ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
  =
  fun uu___ s1 s2 ->
    match s1 with
    | L -> s2
    | N (c, a1, x, vx, b1) ->
        union uu___ a1 (union uu___ b1 (add uu___ x vx s2))
let inter (uu___ : 'a FStar_Class_Ord_Raw.ord) (s1 : ('a, 'b) t)
  (s2 : ('a, 'b) t) : ('a, 'b) t=
  let rec aux s11 acc =
    match s11 with
    | L -> acc
    | N (uu___1, a1, x, vx, b1) ->
        if mem uu___ x s2
        then add uu___ x vx (aux a1 (aux b1 acc))
        else aux a1 (aux b1 acc) in
  aux s1 L
let rec for_all :
  'a 'b . ('a -> 'b -> Prims.bool) -> ('a, 'b) t -> Prims.bool =
  fun p s ->
    match s with
    | L -> true
    | N (uu___, a1, x, vx, b1) ->
        ((p x vx) && (for_all p a1)) && (for_all p b1)
let rec for_any :
  'a 'b . ('a -> 'b -> Prims.bool) -> ('a, 'b) t -> Prims.bool =
  fun p s ->
    match s with
    | L -> false
    | N (uu___, a1, x, vx, b1) ->
        (p x vx) || ((for_all p a1) && (for_all p b1))
let from_list (uu___ : 'a FStar_Class_Ord_Raw.ord)
  (xs : ('a * 'b) Prims.list) : ('a, 'b) t=
  FStar_List_Tot_Base.fold_left
    (fun s uu___1 -> match uu___1 with | (k, v) -> add uu___ k v s) L xs
let addn (uu___ : 'a FStar_Class_Ord_Raw.ord) (xs : ('a * 'b) Prims.list)
  (s : ('a, 'b) t) : ('a, 'b) t=
  FStar_List_Tot_Base.fold_left
    (fun s1 uu___1 -> match uu___1 with | (k, v) -> add uu___ k v s1) s xs
