open Prims
type color =
  | R 
  | B 
let uu___is_R (projectee : color) : Prims.bool=
  match projectee with | R -> true | uu___ -> false
let uu___is_B (projectee : color) : Prims.bool=
  match projectee with | B -> true | uu___ -> false
type 'a t =
  | L 
  | N of (color * 'a t * 'a * 'a t) 
let uu___is_L (projectee : 'a t) : Prims.bool=
  match projectee with | L -> true | uu___ -> false
let uu___is_N (projectee : 'a t) : Prims.bool=
  match projectee with | N _0 -> true | uu___ -> false
let __proj__N__item___0 (projectee : 'a t) : (color * 'a t * 'a * 'a t)=
  match projectee with | N _0 -> _0
let empty (uu___ : unit) : 'a t= L
let singleton (x : 'a) : 'a t= N (R, L, x, L)
let is_empty : 'a t -> Prims.bool= uu___is_L
let balance (c : color) (l : 'uuuuu t) (x : 'uuuuu) (r : 'uuuuu t) :
  'uuuuu t=
  match (c, l, x, r) with
  | (B, N (R, N (R, a, x1, b), y, c1), z, d) ->
      N (R, (N (B, a, x1, b)), y, (N (B, c1, z, d)))
  | (B, a, x1, N (R, N (R, b, y, c1), z, d)) ->
      N (R, (N (B, a, x1, b)), y, (N (B, c1, z, d)))
  | (B, N (R, a, x1, N (R, b, y, c1)), z, d) ->
      N (R, (N (B, a, x1, b)), y, (N (B, c1, z, d)))
  | (B, a, x1, N (R, b, y, N (R, c1, z, d))) ->
      N (R, (N (B, a, x1, b)), y, (N (B, c1, z, d)))
  | (c1, l1, x1, r1) -> N (c1, l1, x1, r1)
let blackroot (s : 'a t) : 'a t=
  match s with | N (uu___, l, x, r) -> N (B, l, x, r)
let add (uu___ : 'a FStar_Class_Ord_Raw.ord) (x : 'a) (s : 'a t) : 'a t=
  let rec add' s1 =
    match s1 with
    | L -> N (R, L, x, L)
    | N (c, a1, y, b) ->
        if FStar_Class_Ord_Raw.op_Less_Question uu___ x y
        then balance c (add' a1) y b
        else
          if FStar_Class_Ord_Raw.op_Greater_Question uu___ x y
          then balance c a1 y (add' b)
          else s1 in
  blackroot (add' s)
let filter (uu___ : 'a FStar_Class_Ord_Raw.ord)
  (predicate : 'a -> Prims.bool) (set : 'a t) : 'a t=
  let rec aux acc s =
    match s with
    | L -> acc
    | N (uu___1, l, v, r) ->
        aux (aux (if predicate v then add uu___ v acc else acc) l) r in
  aux (empty ()) set
let rec extract_min : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a t -> ('a t * 'a)
  =
  fun uu___ s ->
    match s with
    | N (uu___1, L, x, r) -> (r, x)
    | N (c, a1, x, b) ->
        let uu___1 = extract_min uu___ a1 in
        (match uu___1 with | (a', y) -> ((balance c a' x b), y))
let rec remove : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a -> 'a t -> 'a t =
  fun uu___ x s ->
    match s with
    | L -> L
    | N (c, l, y, r) ->
        if FStar_Class_Ord_Raw.op_Less_Question uu___ x y
        then balance c (remove uu___ x l) y r
        else
          if FStar_Class_Ord_Raw.op_Greater_Question uu___ x y
          then balance c l y (remove uu___ x r)
          else
            if uu___is_L r
            then l
            else
              (let uu___1 = extract_min uu___ r in
               match uu___1 with | (r', y') -> balance c l y' r')
let rec mem : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a -> 'a t -> Prims.bool =
  fun uu___ x s ->
    match s with
    | L -> false
    | N (uu___1, a1, y, b) ->
        if FStar_Class_Ord_Raw.op_Less_Question uu___ x y
        then mem uu___ x a1
        else
          if FStar_Class_Ord_Raw.op_Greater_Question uu___ x y
          then mem uu___ x b
          else true
let rec elems : 'a . 'a t -> 'a Prims.list =
  fun s ->
    match s with
    | L -> []
    | N (uu___, a1, x, b) ->
        FStar_List_Tot_Base.op_At (elems a1)
          (FStar_List_Tot_Base.op_At [x] (elems b))
let equal (uu___ : 'a FStar_Class_Ord_Raw.ord) (s1 : 'a t) (s2 : 'a t) :
  Prims.bool=
  FStar_Class_Eq_Raw.op_Equals
    (FStar_Class_Ord_Raw.ord_eq (FStar_Class_Ord_Raw.ord_list uu___))
    (elems s1) (elems s2)
let rec union : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a t -> 'a t -> 'a t =
  fun uu___ s1 s2 ->
    match s1 with
    | L -> s2
    | N (c, a1, x, b) -> union uu___ a1 (union uu___ b (add uu___ x s2))
let inter (uu___ : 'a FStar_Class_Ord_Raw.ord) (s1 : 'a t) (s2 : 'a t) :
  'a t=
  let rec aux s11 acc =
    match s11 with
    | L -> acc
    | N (uu___1, a1, x, b) ->
        if mem uu___ x s2
        then add uu___ x (aux a1 (aux b acc))
        else aux a1 (aux b acc) in
  aux s1 L
let rec diff : 'a . 'a FStar_Class_Ord_Raw.ord -> 'a t -> 'a t -> 'a t =
  fun uu___ s1 s2 ->
    match s2 with
    | L -> s1
    | N (uu___1, a1, x, b) ->
        diff uu___ (diff uu___ (remove uu___ x s1) a1) b
let rec subset :
  'a . 'a FStar_Class_Ord_Raw.ord -> 'a t -> 'a t -> Prims.bool =
  fun uu___ s1 s2 ->
    match s1 with
    | L -> true
    | N (uu___1, a1, x, b) ->
        ((mem uu___ x s2) && (subset uu___ a1 s2)) && (subset uu___ b s2)
let rec for_all : 'a . ('a -> Prims.bool) -> 'a t -> Prims.bool =
  fun p s ->
    match s with
    | L -> true
    | N (uu___, a1, x, b) -> ((p x) && (for_all p a1)) && (for_all p b)
let rec for_any : 'a . ('a -> Prims.bool) -> 'a t -> Prims.bool =
  fun p s ->
    match s with
    | L -> false
    | N (uu___, a1, x, b) -> ((p x) || (for_any p a1)) || (for_any p b)
let from_list (uu___ : 'a FStar_Class_Ord_Raw.ord) (xs : 'a Prims.list) :
  'a t= FStar_List_Tot_Base.fold_left (fun s e -> add uu___ e s) L xs
let addn (uu___ : 'a FStar_Class_Ord_Raw.ord) (xs : 'a Prims.list) (s : 'a t)
  : 'a t= FStar_List_Tot_Base.fold_left (fun s1 e -> add uu___ e s1) s xs
let collect (uu___ : 'a FStar_Class_Ord_Raw.ord) (f : 'a -> 'a t)
  (l : 'a Prims.list) : 'a t=
  FStar_List_Tot_Base.fold_left (fun s e -> union uu___ (f e) s) L l
