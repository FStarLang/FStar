open Prims
type 'a cmp = 'a -> 'a -> Prims.bool
let rec sorted : 'a . 'a cmp -> 'a Prims.list -> Prims.bool =
  fun f l ->
    match l with
    | [] -> true
    | x::[] -> true
    | x::y::tl -> ((f x y) && (x <> y)) && (sorted f (y :: tl))
type ('a, 'f) ordset = 'a Prims.list
let empty (uu___ : 'uuuuu cmp) : ('uuuuu, Obj.t) ordset= []
let tail (f : 'a cmp) (s : ('a, Obj.t) ordset) : ('a, Obj.t) ordset=
  Prims.__proj__Cons__item__tl s
let head (uu___ : 'uuuuu cmp) (s : ('uuuuu, Obj.t) ordset) : 'uuuuu=
  Prims.__proj__Cons__item__hd s
let mem (uu___ : 'uuuuu cmp) (x : 'uuuuu) (s : ('uuuuu, Obj.t) ordset) :
  Prims.bool= FStar_List_Tot_Base.mem x s
let mem_of (f : 'a cmp) (s : ('a, Obj.t) ordset) (x : 'a) : Prims.bool=
  mem f x s
let rec last_direct : 'a . 'a cmp -> ('a, Obj.t) ordset -> 'a =
  fun f s -> match s with | x::[] -> x | h::g::t -> last_direct f (tail f s)
let last_lib (f : 'a cmp) (s : ('a, Obj.t) ordset) : 'a=
  FStar_Pervasives_Native.snd (FStar_List_Tot_Base.unsnoc s)
let last (f : 'a cmp) (s : ('a, Obj.t) ordset) : 'a= last_lib f s
let rec liat_direct : 'a . 'a cmp -> ('a, Obj.t) ordset -> ('a, Obj.t) ordset
  =
  fun f s ->
    match s with | x::[] -> [] | h::g::t -> h :: (liat_direct f (g :: t))
let liat_lib (f : 'a cmp) (s : ('a, Obj.t) ordset) : 'a Prims.list=
  FStar_Pervasives_Native.fst (FStar_List_Tot_Base.unsnoc s)
let liat (f : 'a cmp) (s : ('a, Obj.t) ordset) : ('a, Obj.t) ordset=
  liat_lib f s
let unsnoc (f : 'a cmp) (s : ('a, Obj.t) ordset) : (('a, Obj.t) ordset * 'a)=
  let l = FStar_List_Tot_Base.unsnoc s in
  ((FStar_Pervasives_Native.fst l), (FStar_Pervasives_Native.snd l))
let as_list (f : 'a cmp) (s : ('a, Obj.t) ordset) : 'a Prims.list= s
let rec insert' :
  'uuuuu .
    'uuuuu cmp -> 'uuuuu -> ('uuuuu, Obj.t) ordset -> ('uuuuu, Obj.t) ordset
  =
  fun f x s ->
    match s with
    | [] -> [x]
    | hd::tl ->
        if x = hd
        then hd :: tl
        else if f x hd then x :: hd :: tl else hd :: (insert' f x tl)
let rec distinct' : 'a . 'a cmp -> 'a Prims.list -> ('a, Obj.t) ordset =
  fun f l -> match l with | [] -> [] | x::t -> insert' f x (distinct' f t)
let distinct (f : 'a cmp) (l : 'a Prims.list) : ('a, Obj.t) ordset=
  distinct' f l
let rec union :
  'uuuuu .
    'uuuuu cmp ->
      ('uuuuu, Obj.t) ordset ->
        ('uuuuu, Obj.t) ordset -> ('uuuuu, Obj.t) ordset
  =
  fun uu___ s1 s2 ->
    match s1 with | [] -> s2 | hd::tl -> union uu___ tl (insert' uu___ hd s2)
let rec remove' :
  'a . 'a cmp -> 'a -> ('a, Obj.t) ordset -> ('a, Obj.t) ordset =
  fun f x s ->
    match s with
    | [] -> []
    | hd::tl ->
        let tl1 = tl in if x = hd then tl1 else hd :: (remove' f x tl1)
let size' (f : 'a cmp) (s : ('a, Obj.t) ordset) : Prims.nat=
  FStar_List_Tot_Base.length s
let rec subset' :
  'a . 'a cmp -> ('a, Obj.t) ordset -> ('a, Obj.t) ordset -> Prims.bool =
  fun f s1 s2 ->
    match (s1, s2) with
    | ([], uu___) -> true
    | (hd::tl, hd'::tl') ->
        if (f hd hd') && (hd = hd')
        then subset' f tl tl'
        else
          if (f hd hd') && (Prims.op_Negation (hd = hd'))
          then false
          else subset' f s1 tl'
    | (uu___, uu___1) -> false
let rec remove_until_greater_than :
  'a .
    'a cmp -> 'a -> ('a, Obj.t) ordset -> (('a, Obj.t) ordset * Prims.bool)
  =
  fun f x s ->
    match s with
    | [] -> ([], false)
    | h::t ->
        let t1 = t in
        if h = x
        then (t1, true)
        else if f x h then (s, false) else remove_until_greater_than f x t1
let rec smart_intersect :
  'a .
    'a cmp -> ('a, Obj.t) ordset -> ('a, Obj.t) ordset -> ('a, Obj.t) ordset
  =
  fun f s1 s2 ->
    match s1 with
    | [] -> []
    | h1::t1 ->
        let t11 = t1 in
        (match s2 with
         | [] -> []
         | h2::t2 ->
             let t21 = t2 in
             if h1 = h2
             then h1 :: (smart_intersect f t11 t21)
             else
               if f h1 h2
               then
                 (let uu___ = remove_until_greater_than f h2 t11 in
                  match uu___ with
                  | (skip1, found) ->
                      let subresult = smart_intersect f skip1 t21 in
                      if found then h2 :: subresult else subresult)
               else
                 (let uu___ = remove_until_greater_than f h1 t21 in
                  match uu___ with
                  | (skip2, found) ->
                      let subresult = smart_intersect f t11 skip2 in
                      if found then h1 :: subresult else subresult))
let intersect (f : 'a cmp) (s1 : ('a, Obj.t) ordset)
  (s2 : ('a, Obj.t) ordset) : ('a, Obj.t) ordset= smart_intersect f s1 s2
let choose (f : 'a cmp) (s : ('a, Obj.t) ordset) :
  'a FStar_Pervasives_Native.option=
  match s with
  | [] -> FStar_Pervasives_Native.None
  | x::uu___ -> FStar_Pervasives_Native.Some x
let remove (f : 'a cmp) (x : 'a) (s : ('a, Obj.t) ordset) :
  ('a, Obj.t) ordset= remove' f x s
let size (f : 'a cmp) (s : ('a, Obj.t) ordset) : Prims.nat= size' f s
let subset (f : 'a cmp) (s1 : ('a, Obj.t) ordset) (s2 : ('a, Obj.t) ordset) :
  Prims.bool= subset' f s1 s2
let superset (f : 'a cmp) (s1 : ('a, Obj.t) ordset) (s2 : ('a, Obj.t) ordset)
  : Prims.bool= subset f s2 s1
let singleton (f : 'a cmp) (x : 'a) : ('a, Obj.t) ordset= [x]
let rec smart_minus :
  'a .
    'a cmp -> ('a, Obj.t) ordset -> ('a, Obj.t) ordset -> ('a, Obj.t) ordset
  =
  fun f p q ->
    match p with
    | [] -> []
    | ph::pt ->
        let pt1 = pt in
        (match q with
         | [] -> p
         | qh::qt ->
             let qt1 = qt in
             let uu___ = remove_until_greater_than f ph q in
             (match uu___ with
              | (q_after_ph, found) ->
                  if found
                  then let result = smart_minus f pt1 q_after_ph in result
                  else ph :: (smart_minus f pt1 q_after_ph)))
let ncmp (x : Prims.nat) (y : Prims.nat) : Prims.bool= x <= y
let minus (f : 'a cmp) (s1 : ('a, Obj.t) ordset) (s2 : ('a, Obj.t) ordset) :
  ('a, Obj.t) ordset= smart_minus f s1 s2
let strict_subset (f : 'a cmp) (s1 : ('a, Obj.t) ordset)
  (s2 : ('a, Obj.t) ordset) : Prims.bool= (s1 <> s2) && (subset f s1 s2)
let strict_superset (f : 'a cmp) (s1 : ('a, Obj.t) ordset)
  (s2 : ('a, Obj.t) ordset) : Prims.bool= strict_subset f s2 s1
let disjoint (f : 'a cmp) (s1 : ('a, Obj.t) ordset) (s2 : ('a, Obj.t) ordset)
  : Prims.bool= (intersect f s1 s2) = (empty f)
let fold (f : 'a cmp) (g : 'acc -> 'a -> 'acc) (init : 'acc)
  (s : ('a, Obj.t) ordset) : 'acc= FStar_List_Tot_Base.fold_left g init s
let rec map_internal :
  'a 'b .
    'a cmp ->
      'b cmp -> ('a -> 'b) -> ('a, Obj.t) ordset -> ('b, Obj.t) ordset
  =
  fun fa fb g sa ->
    match sa with
    | [] -> []
    | x::xs ->
        let y = g x in
        let ys = map_internal fa fb g xs in
        if
          (Prims.op_Negation (Prims.uu___is_Cons ys)) ||
            ((Prims.__proj__Cons__item__hd ys) <> y)
        then y :: ys
        else ys
let map (fa : 'a cmp) (fb : 'b cmp) (g : 'a -> 'b) (sa : ('a, Obj.t) ordset)
  : ('b, Obj.t) ordset= map_internal fa fb g sa
type 'a condition = 'a -> Prims.bool
let inv (c : 'a condition) : 'a condition= fun x -> Prims.op_Negation (c x)
let rec count :
  'a . 'a cmp -> ('a, Obj.t) ordset -> 'a condition -> Prims.nat =
  fun f s c ->
    match s with
    | [] -> Prims.int_zero
    | h::t -> if c h then Prims.int_one + (count f t c) else count f t c
let rec all : 'a . 'a cmp -> ('a, Obj.t) ordset -> 'a condition -> Prims.bool
  = fun f s c -> match s with | [] -> true | h::t -> (c h) && (all f t c)
let rec any : 'a . 'a cmp -> ('a, Obj.t) ordset -> 'a condition -> Prims.bool
  = fun f s c -> match s with | [] -> false | h::t -> (c h) || (any f t c)
let rec find_first :
  'a .
    'a cmp ->
      ('a, Obj.t) ordset -> 'a condition -> 'a FStar_Pervasives_Native.option
  =
  fun f s c ->
    match s with
    | [] -> FStar_Pervasives_Native.None
    | h::t ->
        let t1 = t in
        if c h then FStar_Pervasives_Native.Some h else find_first f t1 c
let rec find_last' :
  'a .
    'a cmp ->
      ('a, Obj.t) ordset -> 'a condition -> 'a FStar_Pervasives_Native.option
  =
  fun f s c ->
    if s = (empty f)
    then FStar_Pervasives_Native.None
    else
      (let uu___ = unsnoc f s in
       match uu___ with
       | (liat1, last1) ->
           if c last1
           then FStar_Pervasives_Native.Some last1
           else find_last' f liat1 c)
let find_last (f : 'a cmp) (s : ('a, Obj.t) ordset) (c : 'a condition) :
  'a FStar_Pervasives_Native.option= find_last' f s c
let rec where :
  'a . 'a cmp -> ('a, Obj.t) ordset -> 'a condition -> ('a, Obj.t) ordset =
  fun f s c ->
    match s with
    | [] -> []
    | h::[] -> if c h then [h] else []
    | h::t -> let t1 = t in if c h then h :: (where f t1 c) else where f t1 c
let rec as_set : 'a . 'a cmp -> ('a, Obj.t) ordset -> 'a FStar_Set.set =
  fun f s ->
    match s with
    | [] -> FStar_Set.empty ()
    | hd::tl -> FStar_Set.union (FStar_Set.singleton hd) (as_set f tl)
