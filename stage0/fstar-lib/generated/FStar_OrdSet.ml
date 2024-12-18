open Prims
type ('a, 'f) total_order = unit
type 'a cmp = 'a -> 'a -> Prims.bool
let rec sorted : 'a . 'a cmp -> 'a Prims.list -> Prims.bool =
  fun f ->
    fun l ->
      match l with
      | [] -> true
      | x::[] -> true
      | x::y::tl -> ((f x y) && (x <> y)) && (sorted f (y :: tl))
type ('a, 'f) ordset = 'a Prims.list
let empty : 'uuuuu . 'uuuuu cmp -> ('uuuuu, unit) ordset = fun uu___ -> []
let tail : 'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset =
  fun f -> fun s -> Prims.__proj__Cons__item__tl s
let head : 'uuuuu . 'uuuuu cmp -> ('uuuuu, unit) ordset -> 'uuuuu =
  fun uu___ -> fun s -> Prims.__proj__Cons__item__hd s
let mem :
  'uuuuu . 'uuuuu cmp -> 'uuuuu -> ('uuuuu, unit) ordset -> Prims.bool =
  fun uu___ -> fun x -> fun s -> FStar_List_Tot_Base.mem x s
let mem_of : 'a . 'a cmp -> ('a, unit) ordset -> 'a -> Prims.bool =
  fun f -> fun s -> fun x -> mem f x s
let rec last_direct : 'a . 'a cmp -> ('a, unit) ordset -> 'a =
  fun f ->
    fun s -> match s with | x::[] -> x | h::g::t -> last_direct f (tail f s)
let last_lib : 'a . 'a cmp -> ('a, unit) ordset -> 'a =
  fun f ->
    fun s -> FStar_Pervasives_Native.snd (FStar_List_Tot_Base.unsnoc s)
let last : 'a . 'a cmp -> ('a, unit) ordset -> 'a =
  fun f -> fun s -> last_lib f s
let rec liat_direct : 'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset =
  fun f ->
    fun s ->
      match s with | x::[] -> [] | h::g::t -> h :: (liat_direct f (g :: t))
let liat_lib : 'a . 'a cmp -> ('a, unit) ordset -> 'a Prims.list =
  fun f ->
    fun s -> FStar_Pervasives_Native.fst (FStar_List_Tot_Base.unsnoc s)
let liat : 'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset =
  fun f -> fun s -> liat_lib f s
let unsnoc : 'a . 'a cmp -> ('a, unit) ordset -> (('a, unit) ordset * 'a) =
  fun f ->
    fun s ->
      let l = FStar_List_Tot_Base.unsnoc s in
      ((FStar_Pervasives_Native.fst l), (FStar_Pervasives_Native.snd l))
let as_list : 'a . 'a cmp -> ('a, unit) ordset -> 'a Prims.list =
  fun f -> fun s -> s
let rec insert' :
  'uuuuu .
    'uuuuu cmp -> 'uuuuu -> ('uuuuu, unit) ordset -> ('uuuuu, unit) ordset
  =
  fun f ->
    fun x ->
      fun s ->
        match s with
        | [] -> [x]
        | hd::tl ->
            if x = hd
            then hd :: tl
            else if f x hd then x :: hd :: tl else hd :: (insert' f x tl)
let rec distinct' : 'a . 'a cmp -> 'a Prims.list -> ('a, unit) ordset =
  fun f ->
    fun l -> match l with | [] -> [] | x::t -> insert' f x (distinct' f t)
let distinct : 'a . 'a cmp -> 'a Prims.list -> ('a, unit) ordset =
  fun f -> fun l -> distinct' f l
let rec union :
  'uuuuu .
    'uuuuu cmp ->
      ('uuuuu, unit) ordset -> ('uuuuu, unit) ordset -> ('uuuuu, unit) ordset
  =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        match s1 with
        | [] -> s2
        | hd::tl -> union uu___ tl (insert' uu___ hd s2)
let rec remove' : 'a . 'a cmp -> 'a -> ('a, unit) ordset -> ('a, unit) ordset
  =
  fun f ->
    fun x ->
      fun s ->
        match s with
        | [] -> []
        | hd::tl ->
            let tl1 = tl in if x = hd then tl1 else hd :: (remove' f x tl1)
let size' : 'a . 'a cmp -> ('a, unit) ordset -> Prims.nat =
  fun f -> fun s -> FStar_List_Tot_Base.length s
let rec subset' :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> Prims.bool =
  fun f ->
    fun s1 ->
      fun s2 ->
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
  'a . 'a cmp -> 'a -> ('a, unit) ordset -> (('a, unit) ordset * Prims.bool)
  =
  fun f ->
    fun x ->
      fun s ->
        match s with
        | [] -> ([], false)
        | h::t ->
            let t1 = t in
            if h = x
            then (t1, true)
            else
              if f x h then (s, false) else remove_until_greater_than f x t1
let rec smart_intersect :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> ('a, unit) ordset
  =
  fun f ->
    fun s1 ->
      fun s2 ->
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
                     (let uu___1 = remove_until_greater_than f h2 t11 in
                      match uu___1 with
                      | (skip1, found) ->
                          let subresult = smart_intersect f skip1 t21 in
                          if found then h2 :: subresult else subresult)
                   else
                     (let uu___2 = remove_until_greater_than f h1 t21 in
                      match uu___2 with
                      | (skip2, found) ->
                          let subresult = smart_intersect f t11 skip2 in
                          if found then h1 :: subresult else subresult))
let intersect :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> ('a, unit) ordset
  = fun f -> fun s1 -> fun s2 -> smart_intersect f s1 s2
let choose :
  'a . 'a cmp -> ('a, unit) ordset -> 'a FStar_Pervasives_Native.option =
  fun f ->
    fun s ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | x::uu___ -> FStar_Pervasives_Native.Some x
let remove : 'a . 'a cmp -> 'a -> ('a, unit) ordset -> ('a, unit) ordset =
  fun f -> fun x -> fun s -> remove' f x s
let size : 'a . 'a cmp -> ('a, unit) ordset -> Prims.nat =
  fun f -> fun s -> size' f s
let subset :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> Prims.bool =
  fun f -> fun s1 -> fun s2 -> subset' f s1 s2
let superset :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> Prims.bool =
  fun f -> fun s1 -> fun s2 -> subset f s2 s1
let singleton : 'a . 'a cmp -> 'a -> ('a, unit) ordset =
  fun f -> fun x -> [x]
let rec smart_minus :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> ('a, unit) ordset
  =
  fun f ->
    fun p ->
      fun q ->
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
                      then
                        let result = smart_minus f pt1 q_after_ph in result
                      else ph :: (smart_minus f pt1 q_after_ph)))
let (ncmp : Prims.nat -> Prims.nat -> Prims.bool) = fun x -> fun y -> x <= y
let minus :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> ('a, unit) ordset
  = fun f -> fun s1 -> fun s2 -> smart_minus f s1 s2
let strict_subset :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> Prims.bool =
  fun f -> fun s1 -> fun s2 -> (s1 <> s2) && (subset f s1 s2)
let strict_superset :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> Prims.bool =
  fun f -> fun s1 -> fun s2 -> strict_subset f s2 s1
let disjoint :
  'a . 'a cmp -> ('a, unit) ordset -> ('a, unit) ordset -> Prims.bool =
  fun f -> fun s1 -> fun s2 -> (intersect f s1 s2) = (empty f)
type ('a, 'f, 's1, 's2) equal = unit
let fold :
  'a 'acc .
    'a cmp -> ('acc -> 'a -> 'acc) -> 'acc -> ('a, unit) ordset -> 'acc
  =
  fun f ->
    fun g -> fun init -> fun s -> FStar_List_Tot_Base.fold_left g init s
let rec map_internal :
  'a 'b .
    'a cmp -> 'b cmp -> ('a -> 'b) -> ('a, unit) ordset -> ('b, unit) ordset
  =
  fun fa ->
    fun fb ->
      fun g ->
        fun sa ->
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
let map :
  'a 'b .
    'a cmp -> 'b cmp -> ('a -> 'b) -> ('a, unit) ordset -> ('b, unit) ordset
  = fun fa -> fun fb -> fun g -> fun sa -> map_internal fa fb g sa
type 'a condition = 'a -> Prims.bool
let inv : 'a . 'a condition -> 'a condition =
  fun c -> fun x -> Prims.op_Negation (c x)
let rec count : 'a . 'a cmp -> ('a, unit) ordset -> 'a condition -> Prims.nat
  =
  fun f ->
    fun s ->
      fun c ->
        match s with
        | [] -> Prims.int_zero
        | h::t -> if c h then Prims.int_one + (count f t c) else count f t c
let rec all : 'a . 'a cmp -> ('a, unit) ordset -> 'a condition -> Prims.bool
  =
  fun f ->
    fun s ->
      fun c -> match s with | [] -> true | h::t -> (c h) && (all f t c)
let rec any : 'a . 'a cmp -> ('a, unit) ordset -> 'a condition -> Prims.bool
  =
  fun f ->
    fun s ->
      fun c -> match s with | [] -> false | h::t -> (c h) || (any f t c)
let rec find_first :
  'a .
    'a cmp ->
      ('a, unit) ordset -> 'a condition -> 'a FStar_Pervasives_Native.option
  =
  fun f ->
    fun s ->
      fun c ->
        match s with
        | [] -> FStar_Pervasives_Native.None
        | h::t ->
            let t1 = t in
            if c h then FStar_Pervasives_Native.Some h else find_first f t1 c
let rec find_last' :
  'a .
    'a cmp ->
      ('a, unit) ordset -> 'a condition -> 'a FStar_Pervasives_Native.option
  =
  fun f ->
    fun s ->
      fun c ->
        if s = (empty f)
        then FStar_Pervasives_Native.None
        else
          (let uu___1 = unsnoc f s in
           match uu___1 with
           | (liat1, last1) ->
               if c last1
               then FStar_Pervasives_Native.Some last1
               else find_last' f liat1 c)
let find_last :
  'a .
    'a cmp ->
      ('a, unit) ordset -> 'a condition -> 'a FStar_Pervasives_Native.option
  = fun f -> fun s -> fun c -> find_last' f s c
let rec where :
  'a . 'a cmp -> ('a, unit) ordset -> 'a condition -> ('a, unit) ordset =
  fun f ->
    fun s ->
      fun c ->
        match s with
        | [] -> []
        | h::[] -> if c h then [h] else []
        | h::t ->
            let t1 = t in if c h then h :: (where f t1 c) else where f t1 c
let rec as_set : 'a . 'a cmp -> ('a, unit) ordset -> 'a FStar_Set.set =
  fun f ->
    fun s ->
      match s with
      | [] -> FStar_Set.empty ()
      | hd::tl -> FStar_Set.union (FStar_Set.singleton hd) (as_set f tl)