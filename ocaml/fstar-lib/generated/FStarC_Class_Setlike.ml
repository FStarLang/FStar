open Prims
type ('e, 's) setlike =
  {
  empty: unit -> 's ;
  singleton: 'e -> 's ;
  is_empty: 's -> Prims.bool ;
  add: 'e -> 's -> 's ;
  remove: 'e -> 's -> 's ;
  mem: 'e -> 's -> Prims.bool ;
  equal: 's -> 's -> Prims.bool ;
  subset: 's -> 's -> Prims.bool ;
  union: 's -> 's -> 's ;
  inter: 's -> 's -> 's ;
  diff: 's -> 's -> 's ;
  for_all: ('e -> Prims.bool) -> 's -> Prims.bool ;
  for_any: ('e -> Prims.bool) -> 's -> Prims.bool ;
  elems: 's -> 'e Prims.list ;
  filter: ('e -> Prims.bool) -> 's -> 's ;
  collect: ('e -> 's) -> 'e Prims.list -> 's ;
  from_list: 'e Prims.list -> 's ;
  addn: 'e Prims.list -> 's -> 's }
let __proj__Mksetlike__item__empty : 'e 's . ('e, 's) setlike -> unit -> 's =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> empty
let __proj__Mksetlike__item__singleton : 'e 's . ('e, 's) setlike -> 'e -> 's
  =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> singleton
let __proj__Mksetlike__item__is_empty :
  'e 's . ('e, 's) setlike -> 's -> Prims.bool =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> is_empty
let __proj__Mksetlike__item__add : 'e 's . ('e, 's) setlike -> 'e -> 's -> 's
  =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> add
let __proj__Mksetlike__item__remove :
  'e 's . ('e, 's) setlike -> 'e -> 's -> 's =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> remove
let __proj__Mksetlike__item__mem :
  'e 's . ('e, 's) setlike -> 'e -> 's -> Prims.bool =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> mem
let __proj__Mksetlike__item__equal :
  'e 's . ('e, 's) setlike -> 's -> 's -> Prims.bool =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> equal
let __proj__Mksetlike__item__subset :
  'e 's . ('e, 's) setlike -> 's -> 's -> Prims.bool =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> subset
let __proj__Mksetlike__item__union :
  'e 's . ('e, 's) setlike -> 's -> 's -> 's =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> union
let __proj__Mksetlike__item__inter :
  'e 's . ('e, 's) setlike -> 's -> 's -> 's =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> inter
let __proj__Mksetlike__item__diff :
  'e 's . ('e, 's) setlike -> 's -> 's -> 's =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> diff
let __proj__Mksetlike__item__for_all :
  'e 's . ('e, 's) setlike -> ('e -> Prims.bool) -> 's -> Prims.bool =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> for_all
let __proj__Mksetlike__item__for_any :
  'e 's . ('e, 's) setlike -> ('e -> Prims.bool) -> 's -> Prims.bool =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> for_any
let __proj__Mksetlike__item__elems :
  'e 's . ('e, 's) setlike -> 's -> 'e Prims.list =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> elems
let __proj__Mksetlike__item__filter :
  'e 's . ('e, 's) setlike -> ('e -> Prims.bool) -> 's -> 's =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> filter
let __proj__Mksetlike__item__collect :
  'e 's . ('e, 's) setlike -> ('e -> 's) -> 'e Prims.list -> 's =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> collect
let __proj__Mksetlike__item__from_list :
  'e 's . ('e, 's) setlike -> 'e Prims.list -> 's =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> from_list
let __proj__Mksetlike__item__addn :
  'e 's . ('e, 's) setlike -> 'e Prims.list -> 's -> 's =
  fun projectee ->
    match projectee with
    | { empty; singleton; is_empty; add; remove; mem; equal; subset; 
        union; inter; diff; for_all; for_any; elems; filter; collect;
        from_list; addn;_} -> addn
let empty : 'e . unit -> ('e, Obj.t) setlike -> unit -> Obj.t =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton; is_empty; add; remove; mem; equal;
          subset; union; inter; diff; for_all; for_any; elems; filter;
          collect; from_list; addn;_} -> empty1
let singleton : 'e . unit -> ('e, Obj.t) setlike -> 'e -> Obj.t =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty; add; remove; 
          mem; equal; subset; union; inter; diff; for_all; for_any; elems;
          filter; collect; from_list; addn;_} -> singleton1
let is_empty : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Prims.bool =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1; 
          add; remove; mem; equal; subset; union; inter; diff; for_all;
          for_any; elems; filter; collect; from_list; addn;_} -> is_empty1
let add : 'e . unit -> ('e, Obj.t) setlike -> 'e -> Obj.t -> Obj.t =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove; mem; equal; subset; union; inter; diff;
          for_all; for_any; elems; filter; collect; from_list; addn;_} ->
          add1
let remove : 'e . unit -> ('e, Obj.t) setlike -> 'e -> Obj.t -> Obj.t =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem; equal; subset; union; inter;
          diff; for_all; for_any; elems; filter; collect; from_list; 
          addn;_} -> remove1
let mem : 'e . unit -> ('e, Obj.t) setlike -> 'e -> Obj.t -> Prims.bool =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal; subset; union;
          inter; diff; for_all; for_any; elems; filter; collect; from_list;
          addn;_} -> mem1
let equal : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Prims.bool
  =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal = equal1; subset;
          union; inter; diff; for_all; for_any; elems; filter; collect;
          from_list; addn;_} -> equal1
let subset : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Prims.bool
  =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal = equal1;
          subset = subset1; union; inter; diff; for_all; for_any; elems;
          filter; collect; from_list; addn;_} -> subset1
let union : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Obj.t =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal = equal1;
          subset = subset1; union = union1; inter; diff; for_all; for_any;
          elems; filter; collect; from_list; addn;_} -> union1
let inter : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Obj.t =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal = equal1;
          subset = subset1; union = union1; inter = inter1; diff; for_all;
          for_any; elems; filter; collect; from_list; addn;_} -> inter1
let diff : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Obj.t =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal = equal1;
          subset = subset1; union = union1; inter = inter1; diff = diff1;
          for_all; for_any; elems; filter; collect; from_list; addn;_} ->
          diff1
let for_all :
  'e .
    unit -> ('e, Obj.t) setlike -> ('e -> Prims.bool) -> Obj.t -> Prims.bool
  =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal = equal1;
          subset = subset1; union = union1; inter = inter1; diff = diff1;
          for_all = for_all1; for_any; elems; filter; collect; from_list;
          addn;_} -> for_all1
let for_any :
  'e .
    unit -> ('e, Obj.t) setlike -> ('e -> Prims.bool) -> Obj.t -> Prims.bool
  =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal = equal1;
          subset = subset1; union = union1; inter = inter1; diff = diff1;
          for_all = for_all1; for_any = for_any1; elems; filter; collect;
          from_list; addn;_} -> for_any1
let elems : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> 'e Prims.list =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal = equal1;
          subset = subset1; union = union1; inter = inter1; diff = diff1;
          for_all = for_all1; for_any = for_any1; elems = elems1; filter;
          collect; from_list; addn;_} -> elems1
let filter :
  'e . unit -> ('e, Obj.t) setlike -> ('e -> Prims.bool) -> Obj.t -> Obj.t =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal = equal1;
          subset = subset1; union = union1; inter = inter1; diff = diff1;
          for_all = for_all1; for_any = for_any1; elems = elems1;
          filter = filter1; collect; from_list; addn;_} -> filter1
let collect :
  'e . unit -> ('e, Obj.t) setlike -> ('e -> Obj.t) -> 'e Prims.list -> Obj.t
  =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal = equal1;
          subset = subset1; union = union1; inter = inter1; diff = diff1;
          for_all = for_all1; for_any = for_any1; elems = elems1;
          filter = filter1; collect = collect1; from_list; addn;_} ->
          collect1
let from_list : 'e . unit -> ('e, Obj.t) setlike -> 'e Prims.list -> Obj.t =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal = equal1;
          subset = subset1; union = union1; inter = inter1; diff = diff1;
          for_all = for_all1; for_any = for_any1; elems = elems1;
          filter = filter1; collect = collect1; from_list = from_list1;
          addn;_} -> from_list1
let addn :
  'e . unit -> ('e, Obj.t) setlike -> 'e Prims.list -> Obj.t -> Obj.t =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
          add = add1; remove = remove1; mem = mem1; equal = equal1;
          subset = subset1; union = union1; inter = inter1; diff = diff1;
          for_all = for_all1; for_any = for_any1; elems = elems1;
          filter = filter1; collect = collect1; from_list = from_list1;
          addn = addn1;_} -> addn1
let symdiff : 'e 's . ('e, 's) setlike -> 's -> 's -> 's =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun uu___ ->
           fun s1 ->
             fun s2 ->
               Obj.magic
                 (diff () (Obj.magic uu___) (Obj.magic s1) (Obj.magic s2)))
          uu___2 uu___1 uu___