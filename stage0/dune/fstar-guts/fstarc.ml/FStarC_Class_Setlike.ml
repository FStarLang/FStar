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
let __proj__Mksetlike__item__empty (projectee : ('e, 's) setlike) :
  unit -> 's=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> empty
let __proj__Mksetlike__item__singleton (projectee : ('e, 's) setlike) :
  'e -> 's=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> singleton
let __proj__Mksetlike__item__is_empty (projectee : ('e, 's) setlike) :
  's -> Prims.bool=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> is_empty
let __proj__Mksetlike__item__add (projectee : ('e, 's) setlike) :
  'e -> 's -> 's=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> add
let __proj__Mksetlike__item__remove (projectee : ('e, 's) setlike) :
  'e -> 's -> 's=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> remove
let __proj__Mksetlike__item__mem (projectee : ('e, 's) setlike) :
  'e -> 's -> Prims.bool=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> mem
let __proj__Mksetlike__item__equal (projectee : ('e, 's) setlike) :
  's -> 's -> Prims.bool=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> equal
let __proj__Mksetlike__item__subset (projectee : ('e, 's) setlike) :
  's -> 's -> Prims.bool=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> subset
let __proj__Mksetlike__item__union (projectee : ('e, 's) setlike) :
  's -> 's -> 's=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> union
let __proj__Mksetlike__item__inter (projectee : ('e, 's) setlike) :
  's -> 's -> 's=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> inter
let __proj__Mksetlike__item__diff (projectee : ('e, 's) setlike) :
  's -> 's -> 's=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> diff
let __proj__Mksetlike__item__for_all (projectee : ('e, 's) setlike) :
  ('e -> Prims.bool) -> 's -> Prims.bool=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> for_all
let __proj__Mksetlike__item__for_any (projectee : ('e, 's) setlike) :
  ('e -> Prims.bool) -> 's -> Prims.bool=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> for_any
let __proj__Mksetlike__item__elems (projectee : ('e, 's) setlike) :
  's -> 'e Prims.list=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> elems
let __proj__Mksetlike__item__filter (projectee : ('e, 's) setlike) :
  ('e -> Prims.bool) -> 's -> 's=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> filter
let __proj__Mksetlike__item__collect (projectee : ('e, 's) setlike) :
  ('e -> 's) -> 'e Prims.list -> 's=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> collect
let __proj__Mksetlike__item__from_list (projectee : ('e, 's) setlike) :
  'e Prims.list -> 's=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> from_list
let __proj__Mksetlike__item__addn (projectee : ('e, 's) setlike) :
  'e Prims.list -> 's -> 's=
  match projectee with
  | { empty; singleton; is_empty; add; remove; mem; equal; subset; union;
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> addn
let empty (s : unit) (projectee : ('e, Obj.t) setlike) : unit -> Obj.t=
  match projectee with
  | { empty = empty1; singleton; is_empty; add; remove; mem; equal; subset;
      union; inter; diff; for_all; for_any; elems; filter; collect;
      from_list; addn;_} -> empty1
let singleton (s : unit) (projectee : ('e, Obj.t) setlike) : 'e -> Obj.t=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty; add; remove; 
      mem; equal; subset; union; inter; diff; for_all; for_any; elems;
      filter; collect; from_list; addn;_} -> singleton1
let is_empty (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> Prims.bool=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1; add;
      remove; mem; equal; subset; union; inter; diff; for_all; for_any;
      elems; filter; collect; from_list; addn;_} -> is_empty1
let add (s : unit) (projectee : ('e, Obj.t) setlike) : 'e -> Obj.t -> Obj.t=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove; mem; equal; subset; union; inter; diff; for_all;
      for_any; elems; filter; collect; from_list; addn;_} -> add1
let remove (s : unit) (projectee : ('e, Obj.t) setlike) :
  'e -> Obj.t -> Obj.t=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem; equal; subset; union; inter; 
      diff; for_all; for_any; elems; filter; collect; from_list; addn;_} ->
      remove1
let mem (s : unit) (projectee : ('e, Obj.t) setlike) :
  'e -> Obj.t -> Prims.bool=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal; subset; union; 
      inter; diff; for_all; for_any; elems; filter; collect; from_list;
      addn;_} -> mem1
let equal (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> Obj.t -> Prims.bool=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal = equal1; subset;
      union; inter; diff; for_all; for_any; elems; filter; collect;
      from_list; addn;_} -> equal1
let subset (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> Obj.t -> Prims.bool=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal = equal1;
      subset = subset1; union; inter; diff; for_all; for_any; elems; 
      filter; collect; from_list; addn;_} -> subset1
let union (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> Obj.t -> Obj.t=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal = equal1;
      subset = subset1; union = union1; inter; diff; for_all; for_any; 
      elems; filter; collect; from_list; addn;_} -> union1
let inter (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> Obj.t -> Obj.t=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal = equal1;
      subset = subset1; union = union1; inter = inter1; diff; for_all;
      for_any; elems; filter; collect; from_list; addn;_} -> inter1
let diff (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> Obj.t -> Obj.t=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal = equal1;
      subset = subset1; union = union1; inter = inter1; diff = diff1;
      for_all; for_any; elems; filter; collect; from_list; addn;_} -> diff1
let for_all (s : unit) (projectee : ('e, Obj.t) setlike) :
  ('e -> Prims.bool) -> Obj.t -> Prims.bool=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal = equal1;
      subset = subset1; union = union1; inter = inter1; diff = diff1;
      for_all = for_all1; for_any; elems; filter; collect; from_list; 
      addn;_} -> for_all1
let for_any (s : unit) (projectee : ('e, Obj.t) setlike) :
  ('e -> Prims.bool) -> Obj.t -> Prims.bool=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal = equal1;
      subset = subset1; union = union1; inter = inter1; diff = diff1;
      for_all = for_all1; for_any = for_any1; elems; filter; collect;
      from_list; addn;_} -> for_any1
let elems (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> 'e Prims.list=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal = equal1;
      subset = subset1; union = union1; inter = inter1; diff = diff1;
      for_all = for_all1; for_any = for_any1; elems = elems1; filter;
      collect; from_list; addn;_} -> elems1
let filter (s : unit) (projectee : ('e, Obj.t) setlike) :
  ('e -> Prims.bool) -> Obj.t -> Obj.t=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal = equal1;
      subset = subset1; union = union1; inter = inter1; diff = diff1;
      for_all = for_all1; for_any = for_any1; elems = elems1;
      filter = filter1; collect; from_list; addn;_} -> filter1
let collect (s : unit) (projectee : ('e, Obj.t) setlike) :
  ('e -> Obj.t) -> 'e Prims.list -> Obj.t=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal = equal1;
      subset = subset1; union = union1; inter = inter1; diff = diff1;
      for_all = for_all1; for_any = for_any1; elems = elems1;
      filter = filter1; collect = collect1; from_list; addn;_} -> collect1
let from_list (s : unit) (projectee : ('e, Obj.t) setlike) :
  'e Prims.list -> Obj.t=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal = equal1;
      subset = subset1; union = union1; inter = inter1; diff = diff1;
      for_all = for_all1; for_any = for_any1; elems = elems1;
      filter = filter1; collect = collect1; from_list = from_list1; addn;_}
      -> from_list1
let addn (s : unit) (projectee : ('e, Obj.t) setlike) :
  'e Prims.list -> Obj.t -> Obj.t=
  match projectee with
  | { empty = empty1; singleton = singleton1; is_empty = is_empty1;
      add = add1; remove = remove1; mem = mem1; equal = equal1;
      subset = subset1; union = union1; inter = inter1; diff = diff1;
      for_all = for_all1; for_any = for_any1; elems = elems1;
      filter = filter1; collect = collect1; from_list = from_list1;
      addn = addn1;_} -> addn1
let symdiff (uu___2 : ('e, 's) setlike) (uu___1 : 's) (uu___ : 's) : 
  's=
  (fun uu___ s1 s2 ->
     Obj.magic (diff () (Obj.magic uu___) (Obj.magic s1) (Obj.magic s2)))
    uu___2 uu___1 uu___
