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
  __proj__Mksetlike__item__empty projectee
let singleton (s : unit) (projectee : ('e, Obj.t) setlike) : 'e -> Obj.t=
  __proj__Mksetlike__item__singleton projectee
let is_empty (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> Prims.bool= __proj__Mksetlike__item__is_empty projectee
let add (s : unit) (projectee : ('e, Obj.t) setlike) : 'e -> Obj.t -> Obj.t=
  __proj__Mksetlike__item__add projectee
let remove (s : unit) (projectee : ('e, Obj.t) setlike) :
  'e -> Obj.t -> Obj.t= __proj__Mksetlike__item__remove projectee
let mem (s : unit) (projectee : ('e, Obj.t) setlike) :
  'e -> Obj.t -> Prims.bool= __proj__Mksetlike__item__mem projectee
let equal (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> Obj.t -> Prims.bool= __proj__Mksetlike__item__equal projectee
let subset (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> Obj.t -> Prims.bool= __proj__Mksetlike__item__subset projectee
let union (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> Obj.t -> Obj.t= __proj__Mksetlike__item__union projectee
let inter (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> Obj.t -> Obj.t= __proj__Mksetlike__item__inter projectee
let diff (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> Obj.t -> Obj.t= __proj__Mksetlike__item__diff projectee
let for_all (s : unit) (projectee : ('e, Obj.t) setlike) :
  ('e -> Prims.bool) -> Obj.t -> Prims.bool=
  __proj__Mksetlike__item__for_all projectee
let for_any (s : unit) (projectee : ('e, Obj.t) setlike) :
  ('e -> Prims.bool) -> Obj.t -> Prims.bool=
  __proj__Mksetlike__item__for_any projectee
let elems (s : unit) (projectee : ('e, Obj.t) setlike) :
  Obj.t -> 'e Prims.list= __proj__Mksetlike__item__elems projectee
let filter (s : unit) (projectee : ('e, Obj.t) setlike) :
  ('e -> Prims.bool) -> Obj.t -> Obj.t=
  __proj__Mksetlike__item__filter projectee
let collect (s : unit) (projectee : ('e, Obj.t) setlike) :
  ('e -> Obj.t) -> 'e Prims.list -> Obj.t=
  __proj__Mksetlike__item__collect projectee
let from_list (s : unit) (projectee : ('e, Obj.t) setlike) :
  'e Prims.list -> Obj.t= __proj__Mksetlike__item__from_list projectee
let addn (s : unit) (projectee : ('e, Obj.t) setlike) :
  'e Prims.list -> Obj.t -> Obj.t= __proj__Mksetlike__item__addn projectee
let symdiff (uu___2 : ('e, 's) setlike) (uu___1 : 's) (uu___ : 's) : 
  's=
  (fun uu___ s1 s2 ->
     Obj.magic (diff () (Obj.magic uu___) (Obj.magic s1) (Obj.magic s2)))
    uu___2 uu___1 uu___
