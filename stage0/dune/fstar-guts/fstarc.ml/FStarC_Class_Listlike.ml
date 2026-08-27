open Prims
type ('e, 's) view_t =
  | VNil 
  | VCons of 'e * 's 
let uu___is_VNil (projectee : ('e, 's) view_t) : Prims.bool=
  match projectee with | VNil -> true | uu___ -> false
let uu___is_VCons (projectee : ('e, 's) view_t) : Prims.bool=
  match projectee with | VCons (_0, _1) -> true | uu___ -> false
let __proj__VCons__item___0 (projectee : ('e, 's) view_t) : 'e=
  match projectee with | VCons (_0, _1) -> _0
let __proj__VCons__item___1 (projectee : ('e, 's) view_t) : 's=
  match projectee with | VCons (_0, _1) -> _1
type ('e, 's) listlike =
  {
  empty: 's ;
  cons: 'e -> 's -> 's ;
  view: 's -> ('e, 's) view_t }
let __proj__Mklistlike__item__empty (projectee : ('e, 's) listlike) : 
  's= match projectee with | { empty; cons; view;_} -> empty
let __proj__Mklistlike__item__cons (projectee : ('e, 's) listlike) :
  'e -> 's -> 's= match projectee with | { empty; cons; view;_} -> cons
let __proj__Mklistlike__item__view (projectee : ('e, 's) listlike) :
  's -> ('e, 's) view_t=
  match projectee with | { empty; cons; view;_} -> view
let empty (projectee : ('e, 's) listlike) : 's=
  match projectee with | { empty = empty1; cons; view;_} -> empty1
let cons (projectee : ('e, 's) listlike) : 'e -> 's -> 's=
  match projectee with | { empty = empty1; cons = cons1; view;_} -> cons1
let view (projectee : ('e, 's) listlike) : 's -> ('e, 's) view_t=
  match projectee with
  | { empty = empty1; cons = cons1; view = view1;_} -> view1
let is_empty (uu___ : ('e, 's) listlike) (l : 's) : Prims.bool=
  match view uu___ l with | VNil -> true | VCons (uu___1, uu___2) -> false
let singleton (uu___ : ('e, 's) listlike) (x : 'e) : 's=
  cons uu___ x (empty uu___)
let rec to_list : 'e 's . ('e, 's) listlike -> 's -> 'e Prims.list =
  fun uu___ l ->
    match view uu___ l with
    | VNil -> []
    | VCons (x, xs) -> let uu___1 = to_list uu___ xs in x :: uu___1
let rec from_list : 'e 's . ('e, 's) listlike -> 'e Prims.list -> 's =
  fun uu___ l ->
    match l with
    | [] -> empty uu___
    | x::xs -> let uu___1 = from_list uu___ xs in cons uu___ x uu___1
