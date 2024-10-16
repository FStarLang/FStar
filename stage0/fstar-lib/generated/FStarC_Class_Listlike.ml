open Prims
type ('e, 's) view_t =
  | VNil 
  | VCons of 'e * 's 
let uu___is_VNil : 'e 's . ('e, 's) view_t -> Prims.bool =
  fun projectee -> match projectee with | VNil -> true | uu___ -> false
let uu___is_VCons : 'e 's . ('e, 's) view_t -> Prims.bool =
  fun projectee ->
    match projectee with | VCons (_0, _1) -> true | uu___ -> false
let __proj__VCons__item___0 : 'e 's . ('e, 's) view_t -> 'e =
  fun projectee -> match projectee with | VCons (_0, _1) -> _0
let __proj__VCons__item___1 : 'e 's . ('e, 's) view_t -> 's =
  fun projectee -> match projectee with | VCons (_0, _1) -> _1
type ('e, 's) listlike =
  {
  empty: 's ;
  cons: 'e -> 's -> 's ;
  view: 's -> ('e, 's) view_t }
let __proj__Mklistlike__item__empty : 'e 's . ('e, 's) listlike -> 's =
  fun projectee -> match projectee with | { empty; cons; view;_} -> empty
let __proj__Mklistlike__item__cons :
  'e 's . ('e, 's) listlike -> 'e -> 's -> 's =
  fun projectee -> match projectee with | { empty; cons; view;_} -> cons
let __proj__Mklistlike__item__view :
  'e 's . ('e, 's) listlike -> 's -> ('e, 's) view_t =
  fun projectee -> match projectee with | { empty; cons; view;_} -> view
let empty : 'e . unit -> ('e, Obj.t) listlike -> Obj.t =
  fun s ->
    fun projectee ->
      match projectee with | { empty = empty1; cons; view;_} -> empty1
let cons : 'e . unit -> ('e, Obj.t) listlike -> 'e -> Obj.t -> Obj.t =
  fun s ->
    fun projectee ->
      match projectee with | { empty = empty1; cons = cons1; view;_} -> cons1
let view : 'e . unit -> ('e, Obj.t) listlike -> Obj.t -> ('e, Obj.t) view_t =
  fun s ->
    fun projectee ->
      match projectee with
      | { empty = empty1; cons = cons1; view = view1;_} -> view1
let is_empty : 'e 's . ('e, 's) listlike -> 's -> Prims.bool =
  fun uu___ ->
    fun l ->
      let uu___1 = Obj.magic (view () (Obj.magic uu___) (Obj.magic l)) in
      match uu___1 with | VNil -> true | VCons (uu___2, uu___3) -> false
let singleton : 'e 's . ('e, 's) listlike -> 'e -> 's =
  fun uu___1 ->
    fun uu___ ->
      (fun uu___ ->
         fun x ->
           Obj.magic
             (cons () (Obj.magic uu___) x (empty () (Obj.magic uu___))))
        uu___1 uu___
let rec to_list : 'e 's . ('e, 's) listlike -> 's -> 'e Prims.list =
  fun uu___ ->
    fun l ->
      let uu___1 = Obj.magic (view () (Obj.magic uu___) (Obj.magic l)) in
      match uu___1 with
      | VNil -> []
      | VCons (x, xs) -> let uu___2 = to_list uu___ xs in x :: uu___2
let rec from_list : 'e 's . ('e, 's) listlike -> 'e Prims.list -> 's =
  fun uu___1 ->
    fun uu___ ->
      (fun uu___ ->
         fun l ->
           match l with
           | [] -> Obj.magic (empty () (Obj.magic uu___))
           | x::xs ->
               let uu___1 = from_list uu___ xs in
               Obj.magic (cons () (Obj.magic uu___) x (Obj.magic uu___1)))
        uu___1 uu___