open Prims
type 'a set = ('a, Prims.bool) FStar_FunctionalExtensionality.restricted_t
let mem (x : 'a) (s : 'a set) : Prims.bool= s x
let rec list_nonrepeating : 'a . 'a Prims.list -> Prims.bool =
  fun xs ->
    match xs with
    | [] -> true
    | hd::tl ->
        (Prims.op_Negation (FStar_List_Tot_Base.mem hd tl)) &&
          (list_nonrepeating tl)
let rec remove_repeats : 'a . 'a Prims.list -> 'a Prims.list =
  fun xs ->
    match xs with
    | [] -> []
    | hd::tl ->
        let tl' = remove_repeats tl in
        if FStar_List_Tot_Base.mem hd tl then tl' else hd :: tl'
let intro_set
  (f : ('a, Prims.bool) FStar_FunctionalExtensionality.restricted_t)
  (xs : unit) : 'a set= f
let emptyset (uu___ : unit) : 'a set= intro_set (fun x -> false) ()
let insert (x : 'a) (s : 'a set) : 'a set=
  intro_set (fun x1 -> (x = x1) || (s x1)) ()
let singleton (x : 'a) : 'a set= insert x (emptyset ())
let rec union_lists : 'a . 'a Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun xs ys -> match xs with | [] -> ys | hd::tl -> hd :: (union_lists tl ys)
let union (s1 : 'a set) (s2 : 'a set) : 'a set=
  intro_set (fun x -> (s1 x) || (s2 x)) ()
let rec intersect_lists :
  'a . 'a Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun xs ys ->
    match xs with
    | [] -> []
    | hd::tl ->
        let zs' = intersect_lists tl ys in
        if FStar_List_Tot_Base.mem hd ys then hd :: zs' else zs'
let intersection (s1 : 'a set) (s2 : 'a set) : 'a set=
  intro_set (fun x -> (s1 x) && (s2 x)) ()
let rec difference_lists :
  'a . 'a Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun xs ys ->
    match xs with
    | [] -> []
    | hd::tl ->
        let zs' = difference_lists tl ys in
        if FStar_List_Tot_Base.mem hd ys then zs' else hd :: zs'
let difference (s1 : 'a set) (s2 : 'a set) : 'a set=
  intro_set (fun x -> (s1 x) && (Prims.op_Negation (s2 x))) ()
let remove (x : 'a) (s : 'a set) : 'a set= difference s (singleton x)
let notin (x : 'a) (s : 'a set) : Prims.bool= Prims.op_Negation (mem x s)
let rec remove_from_nonrepeating_list :
  'a . 'a -> 'a Prims.list -> 'a Prims.list =
  fun x xs ->
    match xs with
    | hd::tl ->
        if x = hd then tl else hd :: (remove_from_nonrepeating_list x tl)
