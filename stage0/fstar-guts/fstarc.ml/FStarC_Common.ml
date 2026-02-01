open Prims
let snapshot (msg : Prims.string) (push : 'a -> 'b)
  (stackref : 'c Prims.list FStarC_Effect.ref) (arg : 'a) : (Prims.int * 'b)=
  FStarC_Util.atomically
    (fun uu___ ->
       let len =
         let uu___1 = FStarC_Effect.op_Bang stackref in
         FStarC_List.length uu___1 in
       let arg' = push arg in
       (let uu___2 = FStarC_Debug.any () in
        if uu___2
        then
          FStarC_Format.print2 "(%s)snapshot %s\n" msg
            (Prims.string_of_int len)
        else ());
       (len, arg'))
let rollback (msg : Prims.string) (pop : unit -> 'a)
  (stackref : 'c Prims.list FStarC_Effect.ref)
  (depth : Prims.int FStar_Pervasives_Native.option) : 'a=
  (let uu___1 = FStarC_Debug.any () in
   if uu___1
   then
     FStarC_Format.print2 "(%s)rollback %s ... " msg
       (match depth with
        | FStar_Pervasives_Native.None -> "None"
        | FStar_Pervasives_Native.Some len -> Prims.string_of_int len)
   else ());
  (let rec aux n =
     if n <= Prims.int_zero
     then failwith "(rollback) Too many pops"
     else
       if n = Prims.int_one
       then pop ()
       else ((let uu___4 = pop () in ()); aux (n - Prims.int_one)) in
   let curdepth =
     let uu___1 = FStarC_Effect.op_Bang stackref in FStarC_List.length uu___1 in
   let n =
     match depth with
     | FStar_Pervasives_Native.Some d -> curdepth - d
     | FStar_Pervasives_Native.None -> Prims.int_one in
   (let uu___2 = FStarC_Debug.any () in
    if uu___2
    then
      let uu___3 =
        let uu___4 =
          let uu___5 = FStarC_Effect.op_Bang stackref in
          FStarC_List.length uu___5 in
        Prims.string_of_int uu___4 in
      FStarC_Format.print1 " depth is %s\n " uu___3
    else ());
   FStarC_Util.atomically (fun uu___2 -> aux n))
let raise_failed_assertion (msg : Prims.string) : 'uuuuu=
  let uu___ = FStarC_Format.fmt1 "Assertion failed: %s" msg in failwith uu___
let runtime_assert (b : Prims.bool) (msg : Prims.string) : unit=
  if Prims.op_Negation b then raise_failed_assertion msg else ()
let __string_of_list (delim : Prims.string) (f : 'a -> Prims.string)
  (l : 'a Prims.list) : Prims.string=
  match l with
  | [] -> "[]"
  | x::xs ->
      let strb = FStarC_StringBuffer.create (Prims.of_int (80)) in
      ((let uu___1 =
          let uu___2 = f x in
          let uu___3 = FStarC_StringBuffer.add "[" strb in
          FStarC_StringBuffer.add uu___2 uu___3 in
        ());
       FStarC_List.iter
         (fun x1 ->
            let uu___2 =
              let uu___3 = f x1 in
              let uu___4 = FStarC_StringBuffer.add delim strb in
              FStarC_StringBuffer.add uu___3 uu___4 in
            ()) xs;
       (let uu___3 = FStarC_StringBuffer.add "]" strb in ());
       FStarC_StringBuffer.contents strb)
let string_of_list (f : 'a -> Prims.string) (l : 'a Prims.list) :
  Prims.string= __string_of_list ", " f l
let string_of_list' (f : 'a -> Prims.string) (l : 'a Prims.list) :
  Prims.string= __string_of_list "; " f l
let list_of_option (o : 'a FStar_Pervasives_Native.option) : 'a Prims.list=
  match o with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some x -> [x]
let string_of_option (f : 'a -> Prims.string)
  (uu___ : 'a FStar_Pervasives_Native.option) : Prims.string=
  match uu___ with
  | FStar_Pervasives_Native.None -> "None"
  | FStar_Pervasives_Native.Some x ->
      let uu___1 = f x in Prims.strcat "Some " uu___1
let tabulate (n : Prims.int) (f : Prims.int -> 'a) : 'a Prims.list=
  let rec aux i =
    if i < n
    then
      let uu___ = f i in
      let uu___1 = aux (i + Prims.int_one) in uu___ :: uu___1
    else [] in
  aux Prims.int_zero
let rec max_prefix :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> ('a Prims.list * 'a Prims.list)
  =
  fun f xs ->
    match xs with
    | [] -> ([], [])
    | x::xs1 when f x ->
        let uu___ = max_prefix f xs1 in
        (match uu___ with | (l, r) -> ((x :: l), r))
    | x::xs1 -> ([], (x :: xs1))
let max_suffix (f : 'a -> Prims.bool) (xs : 'a Prims.list) :
  ('a Prims.list * 'a Prims.list)=
  let rec aux acc xs1 =
    match xs1 with
    | [] -> (acc, [])
    | x::xs2 when f x -> aux (x :: acc) xs2
    | x::xs2 -> (acc, (x :: xs2)) in
  let uu___ = aux [] (FStarC_List.rev xs) in
  match uu___ with | (xs1, ys) -> ((FStarC_List.rev ys), xs1)
let rec eq_list :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun f l1 l2 ->
    match (l1, l2) with
    | ([], []) -> true
    | ([], uu___) -> false
    | (uu___, []) -> false
    | (x1::t1, x2::t2) -> (f x1 x2) && (eq_list f t1 t2)
let psmap_to_list (m : 'a FStarC_PSMap.t) : (Prims.string * 'a) Prims.list=
  FStarC_PSMap.fold m (fun k v a1 -> (k, v) :: a1) []
let psmap_keys (m : 'a FStarC_PSMap.t) : Prims.string Prims.list=
  FStarC_PSMap.fold m (fun k v a1 -> k :: a1) []
let psmap_values (m : 'a FStarC_PSMap.t) : 'a Prims.list=
  FStarC_PSMap.fold m (fun k v a1 -> v :: a1) []
let option_to_list (uu___ : 'a FStar_Pervasives_Native.option) :
  'a Prims.list=
  match uu___ with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some x -> [x]
