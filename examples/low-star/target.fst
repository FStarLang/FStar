(*--build-config
    options:--admit_fsi Set --admit_fsi Seq --verify_module Target;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.SeqProperties.fst
  --*)


module Target

open Seq

(* Pointer type *)
type ptr (a:Type) = | Ptr: v:a -> ptr a

(* Tag type *)
type tag = uint8

(* Null type (suppose several values for "null") *)
type null

(* Pairs *)
(* '_' is not allowed in front of constructors, but allowed in front of types *)
type _pair (a:Type) (b:Type) = | Pair_: fst:a -> snd:b -> _pair a b
type pair (a:Type) (b:Type) = | Pair : ptr:(ptr (_pair a b)) -> pair a b

(* Options *)
type _option1 (a:Type) = 
  | None1_
  | Some1_ : v:a -> _option1 a
type option1 (a:Type) = | Option1: ptr:(ptr (_option1 a)) -> option1 a

type _option2 (a:Type) = 
  | Some2_ : v:a -> _option2 a
type option2 (a:Type) =
  | None2
  | Some2: v:ptr (_option2 a) -> option2 a

type _option3 (a:Type) =
  | Some3_: v:a -> _option3 a
type option3 (a:Type) =
  | None3: t:tag -> (* v:(ptr null) -> ? *) option3 a
  | Some3: t:tag -> v:(ptr (_option3 a)) -> option3 a

(* C directed opton : *)
type _option4 (a:Type) =
  | None4_
  | Some4_: v:a -> _option4 a
type option4 (a:Type) =
  | None4: t:tag -> v:ptr (_option4 a){is_None4_ (Ptr.v v)} -> option4 a
  | Some4: t:tag -> v:(ptr (_option4 a)){is_Some4_ (Ptr.v v)} -> option4 a

(* Because the 2 constructors above are not convenient *)
type Is_None (t:tag) = b2t(t = 0uy)
type Is_Some (t:tag) = b2t(t = 1uy)
type _option5 (a:Type) =
  | None5_
  | Some5_: v:a -> _option5 a
type option5 (a:Type) =
  | Option5: 
     t:tag{Is_Some t \/ Is_None t}  -> 
     v:ptr (_option5 a){(Is_Some t ==> is_Some5_ (Ptr.v v))
			 /\ (Is_None t ==> is_None5_ (Ptr.v v))} -> 
     option5 a

(* Lists *)
(* First option *)
type _list1 (a:Type) =
  | Nil1_
  | Cons1_: hd:a -> tl:list1 a -> _list1 a
and list1 (a:Type) = ptr (_list1 a)

(* Second option : no need to dereference if Nil *)
type _list2 (a:Type) =
  | Cons2_: hd:a -> tl:list2 a -> _list2 a
and list2 (a:Type) =
  | Nil2
  | Cons2: ptr (_list2 a) -> list2 a
     
(* Third option : using tags *)
type _list3 (a:Type) =
  | Cons3_: hd:a -> tl:list3 a -> _list3 a
and list3 (a:Type) =
  | Nil3: t:tag -> (* v:ptr (_list3 a) ? -> *) list3 a // We want to turn that to structs here I think
  | Cons3: t:tag -> v:ptr (_list3 a) -> list3 a
     
(* Forth option : using tags and same format *)
type Is_Nil (t:tag) = b2t(t = 0uy)
type Is_Cons (t:tag) = b2t(t = 1uy)
type _list4 (a:Type) =
  | Nil4_ : _list4 a
  | Cons4_: hd:a -> tl:list44 a -> _list4 a
and list44 (a:Type) =
  | List4: t:tag{Is_Nil t \/ Is_Cons t} -> 
           v:ptr (_list4 a) {(* (Is_Nil t <==> is_Nil4_ (Ptr.v v))
                            /\ (Is_Cons t <==> is_Cons4_ (Ptr.v v))*) True } ->
           list44 a

type list (a:Type) = l:list44 a{ (List4.t l = 0uy ==> is_Nil4_ (Ptr.v (List4.v l)))
				       /\ (List4.t l = 1uy ==> 
					   (is_Cons4_ (Ptr.v (List4.v l)))) }
				       

(* Array with immutable length (check how to works out) *)
type _array (a:Type) = | Array_ : l:nat -> c:ref (s:seq a{Seq.length s = l})  -> _array a
type array (a:Type) = ptr (_array a)

(* Test type, not polymorphic *)
type _t = 
  | A_
  | B_
  | C_: x:int -> _t
  | D_: x:int -> y:char -> _t

(* First option *)
type t1 = ptr _t

(* Second option *)
type t2 =
  | A: t:tag -> ptr _t -> t2
  | B: t:tag -> ptr _t -> t2
  | C: t:tag -> v:ptr _t{is_C_ (Ptr.v v)} -> t2
  | D: t:tag -> v:ptr _t{is_D_ (Ptr.v v)} -> t2

(* Third option *)
type t3 = 
  | T: t:tag{ t = 0uy \/ t = 1uy \/ t = 2uy \/ t = 3uy }
    -> v:(ptr _t){
      (t=0uy ==> is_A_ (Ptr.v v))
      /\ (t=1uy ==> is_B_ (Ptr.v v))
      /\ (t=2uy ==> is_C_ (Ptr.v v))
      /\ (t=3uy ==> is_D_ (Ptr.v v)) }
     -> t3
   

(*** Function experiements ***)
let _fst (Pair_ x y) = x
let fst p = 
  (* Ptr (_fst (Ptr.v p)) *) 
  (* SSA style *)
  let v = Ptr.v p in
  let f = _fst v in
  let res = Ptr f in
  res

val _proj1: #a:Type -> o:_option1 a{ is_Some1_ o} -> Tot a
let _proj1 o = Some1_.v o
val proj1 : #a:Type -> o:option1 a{is_Some1_ (Ptr.v (Option1.ptr o))} -> Tot (ptr a)
let proj1 (Option1 ptr) = 
  let obj = Ptr.v ptr in
  let p = _proj1 obj in
  let res = Ptr p in
  res

val _proj2: #a:Type -> o:_option2 a -> Tot a
let _proj2 o = Some2_.v o
val proj2: #a:Type -> o:option2 a{is_Some2 o} -> Tot (ptr a)
let proj2 (Some2 ptr) =
  let obj = Ptr.v ptr in
  let p = _proj2 obj in
  let res = Ptr p in
  res

val _proj3: #a:Type -> o:_option3 a -> Tot a
let _proj3 o = Some3_.v o
val proj3: #a:Type -> o:option3 a{is_Some3 o} -> Tot (ptr a)
let proj3 (Some3 _ ptr) = 
  let obj = Ptr.v ptr in
  let p = _proj3 obj in
  let res = Ptr p in
  res

val _proj4: #a:Type -> o:_option4 a{is_Some4_ o} -> Tot a
let _proj4 o = Some4_.v o
val proj4: #a:Type -> o:option4 a{is_Some4 o} -> Tot (ptr a)
let proj4 (Some4 _ ptr) =
  let obj = Ptr.v ptr in
  let p = _proj4 obj in
  let res = Ptr p in
  res

val _proj5: #a:Type -> o:_option5 a{is_Some5_ o} -> Tot a
let _proj5 o = Some5_.v o
val proj5: #a:Type -> o:option5 a{Is_Some (Option5.t o)} -> Tot (ptr a)
let proj5 (Option5 _ ptr) =
  let obj = Ptr.v ptr in
  let p = _proj5 obj in
  let res = Ptr p in
  res  

val _proj_int: o:_option5 int{ is_Some5_ o } -> Tot int
let _proj_int o = 
  Some5_.v o
val proj_int: o:option5 int{Option5.t o = 1uy} -> Tot (ptr int)
let proj_int (Option5 _ ptr) =
  let obj = Ptr.v ptr in
  let p  = _proj_int obj in
  let res = Ptr p in
  res
    
let _head l =
  match l with
  | Nil4_ -> None5_
  | Cons4_ hd tl -> Some5_ hd
let head1 l =
  let ptr = List4.v l in (* Assumed free : passed by value *)
  let obj = Ptr.v ptr in (* Unbox *)
  let hd = _head obj in (* Original function call *)
  let tag = match hd with | None5_ -> 0uy | _ -> 1uy in
  let ptr_res = Ptr hd in
  let res = Option5 tag ptr_res in
  res

(* Uses tags to avoid a dereference for Nil, supposing that the tag is passed by value *)
val head2: #a:Type -> list a -> Tot (option5 a)
let head2 l = 
  let t = List4.t l in (* Assumed free *)
  match t with
  | 0uy -> 
     let res = Option5 0uy (Ptr None5_) in (* Void ptr *)
     res   (* No dereference was needed *)
  | 1uy -> 
     let ptr = List4.v l in (* Assumed free *)
     let obj = Ptr.v ptr in     
     let hd = _head obj in (* Be smart and use that we know that is_Some4_ obj here *)
     let ptr_res = Ptr hd in
     let res = Option5 1uy ptr_res in
     res

// val _tail: #a:Type -> _list4 a -> Tot (option5 (list44 a))
let _tail l =
  match l with
  | Nil4_ -> None5_
  | Cons4_ hd tl -> Some5_ tl

(* Not satisfying because I do not know how to refine the mutually inductive type *)
let tail1 l =
  let ptr = List4.v l in
  let obj = Ptr.v ptr in
  let tl = _tail obj in (* Given the list type, this should already be boxed *)
  let tag = match tl with | None5_ -> 0uy | _ -> 1uy in
  let ptr' = Ptr tl in
  let res = Option5 tag ptr' in
  res
  
(*
val tail2: #a:Type -> list a -> Tot (option5 (list a))
let tail2 l =
  let t = List4.t l in
  match t with
  | 0uy -> 
     let res = Option5 0uy (Ptr None5_) in (* No dereference was needed *)
     res
  | 1uy -> 
     let ptr = List4.v l in (* Assumed free *)
     let obj = Ptr.v ptr in
     let tl = _tail obj in (* Given the list type, this should already be boxed *)
     let ptr_res = Ptr tl in
     let res = Option5 1uy ptr_res in
     res
*)    

let _pattern_match t =
  match t with
  | A_ -> "A"
  | B_ -> "B"
  | C_ _ -> "C"
  | D_ _ _ -> "D"

let pattern_match1 t =
  let v = Ptr.v t in
  let res = _pattern_match v in
  res

let pattern_match3 t =
  let tag = T.t t in
  match tag with
  | 0uy -> "A"
  | 1uy -> "B"
  | 2uy -> "C" 
  | 3uy -> "D"
