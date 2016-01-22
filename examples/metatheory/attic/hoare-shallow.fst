(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/FStar.FunctionalExtensionality.fst $LIB/FStar.Set.fsi $LIB/FStar.Heap.fst $LIB/FStar.ST.fst
  --*)
module While
open Heap
open ST

kind Asrt = heap -> Type

effect com (a:Type) (p:Asrt) (q:Asrt) = St a (fun h' -> p h')
                                             (fun _ _ h -> q h)

type com' (p:Asrt) (q:Asrt) = unit -> com unit p q

val skip : p:Asrt -> com unit p p
let skip (p:Asrt) = ()

type exp (a:Type) (p:Asrt) (q:(a -> Asrt)) =
       unit -> St a (fun h0 -> p h0) (fun h0 x h1 -> h0=h1 /\ q x h1)

(* Using equality constraints for better type inference *)
val _while: p:Asrt -> q:(bool -> Asrt)
        -> =guard:exp bool p q
        -> =body:(unit -> com unit (fun h -> p h /\ q true h) p)
        -> com unit p (fun h -> p h /\ q false h)
let rec _while guard body =
  if guard () then (body (); _while guard body)


val _while2: p:Asrt -> q:(bool -> Asrt)
        -> =guard:exp bool p q
        -> =body:(unit -> com unit (fun h -> p h /\ q true h) p)
        -> com unit p (fun h -> p h /\ q false h)
let rec _while2 guard body =
  if guard () then (body (); _while guard body)

val cond: p:Asrt -> q:(bool -> Asrt) -> r:Asrt -> s:Asrt
      -> =guard:exp bool p q
      -> =_then:(unit -> com unit (fun h -> q true h) r)
      -> =_else:(unit -> com unit (fun h -> q false h) s)
      -> com unit p (fun h -> r h \/ s h)
(* Loss in precision here, since com does not include 2-state post-conditions *)
let cond guard _then _else =
  if guard()
  then _then()
  else _else()


(* Another way to recover precision is to go WP style *)
val condWP: p:Asrt -> q:(bool -> Asrt)
        -> pre1:Asrt -> pre2:Asrt -> post:Asrt
        -> =guard:exp bool p q
        -> =_then:(unit -> com unit pre1 post)
        -> =_else:(unit -> com unit pre2 post)
        -> com unit (fun h -> p h
                            /\ (q true h ==> pre1 h)
                            /\ (q false h ==> pre2 h))
                    post
let condWP guard _then _else =
    if guard()
    then _then()
    else _else()

val write': a:Type -> p:Asrt -> r:ref a -> v:a
          -> com unit (fun h -> p (upd h r v))
                      p
let write' r v = r := v

val read': a:Type -> p:(a -> Asrt) -> r:ref a -> Tot (exp a (fun h -> p (sel h r) h) p)
let read' r () = !r

(* Yet another way is to break out of com and drop into F*'s St *)
val cond2: p:Asrt -> q:(bool -> Asrt) -> r:Asrt -> s:Asrt
      -> =guard:exp bool p q
      -> =_then:(unit -> com unit (fun h -> q true h) r)
      -> =_else:(unit -> com unit (fun h -> q false h) s)
      -> St unit p (fun h0 _ h1 ->
                      (q true h0 /\ r h1)
                   \/ (q false h0 /\ s h1))
let cond2 guard _then _else =
  if guard()
  then _then()
  else _else()

(* CH: For the record:
      In Hoare logic this is actually even less precise (r = s);
       one has to use explicit weakening *)
val cond3: p:Asrt -> q:(bool -> Asrt) -> r:Asrt
      -> =guard:exp bool p q
      -> =_then:(unit -> com unit (fun h -> q true h) r)
      -> =_else:(unit -> com unit (fun h -> q false h) r)
      -> com unit p (fun h -> r h)
let cond3 guard _then _else =
  if guard()
  then _then()
  else _else()


(* A sample program written against this API *)
logic type pre (r1:ref int) (r2:ref int) (h:heap) =
          (contains h r1
           /\ contains h r2
           /\ sel h r1 <= sel h r2)

logic type post  (r1:ref int) (r2:ref int) (b:bool) (h:heap) =
          (b = (sel h r1 <> sel h r2))

(* equalize r1 r2:
   requires the contents of r1 to be less than or equal to r2
            Repeatedly increments r1
   ensures the contents of r1 is equal to to r2
 *)
val equalize: r1:ref int -> r2:ref int
              -> com unit (requires (pre r1 r2))
                          (ensures (fun h -> sel h r1 = sel h r2))
let equalize r1 r2 =
  let test : exp bool (pre r1 r2) (post r1 r2) =
    (* At the moment, you need to decorate these functions with their
       types; type inference is not yet smart enough to do it for you
       ... it's relatively easy to do ... on my list *)
    fun () -> read r1 <> read r2 in

  let body : unit -> com unit (fun h -> pre r1 r2 h /\ post r1 r2 true h)
                              (pre r1 r2) =
    fun () -> write r1 (read r1 + 1) in

  _while test body

(* Exercise:

     Relax the pre-condition that r1 is less than or equal to r2
     so that it works with any pair of refs.
*)
