(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.IO.fsti FStar.List.fst FStar.List.Tot.fst FStar.Relational.fst ordset.fsi ../../prins.fsi ../ffi.fst ../wysteria.fsi
 --*)

(* PSI *)

module SMC

open FStar.List.Tot
open Prins
open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

type pre_with (m:mode) (t:Type) = fun m0 -> m0 = m /\ t

let to_s2 p1 p2 = union (singleton p1) (singleton p2)

val read_fn: p:prin -> unit -> Wys (list int) (fun m0 -> b2t (m0 = Mode Par (singleton p)))
                                          (fun m0 r t -> True)
let read_fn _ _ = w_read_int_list ()

val nth: n:nat -> l:list int{n < length l} -> Tot int
let rec nth n l = if n = 0 then hd_of_cons l else nth (n - 1) (tl_of_cons l)

val mem_begin: x:int -> n:nat -> l:list int{n <= length l} -> GTot bool (decreases (length l - n))
let rec mem_begin x n l =
  if n = length l then false
  else
    let y = nth n l in
    if x = y then true else mem_begin x (n + 1) l

#set-options "--z3timeout 15"

val mem: x:Box int alice_s -> l:Box (list int) bob_s
         -> len:nat{len = length (v_of_box l)}
         -> n:nat{n <= len}
	 -> Wys (bool * int) (pre (Mode Par ab))
	       (fun _ r _ -> (fst r <==> mem_begin (v_of_box x) n (v_of_box l)) /\
	                  (fst r ==> snd r = v_of_box x))
	   (decreases (len - n))
let rec mem x l len n =
  if n = len then mk_tuple false 0
  else
    let g:unit -> Wys int (pre (Mode Par bob_s))
                       (fun _ r _ -> b2t (r = nth n (v_of_box l))) =
      fun _ -> nth n (unbox_p l)
    in
    let y = as_par bob_s g in
    let _ = cut (b2t (v_of_box y = nth n (v_of_box l))) in
    let cmp:unit
            -> Wys bool (pre (Mode Sec ab))
	          (fun _ r _ -> (r <==> v_of_box x = v_of_box y)) =
      fun _ -> unbox_s x = unbox_s y
    in
    let p = as_sec ab cmp in
    if p then
      let get:unit -> Wys int (pre (Mode Sec ab)) (fun _ r _ -> b2t (r = v_of_box x)) =
	fun _ -> unbox_s x
      in
      let v = as_sec ab get in
      mk_tuple true v
    else mem x l len (n + 1)

#reset-options

val lmem: int -> list int -> GTot bool
let lmem x l = FStar.List.Tot.mem x l

val psi_h: l1:Box (list int) alice_s -> l2:Box (list int) bob_s
	   -> len1:nat{len1 = length (v_of_box l1)} -> len2:nat{len2 = length (v_of_box l2)}
           -> n1:nat{n1 <= len1}
	   -> Wys (list int) (pre (Mode Par ab)) (fun _ r _ -> forall x. lmem x r <==> (mem_begin x 0 (v_of_box l2) /\
	                                                                   mem_begin x n1 (v_of_box l1)))
	     (decreases (len1 - n1))
let rec psi_h l1 l2 len1 len2 n1 =
  let _ = admitP (forall (x:int) (n:nat) (l:list int). (n + 1 <= length l) ==> mem_begin x (n + 1) l ==> mem_begin x n l) in
  if n1 = len1 then (mk_nil ())
  else
    let g:unit -> Wys int (pre (Mode Par alice_s)) (fun _ r _ -> b2t (r = nth n1 (v_of_box l1))) =
      fun _ -> nth n1 (unbox_p l1)
    in
    let x = as_par alice_s g in
    let p = mem x l2 len2 0 in
    let l = psi_h l1 l2 len1 len2 (n1 + 1) in
    if fst p then mk_cons (snd p) l
    else l

val psi_m: l1:Box (list int) alice_s -> l2:Box (list int) bob_s
           -> Wys (list int) (pre (Mode Par ab)) post
let psi_m l1 l2 =
  let len: p:prin -> l:(Box (list int) (singleton p))
           -> unit
	   -> Wys nat (pre (Mode Par (singleton p))) (fun _ r _ -> True /\ r = length (v_of_box l)) =
    fun _ l _ ->
    let l = unbox_p l in
    length l
  in
  let n1 = as_par alice_s (len alice l1) in
  let n2 = as_par bob_s (len bob l2) in

  let g: p:prin{p = alice \/ p = bob} -> n:Box int (singleton p)
         -> unit
	 -> Wys int (pre (Mode Sec ab)) (fun _ r _ -> True /\ r = v_of_box n) =
    fun p n _ -> unbox_s n
  in

  let n1' = as_sec ab (g alice n1) in
  let n2' = as_sec ab (g bob n2) in

  let l = psi_h l1 l2 n1' n2' 0 in
  let _ = assert (forall x. lmem x l <==> (mem_begin x 0 (v_of_box l2) /\
	                            mem_begin x 0 (v_of_box l1))) in
  l

val psi: ps:prins{ps = ab} -> w:Wire (list int) ps -> Wys (Wire (list int) ab) (pre (Mode Par ab)) post
let psi ps w =
  let proj: p:prin{FStar.OrdSet.mem p ab} -> unit -> Wys (list int) (pre (Mode Par (singleton p))) post =
    fun p _ -> projwire_p p w
  in
  let l1 = as_par alice_s (proj alice) in
  let l2 = as_par bob_s (proj bob) in
  let l = psi_m l1 l2 in

  let trivial: unit -> Wys (list int) (pre (Mode Par ab)) post =
    fun _ -> l
  in
  mkwire_p ab (as_par ab trivial)

val regmem: int -> list int -> Tot bool
let rec regmem x l =
  if is_Nil l then false
  else
    if hd_of_cons l = x then true
    else regmem x (tl_of_cons l)

val intersect: l1:list int -> l2:list int -> Tot (list int)
let rec intersect l1 l2 = 
  if is_Nil l1 then mk_nil ()
  else
    if regmem (hd_of_cons l1) l2 then mk_cons (hd_of_cons l1) (intersect (tl_of_cons l1) l2)
    else intersect (tl_of_cons l1) l2

val psi_reg: ps:prins{ps = ab} -> w:Wire (list int) ps -> Wys (Wire (list int) ab) (pre (Mode Par ab)) post
let psi_reg ps w =
  let g:unit -> Wys (Wire (list int) ab) (pre (Mode Sec ab)) post =
    fun _ ->
    let l1 = projwire_s alice w in
    let l2 = projwire_s bob w in
    mkwire_s ab (intersect l1 l2)
  in
  as_sec ab g
