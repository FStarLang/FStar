module RW

(* This module used to encode a read-only/read-write lattice as layered effect
   indices.  With effect indices removed, it is now the underlying heap state
   monad plus a reader submonad, written with let! notation. *)

open SimpleHeap

type reader (a:Type) = heap -> Tot a
type repr (a:Type) = heap -> Tot (a & heap)

let return (#a:Type) (x:a) : repr a = fun h -> (x, h)

let bind (#a #b:Type) (m:repr a) (f:a -> repr b) : repr b =
  fun h0 -> let x, h1 = m h0 in f x h1

let (let!) (#a #b:Type) (m:repr a) (f:a -> repr b) : repr b = bind m f

let ask () : reader heap = fun h -> h
let lift_reader #a (r:reader a) : repr a = fun h -> (r h, h)

let get () : repr heap = lift_reader (ask ())
let put (h:heap) : repr unit = fun _ -> ((), h)
let modify (f:heap -> heap) : repr unit = fun h -> ((), f h)

let alloc_ref #a (init:a) : repr (ref a) = fun h -> SimpleHeap.alloc h init

let read_ref_at #a (r:ref a) (h:heap)
  : Ghost a (requires (h `contains` r)) (ensures fun _ -> True) =
  SimpleHeap.sel h r

let write_ref_at #a (r:ref a) (x:a) (h:heap)
  : Ghost heap (requires (h `contains` r)) (ensures fun _ -> True) =
  SimpleHeap.upd h r x

let app #a #b (f:a -> repr b) (x:a) : repr b = f x

let rec map #a #b (f:a -> repr b) (xs:list a) : repr (list b) =
  match xs with
  | [] -> return []
  | x::xs ->
    let! y = f x in
    let! ys = map f xs in
    return (y::ys)

let rec appn #a (n:nat) (f:a -> repr a) (x:a) : repr a =
  match n with
  | 0 -> return x
  | _ -> let! y = f x in appn (n - 1) f y

let labs0 (n:int) : repr int = if n < 0 then return (-n) else return n

let labs (n:int) : repr nat =
  if n < 0 then return (-n) else return n

let rwi_assert (p:prop) : Pure (repr unit) (requires p) (ensures fun _ -> True) =
  return ()

let rwi_assume (p:prop) : repr unit =
  fun h -> assume p; ((), h)

let test_abs0 (n:int) : repr int =
  let! r = labs0 n in
  return r

let test_abs0' (n:int) : repr nat =
  labs n

let test_abs (n:int) : repr nat = labs n

let plus_readers (f g:unit -> reader int) : reader int =
  fun h -> f () h + g () h

let plus_states (f g:unit -> repr int) : repr int =
  let! x = f () in
  let! y = g () in
  return (x + y)

let state_preserved_by_reader (r:reader int) : repr int =
  fun h -> (r h, h)

let makereader #a (f:repr a) : reader a =
  fun h -> fst (f h)
