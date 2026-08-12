module DM4F

(* This example used to derive a WP-indexed state effect "Dijkstra monad for
   free".  WPs and layered effects are gone, so this file keeps the genuine
   underlying state monad. *)

(* Simulating state effect in DM4F, hopefully doable by a tactic. *)

type repr (a:Type u#ua) (st:Type0) : Type u#ua =
  s0:st -> Pure (a & st)

let return (#a:Type) (#st:Type0) (x:a) : repr a st =
  fun s0 -> (x, s0)

let bind (#a #b:Type) (#st:Type0)
  (c : repr a st)
  (f : a -> repr b st)
: repr b st
= fun s0 ->
    let (y, s1) = c s0 in
    f y s1

let (let!) (#a #b:Type) (#st:Type0) (c : repr a st) (f : a -> repr b st) : repr b st =
  bind c f

let run (#a:Type) (#st:Type0) (c:repr a st) (s0:st) : Pure (a & st) =
  c s0

let get #st () : repr st st =
  fun s0 -> (s0, s0)

let put #st (s:st) : repr unit st =
  fun _ -> ((), s)

let test () : repr int int =
  let! x = get () in
  let! _ = put (x + x) in
  let! y = get () in
  let! z = get () in
  return (y + z)
