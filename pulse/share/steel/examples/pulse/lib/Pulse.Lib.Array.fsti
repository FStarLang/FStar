module Pulse.Lib.Array
open Pulse.Lib.Core
include Pulse.Lib.Array.Core
open Steel.FractionalPermission
open FStar.Ghost
include Pulse.Lib.Array.Core
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8

let elseq (a:Type) (l:SZ.t) = s:Seq.seq a{ Seq.length s == SZ.v l }

let larray t (n:nat) = a:array t { length a == n }

val compare
        (#t:eqtype)
        (l:SZ.t)
        (a1 a2:larray t (SZ.v l))
        (#p1 #p2:perm)
        (#s1 #s2:Ghost.erased (elseq t l))
  : stt bool
        (requires 
            pts_to a1 #p1 s1 **
            pts_to a2 #p2 s2)
        (ensures fun res ->
            pts_to a1 #p1 s1 **
            pts_to a2 #p2 s2 **
            pure (res <==> Seq.equal s1 s2))

val memcpy 
        (#t:eqtype)
        (l:SZ.t)
        (src dst:larray t (SZ.v l))
        (#p:perm)
        (#src0 #dst0:Ghost.erased (elseq t l))
  : stt unit
        (requires 
            pts_to src #p src0 **
            pts_to dst dst0)
        (ensures (fun _ ->
            pts_to src #p src0 **
            pts_to dst src0))

val fill
        (#t:Type0)
        (l:SZ.t)
        (a:larray t (SZ.v l))
        (v:t)
        (#s:Ghost.erased (elseq t l))
  : stt unit
        (requires 
            pts_to a s)
        (ensures fun _ ->
            exists_ (fun (s:Seq.seq t) ->
                pts_to a s **
                pure (s `Seq.equal` Seq.create (SZ.v l) v)))

val zeroize
        (l:SZ.t)
        (a:array U8.t{ SZ.v l == length a })
        (#s:Ghost.erased (elseq U8.t l))
  : stt unit
        (requires 
            pts_to a s)
        (ensures fun _ -> 
            exists_ (fun (s:Seq.seq U8.t) ->
            pts_to a s **
            pure (s `Seq.equal` Seq.create (SZ.v l) 0uy)))
