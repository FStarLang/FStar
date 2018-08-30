module ImmutableBuffer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module U32 = FStar.UInt32

private let crel (a:Type0) :B.srel a = fun s1 s2 -> Seq.equal s1 s2

private let cpred (#a:Type0) (s:Seq.seq a) :B.spred a = fun s1 -> Seq.equal s1 s

type immutable_buffer (a:Type0) = B.mbuffer a (crel a) (crel a)

let gsub (#a:Type0) (b:immutable_buffer a) (i:U32.t) (len:U32.t)
  :Ghost (immutable_buffer a) (requires (U32.v i + U32.v len <= B.length b)) (ensures (fun _ -> True))
  = B.mgsub b i len (crel a)

let sub (#a:Type0) (b:immutable_buffer a) (i:U32.t) (len:U32.t)
  :HST.Stack (immutable_buffer a)
             (requires (fun h -> U32.v i + U32.v len <= B.length b /\ B.live h b))
             (ensures  (fun h y h' -> h == h' /\ y == gsub b i len))
  = B.msub b i len (crel a)

let offset (#a:Type0) (b:immutable_buffer a) (i:U32.t)
  :HST.Stack (immutable_buffer a)
             (requires (fun h -> U32.v i <= B.length b /\ B.live h b))
             (ensures  (fun h y h' -> h == h' /\ y == gsub b i (U32.sub (B.len b) i)))
  = B.moffset b i (crel a)

let gcmalloc_of_list (#a:Type0) (r:HS.rid) (init:list a)
  :HST.ST (b:immutable_buffer a {
    let len = FStar.List.Tot.length init in
    B.recallable b /\
    B.alloc_post_static r len b /\
    B.alloc_of_list_post len b
  })
          (requires (fun h -> HST.is_eternal_region r /\ B.gcmalloc_of_list_pre #a init))
          (ensures  (fun h b h' -> let len = FStar.List.Tot.length init in
                                 B.alloc_post_common r len b h h' /\
                                 B.as_seq h' b == Seq.seq_of_list init /\
				 B.witnessed b (cpred (Seq.seq_of_list init))))
  = let b = B.mgcmalloc_of_list r init in
    B.witness_p b (cpred (Seq.seq_of_list init));
    b

let recall_contents (#a:Type0) (b:immutable_buffer a) (s:Seq.seq a)
  :HST.ST unit (requires (fun _       -> B.witnessed b (cpred s)))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ Seq.equal (B.as_seq h0 b) s))
  = B.recall_p b (cpred s)

assume val havoc (#a:Type0) (#rrel #rel:B.srel a) (b:B.mbuffer a rrel rel) :HST.St unit

let test (l:list int{List.Tot.length l == 10}) :HST.St unit =
  let ls = Seq.seq_of_list l in
  let b =  gcmalloc_of_list HS.root l in

  havoc b;
  B.recall b;
  recall_contents b ls;
  let h = HST.get () in
  assert (B.as_seq h b == ls);
  
  let sb = sub b 0ul 2ul in
  havoc sb;
  B.recall b;
  recall_contents b ls;  
  let h = HST.get () in
  assert (B.as_seq h b == ls)


(*
 * An example of a two elements buffer
 * The first element increases monotonically and the second element remains same
 *)

type immutable_sub_buffer (a:Type0) (rrel:B.srel a) = B.mbuffer a rrel (crel a)

let trel :B.srel int =
  fun s1 s2 -> Seq.length s1 == 2 ==> (Seq.length s2 == 2 /\ Seq.index s1 0 <= Seq.index s2 0 /\ Seq.index s2 1 == Seq.index s1 1)

type tbuffer = b:B.mbuffer int trel trel{B.length b == 2}

let tsub (b:tbuffer)
  :HST.Stack (immutable_sub_buffer _ _)
             (requires (fun h -> B.live h b))
             (ensures  (fun h y h' -> h == h' /\ y == B.mgsub b 1ul 1ul (crel int)))
  = B.msub b 1ul 1ul (crel int)

let test_immutable_sub (b:tbuffer)
  :HST.ST unit (requires (fun h0    -> B.recallable b /\ Seq.index (B.as_seq h0 b) 1 == 2))
               (ensures  (fun _ _ _ -> True))
  = B.recall b;

    let s = Seq.create 1 2 in

    let bb = tsub b in
    let _ = B.witness_p bb (cpred s) in  //witness the contents of the subbuffer

    havoc bb; havoc b;
    B.recall_p bb (cpred s);
    let h = HST.get () in
    assert (B.as_seq h bb == s)


(*
 * Testing normalization of lists in the buffer library
 *)
[@"opaque_to_smt"]
let l :list int = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]

let pre () = assert (B.gcmalloc_of_list_pre l)

let test2 () :HST.St unit =
  let b = B.gcmalloc_of_list HS.root l in
  assert (B.length b == 10)
