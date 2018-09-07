module ImmutableBuffer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module U32 = FStar.UInt32

module IB = LowStar.ImmutableBuffer


(*
 * Testing normalization of lists in the buffer library
 *)
[@"opaque_to_smt"]
let l :list int = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]

let test2 (lll:list int{List.Tot.length lll > 0 /\
                      List.Tot.length lll <= UInt.max_int 32})
  :HST.ST unit (fun h0 -> HS.is_stack_region (HS.get_tip h0)) (fun _ _ _ -> True)=
  let b = B.gcmalloc_of_list HS.root l in
  assert (B.length b == 10);
  let h = HST.get () in
  assert (B.as_seq h b == Seq.seq_of_list l);
  assert (B.length b == List.Tot.length l);
  let ll = [1;2;3;4;5;6;7;8;9;10;11] in
  HST.push_frame ();
  let b = B.alloca_of_list ll in
  assert (B.length b == 11);
  let h = HST.get () in
  assert (B.as_seq h b == Seq.seq_of_list ll);
  assert (B.length b == List.Tot.length ll);
  let b = B.alloca_of_list lll in
  let h = HST.get () in
  assert (B.as_seq h b == Seq.seq_of_list lll);
  assert (B.length b == List.Tot.length lll);
  HST.pop_frame ()

assume val havoc (#a:Type0) (#rrel #rel:B.srel a) (b:B.mbuffer a rrel rel) :HST.St unit

let test (l:list int{List.Tot.length l == 10}) :HST.St unit =
  let ls = Seq.seq_of_list l in
  let b =  IB.igcmalloc_of_list HS.root l in
  assert (B.length b == 10);
  havoc b;
  IB.recall_contents b ls;
  let h = HST.get () in
  assert (B.as_seq h b == ls);
  assert (B.live h b);
  
  let sb = IB.isub b 0ul 2ul in
  IB.witness_contents sb (Seq.slice ls 0 2);
  havoc sb;
  IB.recall_contents sb (Seq.slice ls 0 2);
  IB.recall_contents b ls;
  let h = HST.get () in
  assert (B.as_seq h b == ls);
  assert (B.as_seq h sb = Seq.slice ls 0 2)


// (*
//  * An example of a two elements buffer
//  * The first element increases monotonically and the second element remains same
//  *)

// type immutable_sub_buffer (a:Type0) (rrel:B.srel a) = B.mbuffer a rrel (crel a)

// let trel :B.srel int =
//   fun s1 s2 -> Seq.length s1 == 2 ==> (Seq.length s2 == 2 /\ Seq.index s1 0 <= Seq.index s2 0 /\ Seq.index s2 1 == Seq.index s1 1)

// type tbuffer = b:B.mbuffer int trel trel{B.length b == 2}

// let tsub (b:tbuffer)
//   :HST.Stack (immutable_sub_buffer _ _)
//              (requires (fun h -> B.live h b))
//              (ensures  (fun h y h' -> h == h' /\ y == B.mgsub b 1ul 1ul (crel int)))
//   = B.msub b 1ul 1ul (crel int)

// let test_immutable_sub (b:tbuffer)
//   :HST.ST unit (requires (fun h0    -> B.recallable b /\ Seq.index (B.as_seq h0 b) 1 == 2))
//                (ensures  (fun _ _ _ -> True))
//   = B.recall b;

//     let s = Seq.create 1 2 in

//     let bb = tsub b in
//     let _ = B.witness_p bb (cpred s) in  //witness the contents of the subbuffer

//     havoc bb; havoc b;
//     B.recall_p bb (cpred s);
//     let h = HST.get () in
//     assert (B.as_seq h bb == s)
