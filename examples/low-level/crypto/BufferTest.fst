module BufferTest

module HH     = FStar.HyperHeap
module HS     = FStar.HyperStack
module HST    = FStar.ST
module Buffer = FStar.Buffer

open FStar.HyperStack
open FStar.Seq
open FStar.Buffer

assume val r_0:HH.rid
assume val r_1:HH.rid
assume val r_2:HH.rid
assume val r_3:HH.rid
assume val r_4:HH.rid

assume val ref_0:(r:HS.reference (seq nat){r.id = r_0})
assume val buf_0:(b:buffer nat{frameOf b = r_0})
assume val ref_1:(r:HS.reference (seq nat){r.id = r_1})
assume val buf_1:(b:buffer nat{frameOf b = r_1})
assume val ref_2:(r:HS.reference (seq nat){r.id = r_2})
assume val buf_2:(b:buffer nat{frameOf b = r_2})
assume val ref_3:(r:HS.reference (seq nat){r.id = r_3})
assume val buf_3:(b:buffer nat{frameOf b = r_3})
assume val ref_4:(r:HS.reference (seq nat){r.id = r_4})
assume val buf_4:(b:buffer nat{frameOf b = r_4})

assume Distinct_regions: r_0 <> r_1 /\ r_0 <> r_2 /\ r_0 <> r_3 /\ r_0 <> r_4 /\
                         r_1 <> r_2 /\ r_1 <> r_3 /\ r_1 <> r_4           /\
                         r_2 <> r_3 /\ r_2 <> r_4                     /\
			 r_3 <> r_4

assume Distinct_refs: ~ ((content buf_0).ref === ref_0.ref) /\
                      ~ ((content buf_1).ref === ref_1.ref) /\
		      ~ ((content buf_2).ref === ref_2.ref) /\
		      ~ ((content buf_3).ref === ref_3.ref)

let live b r h =
  HS.contains h r /\
  Buffer.live h b

let bequal b h0 h1 = Buffer.equal h0 b h1 b

let requal r h0 h1 = HS.sel h0 r == HS.sel h1 r

let all_live h =
  live buf_0 ref_0 h /\ live buf_1 ref_1 h /\ live buf_2 ref_2 h /\ live buf_3 ref_3 h /\ live buf_4 ref_4 h

assume val f_0: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> Buffer.modifies_none h0 h1))

assume val f_1: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> HS.modifies (Set.as_set [r_0]) h0 h1 /\
			                             live buf_0 ref_0 h1))

assume val f_2: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> HS.modifies (Set.as_set [r_1]) h0 h1 /\
			                             live buf_1 ref_1 h1))

assume val f_3: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> HS.modifies (Set.as_set [r_2]) h0 h1 /\
			                             live buf_2 ref_2 h1))

assume val f_4: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> HS.modifies (Set.as_set [r_3]) h0 h1 /\
			                             live buf_3 ref_3 h1))

val foo_1: unit -> ST unit (requires (fun h0 -> all_live h0)) (ensures (fun _ _ _ -> True))
let foo_1 () =
  let h0 = HST.get () in
  f_0 ();
  f_1 ();
  f_2 ();
  f_3 ();
  f_4 ();
  let h1 = HST.get () in
  assert (bequal buf_4 h0 h1)

assume val g_0: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> Buffer.modifies_none h0 h1))

assume val g_1: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> HS.modifies (Set.as_set [r_0]) h0 h1          /\
			                             HS.modifies_ref r_0 !{HS.as_ref ref_0} h0 h1    /\
			                             live buf_0 ref_0 h1))

assume val g_2: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> HS.modifies (Set.as_set [r_1]) h0 h1          /\
			                             HS.modifies_ref r_1 !{HS.as_ref ref_1} h0 h1    /\
			                             live buf_1 ref_1 h1))

assume val g_3: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> HS.modifies (Set.as_set [r_2]) h0 h1          /\
			                             HS.modifies_ref r_2 !{HS.as_ref ref_2} h0 h1    /\
			                             live buf_2 ref_2 h1))

assume val g_4: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> HS.modifies (Set.as_set [r_3]) h0 h1          /\
			                             HS.modifies_ref r_3 !{HS.as_ref ref_3} h0 h1    /\
			                             live buf_3 ref_3 h1))

val foo_2: unit -> ST unit (requires (fun h0 -> all_live h0)) (ensures (fun _ _ _ -> True))
let foo_2 () =
  let h0 = HST.get () in
  g_0 ();
  g_1 ();
  g_2 ();
  g_3 ();
  g_4 ();
  let h1 = HST.get () in
  assert (bequal buf_0 h0 h1)

assume val h_0: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> Buffer.modifies_none h0 h1))

assume val h_1: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> HS.modifies (Set.as_set [r_0]) h0 h1        /\
			                             HS.modifies_ref r_0 !{HS.as_ref ref_0} h0 h1  /\
			                             live buf_0 ref_0 h1))

assume val h_2: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> HS.modifies (Set.as_set [r_0; r_1]) h0 h1       /\
			                             HS.modifies_ref r_0 !{HS.as_ref ref_0} h0 h1    /\
			                             HS.modifies_ref r_1 !{HS.as_ref ref_1} h0 h1    /\
			                             live buf_1 ref_1 h1))

assume val h_3: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> HS.modifies (Set.as_set [r_0; r_1; r_2]) h0 h1 /\
			                             HS.modifies_ref r_0 !{HS.as_ref ref_0} h0 h1  /\
			                             HS.modifies_ref r_1 !{HS.as_ref ref_1} h0 h1  /\
			                             HS.modifies_ref r_2 !{HS.as_ref ref_2} h0 h1  /\
			                             live buf_2 ref_2 h1))

assume val h_4: unit -> ST unit (requires (fun h0 -> all_live h0))
			      (ensures  (fun h0 _ h1 -> HS.modifies (Set.as_set [r_0; r_1; r_2; r_3]) h0 h1 /\
			                             HS.modifies_ref r_0 !{HS.as_ref ref_0} h0 h1      /\
			                             HS.modifies_ref r_1 !{HS.as_ref ref_1} h0 h1      /\
			                             HS.modifies_ref r_2 !{HS.as_ref ref_2} h0 h1      /\
			                             HS.modifies_ref r_3 !{HS.as_ref ref_3} h0 h1      /\
			                             live buf_3 ref_3 h1))

(* this takes 14-15s to verify, and needs this rlimit *)
val foo_3: unit -> ST unit (requires (fun h0 -> all_live h0)) (ensures (fun _ _ _ -> True))
#set-options "--z3rlimit 50"
let foo_3 () =
  let h0 = HST.get () in
  h_0 ();
  h_1 ();
  h_2 ();
  h_3 ();
  h_4 ();
  let h1 = HST.get () in
  assert (bequal buf_0 h0 h1)
