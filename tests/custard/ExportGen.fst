(* Section 35.1.  A public API whose types are generic.

   Round 40's reporter drove the real CBOR API off the generated header from
   C++, and needed three typedefs to do it.  Two of the three name types that
   --custard_c_no_prefix renamed for them.  The third names a *specialization*
   -- [CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__cbor_raw] -- which the
   option deliberately leaves alone, because a specialization's name carries
   a section 30.15 hint and hints are bounded, clipped and collision-suffixed.

   So part of a generic API's surface is spelled in generated syntax, and
   nothing said so.  This is that in miniature: [cell] reaches the interface
   only as [cell U32.t], [get] has it in its signature, and a consumer that
   includes the header has to write [ExportGen_cell__uint32] to hold what
   [mk] returned.  Warning 377 says the name is generated before the consumer
   commits to it. *)
module ExportGen

module U32 = FStar.UInt32

noeq type cell (a: Type) = { hd : a; tl : U32.t }

let mk (x: U32.t) : cell U32.t = { hd = x; tl = 1ul }

let get (c: cell U32.t) : U32.t = c.hd

(* Reported once per type, not once per definition: [mk] and [get] both have
   it, and the consumer's problem is the type. *)
let main () : U32.t = if U32.eq (get (mk 7ul)) 7ul then 0ul else 1ul
