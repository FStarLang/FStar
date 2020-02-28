module Steel.Channel.Protocol.Lower
open Steel.Channel.Protocol
module L = FStar.Unsound.UniverseLowering
// Cheating and putting protocols in universe 0 for now
// Until we enrich Memory to store higher universe values
let prot 'a : Type0 = L.lower (protocol 'a)

let more (p:prot 'a) : GTot bool = Msg? (hnf (L.project p))
let msg_t (p:prot 'a) : Type0 = match hnf (L.project p) with | Msg a _ -> a | Return #a _ -> a
let step (p:prot 'a{more p}) (x:msg_t p) : prot 'a = L.inject (Msg?.k (hnf (L.project p)) x)
let hnf (p:prot 'a) : prot 'a = L.inject (hnf (L.project p))
let msg (t:Type0) (q:prot 'a) : prot 'a = L.inject (Msg t (fun _ -> L.project q))

module P = Steel.Channel.Protocol
let trace (p q:prot unit) : Type0 = L.lower (P.trace (L.project p) (L.project q))
let partial_trace_of (p:prot unit) : Type0 = L.lower (P.partial_trace_of (L.project p))
let until (#p:prot unit) (t:partial_trace_of p) : prot unit = L.inject ((L.project t).to)
let next_msg_t (#p:prot unit) (x:partial_trace_of p) = P.next_msg_t (L.project x).to
let extensible (#p:prot unit) (x:partial_trace_of p) = P.more_msgs (L.project x).to

// It's a pain to lift the preorder across the lowering
// Not doing it since this module is temporary anyway
assume
val extended_to (#p:prot unit) : FStar.Preorder.preorder (partial_trace_of p)

let initial_trace (p:prot unit)
  : (q:partial_trace_of p {until q == p})
  = L.inject ({ to = L.project p; tr=Waiting (L.project p)})
let extend_partial_trace (#p:prot unit) (t:partial_trace_of p) (msg:next_msg_t t{extensible t})
  : Tot (s:partial_trace_of p { t `extended_to` s })
  = let s = L.inject (P.extend_partial_trace (L.project t) msg) in
    assume (t `extended_to` s);
    s
let extension_of #p (tr:partial_trace_of p) = ts:partial_trace_of p{tr `extended_to` ts}
