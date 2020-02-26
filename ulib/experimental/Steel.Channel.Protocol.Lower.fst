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
