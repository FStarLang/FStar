module Duplex.PCM
open FStar.PCM
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Channel.Protocol

let dprot' = protocol unit

module P = FStar.Preorder
module R = FStar.ReflexiveTransitiveClosure

// Simplifying protocols for now
let rec no_loop (p:protocol 'a) =
  match p with
  | Return _ -> True
  | Msg _ a k -> (forall x. no_loop (k x))
  | DoWhile _ _ -> False

let dprot = p:dprot'{no_loop p}

let nl_protocol 'a = p:protocol 'a { no_loop p }
let return (#a:_) (x:a) : nl_protocol a = Return x
let done : dprot = return ()
let send a : nl_protocol a = Msg Send a return
let recv a : nl_protocol a = Msg Recv a return
let rec bind #a #b (p:nl_protocol a) (q:(a -> nl_protocol b))
  : nl_protocol b
  = match p with
    | Return v -> q v
    | Msg tag c #a' k ->
       let k : c -> nl_protocol b =
        fun x -> bind (k x) q
      in
      Msg tag c k

////////////////////////////////////////////////////////////////////////////////

type party = | A | B

type send_next_dprot_t (name:party) =
  next:dprot{more next /\ tag_of next == (if name = A then Send else Recv)}

type recv_next_dprot_t (name:party) =
  next:dprot{more next /\ tag_of next == (if name = A then Recv else Send)}

val ch : Type u#1

val ep (name:party) (c:ch) (next:dprot) : slprop u#1

val new_channel (p:dprot)
  : SteelT (ch & ch) emp
           (fun cc -> ep A (fst cc) p `star` ep B (snd cc) p)

val channel_send (#name:party)
                 (#next:send_next_dprot_t name)
                 (c:ch) (x:msg_t next)
  : SteelT unit
           (ep name c next)
           (fun _ -> ep name c (step next x))

val channel_recv (#name:party)
                 (#next:recv_next_dprot_t name)
                 (c:ch)
  : SteelT (msg_t next)
           (ep name c next)
           (fun x -> ep name c (step next x))

////////////////////////////////////////////////////////////////////////////////
// An example
////////////////////////////////////////////////////////////////////////////////

let pingpong : dprot =
  x <-- send int;
  y <-- recv (y:int{y > x});
  done

let client (c:ch)
  : SteelT unit
           (ep A c pingpong)
           (fun _ -> ep A c done)
  = // In this implementation, the client first sends the (arbitrarily chosen) integer 17
    channel_send #A c 17;
    let y = channel_recv #A c in
    // The protocol specifies that the integer received is greater than the one sent.
    // This fact is available in the context and can be asserted.
    assert (y > 17)
