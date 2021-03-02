module Duplex.PCM
open Steel.Channel.Protocol
open Steel.Memory
open Steel.Effect

let dprot' = protocol unit

// Simplifying protocols for now
let rec no_loop (p:protocol 'a) =
  match p with
  | Return _ -> True
  | Msg _ a k -> (forall x. no_loop (k x))
  | DoWhile _ _ -> False

let dprot = p:dprot'{no_loop p}

type party = | A | B

let nl_protocol 'a = p:protocol 'a { no_loop p }
let return (#a:_) (x:a) : nl_protocol a = Return x
let done : dprot = return ()
let send_msg a : nl_protocol a = Msg Send a return
let recv_msg a : nl_protocol a = Msg Recv a return
let rec bind #a #b (p:nl_protocol a) (q:(a -> nl_protocol b))
  : nl_protocol b
  = match p with
    | Return v -> q v
    | Msg tag c #a' k ->
       let k : c -> nl_protocol b =
        fun x -> bind (k x) q
      in
      Msg tag c k

let step (p:dprot{more_msgs p})
         (x:next_msg_t p)
  : dprot
  = Msg?.k (hnf p) x

let is_send_next name (next:dprot) =
  more next /\ tag_of next == (if name = A then Send else Recv)
let is_recv_next name (next:dprot) =
  more next /\ tag_of next == (if name = A then Recv else Send)

type send_next_dprot_t (name:party) =
  next:dprot{more next /\ tag_of next == (if name = A then Send else Recv)}

type recv_next_dprot_t (name:party) =
  next:dprot{more next /\ tag_of next == (if name = A then Recv else Send)}

val ch : Type u#1

val ep (name:party) (c:ch) (next:dprot) : slprop u#1

val send (#name:party)
         (#next:dprot)
         (c:ch { is_send_next name next })
         (x:msg_t next)
  : SteelT unit
      (ep name c next)
      (fun _ -> ep name c (step next x))

val recv (#name:party)
         (#next:dprot)
         (c:ch { is_recv_next name next })
  : SteelT (msg_t next)
      (ep name c next)
      (fun x -> ep name c (step next x))
