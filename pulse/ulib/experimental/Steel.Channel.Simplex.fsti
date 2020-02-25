module Steel.Channel.Simplex
open Steel.Channel.Protocol.Lower
open Steel.Effect
open Steel.Memory

/// Msg int (fun x -> Msg (y:int { y > x }) (fun _ -> Ret unit))
let prot = prot unit

val chan : Type0

val sender (c:chan) (p:prot) : hprop

val receiver (c:chan) (p:prot) : hprop

val new_chan (p:prot)
  : SteelT chan emp (fun c -> sender c p `star` receiver c p)

val send (#p:prot{more p}) (c:chan) (x:msg_t p)
  : SteelT unit (sender c p) (fun _ -> sender c (step p x))

val recv (#p:prot{more p}) (c:chan)
  : SteelT (msg_t p) (receiver c p) (fun x -> receiver c (step p x))
