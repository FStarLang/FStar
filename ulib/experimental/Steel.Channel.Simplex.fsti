module Steel.Channel.Simplex
open Steel.Channel.Protocol.Lower
open Steel.Effect
open Steel.Memory

/// Msg int (fun x -> Msg (y:int { y > x }) (fun _ -> Ret unit))
///
/// DoWhile (Msg int (fun x -> Msg (y:int { y > x }) (fun _ -> Ret bool)))
let prot = prot unit

val chan (p:prot) : Type0

val sender (#p:prot) (c:chan p) (next_action:prot) : hprop

val receiver (#p:prot) (c:chan p) (next_action:prot) : hprop

val new_chan (p:prot)
  : SteelT (chan p) emp (fun c -> sender c p `star` receiver c p)

val send (#p:prot) (c:chan p) (#next:prot{more next}) (x:msg_t next)
  : SteelT unit (sender c next) (fun _ -> sender c (step next x))

val recv (#p:prot) (#next:prot{more next}) (c:chan p)
  : SteelT (msg_t next) (receiver c next) (fun x -> receiver c (step next x))

val history (#p:prot) (c:chan p) (t:partial_trace_of p) : hprop

val history_duplicable (#p:prot) (c:chan p) (t:partial_trace_of p)
  : SteelT unit (history c t) (fun _ -> history c t `star` history c t)

val trace (#p:prot) (#next:prot) (c:chan p) (previous:partial_trace_of p)
  : SteelT (t:partial_trace_of p{previous `extended_to` t /\ until t == next})
           (receiver c next `star` history c previous)
           (fun t -> receiver c next `star` history c t)
