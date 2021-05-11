module Duplex.PingPong
open FStar.PCM
open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect
open Steel.Channel.Protocol
open Duplex.PCM

////////////////////////////////////////////////////////////////////////////////
// An example
////////////////////////////////////////////////////////////////////////////////

let pingpong : dprot =
  x <-- send int;
  y <-- recv (y:int{y > x});
  done

let client (c:ch)
  : SteelSelT unit
           (ep A c pingpong)
           (fun _ -> ep A c done)
  = // In this implementation, the client first sends the (arbitrarily chosen) integer 17
    channel_send #A c 17;
    let y = channel_recv #A c in
    // The protocol specifies that the integer received is greater than the one sent.
    // This fact is available in the context and can be asserted.
    assert (y > 17)
