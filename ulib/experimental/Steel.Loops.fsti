module Steel.Loops
open Steel.Effect.Common
open Steel.Effect
module U32 = FStar.UInt32

let nat_at_most (f:U32.t)
  = x:nat{ x <= U32.v f }

let u32_between (s f:U32.t)
  = x:U32.t { U32.v s <= U32.v x /\ U32.v x < U32.v f}

val for_loop (start:U32.t)
             (finish:U32.t { U32.v start <= U32.v finish })
             (inv: nat_at_most finish -> vprop)
             (body:
                    (i:u32_between start finish ->
                          SteelT unit
                          (inv (U32.v i))
                          (fun _ -> inv (U32.v i + 1))))
  : SteelT unit
      (inv (U32.v start))
      (fun _ -> inv (U32.v finish))
