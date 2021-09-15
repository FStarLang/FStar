module Steel.Loops
open Steel.Memory
open Steel.Effect.Common
open Steel.Effect
open Steel.Reference
module AT = Steel.Effect.Atomic
module U32 = FStar.UInt32

val for_loop' (start:U32.t)
              (finish:U32.t { U32.v start <= U32.v finish })
              (current:U32.t { U32.v start <= U32.v current /\
                               U32.v current <= U32.v finish })
              (inv: nat_at_most finish -> vprop)
              (body:
                    (i:u32_between start finish ->
                          SteelT unit
                          (inv (U32.v i))
                          (fun _ -> inv (U32.v i + 1))))
  : SteelT unit
      (inv (U32.v current))
      (fun _ -> inv (U32.v finish))

#push-options "--fuel 0 --ifuel 0"
let rec for_loop' start finish current inv body
  = if current = finish then (
       AT.change_equal_slprop (inv _) (inv _);
       AT.return ()
    )
    else (
      let _: squash (U32.v current < U32.v finish) = () in //fails without this
      body current;
      let current' = U32.(current +^ 1ul) in
      AT.change_equal_slprop (inv (U32.v current + 1))
                             (inv (U32.v current'));
      for_loop' start finish current' inv body
    )


(* produces 11 queries *)
let for_loop start finish inv body = for_loop' start finish start inv body
