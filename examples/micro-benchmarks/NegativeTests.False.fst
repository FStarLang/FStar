module NegativeTests.False 
(* #284 *)
val foo : f:(unit -> Tot bool){f () = true}
          -> Tot (r:bool {r = f () /\ r = true})
let foo f = f ()
val bar : unit -> Pure bool (requires True) (ensures (fun _ -> False))
[@(expect_failure [19])]
let bar () = foo (fun x -> false)

(*#380*)
val f : p1:(True \/ True) -> p2:(True \/ True) -> Lemma (p1 = p2)
let f p1 p2 = ()
val absurd : unit -> Lemma False
[@expect_failure] // this raises 2 errors on 1-phase, and 4 on 2-phases
let absurd () = f (Left #_ #True T) (Right #True #_ T) //adding implicits to get 2 typing errors

[@expect_failure]
type t :(_:Type0{False}) =
  | C :t
