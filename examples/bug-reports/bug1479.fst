module Bug1479

open FStar.Tactics
open FStar.Tactics.Result

assume val fail : #a:Type -> m:string -> TAC a (fun ps post -> post (Failed m ps))

let guard b : TAC unit (fun ps post -> if b
                                       then post (Success () ps)
                                       else forall m. post (Failed m ps)) =
   if b
   then ()
   else fail "guard failed"
