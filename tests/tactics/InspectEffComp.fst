module InspectEffComp

open FStar.Tactics.V2

let test () : Type0 =
  _ by
    (let t = (`(int -> PURE int (requires True) (ensures fun r -> r == 42))) in
     match inspect t with
     | Tv_Arrow bv c ->
       let c' =
         (* [PURE] is an abbreviation of [Tot], which the desugarer resolves
            away, and a computation's postcondition is now a refinement of its
            result type.  So this inspects as a [Tot] whose result type is
            [r: int{r == 42}], and it is that result type which is rebuilt. *)
         let cv = inspect_comp c in
         if not (is_tot_comp cv) then fail "no"
         else pack_comp ({ cv with result_typ = (`(r:int{r == 17})) })
       in
       let t' = pack (Tv_Arrow bv c') in
       exact t'
     | _ -> fail "impossible")


let _ = assert (test () == (int -> PURE int (requires True) (ensures fun r -> r == 17)))
