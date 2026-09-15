module InspectEffComp

open FStar.Tactics.V2

let test () : Type0 =
  _ by
    (let t = (`(int -> PURE int (requires True) (ensures fun r -> r == 42))) in
     match inspect t with
     | Tv_Arrow bv c ->
       let c' =
         begin match inspect_comp c with
         (* [PURE] is an abbreviation of [Tot], which the desugarer resolves
            away, and a computation's postcondition is now a refinement of its
            result type.  So this inspects as a [C_Total] whose result type is
            [r: int{r == 42}], and it is that result type which is rebuilt. *)
         | C_Total _res -> pack_comp (C_Total (`(r:int{r == 17})))
         | _ -> fail "no"
         end
       in
       let t' = pack (Tv_Arrow bv c') in
       exact t'
     | _ -> fail "impossible")


let _ = assert (test () == (int -> PURE int (requires True) (ensures fun r -> r == 17)))
