module Phase2CoreDeadBranch

(* The refinement [fun (_:nat{_ < n}) -> ...] after a pattern-let elaborates to a match
   with a branch after a wildcard: it is dead code, checked under a false path condition. *)
noeq type view (a:Type) = | SNil | SCons : hd:a -> tl:Seq.seq a -> view a
assume val view_seq (#a:Type) (s:Seq.seq a) : v:view a{Seq.length s > 0 ==> SCons? v}
let rec zeros_ (n : nat)
  : Lemma (ensures Seq.length (Seq.init_ghost n (fun _ -> 0)) == n)
          (decreases n)
  = if n = 0 then ()
    else begin
      let s = Seq.init_ghost n (fun (_:nat{_ < n}) -> 0) in
      let SCons hd tl = view_seq s in
      let s' = Seq.init_ghost (n-1) (fun (_:nat{_ < n-1}) -> 0) in
      assert (Seq.length s' == n - 1);
      zeros_ (n-1)
    end
