module Steel.C.Model.Frac

open Steel.C.Model.PCM
open Steel.C.Model.Ref
open Steel.Effect
open Steel.Effect.Atomic
  
open Steel.FractionalPermission

let frac_pcm_write r x y
= ref_upd r x (Some (y, full_perm)) (frac_pcm_fpu x y);
  change_equal_slprop (r `pts_to` _) (r `pts_to` _)

let frac_pcm_read r x
= let y' = ref_read r in
  assert (Some? y' /\ fst (Some?.v (Ghost.reveal x)) == fst (Some?.v y'));
  fst (Some?.v y')

let exclusive_frac
  (#a: Type)
  (x: option (a & perm))
: Lemma
  (exclusive pcm_frac x <==> ((exists (y: a) . True) ==> (Some? x /\ full_perm `lesser_equal_perm` snd (Some?.v x))))
= match x with
  | None ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (exists (y: a). True)
    then begin
      let y = FStar.IndefiniteDescription.indefinite_description_ghost a (fun _ -> True) in
      let frame = Some (y, full_perm) in
      assert (~ (frame == one pcm_frac));
      assert (composable pcm_frac x frame)
    end else begin
      let phi
        (frame: option (a & perm))
      : Lemma
        (frame == None)
      = match frame with
        | None -> ()
        | Some (z, _) -> assert (exists (y: a) . True)
      in
      Classical.forall_intro phi
    end
  | Some (y, p) ->
    assert (exists (z: a) . True);
    if FStar.StrongExcludedMiddle.strong_excluded_middle (full_perm `lesser_equal_perm` p)
    then ()
    else begin
      let frame = Some (y, MkPerm (let open FStar.Real in one -. p.v)) in
      assert (composable pcm_frac x frame);
      assert (~ (frame == one pcm_frac))
    end
