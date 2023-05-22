module Steel.ST.C.Opt

let opt_read r =
  rewrite (r `pts_to` _) (r `pts_to` _);
  let Some x = ref_read r in
  x

let opt_write #a #b #x r y =
  rewrite (r `pts_to` _) (r `pts_to` _);
  ref_upd r (Some (Ghost.reveal x)) (Some y) (fun (Some _) -> Some y);
  rewrite (r `pts_to` _) (r `pts_to` _)

let exclusive_opt
  #a x
=
  match x with
  | None ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (exists (y: a). True)
    then begin
      let y = FStar.IndefiniteDescription.indefinite_description_ghost a (fun _ -> True) in
      assert (composable opt_pcm x (Some y))
    end else begin
      let phi
        (frame: option a)
      : Lemma
        (frame == None)
      = match frame with
        | None -> ()
        | Some z -> assert (exists (y: a) . True)
      in
      Classical.forall_intro phi
    end
  | Some _ -> ()

let opt_pcm_read
  #a #b r x
= rewrite (r `pts_to` _) (r `pts_to` _);
  let y' = ref_read r in
  assert (Ghost.reveal x == y');
  Some?.v y'

let opt_pcm_write
  #a #b r x y
= rewrite (r `pts_to` _) (r `pts_to` _);
  ref_upd r x (Some y) (opt_pcm_fpu x y);
  rewrite (r `pts_to` _) (r `pts_to` _)
