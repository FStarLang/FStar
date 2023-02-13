module Steel.C.Model.Frac

module P = FStar.PCM
open Steel.C.Model.PCM
open Steel.C.Model.Ref
open Steel.Effect

/// Fractional permissions: from Steel.HigherReference
open Steel.FractionalPermission

let fractional (a:Type u#a) = option (a & perm)

let fractional_composable #a : P.symrel (fractional a) =
  fun (f0 f1:fractional a) ->
    match f0, f1 with
    | None, _
    | _, None -> True
    | Some (x0, p0), Some (x1, p1) -> x0==x1 /\ sum_perm p0 p1 `lesser_equal_perm` full_perm

let fractional_compose #a (f0:fractional a) (f1:fractional a{fractional_composable f0 f1}) : fractional a =
  match f0, f1 with
  | None, f
  | f, None -> f
  | Some (x0, p0), Some (_, p1) -> Some (x0, sum_perm p0 p1)

let fstar_pcm_frac #a : P.pcm (fractional a) = let open P in {
  p = {
         composable = fractional_composable;
         op = fractional_compose;
         one = None
      };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun x -> Some? x /\ snd (Some?.v x) == full_perm)
}

let pcm_frac #a : pcm (fractional a) = pcm_of_fstar_pcm fstar_pcm_frac

let frac_pcm_fpu
  (#a: Type)
  (x: Ghost.erased (fractional a) { Some? x /\ snd (Some?.v x) == full_perm })
  (y: a)
: Tot (frame_preserving_upd pcm_frac x (Some (y, full_perm)))
= base_fpu pcm_frac x (Some (y, full_perm))

val frac_pcm_write
  (#a:Type) (#b: Type)
  (r: ref a (pcm_frac #b)) (x: Ghost.erased (fractional b)) (y: b)
: Steel unit (r `pts_to` x) (fun _ -> r `pts_to` Some (y, full_perm))
  (requires (fun _ -> Some? x /\ snd (Some?.v x) == full_perm))
  (ensures (fun _ _ _ -> True))

val frac_pcm_read
  (#a:Type) (#b: Type)
  (r: ref a (pcm_frac #b)) (x: Ghost.erased (fractional b))
: Steel b (r `pts_to` x) (fun _ -> r `pts_to` x)
  (requires (fun _ -> Some? x))
  (ensures (fun _ y _ -> Some? x /\ y == fst (Some?.v (Ghost.reveal x))))

val exclusive_frac
  (#a: Type)
  (x: option (a & perm))
: Lemma
  (exclusive pcm_frac x <==> ((exists (y: a) . True) ==> (Some? x /\ full_perm `lesser_equal_perm` snd (Some?.v x))))

let frac_view
  (a: Type)
  (p: perm)
: Tot (sel_view (pcm_frac #a) a false)
= {
  to_view_prop = (fun x -> Some? x == true);
  to_view = (fun x -> let Some (v, _) = x in v);
  to_carrier = (fun v -> Some (v, p));
  to_carrier_not_one = ();
  to_view_frame = (fun v frame -> ());
}

let frac_read_sel
  (#a: Type u#0) (#b: Type u#0)
  (#p: perm)
  (r: ref a (pcm_frac #b))
: Steel b
  (pts_to_view r (frac_view _ p))
  (fun _ -> pts_to_view r (frac_view _ p))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    res == h (pts_to_view r (frac_view _ p)) /\
    res == h' (pts_to_view r (frac_view _ p))
  ))
= ref_read_sel r (frac_view _ p)

let frac_write_sel
  (#a: Type u#0) (#b: Type u#0)
  (#p: perm)
  (r: ref a (pcm_frac #b))
  (w: b)
: Steel unit
  (pts_to_view r (frac_view _ p))
  (fun _ -> pts_to_view r (frac_view _ p))
  (requires (fun _ -> p == full_perm))
  (ensures (fun h _ h' ->
    w == h' (pts_to_view r (frac_view _ p))
  ))
=
  let _ = pts_to_view_elim r (frac_view _ _) in
  frac_pcm_write r _ w;
  pts_to_view_intro r _ (frac_view _ p) w

