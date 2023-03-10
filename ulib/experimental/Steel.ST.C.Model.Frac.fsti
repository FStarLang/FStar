module Steel.ST.C.Model.Frac
open Steel.ST.Util

module P = FStar.PCM
open Steel.C.Model.PCM
open Steel.ST.C.Model.Ref

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
: ST unit (r `pts_to` x) (fun _ -> r `pts_to` Some (y, full_perm))
  (requires (Some? x /\ snd (Some?.v x) == full_perm))
  (ensures (fun _ -> True))

val frac_pcm_read
  (#a:Type) (#b: Type)
  (r: ref a (pcm_frac #b)) (x: Ghost.erased (fractional b))
: ST b (r `pts_to` x) (fun _ -> r `pts_to` x)
  (requires (Some? x))
  (ensures (fun y -> Some? x /\ y == fst (Some?.v (Ghost.reveal x))))

val exclusive_frac
  (#a: Type)
  (x: option (a & perm))
: Lemma
  (exclusive pcm_frac x <==> ((exists (y: a) . True) ==> (Some? x /\ full_perm `lesser_equal_perm` snd (Some?.v x))))
