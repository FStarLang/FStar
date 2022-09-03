module Steel.PCMReadOnly
include FStar.PCM

let readonly (a:Type u#a) = option a
let composable #a : symrel (readonly a) =
  fun (f0 f1:readonly a) ->
    match f0, f1 with
    | None, _
    | _, None -> True
    | Some x0, Some x1 -> x0==x1
let compose #a (f0:readonly a) (f1:readonly a{composable f0 f1}) : readonly a =
  match f0, f1 with
  | None, f
  | f, None -> f
  | Some x0, Some _ -> Some x0

let pcm_readonly #a : pcm (readonly a) = {
  p = {
         composable = composable;
         op = compose;
         one = None
      };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun _ -> True)
}

let mk_frame_preserving_upd
  (#a: Type)
  (v0: a)
: Tot (frame_preserving_upd pcm_readonly (Some v0) (Some v0))
= fun _ -> Some v0
