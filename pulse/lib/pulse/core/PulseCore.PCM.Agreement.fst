module PulseCore.PCM.Agreement
open FStar.PCM

let agreement (a:Type u#a) = option a

let composable #a : symrel (agreement a) =
  fun (f0 f1:agreement a) ->
    match f0, f1 with
    | None, _
    | _, None -> True
    | Some x0, Some x1 -> x0==x1
let compose #a (f0:agreement a) (f1:agreement a{composable f0 f1}) : agreement a =
  match f0, f1 with
  | None, f
  | f, None -> f
  | Some x0, Some _ -> Some x0

let pcm_agreement #a : pcm (agreement a) = {
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

let full_values_compatible (#a:Type u#a) (x:a)
: Lemma (compatible pcm_agreement (Some x) (Some x))
= ()