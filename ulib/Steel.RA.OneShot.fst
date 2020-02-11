module Steel.RA.OneShot

open Steel.RA

(* Example, oneshot RA from Iris paper *)

type oneshot_t =
  | Pending
  | Shot of nat
  | Inval

let oneshot_valid x : prop =
  match x with
  | Inval -> False
  | _ -> True

let oneshot_core x =
  match x with
  | Pending -> None
  | Shot n -> Some (Shot n)
  | Inval -> Some Inval

let oneshot_comp x y =
  match x, y with
  | Shot n, Shot m ->
    if n = m
    then Shot n
    else Inval
  | _ ->
    Inval

let oneshot_ra0 = {
  valid       = oneshot_valid;
  core        = oneshot_core;
  comp        = oneshot_comp;
}

open FStar.Tactics

let oneshot_props : ra_props oneshot_ra0 = {
  assoc       = easy;
  comm        = easy;
  coreid      = easy;
  coreidem    = easy;
  coremono    = easy;
  validop     = easy;
}

instance oneshot_ra = Mkra oneshot_ra0 oneshot_props

val pending_excl : a:oneshot_t -> Lemma (valid (Pending @@ a) ==> False)
let pending_excl a = ()

val shot_agree : n:nat -> m:nat -> Lemma (valid (Shot n @@ Shot m) ==> n == m)
let shot_agree n m = ()

val shot_idem : n:nat -> Lemma (Shot n @@ Shot n == Shot n)
let shot_idem n = ()
