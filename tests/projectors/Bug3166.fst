module Bug3166

open FStar.Tactics
open FStar.Tactics.MkProjectors

unfold
let maybe_ghost (b:bool) (post : unit -> prop) =
  if b
  then unit -> squash (post ())
  else unit -> squash (post ())

[@@no_auto_projectors_decls]
noeq
type r (p:Type) = {
   ghost : bool;
   pred : p -> prop;
   bang : y:p -> maybe_ghost ghost (fun _ -> pred y);
}

%splice[
  __proj__Mkr__item__ghost;
  __proj__Mkr__item__pred;
  __proj__Mkr__item__bang
] (mk_projs false (`%r))

let test (x : r int) : bool = x.ghost

#push-options "--no_smt"
let v : r int = { ghost = true; pred = (fun i -> i > 2); bang = (fun y () -> admit()) }
let _ = assert_norm (v.ghost == true)
#pop-options

[@@no_auto_projectors_decls]
noeq
type r2 (p:Type) (k : Type -> int) =
  | Mkr2 : a:nat -> b:bool -> #c:bool -> r2 p k

%splice[
  __proj__Mkr2__item__a;
  __proj__Mkr2__item__b;
  __proj__Mkr2__item__c
] (mk_projs false (`%r2))