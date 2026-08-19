module Bug3166

(* A record whose field types mention earlier fields. Projectors used to be
generated with a `match` body, which did not typecheck here; now they are
declaration-only, so nothing needs to be suppressed. *)

unfold
let maybe_ghost (b:bool) (post : unit -> prop) =
  if b
  then unit -> squash (post ())
  else unit -> squash (post ())

noeq
type r (p:Type) = {
   ghost : bool;
   pred : p -> prop;
   bang : y:p -> maybe_ghost ghost (fun _ -> pred y);
}

let test (x : r int) : bool = x.ghost

#push-options "--no_smt"
let v : r int = { ghost = true; pred = (fun i -> i > 2); bang = (fun y () -> admit()) }
let _ = assert_norm (v.ghost == true)
#pop-options

noeq
type r2 (p:Type) (k : Type -> int) =
  | Mkr2 : a:nat -> b:bool -> #c:bool -> r2 p k

let test2 (x : r2 int (fun _ -> 0)) : nat = Mkr2?.a x
