let while_ cond body =
  while (cond ()) do
    body ()
  done

val unreachable : unit -> 'a
let unreachable () = unreachable ()

(* TODO implement goto using OCaml 5 effects *)

type goto_label_core = int
type 'a goto_label = goto_label_core

let new_goto_lbl : unit -> goto_label_core =
  let ctr = ref 0 in
  fun _ ->
    let i = !ctr in
    ctr := i + 1;
    i

exception Goto of goto_label_core * Obj.t

let goto (lbl: 'a goto_label) (arg: 'a) : unit =
  raise (Goto (lbl, Obj.repr arg))

let forward_jump_label (body: 'a goto_label -> 'a) : 'a =
  let lbl = new_goto_lbl () in
  try
    body lbl
  with
    | Goto (lbl', ret) when lbl' = lbl ->
      Obj.obj ret