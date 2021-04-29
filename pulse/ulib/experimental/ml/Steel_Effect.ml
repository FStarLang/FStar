(*
 * Thread API in OCaml does not allow access to the return value of the thread
 *   computations, therefore specializing it to unit -> unit functions
 *
 * Thus code that relies on non-unit return values will fail to compile in OCaml
 *)

let par
  (preL:unit) (postL:unit) (lpreL:unit) (lpostL:unit) (f:unit -> unit)
  (preR:unit) (postR:unit) (lpreR:unit) (lpostR:unit) (g:unit -> unit) =

  let t1 = Thread.create f () in
  let t2 = Thread.create g () in

  Thread.join t1;
  Thread.join t2;

  (), ()
