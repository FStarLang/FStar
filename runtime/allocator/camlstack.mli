(** Stack operations

  The functions here are for allocating Caml values on a manually-managed,
  growable stack.
*)

external push_frame : int -> unit = "stack_push_frame";;
(** [Camlstack.push_frame n] pushes a frame onto the stack that has at least
    [n] contiguous bytes. The frame will grow, if necessary. 
    (An argument of 0 is acceptable.) 
    Raise [Invalid_argument "Camlstack.push_frame"] if [n] is negative. *)

external pop_frame : unit -> unit = "stack_pop_frame";;
(** Pops the topmost stackframe. 
    Raise [Failure "Camlstack.pop_frame"] if the stack has no frames. *)

external mkpair : 'a -> 'b -> 'a*'b = "stack_mkpair";;
(** [Camlstack.mkpair x y] allocates a pair (x,y) on the stack.
    Raise [Failure "Camlstack.mkpair"] if the stack has no frames. *)

external mktuple3 : 'a -> 'b -> 'c -> 'a*'b*'c = "stack_mktuple3";;
(** [Camlstack.mktuple3 x y z] allocates a triple (x,y,z) on the stack.
    Raise [Failure "Camlstack.mktuple3"] if the stack has no frames. *)

external mktuple4 : 'a -> 'b -> 'c -> 'd -> 'a*'b*'c*'d = "stack_mktuple4";;
(** [Camlstack.mktuple4 x y z w] allocates a pair (x,y,z,w) on the stack.
    Raise [Failure "Camlstack.mktuple4"] if the stack has no frames. *)

external cons: 'a -> 'a list -> 'a list = "stack_mkpair";;
(** [Camlstack.cons x y] allocates a cons cell [x::y] on the stack.
    Raise [Failure "Camlstack.cons"] if the stack has no frames. *)

external print_mask : unit -> unit = "print_mask";;
(** [Camlstack.print_mask ()] is a debugging function. It prints
    a list of Caml heap pointers that occur on the stack, and should
    be scanned by the GC. *)
