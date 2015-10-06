(*
   Copyright 2015 Michael Hicks, Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(** Stack operations

    The functions here are for allocating Caml values on a
    manually-managed, growable stack.

    This library is unsafe. To avoid memory errors, programs must
    satisfy two constraints:

    1) No data allocated on a frame, and no data in the OCaml heap
    reachable from the frame, will be used by the program after the
    frame is popped. (To do so would result in a dangling pointer
    dereference.)

    2) No pointers into the OCaml heap will be installed by mutation
    of a stack-allocated object UNLESS the location that was mutated
    was initially registered, when created, as possibly
    pointer-containing.  (To do so would create a GC root into the
    OCaml heap that is not tracked by the stack implementation.)
*)

external push_frame : unit -> unit = "stack_push_frame";;
(** [Camlstack.push_frame ()] pushes a frame onto the stack which will
    grow as things are allocated. *)

external pop_frame : unit -> unit = "stack_pop_frame";;
(** Pops the topmost stackframe. This means that all of that data is
    now free, and the program must take care not to access it.
    In addition, Caml heap data reachable only from that data will be
    subsequently GCed.
    Raise [Failure "Camlstack.pop_frame"] if the stack has no frames. *)

external set_page_wosize : int -> unit = "stack_set_page_wosize";;
(** [Camlstack.set_page_wosize w] sets the default stack page
    size to [w] words. *)

external is_on_stack : 'a -> bool = "caml_is_stack_pointer";;
(** [Camlstack.is_on_stack v] returns true if [v] is a boxed value allocated
    on the stack (though it may contain pointers into the heap). *)

external mkpair : 'a -> 'b -> 'a*'b = "stack_mkpair";;
(** [Camlstack.mkpair x y] allocates a pair (x,y) on the stack.
    Raise [Failure "Camlstack.mkpair"] if the stack has no frames. *)

external mktuple3 : 'a -> 'b -> 'c -> 'a*'b*'c = "stack_mktuple3";;
(** [Camlstack.mktuple3 x y z] allocates a triple (x,y,z) on the stack.
    Raise [Failure "Camlstack.mktuple3"] if the stack has no frames. *)

external mktuple4 : 'a -> 'b -> 'c -> 'd -> 'a*'b*'c*'d = "stack_mktuple4";;
(** [Camlstack.mktuple4 x y z w] allocates a pair (x,y,z,w) on the stack.
    Raise [Failure "Camlstack.mktuple4"] if the stack has no frames. *)

external mktuple5 : 'a -> 'b -> 'c -> 'd -> 'e -> 'a*'b*'c*'d*'e = "stack_mktuple5";;
(** [Camlstack.mktuple5 x y z w s] allocates a pair (x,y,z,w,s) on the stack.
    Raise [Failure "Camlstack.mktuple5"] if the stack has no frames. *)

external cons: 'a -> 'a list -> 'a list = "stack_mkpair";;
(** [Camlstack.cons x y] allocates a cons cell [x::y] on the stack.
    Raise [Failure "Camlstack.cons"] if the stack has no frames. *)

external concat: string -> string -> string = "stack_concat" "noalloc";;
(** [Camlstack.concat s1 s2] allocates a string of size len(s1) + len(s2) on the
    stack, then write the concatenation of [s1] and [s2] into it. Raises
    [Failure "Camlstack.concat"] if the stack has no frames.] *)

external mkref: 'a -> 'a ref = "stack_mkref";;
(** [Camlstack.mkref x] allocates a ref cell on the stack,
    initializing it with x. Assumes that [x] may point to the
    OCaml heap, and so will scan it.
    Raise [Failure "Camlstack.cons"] if the stack has no frames. *)

external mkref_noscan: 'a -> 'a ref = "stack_mkref_noscan";;
(** [Camlstack.mkref x] allocates a ref cell on the stack,
    initializing it with x. Assumes [x] will never point to the OCaml
    heap, and so never needs to be scanned.
    Raise [Failure "Camlstack.cons"] if the stack has no frames. *)

external mkbytes : int -> bytes = "stack_mkbytes";;
(** [Camlstack.mkbytes n] constructs a byte array of length n.
    The contents are uninitialized. Note that a byte array can be
    coerced to a string by Bytes.unsafe_to_string (but only after
    it's fully initialized and won't change anymore).
    Raise [Failure "Camlstack.mkbytes"] if the stack has no frames.
    Raise [Invalid_argument "Camlstack.mkbytes"] if [n] is non-positive. *)

external mkarray : int -> 'a -> 'a array = "stack_mkarray";;
(** [Camlstack.mkarray n v] allocates an array of length [n] with each
    element initialized to [v].
    Raise [Failure "Camlstack.mkarray"] if the stack has no frames.
    Raise [Invalid_argument "Camlstack.mkarray"] if [n] is non-positive,
    or if you try to make an array of floats (for which you should use
    mkarray_noscan instead). *)

external mkarray_noscan : int -> 'a -> 'a array = "stack_mkarray_noscan";;
(** [Camlstack.mkarray_prim n v] allocates an array of length [n] with each
    element initialized to [v]. Use this when the values 'a that you install
    in the array are either primitives, or they are pointers to the stack, and
    you can be sure that you will never mutate the array to point to the heap.
    Raise [Failure "Camlstack.mkarray"] if the stack has no frames.
    Raise [Invalid_argument "Camlstack.mkarray"] if [n] is non-positive
    or [v] is boxed and not a float, and not a pointer to the stack. *)

(** DEBUGGING **)

external print_mask : unit -> unit = "print_mask";;
(** [Camlstack.print_mask ()] is a debugging function. It prints
    a list of Caml heap pointers that occur on the stack, and should
    be scanned by the GC. *)

external inspect : 'a -> unit = "inspect";;
(** [Camlstack.inspect x] is a debugging function. It prints
    out the structure of the run-time value x that is passed to it. *)
