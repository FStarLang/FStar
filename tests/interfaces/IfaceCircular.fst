module IfaceCircular

(* Issue #4390. The interface of this module is

     val one : False
     let two : False = one

   i.e. [two] is justified by the very [val one] that this implementation has
   to discharge. If [two] were in scope here, this module would prove [False].

   [two] must therefore stay hidden until [one] has been implemented, which the
   expect_failure below pins down (133 is the "name not in scope here" error). *)
[@@expect_failure [133]]
let one : False = two

(* The same thing again, unguarded, so that the recorded output of this test
   also exercises the diagnostic itself. Either way [one] is never implemented,
   so the module is additionally rejected with error 98. *)
let one : False = two
