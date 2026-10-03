module InstantiatedSpecArgs

(* A precondition is a trailing implicit [squash] binder, and extraction drops
   both the binder and the argument that matches it.  The binder is only visible
   once the head's type has been *instantiated*, though: here [identity]'s own
   type has just [#a] and [x], and the [squash (x >= 0)] binder appears only
   after [a] is fixed.  Walking the uninstantiated type left the unit argument
   in the extracted application, which failed to typecheck in ML with Error 76,
   "Ill-typed application ... remaining args are [((), #)]". *)

let identity (#a:Type) (x:a) : a = x

let f (x:int) : Pure int (requires x >= 0) (ensures fun y -> y == x) = x

let caller () : int =
  identity
    #(x:int -> Pure int (requires x >= 0) (ensures fun y -> y == x))
    f 1
