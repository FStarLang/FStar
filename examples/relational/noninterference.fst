(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/st2.fst
  --*)

module NonInterference

open Comp
open Heap

assume val high : ref 'a -> Tot bool
let low x = not (high x)

type ni = unit -> 
          ST2 (unit * unit)
              (requires (fun h2 -> (forall (x:ref int). low x ==> 
                                            sel (fst h2) x = sel (snd h2) x)))
              (ensures  (fun _ _ h2 -> (forall (x:ref int). low x ==> 
                                            sel (fst h2) x = sel (snd h2) x)))

assume val new_low : unit -> x:ref int{low x}
assume val new_high : unit -> x:ref int{high x}
 
let a = new_low ()
let b = new_high ()
let c = new_high ()
let d = new_low ()

let test1 () = (if !b = 0 then
                 a := 2
               else 
                 a := 1); 
               a := 0

val test1_ni : ni
let test1_ni () = compose2 test1 test1 () () 
