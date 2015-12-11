(*--build-config
    options:--admit_fsi FStar.Set --print_implicits --log_types;
    other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
--*)

module M

val f: f:(unit -> Tot unit){True}
let f () = ()

val g: f:(unit -> Tot unit){True} -> Tot (u:unit{f () = ()})
let g f = ()

val v: u:unit{f () = ()}
let v = g f

