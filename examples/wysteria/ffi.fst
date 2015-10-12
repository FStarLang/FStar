(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.OrdSet --admit_fsi Prins --admit_fsi FStar.String --admit_fsi FStar.IO;
    other-files:set.fsi heap.fst st.fst all.fst string.fsi ordset.fsi prins.fsi io.fsti;
 --*)

module FFI

open OrdSet
open Prins

//----- prins interface ---//

val empty: eprins
let empty = OrdSet.empty #prin #p_cmp

val mem: p:prin -> s:eprins -> Tot (b:bool{b ==> not (s = empty)})
let mem p s = OrdSet.mem p s

val singleton: p:prin -> Pure prins (True)
                                   (fun s -> s =!= empty /\ (forall p'. mem p' s = (p = p')))
let singleton p =
  let s = OrdSet.singleton p in
  let _ = assert (not (s = empty)) in
  s

val subset: s1:eprins -> s2:eprins
            -> Pure bool (True) (fun b -> b <==> (forall p. mem p s1 ==> mem p s2))
let subset s1 s2 = OrdSet.subset s1 s2

val union: s1:eprins -> s2:eprins
           -> Pure eprins (True) (fun s -> ((s1 =!= empty \/ s2 =!= empty) ==> s =!= empty) /\
                                    (forall p. mem p s = (mem p s1 || mem p s2)))
let union s1 s2 =
  let s = OrdSet.union s1 s2 in
  let _ = assert (s = empty <==> (s1 = empty /\ s2 = empty)) in
  s

val size: s:eprins -> Pure nat (True) (fun n -> n = 0 <==> s = empty)
let size s = OrdSet.size s

val choose: s:prins -> Pure prin (True) (fun p -> b2t (mem p s))
let choose s = Some.v (OrdSet.choose s)

val remove: p:prin -> s:prins
            -> Pure eprins (b2t (mem p s))
	                  (fun s' -> (forall p'. ((mem p' s /\ p' =!= p) ==> mem p' s') /\
                                         (mem p' s' ==> mem p' s))             /\
                                         not (mem p s')                       /\
                                         size s' = size s - 1)
let remove p s = OrdSet.remove p s

val eq_lemma: s1:eprins -> s2:eprins
              -> Lemma (requires (forall p. mem p s1 = mem p s2)) (ensures (s1 = s2))
	        [SMTPat (s1 = s2)]
let eq_lemma s1 s2 = ()

//----- prins interface -----//

//----- IO interface -----//

val read_int: unit -> int
let read_int x = FStar.IO.input_int ()

val print_string: string -> unit
let print_string s = FStar.IO.print_string s

val print_int: int -> unit
let print_int n = print_string (string_of_int n)

val print_bool: bool -> unit
let print_bool b = print_string (string_of_bool b)

val print_newline: unit -> unit
let print_newline _ = FStar.IO.print_newline ()

//----- IO interface -----//

//----- slice id -----//

val slice_id: prin -> 'a -> Tot 'a
let slice_id p c = c

val compose_ids: 'a -> 'a -> Tot 'a
let compose_ids x _ = x

val slice_id_sps: prin -> 'a -> Tot 'a
let slice_id_sps p x = x

//----- slice id -----//
