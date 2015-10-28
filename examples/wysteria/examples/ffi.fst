(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.OrdSet --admit_fsi Prins --admit_fsi FStar.String --admit_fsi FStar.IO;
    other-files:set.fsi heap.fst st.fst all.fst list.fst listTot.fst string.fsi ordset.fsi ../prins.fsi io.fsti;
 --*)

module FFI

open OrdSet
open Prins

//----- prins interface ---//

val empty: unit -> Tot eprins
let empty _ = OrdSet.empty #prin #p_cmp

val mem: p:prin -> s:eprins -> Tot (b:bool{b ==> not (s = empty ())})
let mem p s = OrdSet.mem p s

type Equal: eprins -> eprins -> Type =
  fun eps1 eps2 -> forall x. mem x eps1 = mem x eps2

val singleton: p:prin -> Pure prins (True)
                                   (fun s -> s =!= empty () /\ (forall p'. mem p' s = (p = p')))
let singleton p =
  let s = OrdSet.singleton p in
  let _ = cut (~ (OrdSet.Equal s OrdSet.empty)) in
  s

val subset: s1:eprins -> s2:eprins
            -> Pure bool (True) (fun b -> b <==> (forall p. mem p s1 ==> mem p s2))
let subset s1 s2 = OrdSet.subset s1 s2

val union: s1:eprins -> s2:eprins
           -> Pure eprins (True) (fun s -> ((s1 =!= empty () \/ s2 =!= empty ()) ==> s =!= empty ()) /\
                                    (forall p. mem p s = (mem p s1 || mem p s2)))
let union s1 s2 =
  let s = OrdSet.union s1 s2 in
  let _ = cut (OrdSet.Equal s OrdSet.empty ==> (OrdSet.Equal s1 OrdSet.empty /\ OrdSet.Equal s2 OrdSet.empty)) in
  s

val size: s:eprins -> Pure nat (True) (fun n -> n = 0 <==> s = empty ())
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
              -> Lemma (requires (Equal s1 s2)) (ensures (s1 = s2))
	        [SMTPatT (Equal s1 s2)]
let eq_lemma s1 s2 = OrdSet.eq_lemma s1 s2

//----- prins interface -----//

//----- IO interface -----//

val read_int: unit -> int
let read_int x =
  FStar.IO.print_string "Enter input: ";
  FStar.IO.input_int ()

val read_int_tuple: unit -> (int * int)
let read_int_tuple x =
  let fst = FStar.IO.input_int () in
  let snd = FStar.IO.input_int () in
  (fst, snd)

val read_int_list: unit -> (list int)
let read_int_list _ =
  let rec helper acc =
    let x = FStar.IO.input_int () in
    if x = 0 then acc else helper (x::acc)
  in
  helper []

val print_newline: unit -> unit
let print_newline _ = FStar.IO.print_newline ()

val print_string: string -> unit
let print_string s = FStar.IO.print_string s; print_newline ()

val print_int: int -> unit
let print_int n = print_string (string_of_int n); print_newline ()

val print_bool: bool -> unit
let print_bool b = print_string (string_of_bool b); print_newline ()

val print_int_list: list int -> unit
let print_int_list l =
  let print_string s = FStar.IO.print_string s in
  let print_int i = print_string (string_of_int i) in
  print_string "[ ";
  FStar.List.iter (fun i -> print_int i; print_string "; ") l;
  print_string " ]"; print_newline ()

//----- IO interface -----//

//----- slice id -----//

val slice_id: prin -> 'a -> Tot 'a
let slice_id p c = c

val compose_ids: 'a -> 'a -> Tot 'a
let compose_ids x _ = x

val slice_id_sps: prin -> 'a -> Tot 'a
let slice_id_sps p x = x

//----- slice id -----//

//----- tuple -----//

val mk_tuple: 'a -> 'b -> Tot ('a * 'b)
let mk_tuple x y = (x, y)

val slice_tuple: (prin -> 'a -> Tot 'a) -> (prin -> 'b -> Tot 'b) -> prin -> ('a * 'b) -> Tot ('a * 'b)
let slice_tuple f g p t = (f p (fst t), g p (snd t))

val compose_tuples: ('a -> 'a -> Tot 'a) -> ('b -> 'b -> Tot 'b) -> ('a * 'b) -> ('a * 'b) -> Tot ('a * 'b)
let compose_tuples f g p1 p2 = (f (fst p1) (fst p2), g (snd p1) (snd p2))

val slice_tuple_sps: (prins -> 'a -> Tot 'a) -> (prins -> 'b -> Tot 'b) -> prins -> ('a * 'b) -> Tot ('a * 'b)
let slice_tuple_sps f g ps t = (f ps (fst t), g ps (snd t))

//----- tuple -----//

//----- option -----//

val mk_none: unit -> Tot (option 'a)
let mk_none _ = None

val mk_some: 'a -> Tot (option 'a)
let mk_some x = Some x

val slice_option: (prin -> 'a -> Tot 'a) -> prin -> option 'a -> Tot (option 'a)
let slice_option f p = function
  | None   -> None
  | Some x -> Some (f p x)

val compose_options: ('a -> 'a -> Tot 'a) -> x:option 'a -> y:option 'a{is_Some x <==> is_Some y} -> Tot (option 'a)
let compose_options f x y = match x, y with
  | None, None       -> None
  | Some x', Some y' -> Some (f x' y')

val slice_option_sps: (prins -> 'a -> Tot 'a) -> prins -> option 'a -> Tot (option 'a)
let slice_option_sps f ps = function
  | None   -> None
  | Some x -> Some (f ps x)

//----- option -----//

//----- list -----//

val mk_nil: unit -> Tot (list 'a)
let mk_nil _ = []

val mk_cons: 'a -> list 'a -> Tot (list 'a)
let mk_cons x l = x::l

val slice_list: (prin -> 'a -> Tot 'a) -> p:prin -> l:list 'a -> Tot (list 'a)
let slice_list f p l = FStar.List.Tot.map (f p) l

val compose_lists: ('a -> 'a -> Tot 'a) -> l1:list 'a -> l2:list 'a -> Tot (list 'a)
let rec compose_lists f l1 l2 = match l1, l2 with
  | x1::tl1, x2::tl2 -> (f x1 x2)::(compose_lists f tl1 tl2)
  | _, _           -> []

val slice_list_sps: (prins -> 'a -> Tot 'a) -> prins -> list 'a -> Tot (list 'a)
let slice_list_sps f ps l = FStar.List.Tot.map (f ps) l

val hd_of_cons: l:list 'a{is_Cons l} -> Tot 'a
let hd_of_cons = function
  | hd::_ -> hd

val tl_of_cons: l:list 'a{is_Cons l} -> Tot (list 'a)
let tl_of_cons = function
  | _::tl -> tl

val length: list 'a -> Tot nat
let length l = FStar.List.Tot.length l

//----- list -----//
