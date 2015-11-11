(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst listTot.fst st2.fst ordset.fsi ../prins.fsi ffi.fst wysteria.fsi
 --*)

module SMC

open FStar.List.Tot
open Prins
open FFI
open Wysteria

let num_cards = 52

(* return [0; 1; ...; 52] *)
val get_unshuffled_deck: nat -> list nat -> Tot (list nat)
let rec get_unshuffled_deck n l =
  if n = 0 then mk_cons n l else get_unshuffled_deck (n - 1) (mk_cons n l)

(* return the list same as input but with nth element (zero-indexed) replaced with x *)
val replace_nth_with: l:list nat -> n:nat{length l > n} -> x:nat
                      -> Tot (r:list nat{length r = length l})
let rec replace_nth_with l n x =
  if n = 0 then mk_cons x (tl_of_cons l)
  else mk_cons (hd_of_cons l) (replace_nth_with (tl_of_cons l) (n - 1) x)

val nth: l:list nat -> n:nat{length l > n} -> Tot nat
let rec nth l n =
  if n = 0 then hd_of_cons l else nth (tl_of_cons l) (n - 1)

(* get a randon number between 0 and (n - 1) *)
assume val rand: n:pos -> Tot (r:nat{r < n})

(*
 * the main algorithm: https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle#The_modern_algorithm
 * deck is the already shuffled deck, and remaining is the remaining cards
 * pick a random card from remaining (say from position n),
 * add it to the shuffled deck, and
 * replace the nth card in remaining with hd remaining
 *)
val get_deck: deck:list nat -> remaining:list nat
              -> Tot (list nat) (decreases (length remaining))
let rec get_deck deck remaining =
  if is_Nil remaining then deck
  else
    let r = rand (length remaining) in  // a random index in the remaining list
    let e = nth remaining r in  // the rth element in the list
    let new_deck = mk_cons e deck in  // add to the deck
    if r = 0 then get_deck new_deck (tl_of_cons remaining) // if r was 0, no replacement required
    else get_deck new_deck (replace_nth_with (tl_of_cons remaining) (r - 1) (hd_of_cons remaining))

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

type pre_with (m:mode) (t:Type) = fun m0 -> m0 = m /\ t

let to_s2 p1 p2 = union (singleton p1) (singleton p2)

val deck_to_int_list: list nat -> Tot (list int)
let rec deck_to_int_list l =
  if is_Nil l then mk_nil () else mk_cons (hd_of_cons l) (deck_to_int_list (tl_of_cons l))
  
val shuffle_deck: ps:prins -> unit -> Wys (list nat * nat) (pre (Mode Par ps)) post
let shuffle_deck ps _ =
  let g:unit -> Wys (list nat * nat) (pre (Mode Sec ps)) post =
    fun _ ->
    let d = get_deck (mk_nil ()) (get_unshuffled_deck (num_cards - 1) (mk_nil ())) in
    mk_tuple d 0
  in
  as_sec ps g

;;

let d = main ab (shuffle_deck ab) in
print_int_list (deck_to_int_list (fst d))
