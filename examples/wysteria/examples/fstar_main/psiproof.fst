(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst listTot.fst listproperties.fst st2.fst ordset.fsi ../../prins.fsi ../ffi.fst ../wysteria.fsi
 --*)

(* PSI *)

module SMC

open FStar.List
open Prins
open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

type pre_with (m:mode) (t:Type) = fun m0 -> m0 = m /\ t

(* this is saying that the trace only consists of TMsg (no scopes) and all boolean values *)
type btrace_t (t:trace) = forall x. List.mem x t ==> (is_TMsg x /\ TMsg.a x == bool)

type btrace = t:trace{btrace_t t}

val tl_btrace: b:btrace -> Lemma (requires (is_Cons b)) (ensures (is_Cons b /\ btrace_t (Cons.tl b)))
let tl_btrace b = ()

val append_btrace_lemma: b1:btrace -> b2:btrace -> Lemma (requires (true)) (ensures (btrace_t (append b1 b2)))
let rec append_btrace_lemma b1 b2 = match b1 with
  | []   -> ()
  | _::tl -> append_btrace_lemma tl b2

(* trace function for each bob *)
val t_for_each_bob: int -> list int -> Tot btrace
let rec t_for_each_bob x l = match l with
  | []   -> []
  | y::tl -> TMsg #bool (x = y)::t_for_each_bob x tl

(* trace function for each alice *)
val t_for_each_alice: list int -> list int -> Tot btrace
let rec t_for_each_alice la lb = match la with
  | []   -> []
  | x::tl ->
    let t1 = t_for_each_bob x lb in
    let t2 = t_for_each_alice tl lb in
    append_btrace_lemma t1 t2;
    append t1 t2

(*
 * the trace contains things like TMsg, hard to reason with
 * lets instead prove that there exists a bijection from btrace to list bool
 * and then reason with that
 *)

val convert_btrace_to_simple_trace: btrace -> Tot (list bool)
let rec convert_btrace_to_simple_trace t = match t with
  | []        -> []
  | TMsg 'a b::tl -> b::(convert_btrace_to_simple_trace tl)

val convert_simple_trace_to_btrace: list bool -> Tot btrace
let rec convert_simple_trace_to_btrace t = match t with
  | []   -> []
  | b::tl -> (TMsg #bool b)::convert_simple_trace_to_btrace tl

val conversions_are_inverse:
  y:list bool -> Lemma (requires (True))
                (ensures (convert_btrace_to_simple_trace (convert_simple_trace_to_btrace y) = y))
let rec conversions_are_inverse y = match y with
  | []     -> ()
  | x1::tl1 -> conversions_are_inverse tl1

opaque type surjection_witness (#a:Type) (x:a) = True

opaque type injection (#a:Type) (#b:Type) (f:a -> Tot b) = 
  (forall (x:a) (y:a). f x = f y ==> x = y)
opaque type surjection (#a:Type)(#b:Type) (f:a -> Tot b) = 
  (forall (y:b). (exists (x:a). f x = y))
opaque type bijection (#a:Type) (#b:Type) (f:a -> Tot b) = 
  injection f /\ surjection f

(* prove btrace to simple trace is injection *)
val btrace_to_simple_trace_is_injection:
  x:btrace -> y:btrace
  -> Lemma
    (requires (convert_btrace_to_simple_trace x = convert_btrace_to_simple_trace y))
    (ensures (x = y))
let rec btrace_to_simple_trace_is_injection x y = match x, y with
  | x1::tl1, x2::tl2 -> btrace_to_simple_trace_is_injection tl1 tl2
  | _ -> ()

(* prove btrace to simple trace is surjection *)
val btrace_to_simple_trace_is_surjection:
  y:list bool -> Lemma (requires (True))
                      (ensures (exists (x:btrace).{:pattern (surjection_witness x)}
		                  convert_btrace_to_simple_trace x = y))
let btrace_to_simple_trace_is_surjection y =
  conversions_are_inverse y;
  cut (surjection_witness (convert_simple_trace_to_btrace y))

(*
 * so, now we will write for_each_alice and for_each_bob functions
 * that return boolean
 *)

val ts_for_each_bob: int -> list int -> Tot (list bool)
let rec ts_for_each_bob x l = match l with
  | []   -> []
  | y::tl -> (x = y)::ts_for_each_bob x tl

val ts_for_each_alice: list int -> list int -> Tot (list bool)
let rec ts_for_each_alice la lb = match la with
  | []   -> []
  | x::tl ->
    let t1 = ts_for_each_bob x lb in
    let t2 = ts_for_each_alice tl lb in
    append t1 t2

(* prove that t_for_each_bob and ts_for_each_alice are related *)

val t_and_ts_append_lemma:
  l1:btrace -> l2:btrace
  -> Lemma (requires (True)) (ensures (btrace_t (append l1 l2) /\
                                   convert_btrace_to_simple_trace (append l1 l2) =
                                   append (convert_btrace_to_simple_trace l1)
				          (convert_btrace_to_simple_trace l2)))
let rec t_and_ts_append_lemma l1 l2 =
  append_btrace_lemma l1 l2;
  match l1 with
    | []   -> ()
    | _::tl -> t_and_ts_append_lemma tl l2

val t_and_ts_for_each_bob_lemma:
  x:int -> l:list int
  -> Lemma (requires (True))
          (ensures (convert_btrace_to_simple_trace (t_for_each_bob x l) =
	            ts_for_each_bob x l))
let rec t_and_ts_for_each_bob_lemma x l = match l with
  | []   -> ()
  | y::tl -> t_and_ts_for_each_bob_lemma x tl

val t_and_ts_for_each_alice_lemma:
  la:list int -> lb:list int
  -> Lemma (requires (True))
          (ensures (convert_btrace_to_simple_trace (t_for_each_alice la lb) =
	            ts_for_each_alice la lb))

let rec t_and_ts_for_each_alice_lemma la lb = match la with
  | []   -> ()
  | x::tl ->
    let t1 = t_for_each_bob x lb in
    let t2 = t_for_each_alice tl lb in
    t_and_ts_append_lemma t1 t2;
    t_and_ts_for_each_bob_lemma x lb;
    t_and_ts_for_each_alice_lemma tl lb


(* NOW, we would just reason with ts_for_each_bob and ts_for_each_alice *)
val mem: int -> list int -> Tot bool
let rec mem x l = match l with
  | []   -> false
  | y::tl -> x = y || mem x tl

val intersect: list int -> list int -> Tot (list int)
let rec intersect l1 l2 = match l1 with
  | []    -> []
  | x::tl1 -> if mem x l2 then x::(intersect tl1 l2) else intersect tl1 l2

val distinct: list int -> Tot bool
let rec distinct l = match l with
  | []     -> true
  | x::tl   -> not (mem x tl) && distinct tl

val num_true: l:list bool -> Tot nat
let rec num_true l = match l with
  | [] -> 0
  | x::tl -> if x then 1 + (num_true tl) else num_true tl

val ts_for_each_bob_num_true_lemma:
  x:int -> l:list int{distinct l}
  -> Lemma (requires (True))
          (ensures (length (ts_for_each_bob x l) = length l /\
                    (mem x l       ==> num_true (ts_for_each_bob x l) = 1) /\
                    (not (mem x l) ==> num_true (ts_for_each_bob x l) = 0)))
let rec ts_for_each_bob_num_true_lemma x l = match l with
  | [] -> ()
  | y::tl -> ts_for_each_bob_num_true_lemma x tl

val num_true_append_lemma:
  l1:list bool -> l2:list bool
  -> Lemma (requires (True)) (ensures (num_true (append l1 l2) = num_true l1 + num_true l2))
let rec num_true_append_lemma l1 l2 = match l1 with
  | [] -> ()
  | _::tl -> num_true_append_lemma tl l2

val length_append_lemma:
  l1:list 'a -> l2:list 'a
  -> Lemma (requires (True)) (ensures (length (append l1 l2) = length l1 + length l2))
let rec length_append_lemma l1 l2 = match l1 with
  | [] -> ()
  | _::tl -> length_append_lemma tl l2

val ts_for_each_alice_length_lemma:
  la:list int{distinct la} -> lb:list int{distinct lb}
  -> Lemma (length (ts_for_each_alice la lb) = length la * length lb)
let rec ts_for_each_alice_length_lemma la lb = match la with
  | [] -> ()
  | x::tl -> 
    let t1 = ts_for_each_bob x lb in
    let t2 = ts_for_each_alice tl lb in
    ts_for_each_alice_length_lemma tl lb;
    ts_for_each_bob_num_true_lemma x lb;
    length_append_lemma t1 t2;
    let _ = assert (length t1 = length lb) in
    let _ = assert (length t2 = (length la - 1) * length lb) in
    let _ = assert (length (append t1 t2) = length lb + ((length la - 1) * length lb)) in
    admit () (*TODO: FIXME: trouble reasoning with multiply ? *)

val ts_for_each_alice_num_true_lemma:
  la:list int{distinct la} -> lb:list int{distinct lb}
  -> Lemma (num_true (ts_for_each_alice la lb) = length (intersect la lb))
let rec ts_for_each_alice_num_true_lemma la lb = match la with
  | [] -> ()
  | x::tl ->
    ts_for_each_bob_num_true_lemma x lb; ts_for_each_alice_num_true_lemma tl lb;
    let t1 = ts_for_each_bob x lb in
    let t2 = ts_for_each_alice tl lb in
    num_true_append_lemma t1 t2

opaque type permutation (l1:list bool) (l2:list bool) = length l1 = length l2 /\ num_true l1 = num_true l2

(* Security proof for unoptimized trace *)
val unoptimized_psi_is_secure:
  la:list int -> lb:list int -> la':list int -> lb':list int
  -> Lemma (requires (distinct la /\ distinct lb /\ distinct la' /\ distinct lb' /\
                     length la = length la' /\ length lb = length lb' /\
                     intersect la lb = intersect la' lb'))
	  (ensures (permutation (ts_for_each_alice la lb)  (ts_for_each_alice la' lb')))
let unoptimized_psi_is_secure la lb la' lb' =
  ts_for_each_alice_length_lemma la lb;
  ts_for_each_alice_length_lemma la' lb';
  ts_for_each_alice_num_true_lemma la lb;
  ts_for_each_alice_num_true_lemma la' lb'

val no_box_list: p:prin -> list (Box int (singleton p)) -> GTot (list int)
let rec no_box_list p l = match l with
  | []   -> []
  | x::tl -> v_of_box x::no_box_list p tl

val for_each_bob:
  x:Box int alice_s -> l:list (Box int bob_s)
  -> Wys (list bool) (pre (Mode Par ab)) (fun _ _ t -> b2t (t = t_for_each_bob (v_of_box x) (no_box_list bob l)))
let rec for_each_bob x l =
  if l = mk_nil () then mk_nil ()
  else
    let y = hd_of_cons l in
    let g:unit -> Wys bool (pre (Mode Sec ab)) (fun _ r t -> r = (v_of_box x = v_of_box y) /\ t = []) =
      fun _ -> unbox_s x = unbox_s y
    in
    let b = as_sec ab g in
    b::(for_each_bob x (tl_of_cons l))

val for_each_alice:
  la:list (Box int alice_s) -> lb:list (Box int bob_s)
  -> Wys (list bool) (pre (Mode Par ab)) (fun _ _ t -> b2t (t = t_for_each_alice (no_box_list alice la) (no_box_list bob lb)))
let rec for_each_alice la lb =
  if la = mk_nil () then mk_nil ()
  else
    append (for_each_bob (hd_of_cons la) lb) (for_each_alice (tl_of_cons la) lb)

val ts_for_each_bob_opt: int -> list int -> Tot (list bool * list int)
let rec ts_for_each_bob_opt x l = match l with
  | []   -> [], []
  | y::tl ->
    if x = y then [true], tl
    else
      let t', l' = ts_for_each_bob_opt x tl in
      false::t', y::l'

val ts_for_each_alice_opt: list int -> list int -> Tot (list bool)
let rec ts_for_each_alice_opt la lb = match la with
  | []   -> []
  | x::tl ->
    let t1, lb' = ts_for_each_bob_opt x lb in
    let t2 = ts_for_each_alice_opt tl lb' in
    append t1 t2

val t_for_each_bob_opt: int -> list int -> Tot (btrace * list int)
let rec t_for_each_bob_opt x l = match l with
  | []   -> [], []
  | y::tl ->
    if x = y then [TMsg #bool true], tl
    else
      let t', l' = t_for_each_bob_opt x tl in
      (TMsg #bool false)::t', y::l'

val t_for_each_alice_opt: list int -> list int -> Tot btrace
let rec t_for_each_alice_opt la lb = match la with
  | []   -> []
  | x::tl ->
    let t1, lb' = t_for_each_bob_opt x lb in
    let t2 = t_for_each_alice_opt tl lb' in
    append_btrace_lemma t1 t2;
    append t1 t2

val for_each_bob_opt:
  x:Box int alice_s -> l:list (Box int bob_s)
  -> Wys (list bool * list (Box int bob_s)) (pre (Mode Par ab))
        (fun _ r t -> t = fst (t_for_each_bob_opt (v_of_box x) (no_box_list bob l)) /\
	           no_box_list bob (snd r) = snd (t_for_each_bob_opt (v_of_box x) (no_box_list bob l)))
let rec for_each_bob_opt x l =
  if l = mk_nil () then mk_nil (), mk_nil ()
  else
    let y = hd_of_cons l in
    let g:unit -> Wys bool (pre (Mode Sec ab)) (fun _ r t -> r = (v_of_box x = v_of_box y) /\ t = []) =
      fun _ -> unbox_s x = unbox_s y
    in
    let b = as_sec ab g in
    if b then [true], tl_of_cons l
    else
      let t', l' = for_each_bob_opt x (tl_of_cons l) in
      false::t', y::l'

val for_each_alice_opt:
  la:list (Box int alice_s) -> lb:list (Box int bob_s)
  -> Wys (list bool) (pre (Mode Par ab)) (fun _ _ t -> b2t (t = t_for_each_alice_opt (no_box_list alice la) (no_box_list bob lb)))
let rec for_each_alice_opt la lb =
  if la = mk_nil () then mk_nil ()
  else
    let r, lb' = for_each_bob_opt (hd_of_cons la) lb in
    append r (for_each_alice_opt (tl_of_cons la) lb')











(* val nth: n:nat -> l:list int{n < length l} -> Tot int *)
(* let rec nth n l = if n = 0 then Cons.hd l else nth (n - 1) (Cons.tl l) *)

(* val trace_mem_helper: p:prin -> int -> l:list int -> n:nat{n <= length l} -> Tot trace (decreases (length l - n)) *)
(* let rec trace_mem_helper p x l n = *)
(*   if n = length l then [] *)
(*   else *)
(*     let y = nth n l in *)
(*     if x = y then TScope (singleton p) []::[TMsg true] else TScope (singleton p) []::TMsg false::(trace_mem_helper p x l (n + 1)) *)

(* val trace_mem: prin -> int -> l:list int -> Tot trace *)
(* let trace_mem p x l = trace_mem_helper p x l 0 *)

(* open FStar.List.Tot *)

(* val trace_helper: p1:prin -> p2:prin -> l1:list int -> l2:list int -> n:nat{n <= length l1} -> Tot trace (decreases (length l1 - n)) *)
(* let rec trace_helper p1 p2 l1 l2 n = *)
(*   if n = length l1 then [] *)
(*   else *)
(*     let x = nth n l1 in *)
(*     append (TScope (singleton p1) []::trace_mem p2 x l2) (trace_helper p1 p2 l1 l2 (n + 1)) *)

(* val trace: p1:prin -> p2:prin -> l1:list int -> l2:list int -> Tot trace *)
(* let trace p1 p2 l1 l2 = trace_helper p1 p2 l1 l2 0 *)

(* val mem: *)
(*   x:Box int alice_s -> l:Box (list int) bob_s -> len:nat{len = length (v_of_box l)} *)
(*   -> n:nat{n <= len} *)
(*   -> Wys bool (pre (Mode Par ab)) (fun _ r t -> b2t (t = trace_mem_helper bob (v_of_box x) (v_of_box l) n)) *)
(* let rec mem x l len n = *)
(*   if n = len then false *)
(*   else *)
(*     let g:unit -> Wys int (pre (Mode Par bob_s)) (fun _ r t -> r = nth n (v_of_box l) /\ t = []) = *)
(*       fun _ -> nth n (unbox_p l) *)
(*     in *)
(*     let y = as_par bob_s g in *)
(*     //let _ = cut (patt (v_of_box x) (v_of_box l) n) in *)
(*     let cmp: unit -> Wys bool (pre (Mode Sec ab)) (fun _ r t -> r = (v_of_box x = v_of_box y) /\ t = []) = *)
(*       fun _ -> unbox_s x = unbox_s y *)
(*     in *)
(*     let b = as_sec ab cmp in *)
(*     if b then b else mem x l len (n + 1) *)

(* val psi_h: *)
(*   l1:Box (list int) alice_s -> l2:Box (list int) bob_s -> len1:nat{len1 = length (v_of_box l1)} -> len2:nat{len2 = length (v_of_box l2)} *)
(*   -> n1:nat{n1 <= len1} *)
(*   -> Wys unit (pre (Mode Par ab)) (fun _ r t -> b2t (t = trace_helper alice bob (v_of_box l1) (v_of_box l2) n1)) *)
(*                                   (\* (n1 = len1 ==> t = []) /\ *\) *)
(*                                   (\* (n1 < len1 ==> t = TScope alice_s []::trace_mem bob (nth n1 (v_of_box l1)) (v_of_box l2))) *\) *)
(* //trace_helper alice bob (v_of_box l1) (v_of_box l2) n1)) *)
(* let rec psi_h l1 l2 len1 len2 n1 = *)
(*   if n1 = len1 then () *)
(*   else *)
(*     let g:unit -> Wys int (pre (Mode Par alice_s)) (fun _ r t -> r = nth n1 (v_of_box l1) /\ t = []) = *)
(*       fun _ -> nth n1 (unbox_p l1) *)
(*     in *)
(*     let g2:unit -> Wys unit (pre (Mode Par ab)) (fun _ _ t -> b2t (t = *)
(*                                       append (TScope alice_s []::trace_mem bob (nth n1 (v_of_box l1)) (v_of_box l2)) *)
(* 				             (trace_helper alice bob (v_of_box l1) (v_of_box l2) (n1 + 1)))) = *)
(*       fun _ ->  *)
(*       let x = as_par alice_s g in *)
(*       let _ = mem x l2 len2 0 in *)
(*       psi_h l1 l2 len1 len2 (n1 + 1) *)
(*     in *)
(*     admit () *)
(*     let b = g2 () in *)
(*     psi_h l1 l2 len1 len2 (n1 + 1) *)
