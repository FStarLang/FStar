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

val append_length: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures (length (append l1 l2) = length l1 + length l2))
let rec append_length l1 l2 = match l1 with
  | [] -> ()
  | hd::tl -> append_length tl l2

(* following are the loops from the paper *)
val for_each_bob:
  x:Box int alice_s -> l:list (Box int bob_s)
  -> Wys (list bool) (pre (Mode Par ab)) (fun _ r _ -> b2t (length r = length l))
let rec for_each_bob x l =
  if l = mk_nil () then mk_nil ()
  else
    let y = hd_of_cons l in
    let g:unit -> Wys bool (pre (Mode Sec ab)) post =
      fun _ -> unbox_s x = unbox_s y
    in
    let b = as_sec ab g in
    mk_cons b (for_each_bob x (tl_of_cons l))

val for_each_alice:
  la:list (Box int alice_s) -> lb:list (Box int bob_s)
  -> Wys (list bool) (pre (Mode Par ab)) (fun _ r _ -> b2t (length r = length la * length lb))
let rec for_each_alice la lb =
  if la = mk_nil () then mk_nil ()
  else
    let l1 = for_each_bob (hd_of_cons la) lb in
    let l2 = for_each_alice (tl_of_cons la) lb in
    append_length l1 l2;
    let _ = admitP (b2t ((length la - 1) * length lb = (length la * length lb) - length lb)) in
    append l1 l2

(* row function, alice will use it to compute intersection *)
val row:
  la:list int -> lenb:nat -> bindex:nat{bindex < lenb}
  -> matrix:list bool{length matrix = (length la * lenb) - bindex}
  -> Tot (list int) (decreases matrix)
let rec row la lenb bindex matrix =
  if is_Nil matrix then mk_nil ()
  else
    let b = hd_of_cons matrix in
    let tl = tl_of_cons matrix in
    let rest =
      let bindex' = bindex + 1 in
      if bindex' = lenb then
	let _ = admitP (b2t ((length la * lenb) - (lenb - 1) = ((length la - 1) * lenb) + 1)) in
	row (tl_of_cons la) lenb 0 tl
      else	
	row la lenb bindex' tl
    in
    if b then mk_cons (hd_of_cons la) rest
    else rest

(* col function, bob will use it to compute intersection *)
val col:
  lb:list int{is_Cons lb} -> lbc:list int{is_Cons lbc}
  -> matrix:list bool
  -> Tot (list int) (decreases matrix)
let rec col lb lbc matrix =
  if is_Nil matrix then mk_nil ()
  else
    let b = hd_of_cons matrix in
    let tl = tl_of_cons matrix in
    let lbc_hd = hd_of_cons lbc in
    let lbc_tl = tl_of_cons lbc in
    let rest =
      if is_Nil lbc_tl then
	col lb lb tl
	else col lb lbc_tl tl
    in
    if b then mk_cons lbc_hd rest else rest

val for_each_bob_opt:
  x:Box int alice_s -> l:list (Box int bob_s)
  -> Wys (list (Box int bob_s) * list bool) (pre (Mode Par ab)) post
let rec for_each_bob_opt x l =
  if l = mk_nil () then mk_tuple (mk_nil ()) (mk_nil ())
  else
    let y = hd_of_cons l in
    let g:unit -> Wys bool (pre (Mode Sec ab)) post =
      fun _ -> unbox_s x = unbox_s y
    in
    let b = as_sec ab g in
    if b then mk_tuple (tl_of_cons l) (mk_cons b (mk_nil ()))
    else
      let tup = for_each_bob_opt x (tl_of_cons l) in
      mk_tuple (mk_cons y (fst tup)) (mk_cons false (snd tup))

val for_each_alice_opt:
  la:list (Box int alice_s) -> lb:list (Box int bob_s) -> Wys (list bool) (pre (Mode Par ab)) post
let rec for_each_alice_opt la lb =
  if la = mk_nil () then mk_nil ()
  else
    let tup = for_each_bob_opt (hd_of_cons la) lb in
    append (snd tup) (for_each_alice_opt (tl_of_cons la) (fst tup))

val row_opt:
  la:list int -> lenb:nat -> bindex:nat
  -> matrix:list bool
  -> s:list nat
  -> Dv (list int) (decreases matrix)
let rec row_opt la lenb bindex matrix s =
  if is_Nil matrix then mk_nil ()
  else
    if not (lmem bindex s) then
      (* the bindex has not been skipped *)
      let b = hd_of_cons matrix in
      let tl = tl_of_cons matrix in
      if b then (* matched *)
	let _ = admitP (b2t (is_Cons la)) in
	let rest = row_opt (tl_of_cons la) lenb 0 tl (mk_cons bindex s) in
	mk_cons (hd_of_cons la) rest
      else
	(* no match *)
	let bindex' = bindex + 1 in
	if bindex' = lenb then
	  let _ = admitP (b2t (is_Cons la)) in
	  row_opt (tl_of_cons la) lenb 0 tl s
	else	
	  row_opt la lenb bindex' tl s
    else
      (* bindex was skipped *)
      let bindex' = bindex + 1 in
      if bindex' = lenb then
	let _ = admitP (b2t (is_Cons la)) in
	row_opt (tl_of_cons la) lenb 0 matrix s
      else	
	row_opt la lenb bindex' matrix s

val col_opt:
  lb:list int -> lbc:list int -> matrix:list bool -> matched:list int
  -> Dv (list int)
let rec col_opt lb lbc matrix matched =
  if is_Nil matrix then mk_nil ()
  else
    let _ = admitP (b2t (is_Cons lbc)) in
    (* this element is being skipped in the matrix *)
    if lmem (hd_of_cons lbc) matched then
      let lbc_tl = tl_of_cons lbc in
      if is_Nil lbc_tl then
	col_opt lb lb matrix matched
      else
	col_opt lb lbc_tl matrix matched
    else
      let b = hd_of_cons matrix in
      let tl = tl_of_cons matrix in

      if b then
	let rest = col_opt lb lb tl (mk_cons (hd_of_cons lbc) matched) in
	mk_cons (hd_of_cons lbc) rest
      else
	let lbc_tl = tl_of_cons lbc in
	if is_Nil lbc_tl then
	  col_opt lb lb tl matched
	else
	  col_opt lb lbc_tl tl matched

val box_list_to_list_box:
  p:prin{mem p ab} -> l:Box (list int) (singleton p) -> len:nat{length (v_of_box l) = len}
  -> Wys (list (Box int (singleton p))) (pre (Mode Par ab)) (fun _ r _ -> b2t (length r = length (v_of_box l)))
let rec box_list_to_list_box p l len =
  if len = 0 then mk_nil ()
  else
    let g:unit -> Wys int (pre (Mode Par (singleton p))) post =
      fun _ -> hd_of_cons (unbox_p l)
    in
    let g':unit -> Wys (list int) (pre (Mode Par (singleton p))) (fun _ r _ -> b2t (r = tl_of_cons (v_of_box l)))  =
      fun _ -> tl_of_cons (unbox_p l)
    in
    let hd = as_par (singleton p) g in
    let tl = as_par (singleton p) g' in
    let rest = box_list_to_list_box p tl (len - 1) in
    mk_cons hd rest

val psi: ps:prins{ps = ab} -> w:Wire (list int) ps -> Wys (Wire (list int) ab) (pre (Mode Par ab)) post
let psi ps w =
  let proj: p:prin{mem p ab} -> unit -> Wys (list int) (pre (Mode Par (singleton p))) post =
    fun p _ -> projwire_p p w
  in

  (* l1 and l2 are Box (list int) *)
  let l1 = as_par alice_s (proj alice) in
  let l2 = as_par bob_s (proj bob) in

  let len: p:prin -> l:(Box (list int) (singleton p))
           -> unit
	   -> Wys nat (pre (Mode Par (singleton p))) (fun _ r _ -> True /\ r = length (v_of_box l)) =
    fun _ l _ ->
    let l = unbox_p l in
    length l
  in

  (* n1 and n2 are Box int *)
  let n1 = as_par alice_s (len alice l1) in
  let n2 = as_par bob_s (len bob l2) in

  let g: p:prin{p = alice \/ p = bob} -> n:Box int (singleton p)
         -> unit
	 -> Wys int (pre (Mode Sec ab)) (fun _ r _ -> True /\ r = v_of_box n) =
    fun p n _ -> unbox_s n
  in

  (* n1' and n2' are ints *)
  let n1' = as_sec ab (g alice n1) in
  let n2' = as_sec ab (g bob n2) in

  if n2' = 0 then
    let trivial: unit -> Wys (list int) (pre (Mode Par ab)) post =
      fun _ -> mk_nil ()
    in
    mkwire_p ab (as_par ab trivial)
  else
    (* l1' and l2' are list (Box int) *)
    let l1' = box_list_to_list_box alice l1 n1' in
    let l2' = box_list_to_list_box bob l2 n2' in
    let matrix = for_each_alice l1' l2' in

    let get_aout: unit -> Wys (list int) (pre (Mode Par alice_s)) post =
      fun _ ->
      let la = unbox_p l1 in
      row la n2' 0 matrix
    in
    let get_bout: unit -> Wys (list int) (pre (Mode Par bob_s)) post =
      fun _ ->
      let lb = unbox_p l2 in
      col lb lb matrix
    in

    let a_out = as_par alice_s get_aout in
    let b_out = as_par bob_s get_bout in

    let w1 = mkwire_p alice_s a_out in
    let w2 = mkwire_p bob_s b_out in
    concat_wire w1 w2

val psi_opt: ps:prins{ps = ab} -> w:Wire (list int) ps -> Wys (Wire (list int) ab) (pre (Mode Par ab)) post
let psi_opt ps w =
  let proj: p:prin{mem p ab} -> unit -> Wys (list int) (pre (Mode Par (singleton p))) post =
    fun p _ -> projwire_p p w
  in

  (* l1 and l2 are Box (list int) *)
  let l1 = as_par alice_s (proj alice) in
  let l2 = as_par bob_s (proj bob) in

  let len: p:prin -> l:(Box (list int) (singleton p))
           -> unit
	   -> Wys nat (pre (Mode Par (singleton p))) (fun _ r _ -> True /\ r = length (v_of_box l)) =
    fun _ l _ ->
    let l = unbox_p l in
    length l
  in

  (* n1 and n2 are Box int *)
  let n1 = as_par alice_s (len alice l1) in
  let n2 = as_par bob_s (len bob l2) in

  let g: p:prin{p = alice \/ p = bob} -> n:Box int (singleton p)
         -> unit
	 -> Wys int (pre (Mode Sec ab)) (fun _ r _ -> True /\ r = v_of_box n) =
    fun p n _ -> unbox_s n
  in

  (* n1' and n2' are ints *)
  let n1' = as_sec ab (g alice n1) in
  let n2' = as_sec ab (g bob n2) in

  if n2' = 0 then
    let trivial: unit -> Wys (list int) (pre (Mode Par ab)) post =
      fun _ -> mk_nil ()
    in
    mkwire_p ab (as_par ab trivial)
  else
    (* l1' and l2' are list (Box int) *)
    let l1' = box_list_to_list_box alice l1 n1' in
    let l2' = box_list_to_list_box bob l2 n2' in
    let matrix = for_each_alice_opt l1' l2' in

    let get_aout: unit -> Wys (list int) (pre (Mode Par alice_s)) post =
      fun _ ->
      let la = unbox_p l1 in
      row_opt la n2' 0 matrix (mk_nil ())
    in
    let get_bout: unit -> Wys (list int) (pre (Mode Par bob_s)) post =
      fun _ ->
      let lb = unbox_p l2 in
      col_opt lb lb matrix (mk_nil ())
    in

    let a_out = as_par alice_s get_aout in
    let b_out = as_par bob_s get_bout in

    let w1 = mkwire_p alice_s a_out in
    let w2 = mkwire_p bob_s b_out in
    concat_wire w1 w2

val psi_m: l1:Box (list int) alice_s -> l2:Box (list int) bob_s
           -> Wys (list int) (pre (Mode Par ab)) post
let psi_m l1 l2 =
  admitP (b2t (List.length (v_of_box l2) > 0));
  let g: unit
	 -> Wys (list int) (pre (Mode Sec ab)) post =
    fun _ ->
    let x = unbox_s l1 in let y = unbox_s l2 in
    FFI.list_intersect x y
  in

  as_sec ab g

val psi_mono: ps:prins{ps = ab} -> w:Wire (list int) ps -> Wys (Wire (list int) ab) (pre (Mode Par ab)) post
let psi_mono ps w =
  let proj: p:prin{FStar.OrdSet.mem p ab} -> unit -> Wys (list int) (pre (Mode Par (singleton p))) post =
    fun p _ -> projwire_p p w
  in
  let l1 = as_par alice_s (proj alice) in
  let l2 = as_par bob_s (proj bob) in
  let l = psi_m l1 l2 in
  let trivial: unit -> Wys (list int) (pre (Mode Par ab)) post =
    fun _ -> l
  in
  mkwire_p ab (as_par ab trivial)




(* val ts_for_each_bob_opt: int -> list int -> Tot (list bool * list int) *)
(* let rec ts_for_each_bob_opt x l = match l with *)
(*   | []   -> [], [] *)
(*   | y::tl -> *)
(*     if x = y then [true], tl *)
(*     else *)
(*       let t', l' = ts_for_each_bob_opt x tl in *)
(*       false::t', y::l' *)

(* val ts_for_each_alice_opt: list int -> list int -> Tot (list bool) *)
(* let rec ts_for_each_alice_opt la lb = match la with *)
(*   | []   -> [] *)
(*   | x::tl -> *)
(*     let t1, lb' = ts_for_each_bob_opt x lb in *)
(*     let t2 = ts_for_each_alice_opt tl lb' in *)
(*     append t1 t2 *)

(* val t_for_each_bob_opt: int -> list int -> Tot (btrace * list int) *)
(* let rec t_for_each_bob_opt x l = match l with *)
(*   | []   -> [], [] *)
(*   | y::tl -> *)
(*     if x = y then [TMsg #bool true], tl *)
(*     else *)
(*       let t', l' = t_for_each_bob_opt x tl in *)
(*       (TMsg #bool false)::t', y::l' *)

(* val t_for_each_alice_opt: list int -> list int -> Tot btrace *)
(* let rec t_for_each_alice_opt la lb = match la with *)
(*   | []   -> [] *)
(*   | x::tl -> *)
(*     let t1, lb' = t_for_each_bob_opt x lb in *)
(*     let t2 = t_for_each_alice_opt tl lb' in *)
(*     append_btrace_lemma t1 t2; *)
(*     append t1 t2 *)

(* val for_each_bob_opt: *)
(*   x:Box int alice_s -> l:list (Box int bob_s) *)
(*   -> Wys (list bool * list (Box int bob_s)) (pre (Mode Par ab)) *)
(*         (fun _ r t -> t = fst (t_for_each_bob_opt (v_of_box x) (no_box_list bob l)) /\ *)
(* 	           no_box_list bob (snd r) = snd (t_for_each_bob_opt (v_of_box x) (no_box_list bob l))) *)
(* let rec for_each_bob_opt x l = *)
(*   if l = mk_nil () then mk_nil (), mk_nil () *)
(*   else *)
(*     let y = hd_of_cons l in *)
(*     let g:unit -> Wys bool (pre (Mode Sec ab)) (fun _ r t -> r = (v_of_box x = v_of_box y) /\ t = []) = *)
(*       fun _ -> unbox_s x = unbox_s y *)
(*     in *)
(*     let b = as_sec ab g in *)
(*     if b then [true], tl_of_cons l *)
(*     else *)
(*       let t', l' = for_each_bob_opt x (tl_of_cons l) in *)
(*       false::t', y::l' *)

(* val for_each_alice_opt: *)
(*   la:list (Box int alice_s) -> lb:list (Box int bob_s) *)
(*   -> Wys (list bool) (pre (Mode Par ab)) (fun _ _ t -> b2t (t = t_for_each_alice_opt (no_box_list alice la) (no_box_list bob lb))) *)
(* let rec for_each_alice_opt la lb = *)
(*   if la = mk_nil () then mk_nil () *)
(*   else *)
(*     let r, lb' = for_each_bob_opt (hd_of_cons la) lb in *)
(*     append r (for_each_alice_opt (tl_of_cons la) lb') *)











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
