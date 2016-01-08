(*--build-config
    options:--admit_fsi OrdSet --admit_fsi OrdMap --admit_fsi Set --admit_fsi Wysteria;
    other-files:FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst ordset.fsi ordmap.fsi FStar.List.fst wysteria.fsi lib.fst
 --*)

module Examples

(*open Set
open Map*)

open OrdSet
open Wysteria
open WLib

type pre  (m:mode)  = fun m0 -> (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) -> True

type pre_with (m:mode) (t:Type) = fun m0 -> m0 = m /\ t

let to_s1 p1       = singleton #prin #p_cmp p1
let to_s2 p1 p2    = union (to_s1 p1) (to_s1 p2)
let to_s3 p1 p2 p3 = union (to_s2 p1 p2) (to_s1 p3)

(**********)


(* millionaire's secure block for any two parties *)
(* only unification, so p1 and p2 can only be inferred if type indices *)
(**********)

(* millionaire's using wires, secure block inlined *)

(* assert (forall s v. const_on s v = restrict s (const v)) fails unless annotated *)

(* return result only to alice *)

val mill7: unit -> Wys (Wire bool) (pre p_ab) post
let mill7 _ =
  let x = as_par alice_s (read #nat) in
  let y = as_par bob_s (read #nat) in

  let g:unit -> Wys (Wire bool) (pre s_ab) post =
    fun _ ->
      let b = (unbox_s x) > (unbox_s y) in
      mkwire_s alice_s b
  in
  as_sec ab g

(**********)

(* generic in number of parties *)

val mill8_sec: ps:prins
               -> w:Wire nat
               -> unit
               -> Wys (option nat) (pre_with (Mode Par ps) (HasDom w ps))  post
let mill8_sec ps w _ =

  let f: option (p:prin{w_contains p w})
         -> (p:prin{w_contains p w}) -> y:nat{w_select p w = y}
         -> Wys (option (p:prin{w_contains p w})) (pre (Mode Sec ps)) post =
    fun x p y ->
      match x with
        | None    -> Some p
        | Some p' ->
          let y' = projwire_s w p' in
          if y > y' then Some p else Some p'
  in

  let g:unit -> Wys (option (p:prin{w_contains p w})) (pre (Mode Sec ps)) (post #(option (p:prin{w_contains p w}))) =
    fun _ -> wfold w f None
  in

  let p = as_sec ps g in
  if p = None then None else Some (prin_to_nat (Some.v p))

(* TODO: FIXME: This is a regression, how can we define can_box for refinement types ? *)
val mill8: unit -> Wys bool (pre p_abc) post
let mill8 _ =
  let x:Box nat alice_s = as_par alice_s (read #nat) in
  let y:Box nat bob_s = as_par bob_s (read #nat) in
  let z:Box nat charlie_s = as_par charlie_s (read #nat) in

  let wa = mkwire_p alice_s x in
  let wb = mkwire_p bob_s y in
  let wc = mkwire_p charlie_s z in

  let w1 = concat_wire wa wb in
  let w2 = concat_wire w1 wc in

  (* call mill for 2 parties *)
  let _ = as_par ab (mill8_sec #ab w1) in

  (* call mill for 3 parties *)
  let _ = as_par abc (mill8_sec #abc w2) in

  true

(**********)

(* nearest neighbor *)
(* TODO: FIXME: finish this *)
(*val gps_sec: ps:prins
             -> w:Wire nat
             -> unit
             -> Wys (Wire (option (p:prin{Set.mem p ps}))) (pre_with (Mode Par ps) (HasDom w ps)) post
let gps_sec ps w _ =

  let l = dom_of_wire w in
  let l = box_l ps l in

  let wfold_f: nat -> option ((p:prin{contains w p}) * nat)
               -> (p:prin{contains w p}) -> y:nat{sel w p = y}
               -> Wys (option ((p:prin{contains w p}) * nat)) (fun m0 -> True) post =
    fun c x p y ->
      if c = y then
        x
      else
        match x with
          | None          -> Some (p, y)
          | Some (p', y') -> if c - y' < c - y then Some (p, y) else x
  in

  let waps_f: p:prin{contains w p} -> x:nat{sel w p = x}
              -> Wys (option (p:prin{contains w p})) (pre (Mode Sec ps)) post =
    fun p x ->
      let y = wfold w (wfold_f x) None in
      match y with
        | None        -> None
        | Some (p, y) -> Some p
  in

  let g: unit -> Wys (Wire (option (p:prin{contains w p}))) (pre (Mode Sec ps)) post =
    fun _ -> waps l w waps_f
  in

  as_sec ps g

val gps: unit -> Wys (Wire (option (p:prin{Set.mem p abc}))) (pre p_abc) post
let gps _ =
  let x:Box nat = as_par alice_s read in
  let y:Box nat = as_par bob_s read in
  let z:Box nat = as_par charlie_s read in

  let w1 = concat_wire (mkwire_p alice_s x) (mkwire_p bob_s y) in
  let w2 = concat_wire w1 (mkwire_p charlie_s z) in

  unbox_p (as_par abc (gps_sec abc w2))

(**********)

(* unoptimized median, TODO: precondition of DISTINCT *)

val unoptimized_median: p1:prin -> p2:prin
                        -> Wys nat (pre (Mode Par (to_s2 p1 p2))) post
let unoptimized_median p1 p2  =
  let x1 = as_par (to_s1 p1) read in
  let x2 = as_par (to_s1 p1) read in
  let y1 = as_par (to_s1 p2) read in
  let y2 = as_par (to_s1 p2) read in

  let f: unit -> Wys nat (pre (Mode Sec (to_s2 p1 p2))) post =
    fun _ ->
      let x1 = unbox_s x1 in
      let x2 = unbox_s x2 in
      let y1 = unbox_s y1 in
      let y2 = unbox_s y2 in

      let a = x1 <= y1 in
      let x3 = if a then x2 else x1 in
      let y3 = if a then y1 else y2 in
      let b = x3 <= y3 in
      if b then x3 else y3
  in

  as_sec (to_s2 p1 p2) f

(**********)

(* optimized median, TODO: precondition of DISTINCT *)

val optimized_median: p1:prin -> p2:prin
                      -> Wys nat (pre (Mode Par (to_s2 p1 p2))) post
let optimized_median p1 p2  =
  let x1 = as_par (to_s1 p1) read in
  let x2 = as_par (to_s1 p1) read in
  let y1 = as_par (to_s1 p2) read in
  let y2 = as_par (to_s1 p2) read in

  let f: x:Box nat{ps_of_box x = to_s1 p1}
         -> y:Box nat{ps_of_box y = to_s1 p2}
         -> unit
         -> Wys bool (pre (Mode Sec (to_s2 p1 p2))) post =
    fun x y _ -> (unbox_s x) <= (unbox_s y)
  in

  let a = as_sec (to_s2 p1 p2) (f x1 y1) in

  let f1: unit -> Wys nat (pre (Mode Par (to_s1 p1))) post
    = fun _ -> if a then unbox_p x2 else unbox_p x1
  in
  let x3 = as_par (to_s1 p1) f1 in

  let f2: unit -> Wys nat (pre (Mode Par (to_s1 p2))) post
    = fun _ -> if a then unbox_p y1 else unbox_p y2
  in
  let y3 = as_par (to_s1 p2) f2 in

  let b = as_sec (to_s2 p1 p2) (f x3 y3) in

  0

(**********)

(* two round bidding *)

type shp (p1:prin) (p2:prin) = x:(Share (nat * nat)){ps_of_sh x = to_s2 p1 p2}

val two_round_bidding: p1:prin -> p2:prin
                       -> Wys prin (pre (Mode Par (to_s2 p1 p2))) post
let two_round_bidding p1 p2 =
  let x1, y1 = as_par (to_s1 p1) read, as_par (to_s1 p2) read in

  let r1: unit -> Wys (bool * (shp p1 p2)) (pre (Mode Sec (to_s2 p1 p2))) post =
    fun _ ->
      let x1, y1 = unbox_s x1, unbox_s y1 in
      x1 < y1, mk_share (x1, y1)
  in

  let y = as_sec (to_s2 p1 p2) r1 in

  (* TODO: does not work without this type annotation *)
  let sh:shp p1 p2 = snd y in

  let x1, y1 = as_par (to_s1 p1) read, as_par (to_s1 p2) read in

  let r2: unit -> Wys prin (pre (Mode Sec (to_s2 p1 p2))) post =
    fun _ ->
      let x1, y1 = unbox_s x1, unbox_s y1 in
      let x1', y1' = comb_share sh in
      if x1 + x1' < y1 + y1' then p1 else p2
  in

  as_sec (to_s2 p1 p2) r2*)

(**********)
