module Phase2CoreStuckMatchByEval

(* Unfolding the head of an application can yield a [match] whose scrutinee
   only reduces after unfolding the definitions in it, e.g.
   [arr_kind u32k 2] to [match pre u32k 2 && u32k.tot = true with ..], or
   [tag_of_data t_sum] to [match t_sum with | DSum _ f -> f]. As Rel does,
   Core evaluates that scrutinee, so that the relations below hold with no
   SMT query (everparse qd tests Amount and T20). The scrutinee [k.hi =
   Some k.lo] needs normalizing in full: in head normal form, [Some k.lo] is
   left as it is, and the primitive equality is stuck. *)

noeq type kind = { lo: int; hi: option int; tot: bool }

let pre (k:kind) (n:nat) : bool = k.lo > 0 && k.hi = Some k.lo && n * k.lo = 8

let u32k : kind = { lo = 4; hi = Some 4; tot = true }

let arr_kind' (n:nat) : kind = { lo = 0; hi = None; tot = false }

let arr_kind (k:kind) (n:nat) : kind =
  if pre k n && k.tot = true then { lo = n + n + n + n; hi = Some (n + n + n + n); tot = true }
  else arr_kind' n

let strong (lo hi:int) : kind = { lo; hi = Some hi; tot = true }

inline_for_extraction let my_kind = strong 8 8

assume val slp : Type0
assume val star : slp -> slp -> slp
assume val pts (k:kind) (x:int) : slp

#push-options "--no_smt"
let test_kind (x:int) (q:slp) (f: slp -> Type0) (h: f (star (pts (arr_kind u32k 2) x) q))
  : f (star (pts my_kind x) q)
  = h
#pop-options

(* Neither side unfolds: [u32k.lo + (arr_kind u32k 2).lo] against [12] is
   closed by evaluation (everparse qd test T24_y). *)
let and_then_kind (k1 k2:kind) : kind = { lo = k1.lo + k2.lo; hi = None; tot = false }
let weak_kind (lo:int) : kind = { lo; hi = None; tot = false }

#push-options "--no_smt"
let test_arith (x:int) (f: slp -> Type0) (h: f (pts (and_then_kind u32k (arr_kind u32k 2)) x))
  : f (pts (weak_kind 12) x)
  = h
#pop-options

(* Nested [match]es, the inner one stuck on [has_lo u32k && u32k.tot] in
   head normal form, against [Some true] (everparse qd test T24_y). Here
   TcTerm leaves an SMT query. *)
let has_lo (k:kind) : bool = k.hi = Some k.lo
assume val opt_pts (o:option bool) (x:int) : slp

#push-options "--no_smt"
let test_field (x:int) (f: slp -> Type0)
  (h: f (opt_pts (match u32k.tot && false with
                  | true -> None
                  | _ -> (match has_lo u32k && u32k.tot with | true -> Some true | _ -> None)) x))
  : f (opt_pts (Some true) x)
  = h
#pop-options

noeq type dsum = | DSum : n:int -> tag_of: (int -> bool) -> dsum

let key_of (x:int) : bool = x > 0

let mk_dsum (n:int) (f: int -> bool) : dsum = DSum (n + 1) f

let tag_of_data (d:dsum) : int -> bool = match d with | DSum _ f -> f

let t_sum = mk_dsum 2 key_of

let refine_with_tag (f: int -> bool) (b:bool) : Type0 = y:int{f y == b}

#push-options "--no_smt"
let test_tag (g: Type0 -> Type0) (h: g (refine_with_tag (tag_of_data t_sum) true))
  : g (refine_with_tag key_of true)
  = h
#pop-options
