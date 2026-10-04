module Phase2CoreJoinBases

(* The type of [en] must not be inferred by joining the branch types [group] and [elem ...],
   which have different bases: that equates them with a (false) SMT guard that phase 1 drops. *)
type nk = | NType | NGroup
type group = | GA | GElem : bool -> typ -> typ -> group | GConcat : group -> group -> group
and typ = | TA | TElem : int -> typ
let elem0 (k:nk) : Type0 = match k with NType -> typ | NGroup -> group
let prop (k:nk) (x:elem0 k) : prop = True
let elem (s:string) (k:nk) : Type0 = x:elem0 k{prop k x}
noeq type senv = { bound : string -> option nk; se_env : string -> string }
noeq type aenv = { sem : senv; e_env : (n:string{Some? (sem.bound n)}) -> elem (sem.se_env n) (Some?.v (sem.bound n)) }
let ok (g:group) : bool = true
let use (en:group{ok en}) : Lemma True = ()
let f (e:aenv) (n:string{Some? (e.sem.bound n)}) : Pure group (requires True) (ensures fun _ -> True) =
  let en = match e.sem.bound n with
    | Some NType ->
      GElem false (TElem 0) (e.e_env n)
    | Some NGroup -> e.e_env n
  in
  let a = GConcat en GA in
  use en;
  a
