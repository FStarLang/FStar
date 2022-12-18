module PrecedesRank

(*
 * This module shows that precedes (<<) cannot be modelled as comparison
 * of integer ranks with some total order. The argument is essentially
 * that we can a find a term (`pid` below) with a rank greater than any
 * integer. But `pid` has a rank itself, hence it has a rank larger than
 * its own, contradiction.
 *
 * This rings a bell of the Burali-Forti paradox. I think this will
 * still hold if the type of ranks is, say, real numbers, but the proof
 * will likely be more complicated.
 *)

noeq
type pack = | Mk : f:(int -> int) -> pack

let pid : pack = Mk (fun n -> n)

(* This relies on the fact that `f x << Mk f` for every `x`. *)
let pid_ge_n (x:int) : Lemma (x << pid) =
  assert (Mk?.f pid x << pid);
  ()

(* The "Rank assumption" packaged as a record. *)
noeq
type ras = {
  rank : #a:Type -> a -> int;
  rank_lem : #a:Type -> #b:Type -> x:a -> y:b -> Lemma (x << y <==> rank x < rank y);
}

(* The rank of an integer `n` is at least `n` over the rank of 0. *)
let rec rank_n_ge_n (r:ras) (n:nat) : Lemma (r.rank #int n >= r.rank #int 0 + n) =
  if n <> 0 then begin
    rank_n_ge_n r (n-1);
    r.rank_lem #int #int (n-1) n
  end

(* Given that above, we can find integers with arbitrarilly large ranks. *)
let bigrank_n (r:ras) (n:int) : i:int{r.rank #int i > n} =
  let n = if n < 0 then 0 else n in
  if r.rank #int 0 >= 0 then begin
    rank_n_ge_n r (n+1);
    (n+1)
  end else begin
    rank_n_ge_n r (n+1 - r.rank #int 0);
    n+1 - r.rank #int 0
  end

(*
 * `pid` has a rank, and it's greater than any integer, but that
 * contradicts the proof just above, that we can find an integer with a
 * rank over it.
 *)
let diag (r:ras) : Lemma (r.rank pid > r.rank pid) =
  let n = r.rank pid in
  let n' = bigrank_n r n in
  assert (r.rank #int n' > r.rank pid);
  assert (r.rank pid < r.rank #int n');
  r.rank_lem #_ #int pid n';
  assert (pid << n');
  pid_ge_n n';
  ()

(* We obviously get false from that. *)
let falso () : Lemma (~(exists (r:ras). True)) =
  let aux (r:ras) : Lemma (True ==> False) = diag r in
  Classical.forall_to_exists aux
