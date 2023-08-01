(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Trace
open FStar.List.Tot
(* Instrumenting recursive functions to provide a trace of their calls *)
(* TODO: update to make use of metaprogrammed let-recs and splicing *)

(* Do not warn about recursive functions not used in their bodies:
since we metaprogram them, the desugaring phase wrongly concludes
they do not have to be recursive, but they do. *)
#push-options "--warn_error -328"

(* We take a function such as
 *
 *  val fall : mynat -> Tot mynat
 *  let rec fall (n : mynat) : Tot mynat =
 *      match n with
 *      | Z -> Z
 *      | S n -> fall n
 *
 * and automatically instrument it to keep a trace of its recursive calls,
 * obtaining the definition:
 *
 *  val fall' : mynat -> list mynat -> (list mynat) * mynat
 *  let rec fall' n t =
 *      match n with
 *      | Z -> (n :: t, Z)
 *      | S n -> fall' n (n :: t)
 *
 * The trace is taken as the last argument to (hopefully) have less impact over
 * termination criteria: having it first would need annotations, since the trace always
 * grows.
 *
 * We don't actually require all recursive calls to be in tail positions, but those
 * are the only ones we will detect and instrument. Note that the instrumented function
 * is also tail-recursive (and the trace is "backwards").
 *)

open FStar.Tactics.V2

type mynat =
    | Z
    | S of mynat

let rec tick_last (ns:list string) =
  match ns with
  | [] -> []
  | [x] -> [x ^ "'"]
  | x::xs -> x :: (tick_last xs)

let tick (nm : fv) : fv =
  let ns = inspect_fv nm in
  pack_fv (tick_last ns)

let cons_fst (x : 'a) (p : list 'a * 'b) : list 'a * 'b =
    let (y, z) = p in (x :: y, z)

let cons_fst_qn = ["Trace"; "cons_fst"]

let term_is_fv hd nm : Tac bool =
    match inspect hd with
    | Tv_FVar fv -> inspect_fv fv = inspect_fv nm
    | _ -> false

noeq
type ins_info = {
    orig_name : fv;
    ins_name : fv;
    args : (args : list term{length args <= 8});
    trace_arg : term;
}

let rec instrument_body (ii : ins_info) (t : term) : Tac term =
  match inspect_unascribe t with
  // descend into matches
  | Tv_Match t ret_opt brs -> begin
    let brs' = map (ins_br ii) brs in
    pack (Tv_Match t ret_opt brs')
    end
  // descend into lets
  | Tv_Let r attrs b ty t1 t2 -> begin
    let t2' = instrument_body ii t2 in
    pack (Tv_Let r attrs b ty t1 t2')
    end
  | _ -> begin
    let hd, args = collect_app t in
    let argpack = mktuple_n ii.args in
    if term_is_fv hd ii.orig_name
    then begin
        // modify the tail call
        // turn `nm <b1,...,bn>` into `nm' (<a1,...,an>::tr) <b1,...,bn>`
        let f' = pack (Tv_FVar ii.ins_name) in
        mk_app f' (args @ [mk_cons argpack ii.trace_arg, Q_Explicit])
    end else begin
        // not a tail call, record the current set of args and be done
        mkpair (mk_cons argpack ii.trace_arg) t
    end
   end

and ins_br (ii : ins_info) (br : branch) : Tac branch =
  let (p, t) = br in
  let t' = instrument_body ii t in
  (p, t')

let rec cutlast (l : list 'a{length l > 0}) : list 'a * 'a =
    match l with
    | [x] -> [], x
    | x::xs -> let ys, y = cutlast xs in x::ys, y

let instrument (f : 'a) : Tac unit =
    let t = quote f in
    // name
    let n = match inspect t with
            | Tv_FVar fv -> fv
            | _ -> fail "Not a top-level"
    in
    let n' = tick n in
    let all_args = intros () in
    if length all_args = 0 then
      fail "Function has no arguments?";
    let real, trace_arg = cutlast all_args in 
    let real = map (fun b -> pack (Tv_Var (binding_to_namedv b))) real in
    if length real > 8 then
      fail "Too many arguments to instrument function";
    assert (length real <= 8);
    let ii = {
        orig_name = n;
        ins_name = n';
        args = real;
        trace_arg = pack (Tv_Var (binding_to_namedv trace_arg))
    } in
    (* Apply the function to the arguments and unfold it. This will only
     * unfold it once, so recursive calls are present *)
    let t = norm_term [delta; zeta] (mk_e_app t ii.args) in
    dup ();
    let t = instrument_body ii t in
    (* dump ""; *)
    let _ = focus (fun () -> exact_guard t; repeat smt) in
    norm [];
    trefl ()

let rec fall (n : mynat) : Tot mynat =
    match n with
    | Z -> Z
    | S n -> fall n

// Because of the way we're building this recursive function, its termination is unprovable.
// So admit queries for now.
#push-options "--admit_smt_queries true"
let rec fall' (n : mynat) (l : list mynat) =
    // We need to annotate the result type.. which sucks.
    // But we could use a tactic later :)
    synth_by_tactic #(mynat -> list mynat -> (list mynat * mynat)) (fun () -> instrument fall) n l
#pop-options

let _ = assert (fall' (S (S (S Z))) [] == ([Z; S Z; S (S Z); S (S (S Z))], Z))

// Beware: the `let acc' = `... gets normalized in the tactic,
// so we're not actually descending through it. Maybe we need a flag
// to control the evaluation of lets.
let rec fact_aux (n acc : nat) : Tot nat =
    if n = 0
    then acc
    else let acc' = acc `op_Multiply` n in fact_aux (n - 1) acc'

let fact (n : nat) : Tot nat = fact_aux n 1

#push-options "--admit_smt_queries true"
let rec fact_aux' (n acc : nat) (tr : list (nat * nat)) : Tot (list (nat * nat) * nat) =
    synth_by_tactic #(nat -> nat -> list (nat * nat) -> (list (nat * nat) * nat)) (fun () -> instrument fact_aux) n acc tr
#pop-options

let _ = assert (fact_aux' 5 1 [] == ([(0, 120); (1, 120); (2, 60); (3, 20); (4, 5); (5, 1)], 120))

(* We can also instrument `fact`, but we won't get anything too
 * interesting as that's not the tail-recursive function *)
#push-options "--admit_smt_queries true"
// TODO: I have to use `int` for the codomains or it complains... why? I'm even admitting SMT
let rec fact' (n : nat) (tr : list nat) : Tot (list nat * int) =
    synth_by_tactic #(nat -> list nat -> (list nat * int)) (fun () -> instrument fact) n tr
#pop-options

let _ = assert (fact' 5 [] == ([5], 120))
