module S = FStarC_Syntax_Syntax
module P = FStar_Profiling
module BU = FStarC_Compiler_Util
let now () = BatUnix.gettimeofday ()
let record_time f = 
    let start = now () in
    let res = f () in
    let elapsed = (now()) -. start in
    res, int_of_float (elapsed *. 1000.0)
let eq_term_ctr = ref (0, 0)
let num_eq_term_calls = ref (0, 0)
let incr (r:(int * int) ref) (time:int) = let n, t = !r in r := (n + 1, time + t)
module HashKey =
  struct
    type t = S.term
    let equal (x:t) (y:t) = FStarC_Syntax_Hash.equal_term x y
(* This function is often hot. Its useful to enable the profiling code when debugging
   P.profile (fun _ -> 
                    let res, time = record_time (fun _ -> FStarC_Syntax_Hash.equal_term x y) in
                    incr num_eq_term_calls time;
                    if res
                    then ( incr eq_term_ctr time; true )
                   else ( false))
               None
              "FStar.Syntax.TermHashTable.equal"
*)              
    let hash (x:t) = FStarC_Syntax_Hash.ext_hash_term x
(*        P.profile (fun _ -> 
                  None
                  "FStar.Syntax.TermHashTable.hash"
*)
  end
module HT = BatHashtbl.Make(HashKey)

type 'a hashtable = 'a HT.t

let create (n:Z.t) = HT.create (Z.to_int n)
module Print = FStarC_Syntax_Print

let insert (key: S.term) (v:'a) (ht:'a hashtable) = HT.add ht key v

let lookup (key: S.term) (ht:'a hashtable) : 'a option =
   try
    let l = HT.find ht key in
    Some l
  with
    | Not_found -> None

let reset_counters (x:'a hashtable) =
  eq_term_ctr := (0,0);
  num_eq_term_calls := (0,0)
  
let clear (x:'a hashtable) = 
  HT.clear x;
  reset_counters x

let print_stats (x:'a hashtable) : unit =
  let stats = HT.stats x in
  let string_of_ctr ctr = let n, t = !ctr in BU.format2 "%s in %s ms" (string_of_int n) (string_of_int t) in
  BU.print4 "THT Statistics { num_bindings = %s; max_bucket_length = %s; num_eq_term_calls = %s; eq_term_ctr = %s }\n"
    (string_of_int stats.num_bindings)
    (string_of_int stats.max_bucket_length)
    (string_of_ctr num_eq_term_calls)
    (string_of_ctr eq_term_ctr)

(*    Histogram
    (BatString.concat "; " 
      (List.map (function Some x -> x)
      (List.filter 
        (function None -> false | _ -> true)
         (Array.to_list (
           (Array.mapi (fun i n -> if n = 0 then None else Some ("(" ^ (string_of_int i) ^", "^ (string_of_int n)^ ")")) stats.bucket_histogram))))))
*)
