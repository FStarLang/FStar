module CherryFStarCHashTable

(* FStarC.HashTable-c.cherry.fst.  Small integers are their own hash codes in
   both builds, so for them the order [iter], [fold] and [keys] see is the
   OCaml build's; CherryFStarCHashTable.expected is what OCaml's own
   [Hashtbl.Make] prints for the same operations. *)

open FStarC.Effect
open FStarC.Class.Deq
open FStarC.Class.Hashable
module HT = FStarC.HashTable
module L = FStarC.List

let rec range (i n:int) : Tot (list int) (decreases (if i < n then n - i else 0)) =
  if i < n then i :: range (i + 1) n else []

let show_int (i:int) : string = string_of_int i

let line (s:string) : ML unit = FStarC.Format.print_string (s ^ "\n")

let show_keys (m:HT.t int string) : ML string =
  String.concat " " (L.map show_int (HT.keys m))

let show_iter (m:HT.t int string) : ML string =
  let acc = mk_ref [] in
  HT.iter m (fun k v -> acc := (show_int k ^ "=" ^ v) :: !acc);
  String.concat " " (L.rev !acc)

let main () : ML unit =
  let m : HT.t int string = HT.create 1 in
  (* Enough keys to resize the table three times; 7919 is prime, so they are
     distinct below 1000, and some land in the same bucket. *)
  L.iter (fun i -> HT.add m ((i * 7919) % 1000) (show_int i)) (range 0 150);
  line ("size " ^ show_int (HT.size m));
  line ("keys " ^ show_keys m);
  (* Replacing keeps the binding where it is. *)
  L.iter (fun i -> HT.add m ((i * 7919) % 1000) ("r" ^ show_int i)) (range 0 20);
  line ("size " ^ show_int (HT.size m));
  L.iter (fun i -> HT.remove m ((i * 7919) % 1000)) (range 10 40);
  HT.remove m 1001;
  line ("size " ^ show_int (HT.size m));
  line ("iter " ^ show_iter m);
  line ("find " ^ (match HT.try_find m 0 with Some v -> v | None -> "none")
        ^ " " ^ (match HT.try_find m ((15 * 7919) % 1000) with Some v -> v | None -> "none"));
  line ("mem " ^ (if HT.mem m 0 then "y" else "n") ^ (if HT.mem m 1001 then "y" else "n"));
  line ("fold " ^ show_int (HT.fold m (fun k _ acc -> (acc * 3 + k) % 1000003) 0));
  let c = HT.copy m in
  HT.add c 5000 "new";
  HT.remove c 0;
  line ("copy " ^ show_int (HT.size c) ^ " " ^ show_int (HT.size m) ^ " " ^ show_keys c);
  HT.clear m;
  line ("clear " ^ show_int (HT.size m) ^ " [" ^ show_keys m ^ "]");
  L.iter (fun i -> HT.add m (i * 64) (show_int i)) (range 0 40);
  line ("after " ^ show_keys m);
  (* [clear] empties only the buckets used since the last clear, unless
     more were noted than there are buckets: here bucket 0 is emptied and
     refilled 40 times in a table of 16. *)
  let z : HT.t int string = HT.create 1 in
  L.iter (fun i -> HT.add z (i * 16) "x"; HT.remove z (i * 16)) (range 0 40);
  HT.add z 1 "a"; HT.add z 32 "b";
  HT.clear z;
  HT.add z 2 "c";
  line ("reclear " ^ show_int (HT.size z) ^ " [" ^ show_keys z ^ "] "
        ^ (if HT.mem z 1 || HT.mem z 32 then "stale" else "ok"));
  (* A copy keeps its own record of used buckets. *)
  let big : HT.t int string = HT.create 4000 in
  HT.add big 7 "a"; HT.add big 4103 "b";
  let bc = HT.copy big in
  HT.clear big;
  HT.add bc 9 "c";
  HT.clear bc;
  line ("bigclear " ^ show_int (HT.size big) ^ " " ^ show_int (HT.size bc) ^ " "
        ^ (if HT.mem big 7 || HT.mem bc 4103 || HT.mem bc 9 then "stale" else "ok"));
  let l = HT.of_list [(3, "a"); (1, "b"); (3, "c"); (35, "d")] in
  line ("of_list " ^ show_iter l);
  (* String keys hash differently in the two builds, so only what does not
     depend on the order is printed. *)
  let s : HT.t string int = HT.create 4 in
  L.iter (fun i -> HT.add s ("k" ^ show_int (i % 50)) i) (range 0 200);
  HT.remove s "k7";
  line ("strings " ^ show_int (HT.size s) ^ " "
        ^ (match HT.try_find s "k3" with Some v -> show_int v | None -> "none") ^ " "
        ^ (match HT.try_find s "k7" with Some v -> show_int v | None -> "none"))
