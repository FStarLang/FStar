module CherryFStarCList

(* FStarC.List-c.cherry.fst: every function, the failures of the ML ones as
   catchable [Failure]s, and long lists in a small stack.  The total partial
   functions are not called outside their domain: that is undefined (and
   caught by debug mode, tests/custard/debug). *)
open FStarC.Effect
module L = FStarC.List

let check (b:bool) (n:int) (acc:int) : int = if b then acc else acc * 100 + n

let fails (#a:Type) (f:unit -> ML a) : ML bool =
  try_with (fun () -> let _ = f () in false)
           (fun e -> match e with Failure _ -> true | _ -> false)

let rec upto (n:int) (acc:list int) : Tot (list int) (decreases (if n < 0 then 0 else n + 1)) =
  if n < 0 then acc else upto (n - 1) (n :: acc)

let main () : ML FStar.UInt32.t =
  let l = [1; 2; 3; 4] in
  let e = 0 in
  let e = check (L.isEmpty ([] <: list int) && not (L.isEmpty l) && L.singleton 5 = [5]) 1 e in
  let e = check (L.hd l = 1 && L.length l = 4 && L.nth l 2 = 3) 2 e in
  let e = check (L.rev l = [4; 3; 2; 1] && L.rev_acc [1; 2] [3] = [2; 1; 3]) 3 e in
  let e = check (L.append [1] [2; 3] = [1; 2; 3] && L.op_At [1; 2] [] = [1; 2]) 4 e in
  let e = check (L.flatten [[1]; []; [2; 3]] = [1; 2; 3] && L.concat [[4]; [5]] = [4; 5]) 5 e in
  let r = alloc 0 in
  L.iter (fun x -> r := !r * 10 + x) l;
  L.iter2 (fun x y -> r := !r * 10 + x + y) [1] [1];
  L.iteri (fun i x -> r := !r * 10 + i * x) [5; 3];
  let e = check (!r = 123420 * 10 + 3) 6 e in
  let ord = alloc [] in
  let m = L.map (fun x -> ord := x :: !ord; x * 2) l in
  let e = check (m = [2; 4; 6; 8] && !ord = [4; 3; 2; 1]) 7 e in
  let e = check (L.mapi (fun i x -> i + x) [10; 20] = [10; 21]
                 && L.mapi_init (fun i x -> i * x) [1; 1] 5 = [5; 6]) 8 e in
  let e = check (L.concatMap (fun x -> [x; x]) [1; 2] = [1; 1; 2; 2]
                 && L.collect (fun x -> if x = 1 then [] else [x]) [1; 2] = [2]) 9 e in
  let e = check (L.map2 (fun x y -> x - y) [5; 6] [1; 2] = [4; 4]
                 && L.map3 (fun x y z -> x + y + z) [1] [2] [3] = [6]) 10 e in
  let e = check (L.fold_left (fun a x -> a * 10 + x) 0 l = 1234
                 && L.fold_right (fun x a -> a * 10 + x) l 0 = 4321) 11 e in
  let e = check (L.fold_left2 (fun a x y -> a + x * y) 0 [1; 2] [3; 4] = 11
                 && L.fold_right2 (fun x y a -> a * 10 + x + y) [1; 2] [1; 1] 0 = 32) 12 e in
  let e = check (L.rev_map_onto (fun x -> x + 1) [1; 2] [0] = [3; 2; 0]) 13 e in
  let e = check (L.init l = [1; 2; 3] && L.last l = 4 && L.last_opt ([] <: list int) = None
                 && L.last_opt l = Some 4) 14 e in
  let e = check (L.existsb (fun x -> x = 3) l && not (L.existsML (fun x -> x > 4) l)) 15 e in
  let e = check (L.find (fun x -> x > 2) l = Some 3 && L.tryFind (fun x -> x > 9) l = None) 16 e in
  let e = check (L.filter (fun x -> x % 2 = 0) l = [2; 4] && L.for_all (fun x -> x > 0) l
                 && L.forall2 (fun x y -> x = y) [1; 2] [1; 2]) 17 e in
  let e = check (L.tryPick (fun x -> if x > 2 then Some (x * 10) else None) l = Some 30
                 && L.choose (fun x -> if x > 2 then Some x else None) l = [3; 4]
                 && L.filter_map (fun x -> if x < 2 then Some x else None) l = [1]) 18 e in
  let e = check (L.partition (fun x -> x < 3) l = ([1; 2], [3; 4])
                 && L.splitAt 1 l = ([1], [2; 3; 4]) && L.splitAt 4 l = (l, [])) 19 e in
  let e = check (L.split [(1, "a"); (2, "b")] = ([1; 2], ["a"; "b"])
                 && L.unzip [(1, 2)] = ([1], [2])
                 && L.unzip3 [(1, 2, 3); (4, 5, 6)] = ([1; 4], [2; 5], [3; 6])) 20 e in
  let e = check (L.zip [1; 2] ["a"; "b"] = [(1, "a"); (2, "b")]
                 && L.zip3 [1] [2] [3] = [(1, 2, 3)]) 21 e in
  let e = check (L.sortWith (fun (a, _) (b, _) -> a - b) [(2, 1); (1, 2); (2, 3); (1, 4)]
                 = [(1, 2); (1, 4); (2, 1); (2, 3)]) 22 e in
  let e = check (L.tail l = [2; 3; 4] && L.tl [1] = [] && L.rev_append [1; 2] [3] = [2; 1; 3]) 23 e in
  let e = check (L.count 1 [1; 2; 1] = 2 && L.mem 2 l && not (L.contains 7 l)
                 && L.assoc 2 [(1, "a"); (2, "b")] = Some "b") 24 e in
  let e = check (L.unique [1; 2; 1; 3; 2] = [1; 3; 2] && L.index (fun x -> x = 3) l = 2
                 && L.span (fun x -> x < 3) [1; 2; 3; 1] = ([1; 2], [3; 1])) 25 e in
  let e = check (L.deduplicate (fun x y -> x = y) [1; 2; 1] = [2; 1]
                 && L.fold_left_map (fun s x -> (s + x, s)) 0 [1; 2; 3] = (6, [0; 1; 3])) 26 e in
  (* The ML functions raise Failure, and the length checks come after the
     elements before the mismatch. *)
  let seen = alloc 0 in
  let f9 = fails (fun () -> L.map2 (fun x _ -> seen := !seen + x) [1; 2] [0]) in
  let f10 = fails (fun () -> L.fold_right2 (fun x _ a -> seen := !seen + x; a) [1; 2] [0] ()) in
  let e = check (f9 && f10 && !seen = 1 && not (L.forall2 (fun _ _ -> false) [1; 2] [1])) 28 e in
  (* A million elements, each function in constant stack. *)
  let big = upto 999999 [] in
  let big2 = L.map (fun x -> x + 1) big in
  let e = check (L.length big2 = 1000000 && L.fold_left (fun a x -> a + x) 0 big2 = 500000500000) 29 e in
  let e = check (L.length (L.filter (fun x -> x % 2 = 0) big) = 500000
                 && L.length (L.append big big) = 2000000
                 && L.fold_right (fun x a -> if a = x + 1 then x else a) big 1000000 = 0) 30 e in
  let s = L.sortWith (fun x y -> y - x) big in
  let e = check (L.hd s = 999999 && L.last s = 0 && L.nth (L.rev s) 12345 = 12345) 31 e in
  let e = check (L.length (L.collect (fun x -> [x]) big) = 1000000
                 && L.length (fst (L.split (L.zip big big))) = 1000000) 32 e in
  if e = 0 then 0ul else 1ul
