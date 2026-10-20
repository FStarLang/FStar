module CherryArray

(* FStarC.Array-c.cherry.fst: make/get/set/append, independence of an
   appended array from its sources, bounds checks, counted elements, and
   in-place updates (10^6 of them). *)
open FStarC.Effect
module S = FStarC.SmallInt
module A = FStarC.Array

let check (b:bool) (n:int) (acc:int) : int = if b then acc else acc * 100 + n

let i (n:int) : S.t = S.of_int n

let raises (f:unit -> ML unit) : ML bool =
  try f (); false with | _ -> true

let rec bump (arr:A.array int) (k:nat) : ML unit =
  if k = 0 then () else begin
    let j = i (k % 1000) in
    A.set arr j (A.get arr j + 1);
    bump arr (k - 1)
  end

let main () : ML FStar.UInt32.t =
  let a = A.make (i 3) "x" in
  let e = 0 in
  let e = check (S.to_int (A.length a) = 3 && A.get a (i 2) = "x") 1 e in
  A.set a (i 1) "y";
  let e = check (A.get a (i 0) = "x" && A.get a (i 1) = "y") 2 e in
  let b = A.make (i 2) "z" in
  let c = A.append a b in
  let e = check (S.to_int (A.length c) = 5 && A.get c (i 1) = "y"
                 && A.get c (i 4) = "z") 3 e in
  A.set c (i 0) "c";
  A.set a (i 2) "a";
  A.set b (i 0) "b";
  let e = check (A.get a (i 0) = "x" && A.get c (i 0) = "c"
                 && A.get c (i 2) = "x" && A.get c (i 3) = "z") 4 e in
  let d = A.append a (A.make S.zero "w") in
  A.set d (i 0) "d";
  let e = check (A.get a (i 0) = "x" && A.get d (i 0) = "d") 5 e in
  let e = check (raises (fun () -> ignore (A.get a (i 3)))) 6 e in
  let e = check (raises (fun () -> A.set a (i (-1)) "q")) 7 e in
  let e = check (raises (fun () -> ignore (A.make (i (-1)) 0))) 8 e in
  let e = check (S.to_int (A.length (A.make S.zero 0)) = 0) 9 e in
  let n = A.make (i 1000) 0 in
  bump n 1000000;
  let e = check (A.get n (i 0) = 1000 && A.get n (i 999) = 1000) 10 e in
  if e = 0 then 0ul else 1ul
