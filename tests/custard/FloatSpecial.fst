module FloatSpecial

open FStar.All

module F64 = FStar.Float64

(* Section 125.5.  [of_literal "nan"] and [of_literal "inf"].  Neither is a
   real number, so neither could be written before; and neither can be
   *computed* either, because [FStar.Float64] exposes no operation that builds
   one out of finite arguments that Custard is willing to constant-fold.  A
   literal is the only way in.

   The answer is reported through the exit code, because the direct-to-C
   backend (section 100) has no [FStar.IO] to print with: the result is the
   number of the first check that failed, and 0 if none did. *)

let check (n:FStar.Int32.t) (b:bool) (k:unit -> ML FStar.Int32.t)
  : ML FStar.Int32.t =
  if b then k () else n

let nan : F64.t = F64.of_literal "nan"
let inf : F64.t = F64.of_literal "inf"
let ninf : F64.t = F64.of_literal "-inf"

let one : F64.t = F64.of_int 1L
let zero : F64.t = F64.of_int 0L

let main () : ML FStar.Int32.t =
  (* A NaN is equal to nothing, itself included: this is the property that
     distinguishes it from every finite value, so it is check 1. *)
  check 1l (not (F64.ieee_eq nan nan)) (fun () ->
  check 2l (not (F64.ieee_eq nan one)) (fun () ->
  check 3l (not (F64.lt nan one)) (fun () ->
  check 4l (not (F64.lt one nan)) (fun () ->
  check 5l (not (F64.lte nan nan)) (fun () ->
  (* An arithmetic result that is a NaN is still one, so the literal is the
     same value the hardware produces and not merely a value that compares
     unequal to itself. *)
  check 6l (not (F64.ieee_eq (F64.add nan one) (F64.add nan one))) (fun () ->
  check 7l (not (F64.ieee_eq (F64.mul nan zero) zero)) (fun () ->
  (* An infinity is ordered above every finite value and equal to itself. *)
  check 8l (F64.ieee_eq inf inf) (fun () ->
  check 9l (F64.lt one inf) (fun () ->
  check 10l (F64.lt ninf one) (fun () ->
  check 11l (F64.lt ninf inf) (fun () ->
  check 12l (not (F64.ieee_eq inf ninf)) (fun () ->
  (* [-inf] is the negation and not a separate magnitude. *)
  check 13l (F64.ieee_eq (F64.sub zero inf) ninf) (fun () ->
  (* Absorbing: an infinity plus a finite value is the same infinity. *)
  check 14l (F64.ieee_eq (F64.add inf one) inf) (fun () ->
  check 15l (F64.ieee_eq (F64.mul inf inf) inf) (fun () ->
  (* And [inf - inf] is a NaN, which closes the loop: the two literals agree
     with each other through the arithmetic. *)
  check 16l (not (F64.ieee_eq (F64.sub inf inf) (F64.sub inf inf))) (fun () ->
  check 17l (F64.lt (F64.div one inf) one) (fun () ->
  0l)))))))))))))))))
