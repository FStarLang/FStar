module Steel.Closure

open Steel.Effect
open Steel.Memory
open Steel.HigherReference
open Steel.SteelT.Basics

/// AF: SteelT requires pre_t to be an hprop u#1,
/// which makes it difficult to handle ref int for instance

let pts_to (#a:Type u#1) (r:ref a) (p:perm) (v:a) : hprop u#1 = pts_to r p v

let full_ptr (#a:Type u#1) (r:ref a) : hprop u#1 =
  h_exists (pts_to r full)

val to_full_ptr (#a:Type u#1) (r:ref a) (v:a)
  : SteelT unit (pts_to r full v) (fun _ -> full_ptr r)

let to_full_ptr #a r v =
  change_hprop (pts_to r full v) (full_ptr r)
               (fun m -> intro_exists v (pts_to r full) m)

let exp_emp (#a:Type) (v:a) : hprop u#1 = emp

let raised_int = FStar.Universe.raise_t int

val next (x:ref raised_int) :
  unit -> (SteelT unit (full_ptr x) (fun _ -> full_ptr x))

let next x _ =
    let open FStar.Universe in
    change_hprop (full_ptr x) (h_exists (fun (v:raised_int) -> pts_to x full v `star` exp_emp v))
      (fun m ->
        Classical.forall_intro emp_unit;
        h_exists_extensionality (pts_to x full) (fun (v:raised_int) -> pts_to x full v `star` exp_emp v));
     let v = read_refine #raised_int #full exp_emp x in
     let v':raised_int = raise_val (downgrade_val v + 1) in
     change_hprop (pts_to x full v `star` exp_emp v) (pts_to x full v) (fun m -> emp_unit (pts_to x full v));
     write x v';
     to_full_ptr x v'

let new_counter () =
  let open FStar.Universe in
  let x = alloc (raise_val 0) in
  let next : unit -> SteelT unit (full_ptr x) (fun _ -> full_ptr x) = next x in
  to_full_ptr x (raise_val 0);
  return #_ #(fun r -> dfst r) (| full_ptr x, next |)
