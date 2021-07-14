module Steel.BasicExamples.References
open Steel.Memory
open Steel.Reference
open Steel.Effect
open Steel.FractionalPermission
open FStar.Ghost
module A = Steel.Effect.Atomic
#push-options "--ide_id_info_off"

(* Allocating a reference *)
let allocate #a (x:a) 
  : SteelT (ref a)
    emp
    (fun r -> pts_to r full_perm x)
  = Steel.Reference.alloc_pt x

(* Swapping two references *)
let swap (#a:Type) (#x #y:erased a)
         (r0 r1: ref a)
  : SteelT unit
    (pts_to r0 full_perm x `star` pts_to r1 full_perm y)
    (fun _ -> pts_to r1 full_perm x `star` pts_to r0 full_perm y)
  = let tmp0 = read_pt r0 in
    let tmp1 = read_pt r1 in
    write_pt r0 tmp1;
    write_pt r1 tmp0;
    ()
    
(* Allocating and copying a reference *)
let copy #a (#v:erased a) (#p:perm) (x:ref a)
  : SteelT (ref a)
    (pts_to x p v)
    (fun y -> pts_to y full_perm v `star` pts_to x p v)
  = let tmp = read_pt x in
    let r = allocate tmp in
    r

(* Copying a reference to a newly allocated on and then freeing it *)
let copy_and_free #a (#v:erased a) (x:ref a)
  : SteelT (ref a)
    (pts_to x full_perm v)
    (fun y -> pts_to y full_perm v)
  = let y = copy x in
    free_pt x;
    y

(* Sharing a reference, copying it twice in two separate threads *)
let share_and_copy_twice #a #p #v (x:ref a)
  : SteelT (ref a & ref a)
    (pts_to x p v)
    (fun rs -> pts_to x p v `star` 
            pts_to (fst rs) full_perm v `star`
            pts_to (snd rs) full_perm v)
  = share_pt x;
    let r = par (fun () -> copy x) (fun () -> copy x) in
    gather_pt x;
    A.return r

(* With mutable *)
let with_mutable #a #b (#rest: pre_t) (#rest': post_t b)
      (init:a) 
      ($k: (x:ref a -> SteelT b (pts_to x full_perm init `star` rest)
                               (fun b -> A.h_exists (pts_to x full_perm) `star` rest' b)))
   : SteelT b rest rest'
   = let x = allocate init in 
     let v = k x in
     let _ = A.witness_exists () in
     free_pt x;
     v

(* Use with mutable *)
let use_with_mutable (v:erased int) (y:ref int) 
  : SteelT unit
    (pts_to y full_perm v)
    (fun _ -> pts_to y full_perm (v + 1)) = 
  with_mutable 
    1
    (fun x -> 
       (let vx = read_pt x in
        let vy = read_pt y in 
        write_pt y (vy + vx);
        A.intro_exists (hide 1) (pts_to x full_perm);
        ())
       <: SteelT unit
          (pts_to x full_perm 1 `star` pts_to y full_perm v)
          (fun _ -> A.h_exists (pts_to x full_perm) `star` pts_to y full_perm (v + 1)))

(* Closures capturing state *)
let counter = v:pre_t & (unit -> SteelT int v (fun _ -> v))
let counter_inv (c:counter) = dfst c
let counter_closure (c:counter)
  : unit -> SteelT int (counter_inv c) (fun _ -> counter_inv c)
  = dsnd c
  
let mk_counter () :
  SteelT counter emp (counter_inv) =
  let x = allocate 0 in
  let next () 
    : SteelT int
      (A.h_exists (pts_to x full_perm)) 
      (fun _ -> A.h_exists (pts_to x full_perm))
    = let _ = A.witness_exists () in
      let tmp = read_pt x in
      write_pt x (tmp + 1); 
      A.intro_exists (hide (tmp + 1)) (pts_to x full_perm);
      A.return tmp
  in
  A.intro_exists (hide 0) (pts_to x full_perm);
  A.return (| A.h_exists (pts_to x full_perm), 
              next |)

let counter_next (c:counter)
  : SteelT int (counter_inv c) (fun _ -> counter_inv c)
  = let n = counter_closure c () in //need to hoist this, but not so bad
    A.return n
    
(* Using the counter *)
let make_and_use_counter ()
  : SteelT (int & counter) emp (fun v -> counter_inv (snd v))
  = let c = mk_counter () in
    let n = counter_next c in 
    n, c
    

                              
                 
