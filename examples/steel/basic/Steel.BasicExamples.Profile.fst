module Steel.BasicExamples.Profile
open Steel.Memory
open Steel.Reference
open Steel.Effect
open Steel.FractionalPermission
open FStar.Ghost
module A = Steel.Effect.Atomic
#push-options "--ide_id_info_off"

assume
val swap (#a:Type) (#x #y:erased a)
         (r0 r1: ref a)
  : SteelT unit
    (pts_to r0 full_perm x `star` pts_to r1 full_perm y)
    (fun _ -> pts_to r1 full_perm x `star` pts_to r0 full_perm y)

let swap_n (#a:Type) (#x #y:erased a)
           (r0 r1: ref a)
  : SteelT unit
    (pts_to r0 full_perm x `star` pts_to r1 full_perm y)
    (fun _ -> pts_to r1 full_perm y `star` pts_to r0 full_perm x)
  = swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;

    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;

    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1;
    swap r0 r1;  swap r0 r1
