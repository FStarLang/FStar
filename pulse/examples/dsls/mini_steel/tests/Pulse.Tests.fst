module Pulse.Tests
module T = FStar.Tactics
open Pulse.Steel.Wrapper
open Pulse.Syntax
open Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
#push-options "--print_universes --print_implicits"

%splice_t[foo] (parse_and_check "return true")

%splice_t[read] (parse_and_check "
   fun (n:FStar.Ghost.erased u#0 Pulse.Steel.Wrapper.u32)
       (r:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
         requires (Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n)) ->
         Pulse.Steel.Wrapper.read n r
   ")

%splice_t[read2] (check (`(fun (n:erased u#0 u32) (r:ref u32) ->
                              Pulse.Steel.Wrapper.read n r 
                            <: stt u#0 u32
                                (pts_to #u32 r full_perm (reveal u#0 #u32 n))
                                (fun x -> pts_to #u32 r full_perm x))))

%splice_t[read_alt_with_post] (parse_and_check "
    fun (n:FStar.Ghost.erased u#0 Pulse.Steel.Wrapper.u32)
        (r:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)   
          requires  (Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n))
          ensures _ . (Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r Steel.FractionalPermission.full_perm 
                                                (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n)) ->
          Pulse.Steel.Wrapper.read_alt n r
    ")

 %splice_t[read_alt_with_post2] (parse_and_check "
   fun (n:FStar.Ghost.erased u#0 Pulse.Steel.Wrapper.u32)
       (r1:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
       (r2:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
         requires  (Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r1 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n) *
                    Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r2 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n))
         ensures _ . (Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r1 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n) *
                      Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r2 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n)) ->
         Pulse.Steel.Wrapper.read_alt n r2
   ")

%splice_t[read_refine] (parse_and_check "
    fun (n:FStar.Ghost.erased u#0 Pulse.Steel.Wrapper.u32)
        (r:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
           requires (Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n)) ->
           Pulse.Steel.Wrapper.read_refine n r
     ")

 %splice_t[write] (parse_and_check "
    fun (n:FStar.Ghost.erased u#0 Pulse.Steel.Wrapper.u32)
        (r1:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
        (x:Pulse.Steel.Wrapper.u32)
        (r2:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
          requires (Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r1 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n) *
                    Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r2 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n)) ->
          Pulse.Steel.Wrapper.write n r2 x
    ")

//Bound variable escapes scope
[@@ expect_failure]
 %splice_t[read_alt_write] (parse_and_check  "
     fun (n:FStar.Ghost.erased u#0 Pulse.Steel.Wrapper.u32)
         (r:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
           requires (Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r Steel.FractionalPermission.full_perm 
                                               (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n)) ->
           let x = Pulse.Steel.Wrapper.read_alt n r;
           Pulse.Steel.Wrapper.write n r x
     ")


%splice_t[read_alt_write_alt] (parse_and_check  "
      fun (n:FStar.Ghost.erased u#0 Pulse.Steel.Wrapper.u32)
          (r:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
           requires (Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r Steel.FractionalPermission.full_perm 
                                               (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n)) ->
            let x = Pulse.Steel.Wrapper.read_alt n r;
            Pulse.Steel.Wrapper.write_alt n r x
      ")

%splice_t[swap] (parse_and_check "
    fun (n1:FStar.Ghost.erased u#0 Pulse.Steel.Wrapper.u32)
        (n2:FStar.Ghost.erased u#0 Pulse.Steel.Wrapper.u32)
        (r1:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
        (r2:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
          requires (Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r1 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n1) *
                    Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r2 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n2))
          ensures _.(Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r1 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n2) *
                     Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r2 Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n1)) ->
          let x = Pulse.Steel.Wrapper.read_refine n1 r1;
          let y = Pulse.Steel.Wrapper.read_refine n2 r2;
          Pulse.Steel.Wrapper.write n1 r1 y;
          Pulse.Steel.Wrapper.write n2 r2 x
    ")

[@@ expect_failure]
%splice_t[read_implicit] (parse_and_check "
  fun (#n:FStar.Ghost.erased u#0 Pulse.Steel.Wrapper.u32)
      (r:Steel.ST.Reference.ref Pulse.Steel.Wrapper.u32)
        requires (Steel.ST.Reference.pts_to #Pulse.Steel.Wrapper.u32 r Steel.FractionalPermission.full_perm (FStar.Ghost.reveal u#0 #Pulse.Steel.Wrapper.u32 n)) ->
        Pulse.Steel.Wrapper.read_implicit r
  ")

//This one doesn't work yet ... some bug in translating the quoted term
[@@expect_failure]
%splice_t[swap2] (check (`(fun (n1 n2:erased u#0 u32)
                             (r1 r2:ref u32) ->
                        (let x = read_refine n1 r1 in
                         let y = read_refine n2 r2 in
                         write n1 r1 y;
                         write n2 r2 x) <:
                         stt u#0 unit 
                          (pts_to #u32 r1 full_perm (reveal u#0 #u32 n1) `star` 
                           pts_to #u32 r2 full_perm (reveal u#0 #u32 n2))
                          (fun _ -> 
                           pts_to #u32 r1 full_perm (reveal u#0 #u32 n2) `star` 
                           pts_to #u32 r2 full_perm (reveal u#0 #u32 n1)))))


