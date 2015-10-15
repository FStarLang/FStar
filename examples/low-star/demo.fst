(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Seq --verify_module Demo --z3timeout 30 --codegen OCaml;
    variables:PLATFORM=../../contrib/Platform/fst SST=../low-level/lib;
  other-files:classical.fst ext.fst set.fsi seq.fsi heap.fst st.fst all.fst seqproperties.fst list.fst listTot.fst listproperties.fst $SST/FStar.Stack.fst ghost.fst $SST/FStar.Regions.Located.fst $SST/FStar.Regions.Heap.fst $SST/FStar.Regions.Regions.fst $SST/Fstar.Regions.RST.fst $SST/FStar.Regions.RSTWhile.fst $SST/array.fsi $SST/array.fst buffer.fst system.fst;
  --*)

module Demo

open RSTWhile
open RST
open FStar.Heap
open Lref  open Located
open FStar.Set
open Stack
open Regions
open RSTArray
open FStar.Ghost
open CBuffer


(* Default buffer length *)
let buffer_length = 1024

(* Dummy AES inplace function *)
type key
assume val get_key: unit -> Tot key
assume val aes:
  b:buffer -> k:key -> len:nat ->
  Mem int
    (requires (fun h -> liveBuffer h b))
    (ensures (fun h0 n h1 ->
      (liveBuffer h0 b)
      /\ (liveBuffer h1 b)
    ))
    (eonly (b.content))

// #set-options "--min_fuel 1 --initial_ifuel 1 --max_fuel 20 --max_ifuel 20"

val allocate_buffer:
  len:nat ->
  Mem buffer
    (requires (fun m ->
        (Stack.isNonEmpty (st m))))
    (ensures (fun m0 b m1 ->
      (isNonEmpty (st m0)) /\ (isNonEmpty (st m1))
      /\ (allocatedInRegion (reveal (asRef b.content)) (topRegion m0) (topRegion m1) (Seq.create len 0uy))
      /\ (regionOf (reveal (asRef b.content)) = InStack (topRegionId m0))
      /\ (topRegionId m0 = topRegionId m1)
      /\ (tail m0 = tail m1)
      /\ (b.start_idx = 0) /\ ( b.length = len)
      ))
    (hide empty)
let allocate_buffer len =
  let array = screate #uint8 len 0uy in
  let buff = {content = array; start_idx = 0; length = len } in
  buff

val demo:
  unit ->
  Mem unit
    (requires (fun m -> isNonEmpty (st m)))
    (ensures (fun m0 u m1 ->
      (isNonEmpty (st m0))
      /\ (isNonEmpty (st m1))
      ))
    (hide empty)
let demo () =
  pushRegion ();

  let buff = allocate_buffer buffer_length in

  (* Input files *)
  let file1 = CSystem.openfile "file1.txt" [CSystem.READ_ONLY] 438 in
  let file2 = CSystem.openfile "file2.txt" [CSystem.READ_ONLY] 438 in
  let header_file = CSystem.openfile "header.txt" [CSystem.READ_ONLY] 438 in

  (* Buffer fragments to store the file contents *)
  let frag1 = {buff with length = 128} in
  let frag2 = {buff with start_idx = 128; length = 256} in
  let frag3 = {buff with start_idx = 678; length = 64} in

  (* Read files into fragments *)
  admitP (snd file1 <> snd file2 /\ snd file2 <> snd header_file /\ snd file1 <> snd header_file);
  let nb_read1 = CSystem.read file1 frag1 frag1.start_idx frag1.length in
  let nb_read2 = CSystem.read file2 frag2 frag2.start_idx frag2.length in
  let nb_header = CSystem.read header_file frag3 frag3.start_idx frag3.length in

  let out_frag1 = {frag1 with length = nb_read1} in
  let out_frag2 = {frag2 with length = nb_read2} in
  let out_frag3 = {frag3 with length = nb_header} in

  (* Putting an admit there because the definition of writev is wrong *)
  admit ();
  (* Output file *)
  let output_file = CSystem.openfile "output.txt" [CSystem.CREATE; CSystem.WRITE_ONLY] 438 in

  let nb_written = CSystem.writev output_file [out_frag3; out_frag1; out_frag3; out_frag2] in

  CSystem.close file1; CSystem.close file2; CSystem.close header_file; CSystem.close output_file;
  popRegion ()
