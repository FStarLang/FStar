#light "off"
module TestSeq
open Prims
open FStar_Pervasives

let rec print_seq : Prims.int FStar_Seq_Base.seq  ->  Prims.nat  ->  unit = (fun ( s  :  Prims.int FStar_Seq_Base.seq ) ( i  :  Prims.nat ) -> (match ((Prims.op_Equality i (FStar_Seq_Base.length s))) with
| true -> begin
()
end
| uu___ -> begin
((FStar_IO.print_string (Prims.string_of_int (FStar_Seq_Base.index s i)));
(FStar_IO.print_string "\n");
(print_seq s (i + (Prims.parse_int "1")));
)
end))


let main : unit = (

let id = (fun ( i  :  Prims.int ) -> i)
in (

let s = (FStar_Seq_Base.init (Prims.parse_int "10") id)
in (print_seq s (Prims.parse_int "0"))))




