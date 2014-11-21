module Prims :
  sig
    type double = float
    type uint16 = int
    type int32 = int
    type byte = char
    type uint8 = char
    val ignore : 'a -> unit
    val fst : 'a * 'b -> 'a
    val snd : 'a * 'b -> 'b
    val failwith : string -> 'a
    val try_with : (unit -> 'a) -> (exn -> 'a) -> 'a
  end
module ST : sig val read : 'a ref -> 'a end
module String :
  sig
    val strcat : string -> string -> string
    val split : char list -> string -> string list
    val compare : BatString.t -> BatString.t -> int
    val concat : string -> string list -> string
    val length : string -> int
    val sub : string -> int -> int -> string
  end
module List :
  sig
    val mem : 'a -> 'a list -> bool
    val hd : 'a list -> 'a
    val tl : 'a list -> 'a list
    val nth : 'a list -> int -> 'a
    val length : 'a list -> int
    val rev : 'a list -> 'a list
    val map : ('a -> 'b) -> 'a list -> 'b list
    val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list
    val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
    val map3 :
      ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
    val iter : ('a -> unit) -> 'a list -> unit
    val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
    val append : 'a list -> 'a list -> 'a list
    val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
    val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
    val collect : ('a -> 'b list) -> 'a list -> 'b list
    val unzip : ('a * 'b) list -> 'a list * 'b list
    val unzip3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
    val filter : ('a -> bool) -> 'a list -> 'a list
    val sortWith : ('a -> 'a -> int) -> 'a list -> 'a list
    val forall2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
    val tryFind : ('a -> bool) -> 'a list -> 'a option
    val flatten : 'a list list -> 'a list
    val split : ('a * 'b) list -> 'a list * 'b list
    val choose : ('a -> 'b option) -> 'a list -> 'b list
    val contains : 'a -> 'a list -> bool
  end
module Option :
  sig val isSome : 'a option -> bool val isNone : 'a option -> bool end
module Microsoft :
  sig
    module FStar :
      sig
        module Util :
          sig
            val return_all : 'a -> 'a
            exception Impos
            exception NYI of string
            exception Failure of string
            type proc = {
              inc : in_channel;
              outc : out_channel;
              mutable killed : bool;
            }
            val all_procs : proc list ref
            val start_process : string -> string -> (string -> bool) -> proc
            val ask_process : proc -> string -> string
            val kill_process : proc -> unit
            val kill_all : unit -> unit
            val run_proc :
              string -> string -> string -> bool * string * string
            val write_JSON : 'a -> string -> unit
            val read_JSON : string -> 'a
            val get_file_extension : string -> string
            type 'a set = 'a list * ('a -> 'a -> bool)
            val set_is_empty : 'a set -> bool
            val new_set : ('a -> 'a -> int) -> ('a -> int) -> 'a set
            val set_elements : 'a set -> 'a list
            val set_add : 'a -> 'a set -> 'a list * ('a -> 'a -> bool)
            val set_remove : 'a -> 'a set -> 'a list * ('a -> 'a -> bool)
            val set_mem : 'a -> 'a set -> bool
            val set_union : 'a set -> 'a set -> 'a list * ('a -> 'a -> bool)
            val set_intersect :
              'a set -> 'a set -> 'a list * ('a -> 'a -> bool)
            val set_is_subset_of : 'a set -> 'a set -> bool
            val set_count : 'a set -> int
            val set_difference : 'a set -> 'a set -> 'a set
            type 'value smap = (string, 'value) BatHashtbl.t
            val smap_create : int -> 'value smap
            val smap_clear : 'value smap -> unit
            val smap_add : 'value smap -> string -> 'value -> unit
            val smap_try_find : 'value smap -> string -> 'value option
            val smap_fold :
              'value smap -> (string -> 'value -> 'a -> 'a) -> 'a -> 'a
            val smap_remove : 'value smap -> string -> unit
            val smap_keys : 'value smap -> string list
            val smap_copy : 'value smap -> (string, 'value) BatHashtbl.t
            val pr : ('a, out_channel, unit) format -> 'a
            val spr : ('a, unit, string) format -> 'a
            val fpr : out_channel -> ('a, out_channel, unit) format -> 'a
            val print_string : string -> unit
            val print_any : 'a -> unit
            val strcat : string -> string -> string
            val concat_l : string -> string list -> string
            val string_of_unicode : char array -> string
            val unicode_of_string : string -> char array
            val char_of_int : int -> char
            val int_of_string : string -> int
            val int_of_char : char -> int
            val int_of_uint8 : char -> int
            val uint16_of_int : int -> int
            val float_of_byte : char -> float
            val float_of_int32 : int -> float
            val float_of_int64 : int64 -> float
            val string_of_int : int -> string
            val string_of_float : float -> string
            val string_of_char : char -> string
            val string_of_bytes : char array -> string
            val starts_with : string -> string -> bool
            val trim_string : string -> string
            val ends_with : string -> string -> bool
            val char_at : string -> int -> char
            val is_upper : char -> bool
            val substring_from : string -> int -> string
            val substring : string -> int -> int -> string
            val replace_char : string -> char -> char -> string
            val replace_string : string -> string -> string -> string
            val hashcode : 'a -> int
            val compare : BatString.t -> BatString.t -> int
            val splitlines : string -> string list
            val split : string -> string -> string list
            val iof : float -> int
            val foi : int -> float
            val format : string -> string list -> string
            val format1 : string -> string -> string
            val format2 : string -> string -> string -> string
            val format3 : string -> string -> string -> string -> string
            val format4 :
              string -> string -> string -> string -> string -> string
            val format5 :
              string ->
              string -> string -> string -> string -> string -> string
            val fprint1 : string -> string -> unit
            val fprint2 : string -> string -> string -> unit
            val fprint3 : string -> string -> string -> string -> unit
            val fprint4 :
              string -> string -> string -> string -> string -> unit
            val fprint5 :
              string ->
              string -> string -> string -> string -> string -> unit
            type ('a, 'b) either = Inl of 'a | Inr of 'b
            val left : ('a, 'b) either -> 'a
            val right : ('a, 'b) either -> 'b
            val ( -<- ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
            val find_dup : ('a -> 'a -> bool) -> 'a list -> 'a option
            val nodups : ('a -> 'a -> bool) -> 'a list -> bool
            val remove_dups : ('a -> 'a -> bool) -> 'a list -> 'a list
            val is_some : 'a option -> bool
            val must : 'a option -> 'a
            val dflt : 'a -> 'a option -> 'a
            val find_opt : ('a -> bool) -> 'a list -> 'a option
            val sort_with : ('a -> 'a -> int) -> 'a list -> 'a list
            val set_eq : ('a -> 'a -> int) -> 'a list -> 'a list -> bool
            val bind_opt : 'a option -> ('a -> 'b option) -> 'b option
            val map_opt : 'a option -> ('a -> 'b) -> 'b option
            val find_map : 'a list -> ('a -> 'b option) -> 'b option
            val fold_map :
              ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
            val choose_map :
              ('a -> 'b -> 'a * 'c option) -> 'a -> 'b list -> 'a * 'c list
            val for_all : ('a -> bool) -> 'a list -> bool
            val for_some : ('a -> bool) -> 'a list -> bool
            val forall_exists :
              ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
            val multiset_equiv :
              ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
            val add_unique : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
            val first_N : int -> 'a list -> 'a list * 'a list
            val nth_tail : int -> 'a list -> 'a list
            val prefix : 'a list -> 'a list * 'a
            val prefix_until :
              ('a -> bool) -> 'a list -> ('a list * 'a * 'a list) option
            val string_to_ascii_bytes : string -> char array
            val ascii_bytes_to_string : char array -> string
            val mk_ref : 'a -> 'a ref
            type ('s, 'a) state = 's -> 'a * 's
            val get : ('s, 's) state
            val upd : ('s -> 's) -> ('s, unit) state
            val put : 's -> ('s, unit) state
            val ret : 'a -> ('s, 'a) state
            val bind :
              ('s, 'a) state -> ('a -> ('s, 'b) state) -> ('s, 'b) state
            val ( >> ) :
              ('a, 'b) state -> ('b -> ('a, 'c) state) -> ('a, 'c) state
            val run_st : 's -> ('s, 'a) state -> 'a * 's
            val stmap :
              'a list -> ('a -> ('s, 'b) state) -> ('s, 'b list) state
            val stmapi :
              'a list -> (int -> 'a -> ('s, 'b) state) -> ('s, 'b list) state
            val stiter :
              'a list -> ('a -> ('s, unit) state) -> ('s, unit) state
            val stfoldr_pfx :
              'a list ->
              ('a list -> 'a -> ('s, unit) state) -> ('s, unit) state
            val stfold :
              'b -> 'a list -> ('b -> 'a -> ('s, 'b) state) -> ('s, 'b) state
            type file_handle = out_channel
            val open_file_for_writing : string -> file_handle
            val append_to_file : file_handle -> string -> unit
            val close_file : file_handle -> unit
            val write_file : string -> string -> unit
            val flush_file : file_handle -> unit
            val for_range : int -> int -> (int -> 'a) -> unit
            val incr : int ref -> unit
            val geq : int -> int -> bool
            val expand_environment_variable : string -> string
            val physical_equality : 'a -> 'a -> bool
            val check_sharing : 'a -> 'a -> string -> unit
          end
        module Unionfind :
          sig
            type 'a cell = { mutable contents : 'a contents; }
            and 'a contents = Data of 'a list * Prims.int32 | Fwd of 'a cell
            type 'a uvar = 'a cell
            exception Impos
            val counter : Prims.int32 ref
            val fresh : 'a -> 'a cell
            val rep : 'a cell -> 'a cell
            val find : 'a cell -> 'a
            val uvar_id : 'a cell -> Prims.int32
            val union : 'a cell -> 'a cell -> unit
            val change : 'a cell -> 'a -> unit
            val equivalent : 'a cell -> 'a cell -> bool
          end
        module Platform : sig val exe : string -> string end
        module Getopt :
          sig
            val noshort : char
            type opt_variant =
                ZeroArgs of (unit -> unit)
              | OneArg of (string -> unit) * string
            type opt = char * string * opt_variant * string
            type parse_cmdline_res = Help | Die of string | GoOn
            val parse :
              opt list ->
              (string -> 'a) ->
              string array -> int -> int -> int -> parse_cmdline_res
            val parse_cmdline :
              opt list -> (string -> 'a) -> parse_cmdline_res
          end
        module Range :
          sig
            val b0 : int -> int
            val b1 : int -> int
            val b2 : int -> int
            val b3 : int -> int
            val lor64 : int64 -> int64 -> int64
            val land64 : int64 -> int64 -> int64
            val lsl64 : int64 -> int -> int64
            val lsr64 : int64 -> int -> int64
            val pown32 : int -> int
            val pown64 : int -> int64
            val mask32 : int -> int -> int
            val mask64 : int -> int -> int64
            val string_ord : string -> string -> int
            val int_ord : int -> int -> int
            val int32_ord : Prims.int32 -> Prims.int32 -> int
            val pair_ord :
              ('a -> 'b -> int) * ('c -> 'd -> int) ->
              'a * 'c -> 'b * 'd -> int
            val proj_ord : ('a -> 'b) -> 'a -> 'a -> int
            type file_idx = Prims.int32
            type pos = Prims.int32
            type range = BatInt64.t
            val col_nbits : int
            val line_nbits : int
            val pos_nbits : int
            val pos_col_mask : int
            val line_col_mask : int
            val mk_pos : int -> int -> int
            val line_of_pos : int -> int
            val col_of_pos : int -> int
            val bits_of_pos : pos -> Prims.int32
            val pos_of_bits : Prims.int32 -> pos
            val file_idx_nbits : int
            val start_line_nbits : int
            val start_col_nbits : int
            val end_line_nbits : int
            val end_col_nbits : int
            val file_idx_mask : int64
            val start_line_mask : int64
            val start_col_mask : int64
            val end_line_mask : int64
            val end_col_mask : int64
            val mk_file_idx_range : int -> int -> int -> int64
            val file_idx_of_range : int64 -> int
            val start_line_of_range : int64 -> int
            val start_col_of_range : int64 -> int
            val end_line_of_range : int64 -> int
            val end_col_of_range : int64 -> int
            module FileIndexTable :
              sig
                type 'a t = {
                  indexToFileTable : 'a BatDynArray.t;
                  fileToIndexTable : (string, int) BatHashtbl.t;
                }
                val fileToIndex : string t -> string -> int
                val indexToFile : 'a t -> int -> 'a
              end
            val maxFileIndex : int
            val fileIndexTable : string FileIndexTable.t
            val file_idx_of_file : string -> int
            val file_of_file_idx : int -> string
            val mk_range : string -> int -> int -> int64
            val file_of_range : int64 -> string
            val start_of_range : int64 -> int
            val end_of_range : int64 -> int
            val dest_file_idx_range : int64 -> int * int * int
            val dest_range : int64 -> string * int * int
            val dest_pos : int -> int * int
            val end_range : range -> int64
            val trim_range_right : int64 -> int -> int64
            val pos_ord : int -> int -> int
            val range_ord : int64 -> int64 -> int
            val output_pos : out_channel -> int -> unit
            val output_range : out_channel -> int64 -> unit
            val boutput_pos : Buffer.t -> int -> unit
            val boutput_range : Buffer.t -> int64 -> unit
            val start_range_of_range : int64 -> int64
            val end_range_of_range : int64 -> int64
            val pos_gt : int -> int -> bool
            val pos_eq : int -> int -> bool
            val pos_geq : int -> int -> bool
            val union_ranges : int64 -> int64 -> int64
            val range_contains_range : int64 -> int64 -> bool
            val range_contains_pos : int64 -> int -> bool
            val range_before_pos : int64 -> int -> bool
            val rangeN : string -> int -> int64
            val pos0 : int
            val range0 : int64
            val rangeStartup : int64
            val encode_file_idx : int -> string
            val encode_file : string -> string
            val decode_file_idx : string -> int
            val string_of_pos : int -> string
            val string_of_range : int64 -> string
          end
        module Bytes :
          sig
            val b0 : int -> int
            val b1 : int -> int
            val b2 : int -> int
            val b3 : int -> int
            val dWw1 : int64 -> int
            val dWw0 : int64 -> int
            type bytes = char array
            val length : bytes -> int
            val get : bytes -> int -> int
            val make : (int -> int) -> int -> char array
            val zero_create : int -> bytes
            val really_input : in_channel -> int -> string
            val maybe_input : in_channel -> int -> string
            val output : out_channel -> string -> unit
            val sub : bytes -> int -> int -> char array
            val set : char array -> int -> Prims.int32 -> unit
            val blit : bytes -> int -> char array -> int -> int -> unit
            val string_as_unicode_bytes : string -> char array
            val utf8_bytes_as_string : bytes -> string
            val unicode_bytes_as_string : bytes -> string
            val compare : bytes -> bytes -> int
            val to_intarray : bytes -> int array
            val of_intarray : int array -> char array
            val string_as_utf8_bytes : string -> char array
            val append : bytes -> bytes -> char array
            val string_as_utf8_bytes_null_terminated : string -> char array
            val string_as_unicode_bytes_null_terminated :
              string -> char array
            module Bytestream :
              sig
                type t = { bytes : bytes; mutable pos : int; max : int; }
                val of_bytes : bytes -> int -> int -> t
                val read_byte : t -> int
                val read_bytes : t -> int -> char array
                val position : t -> int
                val clone_and_seek : t -> int -> t
                val skip : t -> int -> unit
                val read_unicode_bytes_as_string : t -> int -> string
                val read_utf8_bytes_as_string : t -> int -> string
              end
            type bytebuf = {
              mutable bbArray : bytes;
              mutable bbCurrent : int;
            }
            module Bytebuf :
              sig
                val create : int -> bytebuf
                val ensure_bytebuf : bytebuf -> int -> unit
                val close : bytebuf -> char array
                val emit_int_as_byte : bytebuf -> Prims.int32 -> unit
                val emit_byte : bytebuf -> char -> unit
                val emit_bool_as_byte : bytebuf -> bool -> unit
                val emit_bytes : bytebuf -> bytes -> unit
                val emit_i32_as_u16 : bytebuf -> int -> unit
                val fixup_i32 : bytebuf -> int -> int -> unit
                val emit_i32 : bytebuf -> int -> unit
                val emit_i64 : bytebuf -> int64 -> unit
                val emit_intarray_as_bytes :
                  bytebuf -> Prims.int32 array -> unit
                val length : bytebuf -> int
                val position : bytebuf -> int
              end
            val create : int -> bytebuf
            val close : bytebuf -> char array
            val emit_int_as_byte : bytebuf -> Prims.int32 -> unit
            val emit_bytes : bytebuf -> bytes -> unit
          end
        module Parser :
          sig
            module Util :
              sig
                type byte = char
                type sbyte = char
                type bytes = char array
                type decimal = float
                type int16 = int
                type int32 = int
                type uint16 = int
                type uint32 = int
                type uint64 = int64
                type single = float
                type double = float
                val parseState : unit
                val newline : Lexing.lexbuf -> unit
                val pos_of_lexpos : Lexing.position -> int
                val mksyn_range : Lexing.position -> Lexing.position -> int64
                val getLexerRange : Lexing.lexbuf -> int64
                val lhs : unit -> int64
                val rhs : unit -> int -> int64
                val rhspos : unit -> int -> int
                val rhs2 : unit -> int -> int -> int64
                exception WrappedError of exn * Range.range
                exception ReportedError
                exception StopProcessing
                val warningHandler : (exn -> unit) ref
                val errorHandler : (exn -> unit) ref
                val errorAndWarningCount : int ref
                val errorR : exn -> unit
                val warning : exn -> unit
              end
          end
      end
  end
