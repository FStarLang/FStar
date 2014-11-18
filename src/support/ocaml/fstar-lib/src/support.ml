module Prims = struct
  (* Fix this... *)
  type double  = float
  type uint16 = int
  type int32 = int

  type byte = char
  type uint8 = char
  let ignore _ = ()
  let fst = fst
  let snd = snd
  let failwith = failwith
  let try_with f1 f2 = try f1 () with | e -> f2 e
end


module ST = struct
  let read x = !x
end


module String = struct
  let strcat s t = s^t
  let split seps s =
    let rec repeat_split acc = function
      | [] -> acc
      | sep::seps ->
         let l = BatList.flatten (BatList.map (fun x -> BatString.nsplit x (BatString.make 1 sep)) acc) in
         repeat_split l seps in
    repeat_split [s] seps
  let compare x y = BatString.compare x y
  let concat = BatString.concat
  let length = BatString.length
end


module List = struct
  let hd = BatList.hd
  let tl = BatList.tl
  let nth = BatList.nth
  let length = BatList.length
  let rev = BatList.rev
  let map = BatList.map
  let mapi = BatList.mapi
  let map2 = BatList.map2
  let rec map3 f l1 l2 l3 =
    match l1, l2, l3 with
      | [], [], [] -> []
      | x::xs, y::ys, z::zs -> (f x y z)::(map3 f xs ys zs)
      | _, _, _ -> failwith "The lists do not have the same length"
  let iter = BatList.iter
  let partition = BatList.partition
  let append = BatList.append
  let fold_left = BatList.fold_left
  let fold_right = BatList.fold_right
  let collect f l = BatList.flatten (BatList.map f l)
  let unzip = BatList.split
  let rec unzip3 = function
    | [] -> ([],[],[])
    | (x,y,z)::xyzs ->
       let (xs,ys,zs) = unzip3 xyzs in
       (x::xs,y::ys,z::zs)
  let filter = BatList.filter
  let sortWith = BatList.sort
  let forall2 = BatList.for_all2
  let tryFind f l = try Some (BatList.find f l) with | Not_found -> None
  let flatten = BatList.flatten
  let split = unzip
  let choose = BatList.filter_map
  let contains x l = BatList.exists (fun y -> x = y) l
end


module Option = struct
  let isSome = function
    | Some _ -> true
    | None -> false
  let isNone o = not (isSome o)
end


module Microsoft = struct
  module FStar = struct


    module Util = struct

      let return_all x = x

      exception Impos
      exception NYI of string
      exception Failure of string

      type proc =
          {inc : in_channel;
           outc : out_channel;
           mutable killed : bool}

      let all_procs : (proc list) ref = ref []

      let start_process (prog:string) (args:string) (cond:string -> bool) : proc =
        let command = prog^" "^args in
        let (inc,outc) = Unix.open_process command in
        let proc = {inc = inc; outc = outc; killed = false} in
        all_procs := proc::!all_procs;
        proc

      let ask_process (p:proc) (stdin:string) : string =
        output_string p.outc stdin;
        flush p.outc;
        input_line p.inc

      let kill_process (p:proc) =
        let _ = Unix.close_process (p.inc, p.outc) in
        p.killed <- true

      let kill_all () =
        List.iter (fun p -> if not p.killed then kill_process p) !all_procs

      let run_proc (name:string) (args:string) (stdin:string) : bool * string * string =
        let command = name^" "^args in
        let (inc,outc) = Unix.open_process command in
        output_string outc stdin;
        let stdout = ref "" in
        try
          while true do
            let l = input_line inc in
            stdout := !stdout^l^"\n"
          done;
          assert false
        with
          | End_of_file ->
             (true, !stdout, "")

      let write_JSON (o :'a) (file: string) :unit = ()
      (* let s = new DataContractJsonSerializerSettings((\*EmitTypeInformation = EmitTypeInformation.Never*\)) in *)
      (* let d = new DataContractJsonSerializer(typeof<'a>, s) in *)
      (* let fs = new FileStream(file, FileMode.Create) *)
      (* d.WriteObject(fs, o) *)
      (* fs.Close() *)

      let read_JSON (file: string) :'a = assert false
      (* let s = new DataContractJsonSerializerSettings((\*EmitTypeInformation = EmitTypeInformation.Never*\)) in *)
      (* let d = new DataContractJsonSerializer(typeof<'a>, s) in *)
      (* let fs = new FileStream(file, FileMode.Open) *)
      (* let o = (d.ReadObject(fs)) :?> 'a in *)
      (* fs.Close(); o *)

      let get_file_extension (fn:string) : string = snd (BatString.rsplit fn ".")

      type 'a set = ('a list) * ('a -> 'a -> bool)

      let set_is_empty ((s, _):'a set) =
        match s with
          | [] -> true
          | _ -> false

      let new_set (cmp:'a -> 'a -> int) (hash:'a -> int) : 'a set =
        ([], fun x y -> cmp x y = 0)

      let set_elements ((s1, eq):'a set) : 'a list =
        let rec aux out = function
          | [] -> out
          | hd::tl ->
             if BatList.exists (eq hd) out then
               aux out tl
             else
               aux (hd::out) tl in
        aux [] s1
      let set_add a ((s, b):'a set) = (a::s, b)
      let set_remove x ((s1, eq):'a set) =
        (BatList.filter (fun y -> not (eq x y)) s1, eq)
      let set_mem a ((s, b):'a set) = BatList.exists (b a) s
      let set_union ((s1, b):'a set) ((s2, _):'a set) = (s1@s2, b)
      let set_intersect ((s1, eq):'a set) ((s2, _):'a set) =
        (BatList.filter (fun y -> BatList.exists (eq y) s2) s1, eq)
      let set_is_subset_of ((s1, eq):'a set) ((s2, _):'a set) =
        BatList.for_all (fun y -> BatList.exists (eq y) s2) s1
      let set_count ((s1, _):'a set) = BatList.length s1
      let set_difference ((s1, eq):'a set) ((s2, _):'a set) : 'a set =
        (BatList.filter (fun y -> not (BatList.exists (eq y) s2)) s1, eq)

      type 'value smap = (string, 'value) BatHashtbl.t
      let smap_create (i:int) : 'value smap = BatHashtbl.create i
      let smap_clear (s:('value smap)) = BatHashtbl.clear s
      let smap_add (m:'value smap) k (v:'value) = BatHashtbl.add m k v
      let smap_try_find (m:'value smap) k = BatHashtbl.find_option m k
      let smap_fold (m:'value smap) f a = BatHashtbl.fold f m a
      let smap_remove (m:'value smap) k = BatHashtbl.remove m k
      let smap_keys (m:'value smap) = smap_fold m (fun k _ acc -> k::acc) []
      let smap_copy (m:'value smap) = BatHashtbl.copy m

      let pr  = Printf.printf
      let spr = Printf.sprintf
      let fpr = Printf.fprintf

      let print_string s = pr "%s" s
      let print_any s = output_value stdout s
      let strcat s1 s2 = s1 ^ s2
      let concat_l sep (l:string list) = BatString.concat sep l

      let string_of_unicode (bytes:char array) =
        BatArray.fold_left (fun acc b -> acc^(BatUTF8.init 1 (fun _ -> BatUChar.of_char b))) "" bytes
      let unicode_of_string (string:string) =
        let n = BatUTF8.length string in
        let t = Array.create n 'x' in
        let i = ref 0 in
        BatUTF8.iter (fun c -> t.(!i) <- BatUChar.char_of c; incr i) string;
        t

      let char_of_int = char_of_int
      let int_of_string = int_of_string
      let int_of_char = int_of_char
      let int_of_uint8 = int_of_char
      let uint16_of_int (i:int) = i

      let float_of_byte b = float_of_int (int_of_char b)
      let float_of_int32 = float_of_int
      let float_of_int64 = BatInt64.to_float

      let string_of_int = string_of_int
      let string_of_float = string_of_float
      let string_of_char  (i:char) = spr "%c" i
      let string_of_bytes = string_of_unicode
      let starts_with = BatString.starts_with
      let trim_string = BatString.trim
      let ends_with = BatString.ends_with
      let char_at = BatString.get
      let is_upper (c:char) = 'A' <= c && c <= 'Z'
      let substring_from = BatString.tail
      let substring = BatString.sub
      let replace_char (s:string) (c1:char) (c2:char) =
        BatString.map (fun c -> if c = c1 then c2 else c) s
      let replace_string (s:string) (s1:string) (s2:string) =
        BatString.rev (BatString.nreplace ~str:(BatString.rev s) ~sub:s1 ~by:s2)
      let hashcode s = BatHashtbl.hash s
      let compare s1 s2 = BatString.compare s1 s2
      let splitlines s = BatString.nsplit s "\n"
      let split s sep = BatString.nsplit s sep

      let iof = int_of_float
      let foi = float_of_int

      let format (fmt:string) (args:string list) =
        let frags = BatString.nsplit fmt "%s" in
        if BatList.length frags <> BatList.length args + 1 then
          failwith ("Not enough arguments to format string " ^fmt^ " : expected " ^ (string_of_int (BatList.length frags)) ^ " got [" ^ (BatString.concat ", " args) ^ "] frags are [" ^ (BatString.concat ", " frags) ^ "]")
        else
          let args = args@[""] in
          BatList.fold_left2 (fun out frag arg -> out ^ frag ^ arg) "" frags args

      let format1 f a = format f [a]
      let format2 f a b = format f [a;b]
      let format3 f a b c = format f [a;b;c]
      let format4 f a b c d = format f [a;b;c;d]
      let format5 f a b c d e = format f [a;b;c;d;e]

      let fprint1 a b = print_string (format1 a b)
      let fprint2 a b c = print_string (format2 a b c)
      let fprint3 a b c d = print_string (format3 a b c d)
      let fprint4 a b c d e = print_string (format4 a b c d e)
      let fprint5 a b c d e f = print_string (format5 a b c d e f)

      type ('a,'b) either =
        | Inl of 'a
        | Inr of 'b

      let left = function
        | Inl x -> x
        | _ -> failwith "Not in left"
      let right = function
        | Inr x -> x
        | _ -> failwith "Not in right"

      let (-<-) f g x = f (g x)

      let find_dup f l =
        let rec aux = function
          | hd::tl ->
             let hds, tl' = BatList.partition (f hd) tl in
             (match hds with
                | [] -> aux tl'
                | _ -> Some hd)
          | _ -> None in
        aux l

      let nodups f l = match find_dup f l with | None -> true | _ -> false

      let remove_dups f l =
        let rec aux out = function
          | hd::tl -> let _, tl' = BatList.partition (f hd) tl in aux (hd::out) tl'
          | _ -> out in
        aux [] l

      let is_some = function
        | None -> false
        | Some _ -> true

      let must = function
        | Some x -> x
        | None -> failwith "Empty option"

      let dflt x = function
        | None   -> x
        | Some x -> x

      let find_opt f l =
        let rec aux = function
          | [] -> None
          | hd::tl -> if f hd then Some hd else aux tl in
        aux l

      let sort_with = BatList.sort

      let set_eq f l1 l2 =
        let l1 = sort_with f l1 in
        let l2 = sort_with f l2 in
        BatList.for_all2 (fun l1 l2 -> f l1 l2 = 0) l1 l2

      let bind_opt opt f =
        match opt with
          | None -> None
          | Some x -> f x

      let map_opt opt f =
        match opt with
          | None -> None
          | Some x -> Some (f x)

      let rec find_map l f =
        match l with
          | [] -> None
          | x::tl ->
             match f x with
               | None -> find_map tl f
               | y -> y

      let fold_map f state s =
        let fold (state, acc) x =
          let state, v = f state x in (state, v :: acc) in
        let (state, rs) = BatList.fold_left fold (state, []) s in
        (state, BatList.rev rs)

      let choose_map f state s =
        let fold (state, acc) x =
          match f state x with
            | state, None   -> (state, acc)
            | state, Some v -> (state, v :: acc) in
        let (state, rs) = BatList.fold_left fold (state, []) s in
        (state, BatList.rev rs)

      let for_all f l = BatList.for_all f l
      let for_some f l = BatList.exists f l
      let forall_exists rel l1 l2 =
        for_all (fun x -> for_some (rel x) l2) l1
      let multiset_equiv rel l1 l2 =
        BatList.length l1 = BatList.length l2 && forall_exists rel l1 l2

      let add_unique f x l =
        if for_some (f x) l then
          l
        else
          x::l

      let first_N n l =
        let rec f acc i l =
          if i = n then BatList.rev acc,l else
            match l with
              | h::tl -> f (h::acc) (i+1) tl
              | _     -> failwith "firstN"
        in
        f [] 0 l

      let rec nth_tail n l =
        if n=0 then l else nth_tail (n - 1) (BatList.tl l)

      let prefix l =
        match BatList.rev l with
          | hd::tl -> BatList.rev tl, hd
          | _ -> failwith "impossible"

      let prefix_until f l =
        let rec aux prefix = function
          | [] -> None
          | hd::tl ->
             if f hd then Some (BatList.rev prefix, hd, tl)
             else aux (hd::prefix) tl in
        aux [] l

      let string_to_ascii_bytes (s:string) : char array =
        BatArray.of_list (BatString.explode s)
      let ascii_bytes_to_string (b:char array) : string =
        BatString.implode (BatArray.to_list b)
      let mk_ref a = ref a

      (* A simple state monad *)
      type ('s,'a) state = 's -> ('a*'s)
      let get : ('s,'s) state = fun s -> (s,s)
      let upd (f:'s -> 's) : ('s,unit) state = fun s -> ((), f s)
      let put (s:'s) : ('s,unit) state = fun _ -> ((), s)
      let ret (x:'a) : ('s,'a) state = fun s -> (x, s)
      let bind (sa:('s,'a) state) (f : 'a -> ('s,'b) state) : ('s,'b) state =
        fun s1 -> let (a, s2) = sa s1 in f a s2
      let (>>) s f = bind s f
      let run_st init (s:('s,'a) state) = s init

      let rec stmap (l:'a list) (f: 'a -> ('s,'b) state) : ('s, ('b list)) state =
        match l with
          | [] -> ret []
          | hd::tl -> bind (f hd)
                           (fun b ->
                            let stl = stmap tl f in
                            bind stl (fun tl -> ret (b::tl)))

      let stmapi (l:'a list) (f:int -> 'a -> ('s, 'b) state) : ('s, ('b list)) state =
        let rec aux i l =
          match l with
            | [] -> ret []
            | hd::tl ->
               bind (f i hd)
                    (fun b ->
                     let stl = aux (i + 1) tl in
                     bind stl (fun tl -> ret (b::tl))) in
        aux 0 l

      let rec stiter (l:'a list) (f: 'a -> ('s,unit) state) : ('s,unit) state =
        match l with
          | [] -> ret ()
          | hd::tl -> bind (f hd) (fun () -> stiter tl f)

      let rec stfoldr_pfx (l:'a list) (f: 'a list -> 'a -> ('s,unit) state) : ('s,unit) state =
        match l with
          | [] -> ret ()
          | hd::tl -> (stfoldr_pfx tl f) >> (fun _ -> f tl hd)

      let rec stfold (init:'b) (l:'a list) (f: 'b -> 'a -> ('s,'b) state) : ('s,'b) state =
        match l with
          | [] -> ret init
          | hd::tl -> (f init hd) >> (fun next -> stfold next tl f)

      type file_handle = out_channel
      let open_file_for_writing (fn:string) : file_handle = open_out fn
      let append_to_file (fh:file_handle) s = fpr fh "%s\n" s; flush fh
      let close_file (fh:file_handle) = close_out fh
      let write_file (fn:string) s =
        let fh = open_file_for_writing fn in
        append_to_file fh s;
        close_file fh
      let flush_file (fh:file_handle) = flush fh

      let for_range lo hi f =
        for i = lo to hi do
          f i
        done

      let incr r = r := !r + 1
      let geq (i:int) (j:int) = i >= j

      let expand_environment_variable = Sys.getenv

      let physical_equality (x:'a) (y:'a) = x == y
      let check_sharing a b msg = if physical_equality a b then fprint1 "Sharing OK: %s\n" msg else fprint1 "Sharing broken in %s\n" msg


    end


    module Unionfind = struct
    (* Unionfind with path compression but without ranks *)

      type 'a cell = {mutable contents : 'a contents}
       and 'a contents =
         | Data of 'a list * Prims.int32
         | Fwd of 'a cell
      type 'a uvar = 'a cell

      exception Impos

      let counter = ref 0

      let fresh x = counter := !counter + 1; {contents = Data ([x], !counter) }

      let rec rep cell = match cell.contents with
          | Data _ -> cell
          | Fwd cell' ->
             if cell == cell' then
               failwith "YIKES! Cycle in unionfind graph"
             else
               rep cell'

      let find x =
        let y = rep x in
        if not (x == y) then x.contents <- Fwd y; (* path compression *)
        match y.contents with
          | Data ((hd::tl), _) -> hd
          | _ -> failwith "impossible"

      let uvar_id uv = match (rep uv).contents with
          | Data (_, id) -> id
          | _ -> failwith "impossible"

      let union x y =
        let cellX = rep x in
        let cellY = rep y in
        if cellX == cellY then
          ()
        else
          match cellX.contents, cellY.contents with
            | Data (dx, ctrx), Data (dy,_) ->
               cellX.contents <- Data ((dx@dy), ctrx);
               cellY.contents <- Fwd cellX
            | _ -> failwith "impossible"

      let change x a =
        let cellX = rep x in
        match cellX.contents with
	  | Data (_, ctrX) ->
	     cellX.contents <- Data ([a],ctrX)
          | _ -> failwith "impossible"

      let equivalent x y =
        (rep x) == (rep y)

    end


    module Platform = struct
      let exe name =
        if Sys.unix then
          name
        else
          name^".exe"
    end


    module Getopt = struct
      let noshort='\000'
      type opt_variant =
        | ZeroArgs of (unit -> unit)
        | OneArg of (string -> unit) * string
    end


    module Range = struct
      let b0 n =  (n          land 0xFF)
      let b1 n =  ((n lsr 8)  land 0xFF)
      let b2 n =  ((n lsr 16) land 0xFF)
      let b3 n =  ((n lsr 24) land 0xFF)

      let lor64 = BatInt64.logor
      let land64 = BatInt64.logand
      let lsl64 = BatInt64.shift_left
      let lsr64 = BatInt64.shift_right

      let rec pown32 n = if n = 0 then 0  else (pown32 (n-1) lor (1 lsl (n-1)))
      let rec pown64 n = if n = 0 then 0L else (lor64 (pown64 (n-1)) (lsl64 1L (n-1)))
      let mask32 m n = (pown32 n) lsl m
      let mask64 m n = lsl64 (pown64 n) m

      let string_ord (a:string) (b:string) = compare a b
      let int_ord (a:int) (b:int) = compare a b
      let int32_ord (a:Prims.int32) (b:Prims.int32) = compare a b

      let pair_ord (compare1,compare2) (a1,a2) (aa1,aa2) =
        let res1 = compare1 a1 aa1 in
        if res1 <> 0 then res1 else compare2 a2 aa2

      let proj_ord f a1 a2 = compare (f a1)  (f a2)

      type file_idx = Prims.int32
      type pos = Prims.int32
      type range = BatInt64.t

      let col_nbits  = 9
      let line_nbits  = 16

      let pos_nbits = line_nbits + col_nbits
      let _ = assert (pos_nbits <= 32)
      let pos_col_mask  = mask32 0         col_nbits
      let line_col_mask = mask32 col_nbits line_nbits

      let mk_pos l c =
        let l = max 0 l in
        let c = max 0 c in
        (c land pos_col_mask)
        lor ((l lsl col_nbits) land line_col_mask)
      let line_of_pos p =  (p lsr col_nbits)
      let col_of_pos p =  (p land pos_col_mask)

      let bits_of_pos (x:pos) : Prims.int32 = x
      let pos_of_bits (x:Prims.int32) : pos = x

      let file_idx_nbits = 14
      let start_line_nbits = line_nbits
      let start_col_nbits = col_nbits
      let end_line_nbits = line_nbits
      let end_col_nbits = col_nbits
      let _ = assert (file_idx_nbits + start_line_nbits + start_col_nbits + end_line_nbits + end_col_nbits = 64)

      let file_idx_mask   = mask64 0 file_idx_nbits
      let start_line_mask = mask64 (file_idx_nbits) start_line_nbits
      let start_col_mask  = mask64 (file_idx_nbits + start_line_nbits) start_col_nbits
      let end_line_mask   = mask64 (file_idx_nbits + start_line_nbits + start_col_nbits) end_line_nbits
      let end_col_mask    = mask64 (file_idx_nbits + start_line_nbits + start_col_nbits + end_line_nbits) end_col_nbits

      let mk_file_idx_range fidx b e =
        lor64
          (lor64
             (lor64
                (lor64
                   (BatInt64.of_int fidx)
                   (lsl64 (BatInt64.of_int (line_of_pos b)) file_idx_nbits))
                (lsl64 (BatInt64.of_int (col_of_pos b)) (file_idx_nbits + start_line_nbits)))
             (lsl64 (BatInt64.of_int (line_of_pos e)) (file_idx_nbits + start_line_nbits + start_col_nbits)))
          (lsl64 (BatInt64.of_int (col_of_pos e)) (file_idx_nbits + start_line_nbits + start_col_nbits + end_line_nbits))
      let file_idx_of_range r   = BatInt64.to_int (land64 r file_idx_mask)
      let start_line_of_range r = BatInt64.to_int (lsr64 (land64 r start_line_mask) file_idx_nbits)
      let start_col_of_range r  = BatInt64.to_int (lsr64 (land64 r start_col_mask) (file_idx_nbits + start_line_nbits))
      let end_line_of_range r   = BatInt64.to_int (lsr64 (land64 r end_line_mask) (file_idx_nbits + start_line_nbits + start_col_nbits))
      let end_col_of_range r    = BatInt64.to_int (lsr64 (land64 r end_col_mask) (file_idx_nbits + start_line_nbits + start_col_nbits + end_line_nbits))

      (* This is just a standard unique-index table *)
      module FileIndexTable = struct
        type 'a t = {
          indexToFileTable : 'a BatDynArray.t;
          fileToIndexTable  : (string, int) BatHashtbl.t
        }
        let fileToIndex t f =
          try
            BatHashtbl.find t.fileToIndexTable f
          with
            | Not_found ->
               let n = BatDynArray.length t.indexToFileTable in
               BatDynArray.add t.indexToFileTable f;
               BatHashtbl.add t.fileToIndexTable f n;
               n
        let indexToFile t n =
          (if n < 0 then failwith ("file_of_file_idx: negative argument: n = "^(string_of_int n)^"\n"));
          (if n >= BatDynArray.length t.indexToFileTable then failwith ("file_of_file_idx: invalid argument: n = "^(string_of_int n)^"\n"));
          BatDynArray.get t.indexToFileTable n
      end
      open FileIndexTable

      let maxFileIndex = pown32 file_idx_nbits

      let fileIndexTable = {
        indexToFileTable = BatDynArray.make 11;
        fileToIndexTable = BatHashtbl.create 11
      }
      let file_idx_of_file f = (fileToIndex fileIndexTable f) mod maxFileIndex
      let file_of_file_idx n = indexToFile fileIndexTable n

      let mk_range f b e = mk_file_idx_range (file_idx_of_file f) b e
      let file_of_range r = file_of_file_idx (file_idx_of_range r)

      let start_of_range r = mk_pos (start_line_of_range r) (start_col_of_range r)
      let end_of_range r = mk_pos (end_line_of_range r) (end_col_of_range r)
      let dest_file_idx_range r = file_idx_of_range r,start_of_range r,end_of_range r
      let dest_range r = file_of_range r,start_of_range r,end_of_range r
      let dest_pos p = line_of_pos p,col_of_pos p
      let end_range (r:range) = mk_range (file_of_range r) (end_of_range r) (end_of_range r)

      let trim_range_right r n =
        let fidx,p1,p2 = dest_file_idx_range r in
        let l2,c2 = dest_pos p2 in
        mk_file_idx_range fidx p1 (mk_pos l2 (max 0 (c2 - n)))

      let pos_ord   p1 p2 = pair_ord (int_ord   ,int_ord) (dest_pos p1) (dest_pos p2)
      (* range_ord: not a total order, but enough to sort on ranges *)
      let range_ord r1 r2 = pair_ord (string_ord,pos_ord) (file_of_range r1,start_of_range r1) (file_of_range r2,start_of_range r2)

      let output_pos (os:out_channel) m = Printf.fprintf os "(%d,%d)" (line_of_pos m) (col_of_pos m)
      let output_range (os:out_channel) m = Printf.fprintf os "%s%a-%a" (file_of_range m) output_pos (start_of_range m) output_pos (end_of_range m)
      let boutput_pos os m = Printf.bprintf os "(%d,%d)" (line_of_pos m) (col_of_pos m)
      let boutput_range os m = Printf.bprintf os "%s%a-%a" (file_of_range m) boutput_pos (start_of_range m) boutput_pos (end_of_range m)

      let start_range_of_range m =    let f,s,e = dest_file_idx_range m in mk_file_idx_range f s s
      let end_range_of_range m =   let f,s,e = dest_file_idx_range m in mk_file_idx_range f e e
      let pos_gt p1 p2 =
        (line_of_pos p1 > line_of_pos p2 ||
           (line_of_pos p1 = line_of_pos p2 &&
              col_of_pos p1 > col_of_pos p2))

      let pos_eq p1 p2 = (line_of_pos p1 = line_of_pos p2 &&  col_of_pos p1 = col_of_pos p2)
      let pos_geq p1 p2 = pos_eq p1 p2 || pos_gt p1 p2

      let union_ranges m1 m2 =
        if file_idx_of_range m1 <> file_idx_of_range m2 then m2 else
          let b =
            if pos_geq (start_of_range m1) (start_of_range m2) then (start_of_range m2)
            else (start_of_range m1) in
          let e =
            if pos_geq (end_of_range m1) (end_of_range m2) then (end_of_range m1)
            else (end_of_range m2) in
          mk_file_idx_range (file_idx_of_range m1) b e

      let range_contains_range m1 m2 =
        (file_of_range m1) = (file_of_range m2) &&
          pos_geq (start_of_range m2) (start_of_range m1) &&
            pos_geq (end_of_range m1) (end_of_range m2)

      let range_contains_pos m1 p =
        pos_geq p (start_of_range m1) &&
          pos_geq (end_of_range m1) p

      let range_before_pos m1 p =
        pos_geq p (end_of_range m1)

      let rangeN filename line =  mk_range filename (mk_pos line 0) (mk_pos line 80)
      let pos0 = mk_pos 1 0
      let range0 =  rangeN "unknown" 1
      let rangeStartup = rangeN "startup" 1

      (* // Store a file_idx in the pos_fname field, so we don't have to look up the  *)
      (* // file_idx hash table to map back from pos_fname to a file_idx during lexing  *)
      let encode_file_idx idx =
        Util.string_of_unicode [|char_of_int (idx land 0x7F); char_of_int ((idx lsr 7) land 0x7F)|]

      let encode_file file = encode_file_idx (file_idx_of_file file)

      let _ = assert (file_idx_nbits <= 14) (* this encoding is size limited *)
      let decode_file_idx (s:string) =
        if BatString.length s = 0 then 0 else
          let idx =   (int_of_char (BatString.get s 0))
                      lor ((int_of_char (BatString.get s 1)) lsl 7) in
          idx

      (* For Diagnostics *)
      let string_of_pos   pos = let line,col = line_of_pos pos,col_of_pos pos in Printf.sprintf "%d,%d" line col
      let string_of_range r   = Printf.sprintf "%s(%s-%s)" (file_of_range r) (string_of_pos (start_of_range r)) (string_of_pos (end_of_range r))

    end


    module Bytes = struct
      let b0 n =  (n land 0xFF)
      let b1 n =  ((n lsr 8) land 0xFF)
      let b2 n =  ((n lsr 16) land 0xFF)
      let b3 n =  ((n lsr 24) land 0xFF)

      let dWw1 n = BatInt64.to_int (BatInt64.logand (BatInt64.shift_right n 32) 0xFFFFFFFFL)
      let dWw0 n = BatInt64.to_int (BatInt64.logand n 0xFFFFFFFFL)

      type bytes = char array

      let length (b:bytes) = BatArray.length b
      let get (b:bytes) n = int_of_char (BatArray.get b n)
      let make (f : _ -> int) n = BatArray.init n (fun i -> char_of_int (f i))
      let zero_create n : bytes = BatArray.create n (char_of_int 0)

      let really_input (is:in_channel) n =
        let buff = BatString.init n (fun _ -> char_of_int 0) in
        really_input is buff 0 n;
        buff

      let maybe_input (is:in_channel) n =
        let buff = BatString.init n (fun _ -> char_of_int 0) in
        let x = input is buff 0 n in
        BatString.sub buff 0 x

      let output (os:out_channel) b =
        Pervasives.output os b 0 (BatString.length b)

      let sub ( b:bytes) s l = BatArray.sub b s l
      let set bb n (b:Prims.int32) = BatArray.set bb n (char_of_int b)
      let blit (a:bytes) b c d e = BatArray.blit a b c d e
      let string_as_unicode_bytes (s:string) = Util.unicode_of_string s
      let utf8_bytes_as_string (b:bytes) = Util.string_of_unicode b
      let unicode_bytes_as_string (b:bytes) = Util.string_of_unicode b
      let compare (b1:bytes) (b2:bytes) = compare b1 b2

      let to_intarray (b:bytes) =  BatArray.map int_of_char b
      let of_intarray (arr:int array) = BatArray.map char_of_int arr

      let string_as_utf8_bytes (s:string) = Util.unicode_of_string s

      let append (b1: bytes) (b2:bytes) = BatArray.append b1 b2

      let string_as_utf8_bytes_null_terminated (s:string) =
        append (string_as_utf8_bytes s) (of_intarray [| 0x0 |])

      let string_as_unicode_bytes_null_terminated (s:string) =
        append (string_as_unicode_bytes s) (of_intarray [| 0x0 |])


      module Bytestream = struct
        type t = { bytes: bytes; mutable pos: int; max: int }

        let of_bytes b n len =
          if n < 0 || (n+len) > length b then failwith "Bytestream.of_bytes";
          { bytes = b; pos = n; max = n+len }

        let read_byte b  =
          if b.pos >= b.max then failwith "Bytestream.of_bytes.read_byte: end of stream";
          let res = get b.bytes b.pos in
          b.pos <- b.pos + 1;
          res

        let read_bytes b n  =
          if b.pos + n > b.max then failwith "Bytestream.read_bytes: end of stream";
          let res = sub b.bytes b.pos n in
          b.pos <- b.pos + n;
          res

        let position b = b.pos
        let clone_and_seek b pos = { bytes=b.bytes; pos=pos; max=b.max }
        let skip b n = b.pos <- b.pos + n

        let read_unicode_bytes_as_string (b:t) n =
          let res = ref "" in
          for i = 0 to (n-1) do
            res := !res^(BatUTF8.init 1 (fun _ -> BatUChar.of_char (b.bytes.(b.pos + i))))
          done;
          b.pos <- b.pos + n;
          !res

        let read_utf8_bytes_as_string (b:t) n =
          let res = ref "" in
          for i = 0 to (n-1) do
            res := !res^(BatUTF8.init 1 (fun _ -> BatUChar.of_char (b.bytes.(b.pos + i))))
          done;
          b.pos <- b.pos + n;
          !res
      end

      type bytebuf =
          { mutable bbArray: bytes;
            mutable bbCurrent: int }

      module Bytebuf = struct
        let create sz =
          { bbArray=zero_create sz;
            bbCurrent = 0; }

        let ensure_bytebuf buf new_size =
          let old_buf_size = BatArray.length buf.bbArray in
          if new_size > old_buf_size then (
            let old = buf.bbArray in
            buf.bbArray <- zero_create (max new_size (old_buf_size * 2));
            blit old 0 buf.bbArray 0 buf.bbCurrent
          )

        let close buf = sub buf.bbArray 0 buf.bbCurrent

        let emit_int_as_byte buf i =
          let new_size = buf.bbCurrent + 1 in
          ensure_bytebuf buf new_size;
          set buf.bbArray buf.bbCurrent i;
          buf.bbCurrent <- new_size

        let emit_byte buf (b:char) = emit_int_as_byte buf (int_of_char b)
        let emit_bool_as_byte buf (b:bool) = emit_int_as_byte buf (if b then 1 else 0)

        let emit_bytes buf i =
          let n = length i in
          let new_size = buf.bbCurrent + n in
          ensure_bytebuf buf new_size;
          blit i 0 buf.bbArray buf.bbCurrent n;
          buf.bbCurrent <- new_size

        let emit_i32_as_u16 buf n =
          let new_size = buf.bbCurrent + 2 in
          ensure_bytebuf buf new_size;
          set buf.bbArray buf.bbCurrent (b0 n);
          set buf.bbArray (buf.bbCurrent + 1) (b1 n);
          buf.bbCurrent <- new_size

        (* let emit_u16 buf (x:uint16) = emit_i32_as_u16 buf (BatInt64.to_int x) *)

        let fixup_i32 bb pos n =
          set bb.bbArray pos (b0 n);
          set bb.bbArray (pos + 1) (b1 n);
          set bb.bbArray (pos + 2) (b2 n);
          set bb.bbArray (pos + 3) (b3 n)

        let emit_i32 buf n =
          let new_size = buf.bbCurrent + 4 in
          ensure_bytebuf buf new_size;
          fixup_i32 buf buf.bbCurrent n;
          buf.bbCurrent <- new_size

        let emit_i64 buf x =
          emit_i32 buf (dWw0 x);
          emit_i32 buf (dWw1 x)

        let emit_intarray_as_bytes buf arr =
          let n = BatArray.length arr in
          let new_size = buf.bbCurrent + n in
          ensure_bytebuf buf new_size;
          let bbarr = buf.bbArray in
          let bbbase = buf.bbCurrent in
          for i= 0 to n - 1 do set bbarr (bbbase + i) (BatArray.get arr i) done;
          buf.bbCurrent <- new_size

        let length bb = bb.bbCurrent
        let position bb = bb.bbCurrent
      end

      let create i = Bytebuf.create i
      let close t = Bytebuf.close t
      let emit_int_as_byte t i = Bytebuf.emit_int_as_byte t i
      let emit_bytes t b = Bytebuf.emit_bytes t b
    end


    module Parser = struct
      module ParseIt = struct
        let parse_file _ = assert false
      end
    end


  end
end
