module Prims = struct
  (* Fix this... *)
  type double  = float
  type int32 = int

  type byte = char
  let pipe_left f = f
  let pipe_right x f = f x
  let ignore _ = ()
  let fst = fst
  let snd = snd
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
end


module List = struct
  let map = BatList.map
  let iter = BatList.iter
  let partition = BatList.partition
  let append = BatList.append
  let fold_left = BatList.fold_left
end


module Microsoft = struct
  module FStar = struct


    module Util = struct

      let return_all x = x

      exception Impos
      exception NYI of string
      exception Failure of string

      type proc = unit
      (* type proc = {m:BatConcurrent.lock; *)
      (*              outbuf:StringBuilder; *)
      (*              proc:Process; *)
      (*              killed:bool ref} *)
      let all_procs : (proc list) ref = ref []

      let start_process (prog:string) (args:string) (cond:string -> bool) : proc = ()
      (* let signal = new Object() in *)
      (* let with_sig f = *)
      (*     System.Threading.Monitor.Enter(signal); *)
      (*     let res = f() in *)
      (*     System.Threading.Monitor.Exit(signal); *)
      (*     res in *)
      (* let startInfo = new ProcessStartInfo() in *)
      (* let driverOutput = new StringBuilder() in *)
      (* let killed = ref false in *)
      (* let proc = new Process() in *)
      (*     startInfo.FileName <- prog; *)
      (*     startInfo.Arguments <- args; *)
      (*     startInfo.UseShellExecute <- false; *)
      (*     startInfo.RedirectStandardOutput <- true; *)
      (*     startInfo.RedirectStandardInput <- true; *)
      (*     proc.EnableRaisingEvents <- true; *)
      (*     proc.OutputDataReceived.AddHandler( *)
      (*          DataReceivedEventHandler(fun _ args -> *)
      (*             if !killed then () *)
      (*             else with_sig(fun () -> *)
      (*                        ignore <| driverOutput.Append(args.Data); *)
      (*                        ignore <| driverOutput.Append("\n"); *)
      (*                        if null = args.Data *)
      (*                        then (Printf.printf "Unexpected output from %s\n%s\n" prog (driverOutput.ToString())); *)
      (*                        if null = args.Data || cond args.Data *)
      (*                        then System.Threading.Monitor.Pulse(signal)))); *)
      (*     proc.Exited.AddHandler( *)
      (*          EventHandler(fun _ _ -> *)
      (*             if !killed then () *)
      (*             else *)
      (*                 System.Threading.Monitor.Enter(signal); *)
      (*                 killed := true; *)
      (*                 Printf.fprintf stdout "%s exited inadvertently\n%s\n" prog (driverOutput.ToString()); *)
      (*                 stdout.Flush(); *)
      (*                 System.Threading.Monitor.Exit(signal); *)
      (*                 exit(1))); *)
      (*     proc.StartInfo <- startInfo; *)
      (*     proc.Start() |> ignore; *)
      (*     proc.BeginOutputReadLine(); *)
      (*     let proc = {m=signal; *)
      (*                 outbuf=driverOutput; *)
      (*                 proc=proc; *)
      (*                 killed=killed} in *)
      (*     all_procs := proc::!all_procs; *)
      (*     proc *)

      let ask_process (p:proc) (stdin:string) : string = "Not implemented yet"
      (* ignore <| p.outbuf.Clear(); *)
      (* System.Threading.Monitor.Enter(p.m); *)
      (* p.proc.StandardInput.WriteLine(stdin); *)
      (* ignore <| System.Threading.Monitor.Wait(p.m); *)
      (* System.Threading.Monitor.Exit(p.m); *)
      (* p.outbuf.ToString() *)

      let kill_process (p:proc) = ()
      (* p.killed := true; *)
      (* System.Threading.Monitor.Enter(p.m); *)
      (* p.proc.StandardInput.Close(); *)
      (* System.Threading.Monitor.Exit(p.m); *)
      (* p.proc.WaitForExit() *)

      let kill_all () = ()
      (* List.iter (fun p -> if not !p.killed then kill_process p) !all_procs *)

      let run_proc (name:string) (args:string) (stdin:string) : bool * string * string = (true, "Not implemented yet", "Not implemented yet")
      (* let pinfo = new ProcessStartInfo(name, args) in *)
      (* pinfo.RedirectStandardOutput <- true; *)
      (* pinfo.RedirectStandardError <- true; *)
      (* pinfo.UseShellExecute <- false; *)
      (* pinfo.RedirectStandardInput <- true; *)
      (* let proc = new Process() in *)
      (* proc.StartInfo <- pinfo; *)
      (* let result = proc.Start() in *)
      (* proc.StandardInput.Write(stdin); *)
      (* let stdout = proc.StandardOutput.ReadToEnd() in *)
      (* let stderr = proc.StandardError.ReadToEnd() in *)
      (* result, stdout, stderr *)

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
      (* let int_of_uint8 (i:uint8) = int32 i *)
      (* let uint16_of_int (i:int) = uint16 i *)

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


  end
end
