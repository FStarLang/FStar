(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Brian G. Milnes
*)

module FStar.Class.Printable.Unix

open FStar.String
open FStar.Seq.Properties
open FStar.Class.Printable

/// From FStar.In_Channel and FStar.Out_Channel, can I kill this duplication?

instance printable_in_channel_open_flag : printable FStar.In_Channel.open_flag =
{
 to_string = (fun o ->
               match o with 
               | FStar.In_Channel.Open_rdonly -> "Open_rdonly"
               | FStar.In_Channel.Open_wronly -> "Open_wronly"
               | FStar.In_Channel.Open_append -> "Open_append"
               | FStar.In_Channel.Open_creat -> "Open_creat"
               | FStar.In_Channel.Open_trunc -> "Open_trunc"
               | FStar.In_Channel.Open_excl -> "Open_excl"
               | FStar.In_Channel.Open_binary -> "Open_binary"
               | FStar.In_Channel.Open_text -> "Open_text"
               | FStar.In_Channel.Open_nonblock -> "Open_nonblock")
}

instance printable_out_channel_open_flag : printable FStar.Out_Channel.open_flag =
{
 to_string = (fun o ->
               match o with 
               | FStar.Out_Channel.Open_rdonly -> "Open_rdonly"
               | FStar.Out_Channel.Open_wronly -> "Open_wronly"
               | FStar.Out_Channel.Open_append -> "Open_append"
               | FStar.Out_Channel.Open_creat -> "Open_creat"
               | FStar.Out_Channel.Open_trunc -> "Open_trunc"
               | FStar.Out_Channel.Open_excl -> "Open_excl"
               | FStar.Out_Channel.Open_binary -> "Open_binary"
               | FStar.Out_Channel.Open_text -> "Open_text"
               | FStar.Out_Channel.Open_nonblock -> "Open_nonblock")
}

open FStar.Unix 

///  From FStar.Unix

instance printable_unix_error : printable FStar.Unix.error = 
{
 to_string = (fun e ->
             match e with
             | E2BIG -> "E2BIG"
             | EACCES -> "EACCES"
             | EAGAIN -> "EAGAIN"
             | EBADF -> "EBADF"
             | EBUSY -> "EBUSY"
             | ECHILD -> "ECHILD"
             | EDEADLK -> "EDEADLK"
             | EDOM -> "EDOM"
             | EEXIST -> "EEXIST"
             | EFAULT -> "EFAULT"
             | EFBIG -> "EFBIG"
             | EINTR -> "EINTR"
             | EINVAL -> "EINVAL"
             | EIO -> "EIO"
             | EISDIR -> "EISDIR"
             | EMFILE -> "EMFILE"
             | EMLINK -> "EMLINK"
             | ENAMETOOLONG -> "ENAMETOOLONG"
             | ENFILE -> "ENFILE"
             | ENODEV -> "ENODEV"
             | ENOENT -> "ENOENT"
             | ENOEXEC -> "ENOEXEC"
             | ENOLCK -> "ENOLCK"
             | ENOMEM -> "ENOMEM"
             | ENOSPC -> "ENOSPC"
             | ENOSYS -> "ENOSYS"
             | ENOTDIR -> "ENOTDIR"
             | ENOTEMPTY -> "ENOTEMPTY"
             | ENOTTY -> "ENOTTY"
             | ENXIO -> "ENXIO"
             | EPERM -> "EPERM"
             | EPIPE -> "EPIPE"
             | ERANGE -> "ERANGE"
             | EROFS -> "EROFS"
             | ESPIPE -> "ESPIPE"
             | ESRCH -> "ESRCH"
             | EXDEV -> "EXDEV"
             | EWOULDBLOCK -> "EWOULDBLOCK"
             | EINPROGRESS -> "EINPROGRESS"
             | EALREADY -> "EALREADY"
             | ENOTSOCK -> "ENOTSOCK"
             | EDESTADDRREQ -> "EDESTADDRREQ"
             | EMSGSIZE -> "EMSGSIZE"
             | EPROTOTYPE -> "EPROTOTYPE"
             | ENOPROTOOPT -> "ENOPROTOOPT"
             | EPROTONOSUPPORT -> "EPROTONOSUPPORT"
             | ESOCKTNOSUPPORT -> "ESOCKTNOSUPPORT"
             | EOPNOTSUPP -> "EOPNOTSUPP"
             | EPFNOSUPPORT -> "EPFNOSUPPORT"
             | EAFNOSUPPORT -> "EAFNOSUPPORT"
             | EADDRINUSE -> "EADDRINUSE"
             | EADDRNOTAVAIL -> "EADDRNOTAVAIL"
             | ENETDOWN -> "ENETDOWN"
             | ENETUNREACH -> "ENETUNREACH"
             | ENETRESET -> "ENETRESET"
             | ECONNABORTED -> "ECONNABORTED"
             | ECONNRESET -> "ECONNRESET"
             | ENOBUFS -> "ENOBUFS"
             | EISCONN -> "EISCONN"
             | ENOTCONN -> "ENOTCONN"
             | ESHUTDOWN -> "ESHUTDOWN"
             | ETOOMANYREFS -> "ETOOMANYREFS"
             | ETIMEDOUT -> "ETIMEDOUT"
             | ECONNREFUSED -> "ECONNREFUSED"
             | EHOSTDOWN -> "EHOSTDOWN"
             | EHOSTUNREACH -> "EHOSTUNREACH"
             | ELOOP -> "ELOOP"
             | EOVERFLOW -> "EOVERFLOW"
             | EUNKNOWNERR i -> "EUNKNOWNERR " ^ (to_string i))
}

(* Can I do this for exceptions? 
instance printable_unix_Unix_error : printable FStar.Unix.Unix_error =
{
  to_string = (fun e -> 
               match e with
               | Unix_error t -> "Unix_error " ^ (to_string t))
}
*)

instance printable_unix_process_status : printable FStar.Unix.process_status =
{
 to_string = (fun p ->
             match p with
             | WEXITED i   -> "WEXITED "   ^ (to_string i)
             | WSIGNALED i -> "WSIGNALED " ^ (to_string i)
             | WSTOPPED  i -> "WSTOPPED "  ^ (to_string i))
}

instance printable_unix_wait_flag : printable FStar.Unix.wait_flag =
{
 to_string = (fun w ->
             match w with
             | WNOHANG -> "WNOHANG"
             | WUNTRACED -> "WUNTRACED")
}

instance printable_unix_open_flag : printable FStar.Unix.open_flag =
{
 to_string = (fun o ->
             match o with
             | O_RDONLY -> "O_RDONLY"
             | O_WRONLY -> "O_WRONLY"
             | O_RDWR -> "O_RDWR"
             | O_NONBLOCK -> "O_NONBLOCK"
             | O_APPEND -> "O_APPEND"
             | O_CREAT -> "O_CREAT"
             | O_TRUNC -> "O_TRUNC"
             | O_EXCL -> "O_EXCL"
             | O_NOCTTY -> "O_NOCTTY"
             | O_DSYNC -> "O_DSYNC"
             | O_SYNC -> "O_SYNC"
             | O_RSYNC -> "O_RSYNC"
             | O_SHARE_DELETE -> "O_SHARE_DELETE"
             | O_CLOEXEC -> "O_CLOEXEC"
             | O_KEEPEXEC -> "O_KEEPEXEC")
}

instance printable_unix_file_kind : printable FStar.Unix.file_kind =
{
 to_string = (fun f ->
             match f with
             | S_REG -> "S_REG"
             | S_DIR -> "S_DIR"  
             | S_CHR -> "S_CHR"  
             | S_BLK -> "S_BLK" 
             | S_LNK -> "S_LNK"  
             | S_FIFO -> "S_FIFO"
             | S_SOCK -> "S_SOCK")
}

instance printable_unix_stats : printable FStar.Unix.stats =
{
  to_string = (fun r ->
   "{\n" ^
(*     "st_dev = " ^ (to_string r.st_dev) ^ "\n" ^
     "st_ino = " ^ (to_string r.st_ino) ^ "\n" ^*)
     "st_kind = " ^ (to_string r.st_kind) ^ "\n" ^
(*     "st_perm = " ^ (to_string r.st_perm) ^ "\n" ^ *)
(*     "st_nlink = " ^ (to_string r.st_nlink) ^ "\n" ^
     "st_uid = " ^ (to_string r.st_uid) ^ "\n" ^
     "st_gid = " ^ (to_string r.st_gid) ^ "\n" ^
     "st_rdev = " ^ (to_string r.st_rdev) ^ "\n" ^
     "st_size = " ^ (to_string r.st_size) ^ "\n" ^
*)
     "st_atime = " ^ (to_string r.st_atime) ^ "\n" ^
     "st_mtime = " ^ (to_string r.st_mtime) ^ "\n" ^
     "st_ctime = " ^ (to_string r.st_ctime) ^ "\n" ^
  "}\n"
  )
}

instance printable_unix_access_permission : printable FStar.Unix.access_permission =
{
 to_string = (fun a ->
             match a with
             | R_OK -> "R_OK"
             | W_OK -> "W_OK"  
             | X_OK -> "X_OK" 
             | F_OK -> "F_OK")
}

instance printable_unix_lock_command : printable FStar.Unix.lock_command =
{ 
to_string = (fun l ->
             match l with
            | F_ULOCK -> "F_ULOCK"
            | F_LOCK -> "F_LOCK" 
            | F_TLOCK -> "F_TLOCK" 
            | F_TEST -> "F_TEST"
            | F_RLOCK -> "F_RLOCK"  
            | F_TRLOCK -> "F_TRLOCK")
}

instance printable_unix_sigprocmask_command : printable FStar.Unix.sigprocmask_command =
{
 to_string = (fun s ->
             match s with
             | SIG_SETMASK -> "SIG_SETMASK" 
             | SIG_BLOCK -> "SIG_BLOCK" 
             | SIG_UNBLOCK -> "SIG_UNBLOCK")
}

instance printable_unix_process_times : printable FStar.Unix.process_times =
{
  to_string = (fun r -> 
   "{\n" ^
     "tms_utime  = " ^ (to_string r.tms_utime)  ^ "\n" ^
     "tms_stime  = " ^ (to_string r.tms_stime)  ^ "\n" ^
     "tms_cutime = " ^ (to_string r.tms_cutime) ^ "\n" ^
     "tms_cstime = " ^ (to_string r.tms_cstime) ^ "\n" ^
   "}\n")
}

instance printable_unix_tm : printable FStar.Unix.tm =
{
  to_string = (fun r -> 
            "{\n" ^
            "tm_sec = " ^ (to_string r.tm_sec) ^ "\n" ^
            "tm_min = " ^ (to_string r.tm_min) ^ "\n" ^
            "tm_hour = " ^ (to_string r.tm_hour) ^ "\n" ^
            "tm_mday = " ^ (to_string r.tm_mday) ^ "\n" ^
            "tm_mon = " ^ (to_string r.tm_mon) ^ "\n" ^
            "tm_year = " ^ (to_string r.tm_year) ^ "\n" ^
            "tm_wday = " ^ (to_string r.tm_wday) ^ "\n" ^
            "tm_yday = " ^ (to_string r.tm_yday) ^ "\n" ^
            "tm_isdst = " ^ (to_string r.tm_isdst) ^ "\n" ^
            "}\n")
}

instance printable_unix_interval_timer : printable FStar.Unix.interval_timer =
{
 to_string = (fun i ->
             match i with
             | ITIMER_REAL -> "ITIMER_REAL" 
             | ITIMER_VIRTUAL -> "ITIMER_VIRTUAL" 
             | ITIMER_PROF -> "ITIMER_PROF")
}

instance printable_unix_interval_timer_status : printable FStar.Unix.interval_timer_status =
{
  to_string = (fun r ->
              "{\n" ^
                 "it_interval = " ^ (to_string r.it_interval) ^ "\n" ^
                 "it_value = " ^ (to_string r.it_value) ^ "\n" ^
              "}\n")
}

instance printable_unix_passwd_entry : printable FStar.Unix.passwd_entry =
{
  to_string  = (fun r ->
             "pw_name = " ^ (to_string r.pw_name) ^ "\n" ^
              "pw_passwd = " ^ (to_string r.pw_passwd) ^ "\n" ^
              "pw_uid = " ^ (to_string r.pw_uid) ^ "\n" ^
              "pw_gid = " ^ (to_string r.pw_gid) ^ "\n" ^
              "pw_gecos = " ^ (to_string r.pw_gecos) ^ "\n" ^
              "pw_dir = " ^ (to_string r.pw_dir) ^ "\n" ^
              "pw_shell = " ^ (to_string r.pw_shell) ^ "\n" ^
  "}\n")
}

instance printable_unix_group_entry : printable FStar.Unix.group_entry =
{
  to_string = (fun r ->
    "{\n" ^
      "gr_name = " ^ (to_string r.gr_name) ^ "\n" ^
      "gr_passwd = " ^ (to_string r.gr_passwd) ^ "\n" ^
      "gr_gid = " ^ (to_string r.gr_gid) ^ "\n" ^
      "gr_mem = " ^ (to_string r.gr_mem) ^ "\n" ^
   "}\n")
}

instance printable_unix_socket_domain : printable FStar.Unix.socket_domain =
{
 to_string = (fun s ->
             match s with
             | PF_UNIX -> "PF_UNIX" 
             | PF_INET -> "PF_INET" 
             | PF_INET6 -> "PF_INET6")
}

instance printable_unix_socket_type : printable FStar.Unix.socket_type =
{
 to_string = (fun s ->
               match s with
             | SOCK_STREAM -> "SOCK_STREAM" 
             | SOCK_DGRAM -> "SOCK_DGRAM" 
             | SOCK_RAW -> "SOCK_RAW" 
             | SOCK_SEQPACKET -> "SOCK_SEQPACKET")
}

instance printable_inet_addr     : printable FStar.Unix.inet_addr =
{
 to_string = (fun ia -> "inet_adder is abstract")
}

instance printable_unix_sockaddr : printable FStar.Unix.sockaddr =
{
 to_string = (fun s ->
             match s with
             | ADDR_UNIX s  -> "ADDR_UNIX " ^ (to_string s)
             | ADDR_INET (a,i) -> "ADDR_INET " ^ (to_string a) ^ " " ^ (to_string i))
}

instance printable_unix_shutdown_command : printable FStar.Unix.shutdown_command =
{
 to_string = (fun s ->
             match s with
             | SHUTDOWN_RECEIVE -> "SHUTDOWN_RECEIVE"
             | SHUTDOWN_SEND -> "SHUTDOWN_SEND" 
             | SHUTDOWN_ALL -> "SHUTDOWN_ALL")
}


instance printable_unix_msg_flag : printable FStar.Unix.msg_flag =
{
 to_string = (fun m ->
             match m with
             | MSG_OOB -> "MSG_OOB" 
             | MSG_DONTROUTE -> "MSG_DONTROUTE" 
             | MSG_PEEK -> "MSG_PEEK")
}

instance printable_unix_socket_bool_option : printable FStar.Unix.socket_bool_option =
{
 to_string = (fun s ->
             match s with
             | SO_DEBUG -> "SO_DEBUG" 
             | SO_BROADCAST -> "SO_BROADCAST" 
             | SO_REUSEADDR -> "SO_REUSEADDR" 
             | SO_KEEPALIVE -> "SO_KEEPALIVE"
             | SO_DONTROUTE -> "SO_DONTROUTE" 
             | SO_OOBINLINE -> "SO_OOBINLINE" 
             | SO_ACCEPTCONN -> "SO_ACCEPTCONN" 
             | TCP_NODELAY -> "TCP_NODELAY"  
             | IPV6_ONLY -> "IPV6_ONLY"
             | SO_REUSEPORT -> "SO_REUSEPORT")
}


instance printable_unix_socket_int_option : printable FStar.Unix.socket_int_option =
{
 to_string = (fun s ->
             match s with
             | SO_SNDBUF -> "SO_SNDBUF" 
             | SO_RCVBUF -> "SO_RCVBUF" 
             | SO_ERROR -> "SO_ERROR" 
             | SO_TYPE -> "SO_TYPE"
             | SO_RCVLOWAT -> "SO_RCVLOWAT"
             | SO_SNDLOWAT -> "SO_SNDLOWAT")
}

instance printable_unix_socket_optint_option : printable FStar.Unix.socket_optint_option =
{
 to_string = (fun s ->
             match s with
             | SO_LINGER -> "SO_LINGER")
}

instance printable_unix_socket_float_option : printable FStar.Unix.socket_float_option =
{
 to_string = (fun s ->
             match s with
             | SO_RCVTIMEO -> "SO_RCVTIMEO" 
             | SO_SNDTIMEO -> "SO_SNDTIMEO")
}

instance printable_unix_host_entry : printable FStar.Unix.host_entry =
{
  to_string = (fun r ->
    "{\n" ^
      "h_name = " ^ (to_string r.h_name) ^ "\n" ^
     "h_aliases = " ^ (to_string r.h_aliases) ^ "\n" ^
     "h_addrtype = " ^ (to_string r.h_addrtype) ^ "\n" ^
     "h_addr_list = " ^ (to_string r.h_addr_list) ^ "\n" ^
    "}\n")
}

instance printable_unix_protocol_entry : printable FStar.Unix.protocol_entry =
{
  to_string = (fun r ->
          "{\n" ^
          "p_name = " ^ (to_string r.p_name) ^ "\n" ^
          "p_aliases = " ^ (to_string r.p_aliases) ^ "\n" ^
(*          "p_proto = " ^ (to_string r.p_proto) ^*) "\n" ^
          "}\n"
)
}

instance printable_unix_service_entry : printable FStar.Unix.service_entry =
{
  to_string = (fun r ->
  "{\n" ^
        "s_name = " ^ (to_string r.s_name) ^ "\n" ^
        "s_aliases = " ^ (to_string r.s_aliases) ^ "\n" ^
(*        "s_port = " ^ (to_string r.s_port) ^ *) "\n" ^
        "s_proto = " ^ (to_string r.s_proto) ^ "\n" ^
  "}\n")
}

instance printable_unix_addr_info : printable FStar.Unix.addr_info =
{
  to_string = (fun r ->
   "{\n" ^
     "ai_family = " ^ (to_string r.ai_family) ^ "\n" ^
     "ai_socktype = " ^ (to_string r.ai_socktype) ^ "\n" ^
(*     "ai_protocol = " ^ (to_string r.ai_protocol) ^ "\n" ^ *)
     "ai_addr = " ^ (to_string r.ai_addr) ^ "\n" ^
     "ai_canonname = " ^ (to_string r.ai_canonname) ^ "\n" ^
     "}\n")
}

instance printable_unix_getaddrinfo_option : printable FStar.Unix.getaddrinfo_option =
{
 to_string = (fun g ->
             match g with
               | AI_FAMILY sd   -> "AI_FAMILY " ^ (to_string sd)
               | AI_SOCKTYPE st -> "AI_SOCKTYPE " ^ (to_string st)
               | AI_PROTOCOL i  -> "AI_PROTOCOL " ^ (to_string i)
               | AI_NUMERICHOST -> "AI_NUMERICHOST"
               | AI_CANONNAME   -> "AI_CANONNAME"
               | AI_PASSIVE     -> "AI_PASSIVE")
}

instance printable_unix_name_info : printable FStar.Unix.name_info =
{
  to_string = (fun r ->
                 "{\n" ^
                 "ni_hostname = " ^ (to_string r.ni_hostname) ^ "\n" ^
                 "ni_service = " ^ (to_string r.ni_service) ^ "\n" ^
                 "}\n")
}

instance printable_unix_getnameinfo_option : printable FStar.Unix.getnameinfo_option =
{
 to_string = (fun g ->
             match g with
           | NI_NOFQDN -> "NI_NOFQDN" 
           | NI_NUMERICHOST -> "NI_NUMERICHOST"
           | NI_NAMEREQD -> "NI_NAMEREQD" 
           | NI_NUMERICSERV -> "NI_NUMERICSERV"
           | NI_DGRAM -> "NI_DGRAM")
}

instance printable_unix_terminal_io : printable FStar.Unix.terminal_io =
{
  to_string = (fun r ->
  "{\n" ^
        "c_ignbrk = " ^ (to_string r.c_ignbrk) ^ "\n" ^
        "c_brkint = " ^ (to_string r.c_brkint) ^ "\n" ^
        "c_ignpar = " ^ (to_string r.c_ignpar) ^ "\n" ^
        "c_parmrk = " ^ (to_string r.c_parmrk) ^ "\n" ^
        "c_inpck = " ^ (to_string r.c_inpck) ^ "\n" ^
        "c_istrip = " ^ (to_string r.c_istrip) ^ "\n" ^
        "c_inlcr = " ^ (to_string r.c_inlcr) ^ "\n" ^
        "c_igncr = " ^ (to_string r.c_igncr) ^ "\n" ^
        "c_icrnl = " ^ (to_string r.c_icrnl) ^ "\n" ^
        "c_ixon = " ^ (to_string r.c_ixon) ^ "\n" ^
        "c_ixoff = " ^ (to_string r.c_ixoff) ^ "\n" ^
        "c_opost = " ^ (to_string r.c_opost) ^ "\n" ^
        "c_obaud = " ^ (to_string r.c_obaud) ^ "\n" ^
        "c_ibaud = " ^ (to_string r.c_ibaud) ^ "\n" ^
        "c_csize = " ^ (to_string r.c_csize) ^ "\n" ^
        "c_cstopb = " ^ (to_string r.c_cstopb) ^ "\n" ^
        "c_cread = " ^ (to_string r.c_cread) ^ "\n" ^
        "c_parenb = " ^ (to_string r.c_parenb) ^ "\n" ^
        "c_parodd = " ^ (to_string r.c_parodd) ^ "\n" ^
        "c_hupcl = " ^ (to_string r.c_hupcl) ^ "\n" ^
        "c_clocal = " ^ (to_string r.c_clocal) ^ "\n" ^
        "c_isig = " ^ (to_string r.c_isig) ^ "\n" ^
        "c_icanon = " ^ (to_string r.c_icanon) ^ "\n" ^
        "c_noflsh = " ^ (to_string r.c_noflsh) ^ "\n" ^
        "c_echo = " ^ (to_string r.c_echo) ^ "\n" ^
        "c_echoe = " ^ (to_string r.c_echoe) ^ "\n" ^
        "c_echok = " ^ (to_string r.c_echok) ^ "\n" ^
        "c_echonl = " ^ (to_string r.c_echonl) ^ "\n" ^
(* BUG Is this a printables issue or mine?
       "c_vintr = " ^ (to_string r.c_vintr) ^ "\n" ^  
        "c_vquit = " ^ (to_string r.c_vquit) ^ "\n" ^ 

        "c_verase = " ^ (to_string r.c_verase) ^ "\n" ^ 
        "c_vkill = " ^ (to_string r.c_vkill) ^ "\n" ^ 
        "c_veof = " ^ (to_string r.c_veof) ^ "\n" ^ 
        "c_veol = " ^ (to_string r.c_veol) ^ "\n" ^ 
        "c_vmin = " ^ (to_string r.c_vmin) ^ "\n" ^
        "c_vtime = " ^ (to_string r.c_vtime) ^ "\n" ^
        "c_vstart = " ^ (to_string r.c_vstart) ^ "\n" ^
        "c_vstop = " ^ (to_string r.c_vstop) ^  "\n" ^
*) 
    "}\n")
}

instance printable_unix_setattr_when : printable FStar.Unix.setattr_when =
{
 to_string = (fun s ->
             match s with
           | TCSANOW -> "TCSANOW" 
           | TCSADRAIN -> "TCSADRAIN" 
           | TCSAFLUSH -> "TCSAFLUSH")
}

instance printable_unix_flush_queue : printable FStar.Unix.flush_queue =
{
 to_string = (fun f ->
             match f with
           | TCIFLUSH -> "TCIFLUSH" 
           | TCOFLUSH -> "TCOFLUSH" 
           | TCIOFLUSH -> "TCIOFLUSH")
}

instance printable_unix_flow_action : printable FStar.Unix.flow_action =
{
 to_string = (fun f ->
             match f with
           | TCOOFF -> "TCOOFF"
           | TCOON -> "TCOON"
           | TCIOFF -> "TCIOFF"
           | TCION -> "TCION")
}
