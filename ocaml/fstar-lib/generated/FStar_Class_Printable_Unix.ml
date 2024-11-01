open Prims
let (printable_in_channel_open_flag :
  FStar_In_Channel.open_flag FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun o ->
         match o with
         | FStar_In_Channel.Open_rdonly -> "Open_rdonly"
         | FStar_In_Channel.Open_wronly -> "Open_wronly"
         | FStar_In_Channel.Open_append -> "Open_append"
         | FStar_In_Channel.Open_creat -> "Open_creat"
         | FStar_In_Channel.Open_trunc -> "Open_trunc"
         | FStar_In_Channel.Open_excl -> "Open_excl"
         | FStar_In_Channel.Open_binary -> "Open_binary"
         | FStar_In_Channel.Open_text -> "Open_text"
         | FStar_In_Channel.Open_nonblock -> "Open_nonblock")
  }
let (printable_out_channel_open_flag :
  FStar_Out_Channel.open_flag FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun o ->
         match o with
         | FStar_Out_Channel.Open_rdonly -> "Open_rdonly"
         | FStar_Out_Channel.Open_wronly -> "Open_wronly"
         | FStar_Out_Channel.Open_append -> "Open_append"
         | FStar_Out_Channel.Open_creat -> "Open_creat"
         | FStar_Out_Channel.Open_trunc -> "Open_trunc"
         | FStar_Out_Channel.Open_excl -> "Open_excl"
         | FStar_Out_Channel.Open_binary -> "Open_binary"
         | FStar_Out_Channel.Open_text -> "Open_text"
         | FStar_Out_Channel.Open_nonblock -> "Open_nonblock")
  }
let (printable_unix_error : FStar_Unix.error FStar_Class_Printable.printable)
  =
  {
    FStar_Class_Printable.to_string =
      (fun e ->
         match e with
         | FStar_Unix.E2BIG -> "E2BIG"
         | FStar_Unix.EACCES -> "EACCES"
         | FStar_Unix.EAGAIN -> "EAGAIN"
         | FStar_Unix.EBADF -> "EBADF"
         | FStar_Unix.EBUSY -> "EBUSY"
         | FStar_Unix.ECHILD -> "ECHILD"
         | FStar_Unix.EDEADLK -> "EDEADLK"
         | FStar_Unix.EDOM -> "EDOM"
         | FStar_Unix.EEXIST -> "EEXIST"
         | FStar_Unix.EFAULT -> "EFAULT"
         | FStar_Unix.EFBIG -> "EFBIG"
         | FStar_Unix.EINTR -> "EINTR"
         | FStar_Unix.EINVAL -> "EINVAL"
         | FStar_Unix.EIO -> "EIO"
         | FStar_Unix.EISDIR -> "EISDIR"
         | FStar_Unix.EMFILE -> "EMFILE"
         | FStar_Unix.EMLINK -> "EMLINK"
         | FStar_Unix.ENAMETOOLONG -> "ENAMETOOLONG"
         | FStar_Unix.ENFILE -> "ENFILE"
         | FStar_Unix.ENODEV -> "ENODEV"
         | FStar_Unix.ENOENT -> "ENOENT"
         | FStar_Unix.ENOEXEC -> "ENOEXEC"
         | FStar_Unix.ENOLCK -> "ENOLCK"
         | FStar_Unix.ENOMEM -> "ENOMEM"
         | FStar_Unix.ENOSPC -> "ENOSPC"
         | FStar_Unix.ENOSYS -> "ENOSYS"
         | FStar_Unix.ENOTDIR -> "ENOTDIR"
         | FStar_Unix.ENOTEMPTY -> "ENOTEMPTY"
         | FStar_Unix.ENOTTY -> "ENOTTY"
         | FStar_Unix.ENXIO -> "ENXIO"
         | FStar_Unix.EPERM -> "EPERM"
         | FStar_Unix.EPIPE -> "EPIPE"
         | FStar_Unix.ERANGE -> "ERANGE"
         | FStar_Unix.EROFS -> "EROFS"
         | FStar_Unix.ESPIPE -> "ESPIPE"
         | FStar_Unix.ESRCH -> "ESRCH"
         | FStar_Unix.EXDEV -> "EXDEV"
         | FStar_Unix.EWOULDBLOCK -> "EWOULDBLOCK"
         | FStar_Unix.EINPROGRESS -> "EINPROGRESS"
         | FStar_Unix.EALREADY -> "EALREADY"
         | FStar_Unix.ENOTSOCK -> "ENOTSOCK"
         | FStar_Unix.EDESTADDRREQ -> "EDESTADDRREQ"
         | FStar_Unix.EMSGSIZE -> "EMSGSIZE"
         | FStar_Unix.EPROTOTYPE -> "EPROTOTYPE"
         | FStar_Unix.ENOPROTOOPT -> "ENOPROTOOPT"
         | FStar_Unix.EPROTONOSUPPORT -> "EPROTONOSUPPORT"
         | FStar_Unix.ESOCKTNOSUPPORT -> "ESOCKTNOSUPPORT"
         | FStar_Unix.EOPNOTSUPP -> "EOPNOTSUPP"
         | FStar_Unix.EPFNOSUPPORT -> "EPFNOSUPPORT"
         | FStar_Unix.EAFNOSUPPORT -> "EAFNOSUPPORT"
         | FStar_Unix.EADDRINUSE -> "EADDRINUSE"
         | FStar_Unix.EADDRNOTAVAIL -> "EADDRNOTAVAIL"
         | FStar_Unix.ENETDOWN -> "ENETDOWN"
         | FStar_Unix.ENETUNREACH -> "ENETUNREACH"
         | FStar_Unix.ENETRESET -> "ENETRESET"
         | FStar_Unix.ECONNABORTED -> "ECONNABORTED"
         | FStar_Unix.ECONNRESET -> "ECONNRESET"
         | FStar_Unix.ENOBUFS -> "ENOBUFS"
         | FStar_Unix.EISCONN -> "EISCONN"
         | FStar_Unix.ENOTCONN -> "ENOTCONN"
         | FStar_Unix.ESHUTDOWN -> "ESHUTDOWN"
         | FStar_Unix.ETOOMANYREFS -> "ETOOMANYREFS"
         | FStar_Unix.ETIMEDOUT -> "ETIMEDOUT"
         | FStar_Unix.ECONNREFUSED -> "ECONNREFUSED"
         | FStar_Unix.EHOSTDOWN -> "EHOSTDOWN"
         | FStar_Unix.EHOSTUNREACH -> "EHOSTUNREACH"
         | FStar_Unix.ELOOP -> "ELOOP"
         | FStar_Unix.EOVERFLOW -> "EOVERFLOW"
         | FStar_Unix.EUNKNOWNERR i ->
             Prims.strcat "EUNKNOWNERR "
               (FStar_Class_Printable.to_string
                  FStar_Class_Printable.printable_int i))
  }
let (printable_unix_process_status :
  FStar_Unix.process_status FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun p ->
         match p with
         | FStar_Unix.WEXITED i ->
             Prims.strcat "WEXITED "
               (FStar_Class_Printable.to_string
                  FStar_Class_Printable.printable_int i)
         | FStar_Unix.WSIGNALED i ->
             Prims.strcat "WSIGNALED "
               (FStar_Class_Printable.to_string
                  FStar_Class_Printable.printable_int i)
         | FStar_Unix.WSTOPPED i ->
             Prims.strcat "WSTOPPED "
               (FStar_Class_Printable.to_string
                  FStar_Class_Printable.printable_int i))
  }
let (printable_unix_wait_flag :
  FStar_Unix.wait_flag FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun w ->
         match w with
         | FStar_Unix.WNOHANG -> "WNOHANG"
         | FStar_Unix.WUNTRACED -> "WUNTRACED")
  }
let (printable_unix_open_flag :
  FStar_Unix.open_flag FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun o ->
         match o with
         | FStar_Unix.O_RDONLY -> "O_RDONLY"
         | FStar_Unix.O_WRONLY -> "O_WRONLY"
         | FStar_Unix.O_RDWR -> "O_RDWR"
         | FStar_Unix.O_NONBLOCK -> "O_NONBLOCK"
         | FStar_Unix.O_APPEND -> "O_APPEND"
         | FStar_Unix.O_CREAT -> "O_CREAT"
         | FStar_Unix.O_TRUNC -> "O_TRUNC"
         | FStar_Unix.O_EXCL -> "O_EXCL"
         | FStar_Unix.O_NOCTTY -> "O_NOCTTY"
         | FStar_Unix.O_DSYNC -> "O_DSYNC"
         | FStar_Unix.O_SYNC -> "O_SYNC"
         | FStar_Unix.O_RSYNC -> "O_RSYNC"
         | FStar_Unix.O_SHARE_DELETE -> "O_SHARE_DELETE"
         | FStar_Unix.O_CLOEXEC -> "O_CLOEXEC"
         | FStar_Unix.O_KEEPEXEC -> "O_KEEPEXEC")
  }
let (printable_unix_file_kind :
  FStar_Unix.file_kind FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun f ->
         match f with
         | FStar_Unix.S_REG -> "S_REG"
         | FStar_Unix.S_DIR -> "S_DIR"
         | FStar_Unix.S_CHR -> "S_CHR"
         | FStar_Unix.S_BLK -> "S_BLK"
         | FStar_Unix.S_LNK -> "S_LNK"
         | FStar_Unix.S_FIFO -> "S_FIFO"
         | FStar_Unix.S_SOCK -> "S_SOCK")
  }
let (printable_unix_stats : FStar_Unix.stats FStar_Class_Printable.printable)
  =
  {
    FStar_Class_Printable.to_string =
      (fun r ->
         Prims.strcat "{\n"
           (Prims.strcat "st_kind = "
              (Prims.strcat
                 (FStar_Class_Printable.to_string printable_unix_file_kind
                    r.FStar_Unix.st_kind)
                 (Prims.strcat "\n"
                    (Prims.strcat "st_atime = "
                       (Prims.strcat
                          (FStar_Class_Printable.to_string
                             FStar_Class_Printable.printable_double
                             r.FStar_Unix.st_atime)
                          (Prims.strcat "\n"
                             (Prims.strcat "st_mtime = "
                                (Prims.strcat
                                   (FStar_Class_Printable.to_string
                                      FStar_Class_Printable.printable_double
                                      r.FStar_Unix.st_mtime)
                                   (Prims.strcat "\n"
                                      (Prims.strcat "st_ctime = "
                                         (Prims.strcat
                                            (FStar_Class_Printable.to_string
                                               FStar_Class_Printable.printable_double
                                               r.FStar_Unix.st_ctime) "\n}\n"))))))))))))
  }
let (printable_unix_access_permission :
  FStar_Unix.access_permission FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun a ->
         match a with
         | FStar_Unix.R_OK -> "R_OK"
         | FStar_Unix.W_OK -> "W_OK"
         | FStar_Unix.X_OK -> "X_OK"
         | FStar_Unix.F_OK -> "F_OK")
  }
let (printable_unix_lock_command :
  FStar_Unix.lock_command FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun l ->
         match l with
         | FStar_Unix.F_ULOCK -> "F_ULOCK"
         | FStar_Unix.F_LOCK -> "F_LOCK"
         | FStar_Unix.F_TLOCK -> "F_TLOCK"
         | FStar_Unix.F_TEST -> "F_TEST"
         | FStar_Unix.F_RLOCK -> "F_RLOCK"
         | FStar_Unix.F_TRLOCK -> "F_TRLOCK")
  }
let (printable_unix_sigprocmask_command :
  FStar_Unix.sigprocmask_command FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun s ->
         match s with
         | FStar_Unix.SIG_SETMASK -> "SIG_SETMASK"
         | FStar_Unix.SIG_BLOCK -> "SIG_BLOCK"
         | FStar_Unix.SIG_UNBLOCK -> "SIG_UNBLOCK")
  }
let (printable_unix_process_times :
  FStar_Unix.process_times FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun r ->
         Prims.strcat "{\n"
           (Prims.strcat "tms_utime  = "
              (Prims.strcat
                 (FStar_Class_Printable.to_string
                    FStar_Class_Printable.printable_double
                    r.FStar_Unix.tms_utime)
                 (Prims.strcat "\n"
                    (Prims.strcat "tms_stime  = "
                       (Prims.strcat
                          (FStar_Class_Printable.to_string
                             FStar_Class_Printable.printable_double
                             r.FStar_Unix.tms_stime)
                          (Prims.strcat "\n"
                             (Prims.strcat "tms_cutime = "
                                (Prims.strcat
                                   (FStar_Class_Printable.to_string
                                      FStar_Class_Printable.printable_double
                                      r.FStar_Unix.tms_cutime)
                                   (Prims.strcat "\n"
                                      (Prims.strcat "tms_cstime = "
                                         (Prims.strcat
                                            (FStar_Class_Printable.to_string
                                               FStar_Class_Printable.printable_double
                                               r.FStar_Unix.tms_cstime)
                                            "\n}\n"))))))))))))
  }
let (printable_unix_tm : FStar_Unix.tm FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun r ->
         Prims.strcat "{\n"
           (Prims.strcat "tm_sec = "
              (Prims.strcat
                 (FStar_Class_Printable.to_string
                    FStar_Class_Printable.printable_int r.FStar_Unix.tm_sec)
                 (Prims.strcat "\n"
                    (Prims.strcat "tm_min = "
                       (Prims.strcat
                          (FStar_Class_Printable.to_string
                             FStar_Class_Printable.printable_int
                             r.FStar_Unix.tm_min)
                          (Prims.strcat "\n"
                             (Prims.strcat "tm_hour = "
                                (Prims.strcat
                                   (FStar_Class_Printable.to_string
                                      FStar_Class_Printable.printable_int
                                      r.FStar_Unix.tm_hour)
                                   (Prims.strcat "\n"
                                      (Prims.strcat "tm_mday = "
                                         (Prims.strcat
                                            (FStar_Class_Printable.to_string
                                               FStar_Class_Printable.printable_int
                                               r.FStar_Unix.tm_mday)
                                            (Prims.strcat "\n"
                                               (Prims.strcat "tm_mon = "
                                                  (Prims.strcat
                                                     (FStar_Class_Printable.to_string
                                                        FStar_Class_Printable.printable_int
                                                        r.FStar_Unix.tm_mon)
                                                     (Prims.strcat "\n"
                                                        (Prims.strcat
                                                           "tm_year = "
                                                           (Prims.strcat
                                                              (FStar_Class_Printable.to_string
                                                                 FStar_Class_Printable.printable_int
                                                                 r.FStar_Unix.tm_year)
                                                              (Prims.strcat
                                                                 "\n"
                                                                 (Prims.strcat
                                                                    "tm_wday = "
                                                                    (
                                                                    Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_int
                                                                    r.FStar_Unix.tm_wday)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "tm_yday = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_int
                                                                    r.FStar_Unix.tm_yday)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "tm_isdst = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.tm_isdst)
                                                                    "\n}\n")))))))))))))))))))))))))))
  }
let (printable_unix_interval_timer :
  FStar_Unix.interval_timer FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun i ->
         match i with
         | FStar_Unix.ITIMER_REAL -> "ITIMER_REAL"
         | FStar_Unix.ITIMER_VIRTUAL -> "ITIMER_VIRTUAL"
         | FStar_Unix.ITIMER_PROF -> "ITIMER_PROF")
  }
let (printable_unix_interval_timer_status :
  FStar_Unix.interval_timer_status FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun r ->
         Prims.strcat "{\n"
           (Prims.strcat "it_interval = "
              (Prims.strcat
                 (FStar_Class_Printable.to_string
                    FStar_Class_Printable.printable_double
                    r.FStar_Unix.it_interval)
                 (Prims.strcat "\n"
                    (Prims.strcat "it_value = "
                       (Prims.strcat
                          (FStar_Class_Printable.to_string
                             FStar_Class_Printable.printable_double
                             r.FStar_Unix.it_value) "\n}\n"))))))
  }
let (printable_unix_passwd_entry :
  FStar_Unix.passwd_entry FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun r ->
         Prims.strcat "pw_name = "
           (Prims.strcat
              (FStar_Class_Printable.to_string
                 FStar_Class_Printable.printable_string r.FStar_Unix.pw_name)
              (Prims.strcat "\n"
                 (Prims.strcat "pw_passwd = "
                    (Prims.strcat
                       (FStar_Class_Printable.to_string
                          FStar_Class_Printable.printable_string
                          r.FStar_Unix.pw_passwd)
                       (Prims.strcat "\n"
                          (Prims.strcat "pw_uid = "
                             (Prims.strcat
                                (FStar_Class_Printable.to_string
                                   FStar_Class_Printable.printable_int
                                   r.FStar_Unix.pw_uid)
                                (Prims.strcat "\n"
                                   (Prims.strcat "pw_gid = "
                                      (Prims.strcat
                                         (FStar_Class_Printable.to_string
                                            FStar_Class_Printable.printable_int
                                            r.FStar_Unix.pw_gid)
                                         (Prims.strcat "\n"
                                            (Prims.strcat "pw_gecos = "
                                               (Prims.strcat
                                                  (FStar_Class_Printable.to_string
                                                     FStar_Class_Printable.printable_string
                                                     r.FStar_Unix.pw_gecos)
                                                  (Prims.strcat "\n"
                                                     (Prims.strcat
                                                        "pw_dir = "
                                                        (Prims.strcat
                                                           (FStar_Class_Printable.to_string
                                                              FStar_Class_Printable.printable_string
                                                              r.FStar_Unix.pw_dir)
                                                           (Prims.strcat "\n"
                                                              (Prims.strcat
                                                                 "pw_shell = "
                                                                 (Prims.strcat
                                                                    (
                                                                    FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_string
                                                                    r.FStar_Unix.pw_shell)
                                                                    "\n}\n"))))))))))))))))))))
  }
let (printable_unix_group_entry :
  FStar_Unix.group_entry FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun r ->
         Prims.strcat "{\n"
           (Prims.strcat "gr_name = "
              (Prims.strcat
                 (FStar_Class_Printable.to_string
                    FStar_Class_Printable.printable_string
                    r.FStar_Unix.gr_name)
                 (Prims.strcat "\n"
                    (Prims.strcat "gr_passwd = "
                       (Prims.strcat
                          (FStar_Class_Printable.to_string
                             FStar_Class_Printable.printable_string
                             r.FStar_Unix.gr_passwd)
                          (Prims.strcat "\n"
                             (Prims.strcat "gr_gid = "
                                (Prims.strcat
                                   (FStar_Class_Printable.to_string
                                      FStar_Class_Printable.printable_int
                                      r.FStar_Unix.gr_gid)
                                   (Prims.strcat "\n"
                                      (Prims.strcat "gr_mem = "
                                         (Prims.strcat
                                            (FStar_Class_Printable.to_string
                                               (FStar_Class_Printable.printable_array
                                                  FStar_Class_Printable.printable_string)
                                               r.FStar_Unix.gr_mem) "\n}\n"))))))))))))
  }
let (printable_unix_socket_domain :
  FStar_Unix.socket_domain FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun s ->
         match s with
         | FStar_Unix.PF_UNIX -> "PF_UNIX"
         | FStar_Unix.PF_INET -> "PF_INET"
         | FStar_Unix.PF_INET6 -> "PF_INET6")
  }
let (printable_unix_socket_type :
  FStar_Unix.socket_type FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun s ->
         match s with
         | FStar_Unix.SOCK_STREAM -> "SOCK_STREAM"
         | FStar_Unix.SOCK_DGRAM -> "SOCK_DGRAM"
         | FStar_Unix.SOCK_RAW -> "SOCK_RAW"
         | FStar_Unix.SOCK_SEQPACKET -> "SOCK_SEQPACKET")
  }
let (printable_inet_addr :
  FStar_Unix.inet_addr FStar_Class_Printable.printable) =
  { FStar_Class_Printable.to_string = (fun ia -> "inet_adder is abstract") }
let (printable_unix_sockaddr :
  FStar_Unix.sockaddr FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun s ->
         match s with
         | FStar_Unix.ADDR_UNIX s1 ->
             Prims.strcat "ADDR_UNIX "
               (FStar_Class_Printable.to_string
                  FStar_Class_Printable.printable_string s1)
         | FStar_Unix.ADDR_INET (a, i) ->
             Prims.strcat "ADDR_INET "
               (Prims.strcat
                  (FStar_Class_Printable.to_string printable_inet_addr a)
                  (Prims.strcat " "
                     (FStar_Class_Printable.to_string
                        FStar_Class_Printable.printable_int i))))
  }
let (printable_unix_shutdown_command :
  FStar_Unix.shutdown_command FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun s ->
         match s with
         | FStar_Unix.SHUTDOWN_RECEIVE -> "SHUTDOWN_RECEIVE"
         | FStar_Unix.SHUTDOWN_SEND -> "SHUTDOWN_SEND"
         | FStar_Unix.SHUTDOWN_ALL -> "SHUTDOWN_ALL")
  }
let (printable_unix_msg_flag :
  FStar_Unix.msg_flag FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun m ->
         match m with
         | FStar_Unix.MSG_OOB -> "MSG_OOB"
         | FStar_Unix.MSG_DONTROUTE -> "MSG_DONTROUTE"
         | FStar_Unix.MSG_PEEK -> "MSG_PEEK")
  }
let (printable_unix_socket_bool_option :
  FStar_Unix.socket_bool_option FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun s ->
         match s with
         | FStar_Unix.SO_DEBUG -> "SO_DEBUG"
         | FStar_Unix.SO_BROADCAST -> "SO_BROADCAST"
         | FStar_Unix.SO_REUSEADDR -> "SO_REUSEADDR"
         | FStar_Unix.SO_KEEPALIVE -> "SO_KEEPALIVE"
         | FStar_Unix.SO_DONTROUTE -> "SO_DONTROUTE"
         | FStar_Unix.SO_OOBINLINE -> "SO_OOBINLINE"
         | FStar_Unix.SO_ACCEPTCONN -> "SO_ACCEPTCONN"
         | FStar_Unix.TCP_NODELAY -> "TCP_NODELAY"
         | FStar_Unix.IPV6_ONLY -> "IPV6_ONLY"
         | FStar_Unix.SO_REUSEPORT -> "SO_REUSEPORT")
  }
let (printable_unix_socket_int_option :
  FStar_Unix.socket_int_option FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun s ->
         match s with
         | FStar_Unix.SO_SNDBUF -> "SO_SNDBUF"
         | FStar_Unix.SO_RCVBUF -> "SO_RCVBUF"
         | FStar_Unix.SO_ERROR -> "SO_ERROR"
         | FStar_Unix.SO_TYPE -> "SO_TYPE"
         | FStar_Unix.SO_RCVLOWAT -> "SO_RCVLOWAT"
         | FStar_Unix.SO_SNDLOWAT -> "SO_SNDLOWAT")
  }
let (printable_unix_socket_optint_option :
  FStar_Unix.socket_optint_option FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun s -> match s with | FStar_Unix.SO_LINGER -> "SO_LINGER")
  }
let (printable_unix_socket_float_option :
  FStar_Unix.socket_float_option FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun s ->
         match s with
         | FStar_Unix.SO_RCVTIMEO -> "SO_RCVTIMEO"
         | FStar_Unix.SO_SNDTIMEO -> "SO_SNDTIMEO")
  }
let (printable_unix_host_entry :
  FStar_Unix.host_entry FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun r ->
         Prims.strcat "{\n"
           (Prims.strcat "h_name = "
              (Prims.strcat
                 (FStar_Class_Printable.to_string
                    FStar_Class_Printable.printable_string
                    r.FStar_Unix.h_name)
                 (Prims.strcat "\n"
                    (Prims.strcat "h_aliases = "
                       (Prims.strcat
                          (FStar_Class_Printable.to_string
                             (FStar_Class_Printable.printable_array
                                FStar_Class_Printable.printable_string)
                             r.FStar_Unix.h_aliases)
                          (Prims.strcat "\n"
                             (Prims.strcat "h_addrtype = "
                                (Prims.strcat
                                   (FStar_Class_Printable.to_string
                                      printable_unix_socket_domain
                                      r.FStar_Unix.h_addrtype)
                                   (Prims.strcat "\n"
                                      (Prims.strcat "h_addr_list = "
                                         (Prims.strcat
                                            (FStar_Class_Printable.to_string
                                               (FStar_Class_Printable.printable_array
                                                  printable_inet_addr)
                                               r.FStar_Unix.h_addr_list)
                                            "\n}\n"))))))))))))
  }
let (printable_unix_protocol_entry :
  FStar_Unix.protocol_entry FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun r ->
         Prims.strcat "{\n"
           (Prims.strcat "p_name = "
              (Prims.strcat
                 (FStar_Class_Printable.to_string
                    FStar_Class_Printable.printable_string
                    r.FStar_Unix.p_name)
                 (Prims.strcat "\n"
                    (Prims.strcat "p_aliases = "
                       (Prims.strcat
                          (FStar_Class_Printable.to_string
                             (FStar_Class_Printable.printable_array
                                FStar_Class_Printable.printable_string)
                             r.FStar_Unix.p_aliases) "\n\n}\n"))))))
  }
let (printable_unix_service_entry :
  FStar_Unix.service_entry FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun r ->
         Prims.strcat "{\n"
           (Prims.strcat "s_name = "
              (Prims.strcat
                 (FStar_Class_Printable.to_string
                    FStar_Class_Printable.printable_string
                    r.FStar_Unix.s_name)
                 (Prims.strcat "\n"
                    (Prims.strcat "s_aliases = "
                       (Prims.strcat
                          (FStar_Class_Printable.to_string
                             (FStar_Class_Printable.printable_array
                                FStar_Class_Printable.printable_string)
                             r.FStar_Unix.s_aliases)
                          (Prims.strcat "\n"
                             (Prims.strcat "\n"
                                (Prims.strcat "s_proto = "
                                   (Prims.strcat
                                      (FStar_Class_Printable.to_string
                                         FStar_Class_Printable.printable_string
                                         r.FStar_Unix.s_proto) "\n}\n"))))))))))
  }
let (printable_unix_addr_info :
  FStar_Unix.addr_info FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun r ->
         Prims.strcat "{\n"
           (Prims.strcat "ai_family = "
              (Prims.strcat
                 (FStar_Class_Printable.to_string
                    printable_unix_socket_domain r.FStar_Unix.ai_family)
                 (Prims.strcat "\n"
                    (Prims.strcat "ai_socktype = "
                       (Prims.strcat
                          (FStar_Class_Printable.to_string
                             printable_unix_socket_type
                             r.FStar_Unix.ai_socktype)
                          (Prims.strcat "\n"
                             (Prims.strcat "ai_addr = "
                                (Prims.strcat
                                   (FStar_Class_Printable.to_string
                                      printable_unix_sockaddr
                                      r.FStar_Unix.ai_addr)
                                   (Prims.strcat "\n"
                                      (Prims.strcat "ai_canonname = "
                                         (Prims.strcat
                                            (FStar_Class_Printable.to_string
                                               FStar_Class_Printable.printable_string
                                               r.FStar_Unix.ai_canonname)
                                            "\n}\n"))))))))))))
  }
let (printable_unix_getaddrinfo_option :
  FStar_Unix.getaddrinfo_option FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun g ->
         match g with
         | FStar_Unix.AI_FAMILY sd ->
             Prims.strcat "AI_FAMILY "
               (FStar_Class_Printable.to_string printable_unix_socket_domain
                  sd)
         | FStar_Unix.AI_SOCKTYPE st ->
             Prims.strcat "AI_SOCKTYPE "
               (FStar_Class_Printable.to_string printable_unix_socket_type st)
         | FStar_Unix.AI_PROTOCOL i ->
             Prims.strcat "AI_PROTOCOL "
               (FStar_Class_Printable.to_string
                  FStar_Class_Printable.printable_int i)
         | FStar_Unix.AI_NUMERICHOST -> "AI_NUMERICHOST"
         | FStar_Unix.AI_CANONNAME -> "AI_CANONNAME"
         | FStar_Unix.AI_PASSIVE -> "AI_PASSIVE")
  }
let (printable_unix_name_info :
  FStar_Unix.name_info FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun r ->
         Prims.strcat "{\n"
           (Prims.strcat "ni_hostname = "
              (Prims.strcat
                 (FStar_Class_Printable.to_string
                    FStar_Class_Printable.printable_string
                    r.FStar_Unix.ni_hostname)
                 (Prims.strcat "\n"
                    (Prims.strcat "ni_service = "
                       (Prims.strcat
                          (FStar_Class_Printable.to_string
                             FStar_Class_Printable.printable_string
                             r.FStar_Unix.ni_service) "\n}\n"))))))
  }
let (printable_unix_getnameinfo_option :
  FStar_Unix.getnameinfo_option FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun g ->
         match g with
         | FStar_Unix.NI_NOFQDN -> "NI_NOFQDN"
         | FStar_Unix.NI_NUMERICHOST -> "NI_NUMERICHOST"
         | FStar_Unix.NI_NAMEREQD -> "NI_NAMEREQD"
         | FStar_Unix.NI_NUMERICSERV -> "NI_NUMERICSERV"
         | FStar_Unix.NI_DGRAM -> "NI_DGRAM")
  }
let (printable_unix_terminal_io :
  FStar_Unix.terminal_io FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun r ->
         Prims.strcat "{\n"
           (Prims.strcat "c_ignbrk = "
              (Prims.strcat
                 (FStar_Class_Printable.to_string
                    FStar_Class_Printable.printable_bool
                    r.FStar_Unix.c_ignbrk)
                 (Prims.strcat "\n"
                    (Prims.strcat "c_brkint = "
                       (Prims.strcat
                          (FStar_Class_Printable.to_string
                             FStar_Class_Printable.printable_bool
                             r.FStar_Unix.c_brkint)
                          (Prims.strcat "\n"
                             (Prims.strcat "c_ignpar = "
                                (Prims.strcat
                                   (FStar_Class_Printable.to_string
                                      FStar_Class_Printable.printable_bool
                                      r.FStar_Unix.c_ignpar)
                                   (Prims.strcat "\n"
                                      (Prims.strcat "c_parmrk = "
                                         (Prims.strcat
                                            (FStar_Class_Printable.to_string
                                               FStar_Class_Printable.printable_bool
                                               r.FStar_Unix.c_parmrk)
                                            (Prims.strcat "\n"
                                               (Prims.strcat "c_inpck = "
                                                  (Prims.strcat
                                                     (FStar_Class_Printable.to_string
                                                        FStar_Class_Printable.printable_bool
                                                        r.FStar_Unix.c_inpck)
                                                     (Prims.strcat "\n"
                                                        (Prims.strcat
                                                           "c_istrip = "
                                                           (Prims.strcat
                                                              (FStar_Class_Printable.to_string
                                                                 FStar_Class_Printable.printable_bool
                                                                 r.FStar_Unix.c_istrip)
                                                              (Prims.strcat
                                                                 "\n"
                                                                 (Prims.strcat
                                                                    "c_inlcr = "
                                                                    (
                                                                    Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_inlcr)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_igncr = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_igncr)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_icrnl = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_icrnl)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_ixon = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_ixon)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_ixoff = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_ixoff)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_opost = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_opost)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_obaud = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_int
                                                                    r.FStar_Unix.c_obaud)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_ibaud = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_int
                                                                    r.FStar_Unix.c_ibaud)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_csize = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_int
                                                                    r.FStar_Unix.c_csize)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_cstopb = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_int
                                                                    r.FStar_Unix.c_cstopb)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_cread = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_cread)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_parenb = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_parenb)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_parodd = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_parodd)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_hupcl = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_hupcl)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_clocal = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_clocal)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_isig = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_isig)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_icanon = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_icanon)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_noflsh = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_noflsh)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_echo = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_echo)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_echoe = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_echoe)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_echok = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_echok)
                                                                    (Prims.strcat
                                                                    "\n"
                                                                    (Prims.strcat
                                                                    "c_echonl = "
                                                                    (Prims.strcat
                                                                    (FStar_Class_Printable.to_string
                                                                    FStar_Class_Printable.printable_bool
                                                                    r.FStar_Unix.c_echonl)
                                                                    "\n}\n"))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  }
let (printable_unix_setattr_when :
  FStar_Unix.setattr_when FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun s ->
         match s with
         | FStar_Unix.TCSANOW -> "TCSANOW"
         | FStar_Unix.TCSADRAIN -> "TCSADRAIN"
         | FStar_Unix.TCSAFLUSH -> "TCSAFLUSH")
  }
let (printable_unix_flush_queue :
  FStar_Unix.flush_queue FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun f ->
         match f with
         | FStar_Unix.TCIFLUSH -> "TCIFLUSH"
         | FStar_Unix.TCOFLUSH -> "TCOFLUSH"
         | FStar_Unix.TCIOFLUSH -> "TCIOFLUSH")
  }
let (printable_unix_flow_action :
  FStar_Unix.flow_action FStar_Class_Printable.printable) =
  {
    FStar_Class_Printable.to_string =
      (fun f ->
         match f with
         | FStar_Unix.TCOOFF -> "TCOOFF"
         | FStar_Unix.TCOON -> "TCOON"
         | FStar_Unix.TCIOFF -> "TCIOFF"
         | FStar_Unix.TCION -> "TCION")
  }