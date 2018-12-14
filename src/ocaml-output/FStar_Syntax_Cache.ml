open Prims
type 'a cache = (FStar_Syntax_Syntax.term * 'a) FStar_Util.imap
let create : 'Auu____15 . unit -> 'Auu____15 FStar_Util.imap =
  fun uu____22  -> FStar_Util.imap_create (Prims.parse_int "100") 
let add : 'a . 'a cache -> FStar_Syntax_Syntax.term -> 'a -> unit =
  fun c  ->
    fun t  ->
      fun v1  ->
        let hash = FStar_Util.generic_hash t  in
        FStar_Util.imap_add c hash (t, v1)
  
let find :
  'a .
    'a cache ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
          FStar_Pervasives_Native.option -> 'a FStar_Pervasives_Native.option
  =
  fun c  ->
    fun t  ->
      fun f_opt  ->
        let uu____114 =
          let uu____121 = FStar_All.pipe_right t FStar_Util.generic_hash  in
          FStar_All.pipe_right uu____121 (FStar_Util.imap_try_find c)  in
        FStar_All.pipe_right uu____114
          (fun v_opt  ->
             match v_opt with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (t',v1) ->
                 (match f_opt with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.Some v1
                  | FStar_Pervasives_Native.Some f ->
                      let uu____189 = f t t'  in
                      if uu____189
                      then FStar_Pervasives_Native.Some v1
                      else FStar_Pervasives_Native.None))
  