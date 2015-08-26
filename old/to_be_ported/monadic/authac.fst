(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#monadic(DST, returnTX, bindTX)

module Authentication
  type prin =
    | U : string -> prin
    | Admin : prin

  private type cred :: prin => * = 
    | Cred : p:prin -> cred p

  val login : p:prin -> pw:string -> D (option (cred p))
  let login p pw = match p, pw with
    | U "Alice", "APassword" -> Some(Cred p)
    | Admin, "Secret" -> Some(Cred p)
    | _ -> None
end

module FileAC
  open Authentication

  type file
  type CanWrite :: prin => file => P
  assume Ax1:forall (f:file). CanWrite Admin f

  val fwrite: p:prin -> cred p -> (f:file {CanWrite p f}) -> string -> D unit 
  (* let fwrite p c f s = (\* Call system write here  *\)() *)
end

module Client
open Authentication
open FileAC

val client : p:prin -> cred p -> file -> D unit
let client p c f = match p with
  | Admin -> fwrite p c f "Hello"
  | _ -> ()
end
