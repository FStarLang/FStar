(*
   Copyright 2023 Microsoft Research

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

module Async.Examples

open Pulse.Lib.Pervasives
open Async

```pulse
fn mock_http_req (cb : (string -> stt int emp (fun _ -> emp)))
  requires emp
  returns _:int
  ensures emp
{
  let t1 = async (fun () -> cb "/index.html");
  let t2 = async (fun () -> cb "/favicon.ico");
  let v1 = await t1;
  let v2 = await t2;
  let v = v1+v2;
  v
}
```

```pulse
fn mock_http_req2_retasync (cb : (string -> stt int emp (fun _ -> emp)))
  requires emp
  returns r:(asynch int (fun _ -> emp))
  ensures async_joinable r
{
  let t1 = async (fun () -> cb "/index.html");
  let t2 = async (fun () -> cb "/favicon.ico");
  let v1 = await t1;
  t2
}
```
