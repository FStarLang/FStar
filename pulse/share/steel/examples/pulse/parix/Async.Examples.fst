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
  let t2 = async (fun () -> cb "/whatever");
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
  let t2 = async (fun () -> cb "/whatever");
  let v1 = await t1;
  t2
}
```
