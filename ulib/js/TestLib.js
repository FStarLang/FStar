/* @flow */

import * as FStar_Buffer from "./FStar_Buffer";

export type uint8_p = FStar_Buffer.buffer<number>;

export let uint8_p_to_string = (b:FStar_Buffer.buffer<number>) : ((len:number) => string) => ((len:number) => {
    let res = "";
    for (let i = 0; i < len; i++){
        res = res.concat(b._content[i].toString());
    };
    return res;
});

export let compare_and_print = (txt:any) => ((reference:uint8_p) => ((produced:uint8_p) => ((len:number) => {
    let ref_string = uint8_p_to_string(reference)(len);
    let prod_string = uint8_p_to_string(produced)(len);
    console.log("[test] expected output is \n" + ref_string);
    console.log("[test] computed output is \n" + prod_string);
    for (let i = 0; i < len; i++){
        if (ref_string.charAt(i) != prod_string.charAt(i)){
            console.log("[test] reference and expected strings differ at byte " + i);
            throw "Bad crypto";   
        }
    };
    console.log("Good crypto");
})));