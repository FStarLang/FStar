/* @flow */

import * as FStar_Array from "./FStar_Array";

export type seq<T> = T[];

export let create = FStar_Array.create;
export let append = FStar_Array.append;
export let length = FStar_Array.length;
export let index  = FStar_Array.index;
export let eq = FStar_Array.eq; 
