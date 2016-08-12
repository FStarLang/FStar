
module VerSGXState

open FStar.UInt64
open Ast


type cpuregstate =
{
 rsp: dword;
 rbp: dword;
 rax: dword;
 rbx: dword;
 rcx: dword;
 rdx: dword;
 r8: dword;
 r9: dword;
}


let search_reg (regname:string) (env:cpuregstate) :(Tot dword) = 
	if regname = "rsp" then
		env.rsp
	else if regname = "rbp" then
		env.rbp
	else if regname = "rax" then
		env.rax
	else if regname = "rbx" then
		env.rbx
	else if regname = "rcx" then
		env.rcx
	else if regname = "rdx" then
		env.rdx
	else if regname = "r8" then
		env.r8
	else 
		env.r9
	

let read (regname:string) (env:cpuregstate) :(Tot dword)  =
	search_reg regname (env)

