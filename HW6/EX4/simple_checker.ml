(*
 * SNU 4190.310 Programming Languages
 * Type Checker Skeleton Code
 *)

open M
open Pp

type var = string

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

type typ = 
  | TInt
  | TBool
  | TString
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var
  (* Modify, or add more if needed *)

let rec check' : M.exp -> M.types = fun exp ->
  match exp with
  | CONST c
  | VAR x
  | FN (x, e)
  | APP (e1, e2)
  | LET (d, e2)
  | IF (e1, e2, e3)
  | BOP (bop, e1, e2)
  | READ
  | WRITE e
  | MALLOC e          (*   malloc e *)
  | ASSIGN (e1, e2)    (*   e := e   *)
  | BANG e         (*   !e       *)
  | SEQ (e1, e2)       (*   e ; e    *)
  | PAIR (e1, e2)      (*   (e, e)   *)
  | FST e          (*   e.1      *)
  | SND e            (*   e.2      *)

(* TODO : Implement this function *)
let check : M.exp -> M.types = fun exp ->
  raise (M.TypeError "Type Checker Unimplemented")
