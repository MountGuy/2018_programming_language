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

let (@+) f (x, v) = (fun y -> if y = x then v else f y)

type gamma = var -> typ

type equation =
  | EQUAL typ * typ
  | PAIR equation * equation

type solution = (typvar * typ) list

let get_var tvar =
  match tvar with
  | TVar x -> x

let rec struct_equation gam exp tvar =
  match exp with
  | CONST c ->
  (
    match c with
    | S _ -> EQUAL(TString, tvar)
    | N _ -> TInt(TInt, tvar)
    | B _ -> TBool(TBool, tvar)
  )
  | VAR x ->
    let v = new_var() in
    let t = gam x in
    
    if(get_var t == "#unbounded") then EQUAL(TVar(v), tvar) else EQUAL(t, tvar)

  | FN (x, e) -> 
    let vx = new_var() in
    let ve = new_var() in
    PAIR(EQUAL(TFun(TVar(vx), TVar(ve)), tvar),
        struct_equation (gam @+ (x, TVar(vx)), e, TVar(ve)))
  | APP (e1, e2) ->
    let v = new_var() in
    PAIR((struct_equation gam, e1, TFun(TVar(v), tvar)), (struct_equation gam, e2, Tvar(v)))
  | LET (dec, e) ->
  (
    match dec with
    | REC (f, x, e') -> EQUAL(TBool, TBool)
    | VAL (x, e') ->
      let v1 = new_var() in
      PAIR(
      (struct_equation gam e' TVar(v1)),
      (struct_equation (gam @+ (x, TVar(v1))) e tvar))
  )
  | IF (e1, e2, e3) ->
    let b = new_var() in
    let v1 = new_var() in
    let v2 = new_var() in
    
    PAIR(PAIR((struct_equation gam e1 TBool),
              (struct_equation gam e2 tvar)),
              (struct_equation gam e3 tvar))

  | BOP (b, e1, e2) ->
  (
    match b with
    | ADD -> PAIR(PAIR((struct_equation gam e1 TInt),
                       (struct_equation gam e2 TInt)),
                       (EQUAL(tvar, TInt)))
    | SUB -> PAIR(PAIR((struct_equation gam e1 TInt),
                       (struct_equation gam e2 TInt)),
                       (EQUAL(tvar, TInt)))
    | EQ ->
      let v1 = new_var() in
      let v2 = new_var() in
      PAIR(PAIR(PAIR(
        (struct_equation gam e1 TVar(v1)),
        (struct_equation gam e2 TVar(v2))),
      EQUAL(TVar(v1), TVar(v2))),
      EQUAL(TBool, tvar))

    | AND ->
      PAIR(PAIR(
        (struct_equation gam e1 TBool),
        (struct_equation gam e2 TBool)),
      EQUAL(tvar, TBool))
    | OR ->
      PAIR(PAIR(
        (struct_equation gam e1 TBool),
        (struct_equation gam e2 TBool)),
      EQUAL(tvar, TBool))
  )
  | READ -> EQUAL(tvar, TInt)
  | WRITE e ->
    struct_equation gam e tvar
  | MALLOC e ->
    struct_equation gam e TLoc(tvar)
  | ASSIGN (e1, e2) ->
    PAIR(
      (struct_equation gam e1 TLoc(tvar)),
      (struct_equation gam e2 tvar)
    )
  | BANG e ->
    struct_equation gam e TLoc(tvar)
  | SEQ (e1, e2) ->
    let v = new_var() in
    PAIR(
      (struct_equation gam e1 TVar(v)),
      (struct_equation gam e2 tvar))
  | PAIR (e1, e2) ->
    let v1 = new_var() in
    let v2 = new_var() in
    PAIR(PAIR(
    (struct_equation gam e1 v1),
    (struct_equation gam e2 v2)),
    EQUAL(TPair((TVar v1), (TVar v2)), tvar))

  | FST e ->
    let v1 = new_var() in
    let v2 = new_var() in
    struct_equation gam e v1
    EQUAL(TPair(tvar, v2), v1)

  | SND e ->
    let v1 = new_var() in
    let v2 = new_var() in
    struct_equation gam e v1
    EQUAL(TPair(v2, tvar), v1)

let rec solve equ = 

let emptyMem = 
  (0, fun l -> TVar("#unbounded"))


let rec check' : M.exp -> M.types = fun exp ->
  match exp with
  | CONST c ->
  (
    match c with
    | S _ -> TString
    | N _ -> TInt
    | B _ -> TBool
  )
  | VAR x -> TVAR(x)
  | FN (x, e) -> TFUN(TVar(x), (check' e) )
  | APP (e1, e2) ->
    let function = check' e1 in
    let v = check' e2 in
    
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
