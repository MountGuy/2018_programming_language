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
  | EQUAL of typ * typ
  | PAIR of equation * equation

type solution = (var * typ) list

let rec get_var tvar =
  match tvar with
  | TVar x -> x
  | TInt -> "INT"
  | TBool -> "BOOL"
  | TString -> "STRING"
  | TLoc t -> "LOC(" ^ (get_var t)^")"
  | TFun (t1, t2) -> "FUN("^(get_var t1) ^ " " ^ (get_var t2) ^ ")"
  | TPair (t1, t2) -> "PAIR("^(get_var t1) ^ " " ^ (get_var t2) ^ ")"

let rec get_typ tvar sol =
  match tvar with
  | TVar var ->(
    match sol with
    | head :: tail ->
    (
      match head with
      | (v, t) -> if(v == (var)) then t else get_typ tvar tail
    )
    | [] -> tvar
  )
  | _ -> tvar

let rec struct_equation gam exp tvar =
  match exp with
  | M.CONST c ->
  (
    match c with
    | M.S _ -> EQUAL(TString, tvar)
    | M.N _ -> EQUAL(TInt, tvar)
    | M.B _ -> EQUAL(TBool, tvar)
  )
  | M.VAR x ->
    let v = new_var() in
    let t = gam x in
    
    if(get_var t == "#unbounded") then EQUAL(TVar(v), tvar) else EQUAL(t, tvar)

  | M.FN (x, e) -> 
    let vx = new_var() in
    let ve = new_var() in
    PAIR(EQUAL(TFun(TVar(vx), TVar(ve)), tvar),
        (struct_equation (gam @+ (x, TVar(vx))) e (TVar(ve))))
  | M.APP (e1, e2) ->
    let v = new_var() in
    PAIR((struct_equation gam e1 (TFun(TVar(v), tvar))),
    (struct_equation gam e2 (TVar(v))))
  | M.LET (dec, e) ->
  (
    match dec with
    | M.REC (f, x, e') -> (*EQUAL(TBool, TBool)*)
      let vx = new_var() in
      let ve = new_var() in

      let gam' = ((gam @+ (x, (TVar(vx)))) @+ (f, (TFun(TVar(vx), TVar(ve))))) in
      let gam'' = (gam @+ (f, (TFun(TVar(vx), TVar(ve))))) in
      PAIR((struct_equation gam' e' (TVar(ve))),
      (struct_equation gam'' e tvar))

    | M.VAL (x, e') ->
      let v1 = new_var() in
      PAIR(
      (struct_equation gam e' (TVar(v1))),
      (struct_equation (gam @+ (x, (TVar(v1)))) e tvar))
  )
  | M.IF (e1, e2, e3) ->
    PAIR(PAIR((struct_equation gam e1 TBool),
              (struct_equation gam e2 tvar)),
              (struct_equation gam e3 tvar))

  | M.BOP (b, e1, e2) ->
  (
    match b with
    | M.ADD -> PAIR(PAIR((struct_equation gam e1 TInt),
                       (struct_equation gam e2 TInt)),
                       (EQUAL(tvar, TInt)))
    | M.SUB -> PAIR(PAIR((struct_equation gam e1 TInt),
                       (struct_equation gam e2 TInt)),
                       (EQUAL(tvar, TInt)))
    | M.EQ ->
      let v1 = new_var() in
      let v2 = new_var() in
      PAIR(PAIR(PAIR(
        (struct_equation gam e1 (TVar(v1))),
        (struct_equation gam e2 (TVar(v2)))),
      EQUAL(TVar(v1), TVar(v2))),
      EQUAL(TBool, tvar))

    | M.AND ->
      PAIR(PAIR(
        (struct_equation gam e1 TBool),
        (struct_equation gam e2 TBool)),
      EQUAL(tvar, TBool))
    | M.OR ->
      PAIR(PAIR(
        (struct_equation gam e1 TBool),
        (struct_equation gam e2 TBool)),
      EQUAL(tvar, TBool))
  )
  | M.READ -> EQUAL(tvar, TInt)
  | M.WRITE e ->
    struct_equation gam e tvar
  | M.MALLOC e ->
    let v = new_var() in
    PAIR(struct_equation gam e (TVar(v)),
    EQUAL(TLoc(TVar(v)), tvar))  
  | M.ASSIGN (e1, e2) ->
    PAIR(
      (struct_equation gam e1 (TLoc(tvar))),
      (struct_equation gam e2 tvar)
    )
  | M.BANG e ->
    struct_equation gam e (TLoc(tvar))
  | M.SEQ (e1, e2) ->
    let v = new_var() in
    PAIR(
      (struct_equation gam e1 (TVar(v))),
      (struct_equation gam e2 tvar))
  | M.PAIR (e1, e2) ->
    let v1 = new_var() in
    let v2 = new_var() in
    PAIR(PAIR(
    (struct_equation gam e1 (TVar(v1))),
    (struct_equation gam e2 (TVar(v2)))),
    EQUAL(TPair((TVar v1), (TVar v2)), tvar))

  | M.FST e ->
    let v1 = new_var() in
    let v2 = new_var() in
    PAIR(struct_equation gam e (TVar(v1)),
    EQUAL(TPair(tvar, (TVar(v2))), (TVar(v1))))

  | M.SND e ->
    let v1 = new_var() in
    let v2 = new_var() in
    PAIR(struct_equation gam e (TVar(v1)),
    EQUAL(TPair((TVar(v2)), tvar), (TVar(v1))))


let rec typeIsConst typ =
  match typ with
  | TPair(t1, t2) -> (typeIsConst t1) && (typeIsConst t2)
  | TLoc t -> (typeIsConst t)
  | TFun (t1, t2) -> (typeIsConst t1) && (typeIsConst t2)
  | TInt -> true
  | TBool -> true
  | TString -> true
  | TVar _ -> false

let rec identicalT t1 t2 =
  match t1 with
  | TPair(t11, t12) ->(
    match t2 with
    | TPair(t21, t22) -> identicalT t11 t21 && identicalT t12 t22
    | _ -> false
  )
  | TLoc t -> (
    match t2 with
    | TLoc(t') -> identicalT t t'
    | _ -> false
  )
  | TFun(t11, t12) ->(
    match t2 with
    | TFun(t21, t22) -> identicalT t11 t21 && identicalT t12 t22
    | _ -> false
  )
  | TInt -> (
    match t2 with
    | TInt -> true
    | _ -> false
  )
  | TBool -> (
    match t2 with
    | TBool -> true
    | _ -> false
  )
  | TString -> (
    match t2 with
    | TString -> true
    | _ -> false
  )
  | TVar v1 ->  (
    match t2 with
    | TVar v2 -> (v1 == v2)
    | _ -> false
  )

let rec solve equ sol =
  match equ with
  | EQUAL(t1, t2) ->
  (
    if typeIsConst t1 && typeIsConst t2 && not(identicalT t1 t2)
    then raise(M.TypeError("asdf1"))
    else
    match get_typ t1 sol with
    | TVar v1 -> (
      let t2Typ = get_typ t2 sol in
      if typeIsConst t2Typ then [(v1, t2Typ)] else []

    )
    | _ -> (
      match get_typ t2 sol with
      | TVar v2 -> (
        let t1Typ = get_typ t1 sol in
        if typeIsConst t1Typ then [(v2, t1Typ)] else []
      )
      | _ -> []
    )
  )
  | PAIR (e1, e2) -> (solve e1 sol) @ (solve e2 sol)
    (*let (equ1, sol1) = solve e1 sol in
    let (equ2, sol2) = solve e2 sol in
    ((PAIR(equ1, equ2)), sol1 @ sol2)*)



let rec relocateT typ sol =
  match typ with
  | TPair(t1, t2) -> TPair(relocateT t1 sol, relocateT t2 sol)
  | TLoc t -> TLoc(relocateT t sol)
  | TFun (t1, t2) -> TFun(relocateT t1 sol, relocateT t2 sol)
  | TVar v -> 
    if(typeIsConst (get_typ typ sol)) then get_typ typ sol else typ
  | _ -> typ

let rec relocateE equ sol =
  match equ with
  | EQUAL(t1, t2) -> (*EQUAL(relocateT t1 sol, relocateT t2 sol)*)
    let typ1 = get_typ t1 sol in
    let typ2 = get_typ t2 sol in
    (match typ1 with
      | TPair(t11, t12) ->(
        match typ2 with
        | TPair(t21, t22) -> PAIR(EQUAL(t11, t21),EQUAL(t12, t22))
        | TVar _ -> EQUAL(relocateT typ1 sol, typ2)
        | _ -> raise(M.TypeError "asdf2") 
      )
      | TLoc t ->(
        match typ2 with
        | TLoc(t') -> EQUAL(t, t')
        | TVar _ -> EQUAL(relocateT typ1 sol, typ2)
        | _ -> raise(M.TypeError "asdf3")
      )
      | TFun(t11, t12) ->(
        match typ2 with
        | TFun(t21, t22) -> PAIR(EQUAL(t11, t21),EQUAL(t12, t22))
        | TVar _ -> EQUAL(relocateT typ1 sol, typ2)
        | _ -> raise(M.TypeError "asdf4")
      )
      | _ ->EQUAL(relocateT t1 sol, relocateT t2 sol)
    )
  | PAIR(e1, e2) -> PAIR(relocateE e1 sol, relocateE e2 sol)
  
let rec print_equ equ =
  match equ with
  | EQUAL(t1, t2) -> print_endline(get_var t1 ^ "=" ^ get_var t2)
  | PAIR(e1, e2) -> print_equ e1; print_equ e2

let rec type2str typ =
  match typ with
  | TInt -> "INT"
  | TBool -> "BOOL"
  | TString -> "STRING"
  | TPair (t1, t2) -> "PAIR("^(type2str t1) ^ " " ^ (type2str t2) ^ ")"
  | TFun (t1, t2) -> "FUN("^(type2str t1) ^ " " ^ (type2str t2) ^ ")"
  | TLoc t -> "LOC(" ^ (type2str t) ^")"
  | TVar v -> "VAR"
  

let rec print_sol sol =
  match sol with
  | (v, t) :: tail -> let _ = print_endline(v ^ " " ^ (type2str t)) in print_sol tail
  | [] -> print_string("")

let rec refine sol =
  match sol with
  | (var, typ)::tail ->
    let (vars, typs) = List.split tail in
    if List.mem var vars then
      let (var', typ') = List.find (fun a -> fst a == var) tail in
      if (identicalT typ typ') then refine tail else raise(M.TypeError"asdf5")
     else ((var, typ) :: (refine tail))
  | [] -> []


let rec identicalE equ1 equ2 =
  match equ1 with
  | EQUAL(t1, t2) ->
  (
    match equ2 with
    | EQUAL(t1', t2') -> (identicalT t1 t1') && (identicalT t2' t2)
    | PAIR _ -> false
  )
  | PAIR(e1, e2) ->
  (
    match equ2 with
    | EQUAL _ -> false
    | PAIR(e1', e2') -> (identicalE e1 e1') && (identicalE e2 e2')
  )



let check : M.exp -> M.types = fun exp ->
  let empGam = fun l -> TVar("#unbounded") in
  let tvar = TVar("#result") in
  let equ = struct_equation empGam exp tvar in
  let sol = [] in


  let rec eval equ sol =(
    let sol' = sol @ solve equ sol in
    let equ' = relocateE equ sol' in
    let sol'' = refine sol' in
    let _ = print_equ equ' in
    let _ = print_endline("=====") in
    if(List.length sol < List.length sol'' || not(identicalE equ equ')) then eval equ' sol' else sol) in

  let answer = eval equ sol in

  let ans = get_typ tvar answer in

  let rec typ2mtyp ans =
  match ans with
  | TInt -> M.TyInt
  | TBool -> M.TyBool
  | TString -> M.TyString
  | TPair(t1, t2) -> M.TyPair(typ2mtyp t1, typ2mtyp t2)
  | TLoc(t) -> M.TyLoc(typ2mtyp t)
  | TFun(t1, t2) -> M.TyArrow(typ2mtyp t1, typ2mtyp t2) in

  typ2mtyp ans
