(*
 * SNU 4190.310 Programming Languages
 * Type Checker Skeleton
 *)

open M

type var = string

type typ = 
  | TInt
  | TBool
  | TString
  | TPair  typ * typ
  | TLoc  typ
  | TFun  typ * typ
  | TVar  var
  (* Modify, or add more if needed *)

type typ_scheme =
  | SimpleTyp  typ 
  | GenTyp  (var list * typ)

type typ_env = (M.id * typ_scheme) list

let rec ref_tenv typ_env x =
  match typ_env with
  | (x1, t) :: tail ->
    if x = x1 then t else ref_tenv tail x
  | [] -> raise(TypeError "???")


let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string__int !count)

(* Definitions related to free type variable *)

let union_ftv ftv_1 ftv_2 = 
  let ftv_1' = List.filter (fun v -> not (List.mem v ftv_2)) ftv_1 in
  ftv_1' @ ftv_2
  
let sub_ftv ftv_1 ftv_2 =
  List.filter (fun v -> not (List.mem v ftv_2)) ftv_1

let rec ftv__typ : typ -> var list = function
  | TInt | TBool | TString -> []
  | TPair (t1, t2) -> union_ftv (ftv__typ t1) (ftv__typ t2)
  | TLoc t -> ftv__typ t
  | TFun (t1, t2) ->  union_ftv (ftv__typ t1) (ftv__typ t2)
  | TVar v -> [v]

let ftv__scheme : typ_scheme -> var list = function
  | SimpleTyp t -> ftv__typ t
  | GenTyp (alphas, t) -> sub_ftv (ftv__typ t) alphas 

let ftv__env : typ_env -> var list = fun tyenv ->
  List.fold_left 
    (fun acc_ftv (id, tyscm) -> union_ftv acc_ftv (ftv__scheme tyscm))
    [] tyenv 

(* Generalize given type into a type scheme *)
let generalize : typ_env -> typ -> typ_scheme = fun tyenv t ->
  let env_ftv = ftv__env tyenv in
  let typ_ftv = ftv__typ t in
  let ftv = sub_ftv typ_ftv env_ftv in
  if List.length ftv = 0 then
    SimpleTyp t
  else
    GenTyp(ftv, t)

(* Definitions related to substitution *)

type subst = typ -> typ

let empty_subst : subst = fun t -> t

let make_subst : var -> typ -> subst = fun x t ->
  let rec subs t' = 
    match t' with
    | TVar x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | TInt | TBool | TString -> t'
  in subs

let (@@) s1 s2 = (fun t -> s1 (s2 t)) (* substitution composition *)

let subst_scheme : subst -> typ_scheme -> typ_scheme = fun subs tyscm ->
  match tyscm with
  | SimpleTyp t -> SimpleTyp (subs t)
  | GenTyp (alphas, t) ->
    (* S (\all a.t) = \all b.S{a->b}t  (where b is new variable) *)
    let betas = List.map (fun _ -> new_var()) alphas in
    let s' =
      List.fold_left2
        (fun acc_subst alpha beta -> make_subst alpha (TVar beta) @@ acc_subst)
        empty_subst alphas betas
    in
    GenTyp (betas, subs (s' t))

let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
  List.map (fun (x, tyscm) -> (x, subst_scheme subs tyscm)) tyenv

let rec unify : (typ * typ) -> subst = fun (t1, t2) ->
  match t1 with
  | TInt ->
  (
    match t2 with
    | TInt -> empty_subst
    | TVar x -> make_subst x t1
    | _ -> raise(M.TypeError"oops")
  )
  | TBool ->
  (
    match t2 with
    | TBool -> empty_subst
    | TVar x -> make_subst x t1
    | _ -> raise(M.TypeError"oops")
  )
  | TString ->
  (
    match t2 with
    | TString -> empty_subst
    | TVar x -> make_subst x t1
    | _ -> raise(M.TypeError"oops")
  )
  | TPair (t1f, t1s) ->
  (
    match t2 with
    | TPair (t2f, t2s) ->
      let s = unify t1f t2f in
      let s' = unify (s t1s) (s t2s) in
      (@@) s s'
    | TVar x -> make_subst x t1
    | _ -> raise(M.TypeError"oops")
  )
  | TLoc t1l ->
  (
    match t2 with
    | TLoc t2l -> unify t1l t2l
    | TVar x -> make_subst x t1
    | _ -> raise(M.TypeError"oops")
  )
  | TFun (t1i, t1o) ->
  (
    match t2 with
    | TPair (t2i, t2o) ->
      let s = unify t1i t2i in
      let s' = unify (s t1o) (s t2o) in
      (@@) s s'
    | TVar x -> make_subst x t1
    | _ -> raise(M.TypeError"oops")
  )
  | TVar x1 -> make_subst x1 t2
  (*
    match t2 with
    | TVar x2 -> raise(M.TypeError"oops")
    | _ -> make_subst x1 t2
  *)

let rec expansive : M.exp -> bool = fun exp ->
  match exp with
  | CONST _ -> false
  | VAR _ -> false
  | FN   _ -> false
  | APP _ -> true
  | LET (dec, e) ->
  (
    match dec with
    | REC _ -> expansive e
    | VAL (x, e') -> expansive e || expansive e'
  )
  | IF (e1, e2, e3) -> expansive e1 || expansive e2 || expansive e3
  | BOP (bop, e1, e2) -> expansive e1 || expansive e2
  | READ -> true
  | WRITE e -> expansive e
  | MALLOC e -> true
  | ASSIGN (e1, e2) -> expansive e1 || expansive e2
  | BANG e -> expansive e
  | SEQ (e1, e2) -> expansive e1 || expansive e2
  | PAIR (e1, e2) -> expansive e1 || expansive e2
  | FST e -> expansive e
  | SND e -> expansive e

let rec oneline : typ_env -> M.exp -> ((typ -> typ) * typ) = fun (tyenv, exp) ->
  match exp with
  | M.CONST c ->
  (
    match c with
    | M.S _ -> (empty_subst, TString)
    | M.N _ -> (empty_subst, TInt)
    | M.B _ -> (empty_subst, TBool)
  )
  | M.VAR x ->
    let sigma = ref_tenv tyenv x in
    let s_sig = subst_scheme empty_subst sigma in
    (
      match s_sig with
      | SimpleTyp t -> (empty_subst, t)
      | GenTyp (_, t) -> (empty_subst, t)
    )
  | M.FN (x, e) ->
    let beta = (TVar new_var())in
    let (s1, t1) = online ((x, (SimpleTyp beta)) :: tyenv) e in
    (s1, (TFun s1 beta, t1))
  | M.APP (e1, e2) ->
    let (s1, t1) = online tyenv e1 in
    let s1gam = subst_env s1 tyenv in
    let (s2, t2) = online s1gam e2 in
    let beta = (TVar new_var())in
    let s3 = unify (s2 t1, (TFun t2, beta)) in
    let s1s2 = (@@) s1 s2 in
    ((@@) s3 s1s2, s3 beta)
  | M.LET (dec, e2) ->
  (
    match dec with
    | M.REC (f, x, e1) ->
      let beta = (TVar new_var())in
      let (s1, t1) = online ((f, beta) :: tyenv) M.FN(x, e1) in
      let s2 = unify (s1 beta, t1) in
      ((@@) s2 s1, s2 t1)
    | M.VAL (x, e1) ->
      let (s1, t1) = online tyenv e1 in
      let s1gam = subst_env s1 tyenv in
      let (s2, t2) = online ((x, generalize s1gam t1) :: s1gam) e2 in
      (((@@) s1 s2), t2)
  )
  | M.IF (e1, e2, e3) ->
    let (s1, t1) = online tyenv e1 in
    let s1' = unify (t1, TBool) in
    let s1gam = subst_env ((@@) s1 s1') tyenv in

    let (s2, t2) = online s1gam e2 in
    let s2gam = subst_env s2 s1gam in

    let (s3, t3) = online s2gam e3 in
    let s4 = unify (s3 t2, t3) in

    let s1s2 = (@@) s1 s2 in
    let s3s4 = (@@) s3 s4 in
    ((@@) s1s2 s3s4 , s4 t3)
  | M.BOP (op, e1, e2) ->
  (
    match op with
    | ADD
    | SUB ->
      let (s1, t1) = online tyenv e1 in
      let s1' = unify (t1, TInt) in
      let s1gam = subst_env ((@@) s1 s1') tyenv in

      let (s2, t2) = online s1gam e2 in
      let s2' = unify (t2, TInt) in
      let s2gam = subst_env ((@@) s2 s2') in

      ((@@) ((@@) s1 s1') ((@@) s2 s2'), TInt)
    | EQ ->
      let (s1, t1) = online tyenv e1 in
      let s1gam = subst_env s1 tyenv in

      let (s2, t2) = online s1gam e2 in
      let s2' = unify (t1, t2) in

      (((@@) ((@@) s1 s2) s2'), t1)
    | AND
    | OR ->
      let (s1, t1) = online tyenv e1 in
      let s1' = unify (t1, TBool) in
      let s1gam = subst_env ((@@) s1 s1') tyenv in

      let (s2, t2) = online s1gam e2 in
      let s2' = unify (t2, TBool) in
      let s2gam = subst_env ((@@) s2 s2') in

      ((@@) ((@@) s1 s1') ((@@) s2 s2'), TBool)
  )
  | M.READ -> (empty_subst, TInt)
  | M.WRITE e -> online tyenv e
  | M.MALLOC e ->
    let (s1, t1) = online tyenv e in
    let beta = (TVar new_var())in
    let s1' = unify(TLoc(t1), beta) in
    ((@@) s1' s1, s1' beta)
  | M.ASSIGN (e1, e2) ->
    let (s1, t1) = online tyenv e1 in
    let s1gam = subst_env s1 tyenv in
    let (s2, t2) = online tyenv e2 in
  | M.BANG e ->
  | M.SEQ (e1, e2) ->
  | M.PAIR (e1, e2) ->
  | M.FST e ->
  | M.SND e ->

(* TODO : Implement this function *)
let check : M.exp -> M.typ =
  raise (M.TypeError "Type Checker Unimplemented")
