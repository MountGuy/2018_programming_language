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
   | TPair of typ * typ
   | TLoc of typ
   | TFun of typ * typ
   | TVar of var
   | TPrint of var
   | TEqual of var
   (* Modify, or add more if needed *)
 
 type typ_scheme =
   | SimpleTyp of typ
   | GenTyp of (var list * typ)
 
 type typ_env = (M.id * typ_scheme) list
  
 let equaled = ref []
 let printed = ref []
 
 let rec ref_tenv typ_env x =
   match typ_env with
   | (x1, t) :: tail ->
     if x = x1 then t else ref_tenv tail x
   | [] -> let _ = print_string("hugh??") in raise(M.TypeError "???")
 
 
 let rec typ_to_str t = 
   match t with
   | TInt -> "INT"
   | TBool -> "BOOL"
   | TString -> "STRING"
   | TPair (t1, t2) -> "PAIR("^ typ_to_str t1 ^ ", "^typ_to_str t2 ^ ")"
   | TLoc t -> "LOC(" ^ typ_to_str t ^ ")"
   | TFun (t1, t2) -> "FUN("^ typ_to_str t1 ^ ", "^typ_to_str t2 ^ ")"
   | TVar v -> v
   | TPrint v -> "printable"
   | TEqual v -> "equalable"
 
 
 let count = ref 0
  
 let new_var () =
   let _ = count := !count +1 in
   "x_" ^ (string_of_int !count)
  
  (* Definitions related to free type variable *)
  
 let union_ftv ftv_1 ftv_2 =
   let ftv_1' = List.filter (fun v -> not (List.mem v ftv_2)) ftv_1 in
   ftv_1' @ ftv_2
  
 let sub_ftv ftv_1 ftv_2 =
   List.filter (fun v -> not (List.mem v ftv_2)) ftv_1
  
 let rec ftv_of_typ : typ -> var list = function
   | TInt | TBool | TString -> []
   | TPair (t1, t2) -> union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
   | TLoc t -> ftv_of_typ t
   | TFun (t1, t2) ->  union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
   | TVar v | TPrint v | TEqual v -> [v]
  
 let ftv_of_scheme : typ_scheme -> var list = function
   | SimpleTyp t -> ftv_of_typ t
   | GenTyp (alphas, t) -> sub_ftv (ftv_of_typ t) alphas
  
 let ftv_of_env : typ_env -> var list = fun tyenv ->
   List.fold_left
     (fun acc_ftv (id, tyscm) -> union_ftv acc_ftv (ftv_of_scheme tyscm))
     [] tyenv
  
 (* Generalize given type into a type scheme *)
 let generalize : typ_env -> typ -> typ_scheme = fun tyenv t ->
   let env_ftv = ftv_of_env tyenv in
   let typ_ftv = ftv_of_typ t in
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
     | TInt | TBool | TString -> t'
     | TPair (t1, t2) -> TPair (subs t1, subs t2)
     | TLoc t'' -> TLoc (subs t'')
     | TFun (t1, t2) -> TFun (subs t1, subs t2)
     | TVar x'
     | TPrint x'
     | TEqual x' -> if (x = x') then t else t'
   in subs
  
 let make_subst_var : var -> var -> subst = fun x y ->
   let rec subs t' =
     match t' with
     | TInt | TBool | TString -> t'
     | TPair (t1, t2) -> TPair (subs t1, subs t2)
     | TLoc t'' -> TLoc (subs t'')
     | TFun (t1, t2) -> TFun (subs t1, subs t2)
     | TVar x' -> if x = x' then TVar y else t'
     | TPrint x' -> if x = x' then TPrint y else t'
     | TEqual x' -> if x = x' then TEqual y else t'
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
         (fun acc_subst alpha beta -> make_subst_var alpha beta @@ acc_subst)
         empty_subst alphas betas
     in
     GenTyp (betas, subs (s' t))
  
 let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
    List.map (fun (x, tyscm) -> (x, subst_scheme subs tyscm)) tyenv
  
 let rec invalid : typ * var -> bool = fun (t, x) ->
   match t with
   | TInt
   | TBool
   | TString -> false
   | TPair (t1, t2) -> invalid (t1, x) || invalid (t2, x)
   | TLoc t -> invalid(t, x)
   | TFun (t1, t2) -> invalid(t1, x) || invalid(t2, x)
   | TVar a
   | TPrint a
   | TEqual a -> if a = x then true else false
 
 
 let rec unify : (typ * typ) -> subst = fun (t1, t2) ->
   match t1 with
   | TInt ->
   (
     match t2 with
     | TInt -> empty_subst
     | TPrint x
     | TEqual x
     | TVar x -> make_subst x t1
     | _ ->raise(M.TypeError"oops")
   )
   | TBool ->
   (
     match t2 with
     | TBool -> empty_subst
     | TPrint x
     | TEqual x
     | TVar x -> make_subst x t1
     | _ -> raise(M.TypeError"oops")
   )
   | TString ->
   (
     match t2 with
     | TString -> empty_subst
     | TPrint x
     | TEqual x
     | TVar x -> make_subst x t1
     | _ -> raise(M.TypeError"oops")
   )
   | TPair (t1f, t1s) ->
   (
     match t2 with
     | TPair (t2f, t2s) ->
       let s = unify (t1f, t2f) in
       let s' = unify ((s t1s), (s t2s)) in
       s @@ s'
     | TVar x -> 
       if invalid (t1, x) then raise(M.TypeError"oops") else make_subst x t1
     | _ -> raise(M.TypeError"oops")
   )
   | TLoc t1l ->
   (
     match t2 with
     | TLoc t2l -> unify (t1l, t2l)
     | TEqual x -> make_subst x t1
     | TVar x -> 
       if invalid (t1, x) then raise(M.TypeError"oops") else make_subst x t1
     | _ -> raise(M.TypeError"oops")
   )
   | TFun (t1i, t1o) ->
   (
     match t2 with
     | TFun (t2i, t2o) ->
       let s = unify (t1i, t2i) in
       let s' = unify ((s t1o), (s t2o)) in
       s @@ s'
     | TVar x ->
       if invalid (t1, x) then raise(M.TypeError"oops") else make_subst x t1
     | _ -> raise(M.TypeError"oops")
   )
   | TPrint x1 ->
   (
     match t2 with
     | TInt -> make_subst x1 TInt
     | TBool -> make_subst x1 TBool
     | TString -> make_subst x1 TString
     | TVar x -> make_subst x t1
     | TPrint x2 -> make_subst x1 t2
     | _ -> raise(M.TypeError"oops")
   )
   | TEqual x1 ->
   (
     match t2 with
     | TInt -> make_subst x1 TInt
     | TBool -> make_subst x1 TBool
     | TString -> make_subst x1 TString
     | TLoc t2l -> make_subst x1 t2
     | TEqual x2 -> make_subst x1 t2
     | TVar x -> make_subst x t1
     | _ -> raise(M.TypeError"oops")
   )
   | TVar x1 ->
   (
     match t2 with
     | TVar x2 -> if x1 = x2 then empty_subst else (make_subst x1 t2)
     | _ ->
       if invalid(t2, x1) then 
       raise(M.TypeError"oops") else make_subst x1 t2
   )
   (*
     match t2 with
     | TVar x2 -> raise(M.TypeError"oops")
     | _ -> make_subst x1 t2
   *)
 
 let rec expansive : M.exp -> bool = fun exp ->
   match exp with
   | M.CONST _ -> false
   | M.VAR _ -> false
   | M.FN   _ -> false
   | M.APP _ -> true
   | M.LET (dec, e) ->
   (
     match dec with
     | REC _ -> expansive e
     | VAL (x, e') -> expansive e || expansive e'
   )
   | M.IF (e1, e2, e3) -> expansive e1 || expansive e2 || expansive e3
   | M.BOP (bop, e1, e2) -> expansive e1 || expansive e2
   | M.READ -> true
   | M.WRITE e -> expansive e
   | M.MALLOC e -> true
   | M.ASSIGN (e1, e2) -> expansive e1 || expansive e2
   | M.BANG e -> expansive e
   | M.SEQ (e1, e2) -> expansive e1 || expansive e2
   | M.PAIR (e1, e2) -> expansive e1 || expansive e2
   | M.FST e -> expansive e
   | M.SND e -> expansive e
 
 let rec online : typ_env -> M.exp -> (subst* typ) = fun tyenv exp ->
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
       | SimpleTyp t   -> (empty_subst, t)
       | GenTyp (_, t) -> (empty_subst, t)
     )
   | M.FN (x, e) ->
     let beta = TVar(new_var())in
     let (s1, t1) = online ((x, (SimpleTyp beta)) :: tyenv) e in
     (s1, TFun(s1 beta, t1))
   | M.APP (e1, e2) ->
     let (s1, t1) = online tyenv e1 in
     let tyenv' = subst_env s1 tyenv in
     let (s2, t2) = online tyenv' e2 in
     let beta = TVar(new_var())in
     let s3 = unify (s2 t1, TFun(t2, beta)) in
     (s3 @@ s2 @@ s1, s3 beta)
   | M.LET (dec, e2) ->
   (
     match dec with
     | M.REC (f, x, e1) ->
       let beta = TVar(new_var())in
       let (s1, t1) = online ((f, SimpleTyp beta) :: tyenv) (M.FN(x, e1)) in
       let s2 = unify (s1 beta, t1) in
       let tyenv' = subst_env (s2 @@ s1) tyenv in 
       let (s3, t3) = online ((f, generalize tyenv' (s2 t1)) :: tyenv') e2 in
       (s3 @@ s2 @@ s1, t3)
     | M.VAL (x, e1) ->
       let (s1, t1) = online tyenv e1 in
       let tyenv' = subst_env s1 tyenv in
       if not(expansive e1) 
       then 
       let (s2, t2) = online ((x, generalize tyenv' t1) :: tyenv') e2 in
       ((s2 @@ s1), t2)
       else
       let (s2, t2) = online ((x, SimpleTyp t1) :: tyenv') e2 in
       ((s2 @@ s1), t2)
   )
   | M.IF (e1, e2, e3) ->
     let (s1, t1) = online tyenv e1 in
     let s1' = unify (t1, TBool) in
     let tyenv' = subst_env (s1' @@  s1) tyenv in
     let (s2, t2) = online tyenv' e2 in
     let typenv'' = subst_env s2 tyenv' in
     let (s3, t3) = online typenv'' e3 in
     let s4 = unify (s3 t2, t3) in
     (s4 @@ s3 @@ s2 @@ s1' @@ s1, s4 t3)
   | M.BOP (op, e1, e2) ->
   (
     match op with
     | M.ADD
     | M.SUB ->
       let (s1, t1) = online tyenv e1 in
       let s1' = unify (t1, TInt) in
       let tyenv' = subst_env ( s1' @@  s1) tyenv in
       let (s2, t2) = online tyenv' e2 in
       let s2' = unify (t2, TInt) in
       (s2' @@ s2 @@ s1' @@ s1, TInt)
     | M.EQ ->
       let (s1, t1) = online tyenv e1 in
       let tyenv' = subst_env s1 tyenv in
       let (s2, t2) = online tyenv' e2 in
       let s2' = unify (t1, t2) in
       let beta = new_var() in
       let s3 = unify (t1, TEqual beta) in
       (s3 @@ s2' @@ s2 @@ s1, TBool)
     | M.AND
     | M.OR ->
       let (s1, t1) = online tyenv e1 in
       let s1' = unify (t1, TBool) in
       let tyenv' = subst_env (s1' @@ s1) tyenv in
       let (s2, t2) = online tyenv' e2 in
       let s2' = unify (t2, TBool) in
       (s2' @@ s2 @@ s1' @@ s1, TBool)
   )
   | M.READ -> (empty_subst, TInt)
   | M.WRITE e -> 
     let (s, t) = online tyenv e in
     let beta = new_var() in
     let s' = unify(t, TPrint beta) in
     (s' @@ s, t)
   | M.MALLOC e ->
     let (s1, t1) = online tyenv e in
     (s1, TLoc t1)
     (*
     let beta = TVar(new_var())in
     let s1' = unify(TLoc(t1), beta) in
     ((@@) s1' s1, s1' beta)*)
   | M.ASSIGN (e1, e2) ->
     let (s1, t1) = online tyenv e1 in
     let tyenv' = subst_env s1 tyenv in
     let (s2, t2) = online tyenv' e2 in
     let s2' = unify(TLoc(t2), s2 t1) in
     (s2' @@ s2 @@ s1, t2)
   | M.BANG e ->
     let (s1, t1) = online tyenv e in
     let beta = TVar(new_var()) in
     let s1' = unify(t1, TLoc(beta)) in
     (s1' @@ s1, beta)
   | M.SEQ (e1, e2) ->
     let (s1, t1) = online tyenv e1 in
     let tyenv' = subst_env s1 tyenv in
     let (s2, t2) = online tyenv' e2 in
     (s2 @@ s1, t2)
   | M.PAIR (e1, e2) ->
     let (s1, t1) = online tyenv e1 in
     let tyenv' = subst_env s1 tyenv in
     let (s2, t2) = online tyenv' e2 in
     (s2 @@ s1, TPair(s2 t1, t2))
   | M.FST e ->
     let (s1, t1) = online tyenv e in
     let beta1 = TVar(new_var()) in
     let beta2 = TVar(new_var()) in
     let s1' = unify(t1, TPair(beta1, beta2)) in
     (s1' @@ s1, (s1' @@ s1) beta1)
   | M.SND e ->
     let (s1, t1) = online tyenv e in
     let beta1 = TVar(new_var()) in
     let beta2 = TVar(new_var()) in
     let s1' = unify(t1, TPair(beta1, beta2)) in
     (s1' @@ s1, (s1' @@ s1) beta2)(* TODO : Implement this function *)
 let check : M.exp -> M.typ = fun exp ->
   let (s, t) = online [] exp in
 
   let rec typ2mtyp ans =
     match ans with
     | TInt -> M.TyInt
     | TBool -> M.TyBool
     | TString -> M.TyString
     | TPair(t1, t2) -> M.TyPair(typ2mtyp t1, typ2mtyp t2)
     | TLoc(t) -> M.TyLoc(typ2mtyp t)
     |  _ -> raise(M.TypeError"asdf") in
     
   typ2mtyp (s t)
 