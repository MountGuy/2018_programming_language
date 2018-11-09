(*
 * SNU 4190.310 Programming Languages 2018 Fall
 *  K- Interpreter Skeleton Code
 *)

(* Location Signature *)
module type LOC =
sig
  type t
  val base : t
  val equal : t -> t -> bool
  val diff : t -> t -> int
  val increase : t -> int -> t
end

module Loc : LOC =
struct
  type t = Location of int
  let base = Location(0)
  let equal (Location(a)) (Location(b)) = (a = b)
  let diff (Location(a)) (Location(b)) = a - b
  let increase (Location(base)) n = Location(base+n)
end

(* Memory Signature *)
module type MEM = 
sig
  type 'a t
  exception Not_allocated
  exception Not_initialized
  val empty : 'a t (* get empty memory *)
  val load : 'a t -> Loc.t  -> 'a (* load value : Mem.load mem loc => value *)
  val store : 'a t -> Loc.t -> 'a -> 'a t (* save value : Mem.store mem loc value => mem' *)
  val alloc : 'a t -> Loc.t * 'a t (* get fresh memory cell : Mem.alloc mem => (loc, mem') *)
end

(* Environment Signature *)
module type ENV =
sig
  type ('a, 'b) t
  exception Not_bound
  val empty : ('a, 'b) t (* get empty environment *)
  val lookup : ('a, 'b) t -> 'a -> 'b (* lookup environment : Env.lookup env key => content *)
  val bind : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t  (* id binding : Env.bind env key content => env'*)
end

(* Memory Implementation *)
module Mem : MEM =
struct
  exception Not_allocated
  exception Not_initialized
  type 'a content = V of 'a | U
  type 'a t = M of Loc.t * 'a content list
  let empty = M (Loc.base,[])

  let rec replace_nth = fun l n c -> 
    match l with
    | h::t -> if n = 1 then c :: t else h :: (replace_nth t (n - 1) c)
    | [] -> raise Not_allocated

  let load (M (boundary,storage)) loc =
    match (List.nth storage ((Loc.diff boundary loc) - 1)) with
    | V v -> v 
    | U -> raise Not_initialized

  let store (M (boundary,storage)) loc content =
    M (boundary, replace_nth storage (Loc.diff boundary loc) (V content))

  let alloc (M (boundary,storage)) = 
    (boundary, M (Loc.increase boundary 1, U :: storage))
end

(* Environment Implementation *)
module Env : ENV=
struct
  exception Not_bound
  type ('a, 'b) t = E of ('a -> 'b)
  let empty = E (fun x -> raise Not_bound)
  let lookup (E (env)) id = env id
  let bind (E (env)) id loc = E (fun x -> if x = id then loc else env x)
end

(*
 * K- Interpreter
 *)
module type KMINUS =
sig
  exception Error of string
  type id = string
  type exp =
    | NUM of int | TRUE | FALSE | UNIT
    | VAR of id
    | ADD of exp * exp
    | SUB of exp * exp
    | MUL of exp * exp
    | DIV of exp * exp
    | EQUAL of exp * exp
    | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
    | ASSIGNF of exp * id * exp   (* assign to record field *)
    | READ of id
    | WRITE of exp
    
  type program = exp
  type memory
  type env
  type value =
    | Num of int
    | Bool of bool
    | Unit
    | Record of (id -> Loc.t)
  val emptyMemory : memory
  val emptyEnv : env
  val run : memory * env * program -> value
end

module K : KMINUS =
struct
  exception Error of string

  type id = string
  type exp =
    | NUM of int
    | TRUE
    | FALSE
    | UNIT
    | VAR of id
    | ADD of exp * exp
    | SUB of exp * exp
    | MUL of exp * exp
    | DIV of exp * exp
    | EQUAL of exp * exp
    | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
    | ASSIGNF of exp * id * exp   (* assign to record field *)
    | READ of id
    | WRITE of exp

  type program = exp

  type value =
    | Num of int
    | Bool of bool
    | Unit
    | Record of (id -> Loc.t)
    
  type memory = value Mem.t
  type env = (id, env_entry) Env.t
  and  env_entry = Addr of Loc.t | Proc of id list * exp * env

  let emptyMemory = Mem.empty
  let emptyEnv = Env.empty

  let value_int v =
    match v with
    | Num n -> n
    | _ -> raise (Error "TypeError : not int")

  let value_bool v =
    match v with
    | Bool b -> b
    | _ -> raise (Error "TypeError : not bool")

  let value_unit v =
    match v with
    | Unit -> ()
    | _ -> raise (Error "TypeError : not unit")

  let value_record v =
    match v with
    | Record r -> r
    | _ -> raise (Error "TypeError : not record")

  let lookup_env_loc e x =
    try
      (match Env.lookup e x with
      | Addr l -> l
      | Proc _ -> raise (Error "TypeError : not addr")) 
    with Env.Not_bound -> raise (Error "Unbound")

  let lookup_env_proc e f =
    try
      (match Env.lookup e f with
      | Addr _ -> raise (Error "TypeError : not proc") 
      | Proc (id_list, exp, env) -> (id_list, exp, env))
    with Env.Not_bound -> raise (Error "Unbound")

  let rec eval mem env e =
    match e with
    | READ x -> 
      let v = Num (read_int()) in
      let l = lookup_env_loc env x in
      (v, Mem.store mem l v)
    | WRITE e ->
      let (v, mem') = eval mem env e in
      let n = value_int v in
      let _ = print_endline (string_of_int n) in
      (v, mem')
    | LETV (x, e1, e2) ->
      let (v, mem') = eval mem env e1 in
      let (l, mem'') = Mem.alloc mem' in
      eval (Mem.store mem'' l v) (Env.bind env x (Addr l)) e2
    | ASSIGN (x, e) ->
      let (v, mem') = eval mem env e in
      let l = lookup_env_loc env x in
      (v, Mem.store mem' l v)
    | NUM n -> (Num n, mem)
    | TRUE -> (Bool true, mem)
    | FALSE -> (Bool false, mem)
    | UNIT -> (Unit, mem)
    | VAR x ->
      let l = lookup_env_loc env x in
      let v = (Mem.load mem l) in
      (v, mem)
    | ADD (e1,e2) -> 
      let (v1, mem1) = (eval mem env e1) in
      let (v2, mem2) = (eval mem1 env e2) in
      (Num((value_int v1) + (value_int v2)), mem2)
    | SUB (e1,e2) -> 
      let (v1, mem1) = (eval mem env e1) in
      let (v2, mem2) = (eval mem1 env e2) in
      (Num((value_int v1) - (value_int v2)), mem2)
    | MUL (e1,e2) -> 
      let (v1, mem1) = (eval mem env e1) in
      let (v2, mem2) = (eval mem1 env e2) in
      (Num((value_int v1) * (value_int v2)), mem2)
    | DIV (e1,e2) -> 
      let (v1, mem1) = (eval mem env e1) in
      let (v2, mem2) = (eval mem1 env e2) in
      (Num((value_int v1) / (value_int v2)), mem2)
    | EQUAL (e1,e2) ->
      let (v1, mem1) = (eval mem env e1) in
      let (v2, mem2) = (eval mem1 env e2) in
      (match v1 with
      | Num n1 ->
        (match v2 with
        | Num n2 -> (Bool(n1==n2), mem2)
        | _ -> (Bool(false), mem2)
        )
      | Bool b1 ->
        (match v2 with
        | Bool b2 -> (Bool(b1==b2), mem2)
        | _ -> (Bool(false), mem2)
        )
      | Unit ->
        (match v2 with
        | Unit -> (Bool(true), mem2)
        | _ -> (Bool(false), mem2)
        )
      | _ -> (Bool(false), mem2)
      )
    | LESS (e1,e2) -> 
      let (v1, mem1) = (eval mem env e1) in
      let (v2, mem2) = (eval mem1 env e2) in
      (Bool((value_int v1) < (value_int v2)), mem2)
    | NOT e ->
      let (v1, mem1) = (eval mem env e) in
      (Bool(not (value_bool v1)), mem1)
    | SEQ (e1,e2) ->
      let (v, mem') = (eval mem env e1) in
      let (v', mem'') = (eval mem' env e2) in
      (v', mem'')
    | IF (e1,e2, e3) ->
      let (v, mem') = (eval mem env e1) in
      if(value_bool v) then (eval mem' env e2) else (eval mem' env e3)
    | WHILE (e1,e2) ->
      let (v, mem') = (eval mem env e1) in
      if(value_bool v) then (eval mem' env (SEQ(e2,WHILE(e1, e2)))) else (Unit, mem')
    | LETF (x, xlist, e1, e2) ->
      let env' = (Env.bind env x (Proc(xlist, e1, env))) in
      (eval mem env' e2)
    | CALLV (f, explist) ->
      let (xlist, e1, env') = (lookup_env_proc env f) in
      if(not ((List.length xlist) = (List.length explist)))
      then raise (Error "InvalidArg")
      else (
        let rec getMn mem' env' expl =
          (match expl with
          | head' :: tail' ->
            let (v, mem'') = (eval mem' env' head') in
            let (vallist, mem''') = (getMn mem'' env' tail') in
            (v::vallist, mem''')
            | [] -> ([], mem')
            ) in

            let (vall, mem') = (getMn mem env explist) in

        let rec bind xlist' vallist envl meml = 
          (match xlist' with
          | head'::tail' ->
            let (l, meml') = Mem.alloc meml in
            let meml'' = (Mem.store meml' l (List.hd vallist)) in
            let envl' = (Env.bind envl head' (Addr(l))) in
            (bind tail' (List.tl vallist) envl' meml'')
          | [] -> (envl,meml)
          ) in
        
        let (env'', mem'') = (bind xlist vall env' mem') in
        let env''' = (Env.bind env'' f (Proc(xlist, e1, env'))) in
        (eval mem'' env''' e1)
      )
    | CALLR (f, ylist) ->
      let (xlist, e1, env') = (lookup_env_proc env f) in
      if(not ((List.length xlist) = (List.length ylist)))
      then raise (Error "InvalidArg")
      else (
        let rec bind xlist ylist envl =
          (match xlist with
          | head::tail ->
            let sigy = Env.lookup envl (List.hd ylist) in
            let env' = Env.bind envl head sigy in
            (bind tail (List.tl ylist) env')
          | [] -> envl 
          )in
        let env'' = bind xlist ylist env in
        let env''' = (Env.bind env'' f (Proc(xlist, e1, env'))) in
        (eval mem env''' e1)
      )
    | RECORD idexlist ->
      (match idexlist with
      | h::d ->
        let rec calcexp idexlistl meml envl =
          (match idexlistl with
          | head::tail ->
            let (vall,meml') = (eval meml envl (snd head))in
            let (idexlistl', meml'') = (calcexp tail meml' envl)in
            ((fst head,vall)::idexlistl', meml'')
          | []-> ([], meml)
          )in

        let (idvallist, mem') = calcexp idexlist mem env in

        let rec storeNbind idvallistl meml envl = 
          (match idvallistl with
          | head :: tail ->
            let (l, meml') = Mem.alloc meml in
            let meml'' = Mem.store meml' l (snd head) in
            let envl' = Env.bind envl (fst head) (Addr l) in
            (match tail with
            | head' :: tail' -> 
              let (record, meml''', envl'') = storeNbind tail meml'' envl' in
              let record' = (fun x -> if x = (fst head) then l else record x) in
              (record', meml''', envl'')
            | [] ->
            (
              (fun x -> if x = (fst head) then l else raise (Error "Unbound")), meml'', envl')
            )
            | [] -> raise (Error "empty list error")
          ) in
        let (record, mem'', env') = storeNbind idvallist mem' env in
   
        ((Record(record)), mem'')
      | [] -> (Unit, mem)
      )
    | FIELD (e, x) ->
      let (r, mem') = (eval mem env e)in
      let loc = ((value_record r) x) in
      ((Mem.load mem' loc), mem')
    | ASSIGNF (e1, x, e2) ->
      let (r, mem') = (eval mem env e1)in
      let (v, mem'') = (eval mem' env e2)in
      let loc = ((value_record r) x) in
      (v, (Mem.store mem'' loc v))
  let run (mem, env, pgm) = 
    let (v, _ ) = eval mem env pgm in
    v
end
