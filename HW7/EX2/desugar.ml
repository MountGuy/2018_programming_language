(*
 * SNU 4190.310 Programming Languages 
 * Homework "Exceptions are sugar" Skeleton
 *)

open Xexp

(* TODO : Implement this function *)

let count = ref 0

let new_var () = 
  let _ = count := !count + 1 in
  "x_" ^ (string_of_int !count)


let rec alpha_conv e subs =
  match e with
  | Num n -> Num n
  | Var x -> (try Var (List.assoc x subs) with Not_found -> Var x)
  | Fn (x, exp) ->
      let v = new_var () in
      Fn (v, alpha_conv exp ((x, v)::subs))
  | App (exp1, exp2) -> App (alpha_conv exp1 subs, alpha_conv exp2 subs)
  | If (exp1, exp2, exp3) -> If (alpha_conv exp1 subs, alpha_conv exp2 subs, alpha_conv exp3 subs)
  | Equal (exp1, exp2) -> Equal (alpha_conv exp1 subs, alpha_conv exp2 subs)
  | Raise exp -> Raise (alpha_conv exp subs)
  | Handle (exp1, n, exp2) -> Handle (alpha_conv exp1 subs, n, alpha_conv exp2 subs)

let rec removeExn' e =
  let k = new_var() in
  let h = new_var() in
  match e with
  | Num n -> Fn(k, Fn(h, App(Var k, Num n)))
  | Var x -> Fn(k, Fn(h, App(Var k, Var x)))
  | Fn (x, exp) -> Fn(k, Fn(h, App(Var k, Fn(x, removeExn' exp))))
  | App (exp1, exp2) ->
    let f = new_var() in
    let v = new_var() in
    Fn(k, 
      Fn(h,
        App(
          App(removeExn' exp1, 
            Fn(f,
              App(
                App(removeExn' exp2,
                  Fn(v,
                    App(
                      App(
                        App(Var f, Var v), 
                      Var k
                      ),
                      Var h
                    )
                  )
                ),
                Var h
              )
            )
          ),
          Var h
        )
      )
    )
  | If (exp1, exp2, exp3) ->
    let v = new_var() in
    Fn(k, 
      Fn(h,
        App(
          App(removeExn' exp1, 
            Fn(v, If(Var v, App(App(removeExn' exp2, Var k), Var h), App(App(removeExn' exp3, Var k), Var h))
            )
          ),
          Var h
        )
      )
    )
  | Equal (exp1, exp2) ->
    let v1 = new_var() in
    let v2 = new_var() in
    Fn(k, 
      Fn(h,
        App(
          App(removeExn' exp1, 
            Fn(v1,
              App(
                App(removeExn' exp2,
                  Fn(v2, App(Var k, Equal(Var v1, Var v2)))
                ),
                Var h
              )
            )
          ),
          Var h
        )
      )
    )
  | Raise exp ->  Fn(k, Fn(h, App(App(removeExn' exp, Var h), Var h)))
  | Handle (exp1, n, exp2) ->
    let v = new_var() in
    Fn(k, 
      Fn(h,
        App(
          App(removeExn' exp1, 
            Var k
          ),
          Fn(v,
            If(
              Equal(
                Var v, Num n
              ), 
              App(
                App(removeExn' exp2, Var k), Var h
              ),
              App(
                Var h, Var v
              )
            )
          )
        )
      )
    )
  

let removeExn : xexp -> xexp = fun e ->
  let x = new_var() in
  App(App(removeExn' (alpha_conv e []), Fn(x, Var x)), Fn(x, Num 201812))
