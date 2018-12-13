(*
 * SNU 4190.310 Programming Languages 
 * Homework "Exceptions are sugar" Skeleton
 *)

open Xexp

(* TODO : Implement this function *)

let rec removeExn' e = 
  match e with
  | Num n -> Fn(k, Fn(h, App(k, Num n)))
  | Var x -> Fn(k, Fn(h, App(k, Var n)))
  | Fn (x, exp) -> Fn(k, Fn(h, App(k, Fn(x, removeExn' exp))))
  | App (exp1, exp2) -> 
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
    Fn(k, 
      Fn(h,
        App(
          App(removeExn' exp1, 
            Var k
          ),
          Fn(v,
            If(Var v, App(App(removeExn' exp2, Var k), Var h),App(Var h, Var v))
          )
        )
      )
    )
  

let removeExn : xexp -> xexp = fun e ->
  App(App(removeExn' e, Fn(x, Var x)), Fn(x, Var x))
