type exp = X | INT of int | REAL of float | ADD of exp * exp | SUB of exp * exp | MUL of exp * exp | DIV of exp * exp | SIGMA of exp * exp * exp | INTEGRAL of exp * exp * exp

exception FreeVariable

let rec sigma: (float -> float)*int*int -> float = fun(f,a,b) ->
        if(a > b) then 0.0
        else sigma(f,a,b-1) +. f(float_of_int b)

let rec integral: (float -> float)*float*float -> float = fun(f,a,b) ->
        if(a > b) then -1.0 *. integral(f,b,a)
        else if(b -. a < 0.1) then 0.0
        else 0.1 *. f(a) +. integral(f,a+.0.1,b)


let rec f_x: exp -> (float -> float) = fun(expr) ->
        match expr with
        |X -> (fun x -> x)
        |INT i -> (fun x -> float_of_int(i))
        |REAL f -> (fun x -> f)
        |ADD (expr1, expr2) -> (fun x -> (f_x(expr1)(x) +. f_x(expr2)(x)))
        |SUB (expr1, expr2) -> (fun x -> (f_x(expr1)(x) -. f_x(expr2)(x)))
        |MUL (expr1, expr2) -> (fun x -> (f_x(expr1)(x) *. f_x(expr2)(x)))
        |DIV (expr1, expr2) -> (fun x -> (f_x(expr1)(x) /. f_x(expr2)(x)))
        |SIGMA (expr1, expr2, expr3) -> (fun x -> sigma(f_x(expr3),int_of_float(f_x(expr1)(1.0)), int_of_float(f_x(expr2)(2.0))))
        |INTEGRAL (expr1, expr2, expr3) -> (fun x -> integral(f_x(expr3), f_x(expr1)(1.0), f_x(expr2)(1.0)))

let rec calculate: exp -> float = fun(expr) ->
        match expr with
        |X -> raise FreeVariable
        |INT i -> float_of_int (i)
        |REAL f -> f
        |ADD (expr1, expr2) -> calculate(expr1) +. calculate(expr2)
        |SUB (expr1, expr2) -> calculate(expr1) -. calculate(expr2)
        |MUL (expr1, expr2) -> calculate(expr1) *. calculate(expr2)
        |DIV (expr1, expr2) -> calculate(expr1) /. calculate(expr2)
        |SIGMA (expr1, expr2, expr3) -> sigma(f_x(expr3), int_of_float(calculate(expr1)), int_of_float(calculate(expr2)))
        |INTEGRAL (expr1, expr2, expr3) -> integral(f_x(expr3), calculate(expr1), calculate(expr2))




