let rec sigma : int*int*(int->float)->float = fun(a,b,f) -> 
        if(a > b) then 0.0
        else f(b) +. sigma(a, (b-1), f)

let rec prod : (int*int -> float)*int*int -> float = fun(m,i,k) ->
        if(k < 1) then 1.0
        else m(i,k)*.prod(m,i,k-1)

let rec sumprod : (int*int->float)*int*int -> float = fun(m,n,k) ->
        sigma(1,n,fun i -> prod(m,i,k))

