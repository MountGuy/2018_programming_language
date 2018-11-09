let rec sigma :  int*int*(int->int) -> int = fun(a,b,f) ->
        if(a > b) then 0
        else sigma(a,b-1,f) + f(b)
