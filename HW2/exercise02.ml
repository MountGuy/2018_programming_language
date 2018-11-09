type ae = CONST of int | VAR of string | POWER of string*int | TIMES of ae list | SUM of ae list

exception InvalidArgument

let rec diff: ae * string -> ae = fun(alexp, var) ->
        match alexp with
        |CONST i -> (CONST(0))
        |VAR var1 -> if(var = var1) then (CONST(1))
                        else (CONST(0))
        |POWER (var1, i) -> if(var = var1) then TIMES [CONST i; POWER(var1, i-1)]
                                            else (CONST (0))
        |TIMES list1 ->
                        (match list1 with
                        |head :: tail -> if(tail == []) then diff(head, var)
                                            else SUM([TIMES[diff(head, var); (TIMES tail)]; TIMES[head; diff((TIMES tail), var)]])
                        |[] -> raise InvalidArgument)

        |SUM list2 ->
                        (match list2 with
                        |head :: tail -> if(tail == []) then diff(head, var)
                                            else SUM([diff(head, var); diff((SUM tail), var)])
                        |[] -> raise InvalidArgument)

