type nat = ZERO | SUCC of nat

let rec natadd : nat*nat -> nat = fun(num1, num2) ->
        match num1 with
        |ZERO -> num2
        |SUCC num3 -> SUCC(natadd(num2, num3))

let rec natmul : nat*nat -> nat = fun(num1, num2) ->
        match num1 with
        |ZERO -> ZERO
        |SUCC num3 -> natadd(num2, natmul(num3, num2))


let rec int_of_nat : nat -> int = fun num1 ->
        match num1 with
        |ZERO -> 0
        |SUCC num2 -> 1 + (int_of_nat num2)

