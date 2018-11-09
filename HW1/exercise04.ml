type expr = NUM of int | PLUS of expr * expr | MINUS of expr * expr

type formula = TRUE | FALSE | NOT of formula | ANDALSO of formula * formula | ORELSE of formula * formula | IMPLY of formula * formula | LESS of expr * expr

let rec int_of_expr : expr -> int = fun exp->
        match exp with
        |NUM i -> i
        |PLUS (i, j) -> (int_of_expr i) + (int_of_expr j)
        |MINUS (i, j) -> (int_of_expr i) - (int_of_expr j)

let rec eval : formula -> bool = fun form ->
        match form with
        |TRUE -> true
        |FALSE -> false
        |NOT form1 -> not(eval form1)
        |ANDALSO (form1, form2) -> (eval form1) && (eval form2)
        |ORELSE (form1, form2) -> (eval form1) || (eval form2)
        |IMPLY (form1, form2) -> not((eval form1) && (not(eval form2)))
        |LESS (exp1, exp2) -> (int_of_expr exp1) < (int_of_expr exp2)

