type team = Korea | France | Usa | Brazil | Japan | Nigeria | Cameroon | Poland | Portugal | Italy | Germany | Norway | Sweden | England | Argentina

type tourna = LEAF of team | NODE of tourna * tourna

let mapping : team -> string = fun ateam ->
        match ateam with
        |Korea -> "Korea"
        |France -> "France"
        |Usa -> "Usa"
        |Brazil -> "Brazil"
        |Japan -> "Japan"
        |Nigeria -> "Nigeria"
        |Cameroon -> "Cameroon"
        |Poland -> "Poland"
        |Portugal -> "Portugal"
        |Italy -> "Italy"
        |Germany -> "Germany"
        |Norway -> "Norway"
        |Sweden -> "Sweden"
        |England -> "England"
        |Argentina -> "Argentina"

let rec parenize : tourna -> string = fun tour ->
        match tour with
        |LEAF i -> mapping(i)
        |NODE (tour1, tour2) -> "(" ^ parenize(tour1) ^ " " ^ parenize(tour2) ^ ")"
