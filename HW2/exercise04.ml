module type Queue = 
        sig
                type element
                type queue
                exception EMPTY_Q
                val emptyQ: queue
                val enQ: queue * element -> queue
                val deQ: queue -> element * queue
        end

module IntListQ =
        struct
                type element = int list
                
                type queue = (element list) * (element list)
                
                exception EMPTY_Q
                
                let rec reverse_list: (element list) -> (element list) = fun(lst)->
                        match lst with
                        |[] -> []
                        |head::tail -> reverse_list(tail)@[head]
                
                let emptyQ: queue = ([],[])
                
                let enQ: queue * element -> queue = fun(que, elm) -> (elm::(fst que), snd que)
                
                let rec deQ: queue -> (element * queue) = fun(que) ->
                        match snd que with
                        |head::tail -> (head, (fst que, tail))
                        |[] ->
                                        (match fst que with
                                        |head::tail -> deQ(([],reverse_list (fst que)))
                                        |[] -> raise EMPTY_Q)
        end


module ValidintListQ = (IntListQ:Queue)
