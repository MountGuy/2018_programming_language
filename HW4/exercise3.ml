type require = id * (cond list)
and cond
  = Items of gift list 
  | Same of id
  | Common of cond * cond
  | Except of cond * gift list
and gift = int
and id = A | B | C | D | E

let rec commonSet : 'a list -> 'a list -> 'a list = fun list1 list2 ->
  match list1 with
  | [] -> list2
  | head :: tail ->
    let list' = (commonSet tail list2) in
    if(List.mem head list') then list' else head :: list'

let rec intersection : 'a list -> 'a list -> 'a list = fun list1 list2 ->
  match list1 with
  | [] -> []
  | head :: tail ->
    if(List.mem head list2) then head :: (intersection tail list2) else (intersection tail list2)

let rec diffSet : 'a list-> 'a list -> 'a list = fun list1 list2 -> 
  match list1 with
  | [] -> []
  | head :: tail -> 
    if(List.mem head list2) then (diffSet tail list2) else head :: (diffSet tail list2)

let getGiftsById : id -> (id * gift list) list -> gift list = fun id giftsList ->
  let (_, result) = List.find (fun (id',gifts') -> id' = id) giftsList in
  result

let rec computeCond : cond -> (id * gift list) list -> gift list = fun cond giftsList ->
  match cond with
  | Items gifts -> gifts
  | Same id -> getGiftsById id giftsList
  | Common (cond1, cond2) -> intersection (computeCond cond1 giftsList) (computeCond cond2 giftsList)
  | Except (cond, gifts) -> diffSet (computeCond cond giftsList) gifts

let rec computeRequire : require -> (id * gift list) list -> (id * gift list) = fun requ giftsList ->
  let (id, requires) = requ in
  match requires with
  | [] -> (id, [])
  | head :: tail ->
    let giftListOfHead = (computeCond head giftsList) in
    let (_,giftListOfTail) = (computeRequire (id, tail) giftsList) in
    (id, (commonSet giftListOfHead giftListOfTail))

let rec computeWholeList : require list -> (id * gift list) list -> (id * gift list) list = fun reqlist giftslist ->
  match reqlist with
  | [] -> []
  | head :: tail -> 
    (computeRequire head giftslist) :: (computeWholeList tail giftslist)

let rec giftsSize : (id * gift list) list -> int = fun giftslist ->
  match giftslist with
  | [] -> 0
  | head :: tail ->
    let (_, gifts) = head in
    (List.length gifts) + (giftsSize tail)

let rec computeList : require list -> (id * gift list) list -> (id * gift list) list = fun reqlist giftslist ->
  let giftslist' = computeWholeList reqlist giftslist in
  if((giftsSize giftslist) != (giftsSize giftslist')) then computeList reqlist giftslist' else giftslist

let rec sortGiftList : (id * gift list) list -> (id * gift list) list = fun giftslist ->
  match giftslist with
  | [] -> []
  | (id, gifts) :: tail -> (id, List.sort (fun x y -> x-y) gifts) :: (sortGiftList tail)

let rec searchInRequireList : require list -> id -> require = fun reqlist id ->
  let result = List.filter (fun (x,y) -> x=id) reqlist in
  if(result = []) then (id, []) else List.hd result

let shoppingList : require list -> (id * gift list) list = fun reqlist ->
  let reqlist' = [searchInRequireList reqlist A;
                  searchInRequireList reqlist B;
                  searchInRequireList reqlist C;
                  searchInRequireList reqlist D;
                  searchInRequireList reqlist E;] in
  let rawList = computeList reqlist' [(A, []);(B, []);(C, []);(D, []);(E, [])] in
  sortGiftList rawList