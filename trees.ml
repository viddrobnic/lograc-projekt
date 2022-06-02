type 'a tree =
    | Empty
    | Node2 of 'a tree * 'a * 'a tree
    | Node3 of 'a tree * 'a * 'a tree * 'a * 'a tree

let insert t (k, v) =
    let rec insert_aux t (k, v) = 
    match t with
        | Empty -> Node2(Empty, (k, v), Empty), true
        | Node2(l, (k', v'), r) ->
            if k < k' then
                match insert_aux l (k, v) with
                    | Node2(l', a, r'), true -> Node3(l', a, r', (k', v'), r), false
                    | Node2(l', a, r'), false -> Node2(Node2(l', a, r'), (k', v'), r), false
                    | Node3(l', a, m', b, r'), _ -> Node2(Node3(l', a, m', b, r'), (k', v'), r), false
                    | Empty, _ -> failwith "got empty after insert2 left"
            else if k > k' then
                match insert_aux r (k, v) with
                    | Node2(l', a, r'), true -> Node3(l, (k', v'), l', a, r'), false
                    | Node2(l', a, r'), false -> Node2(l, (k', v'), Node2(l', a, r')), false
                    | Node3(l', a, m', b, r'), _ -> Node2(l, (k', v'), Node3(l', a, m', b, r')), false
                    | Empty, _ -> failwith "got empty after insert2 right"
            else Node2(l, (k', v), r), false
        | Node3(l, (k', v'), m, (k'', v''), r) ->
            if k < k' then
                match insert_aux l (k, v) with
                    | Node2(l', a, r'), true -> Node2(Node2(l', a, r'), (k', v'), Node2(m, (k'', v''), r)), true
                    | Node2(l', a, r'), false -> Node3(Node2(l', a, r'), (k', v'), m, (k'', v''), r), false
                    | Node3(l', a, m', b, r'), _ -> Node3(Node3(l', a ,m', b, r'), (k', v'), m, (k'', v''), r), false
                    | Empty, _ -> failwith "got empty after insert3 left"
            else if k > k' && k < k'' then
                match insert_aux m (k, v) with
                    | Node2(l', a, r'), true -> Node2(Node2(l, (k', v'), l'), a, Node2(r', (k'', v''), r)), true
                    | Node2(l', a, r'), false -> Node3(l, (k', v'), Node2(l', a, r'), (k'', v''), r), false
                    | Node3(l', a, m', b, r'), _ -> Node3(l, (k', v'), Node3(l', a, m', b, r'), (k'', v''), r), false
                    | Empty, _ -> failwith "got empty after insert3 middle"
            else if k > k'' then
                match insert_aux r (k, v) with
                    | Node2(l', a, r'), true -> Node2(Node2(l, (k', v'), m), (k'', v''), Node2(l', a, r')), true
                    | Node2(l', a, r'), false -> Node3(l, (k', v'), m, (k'', v''), Node2(l', a, r')), false
                    | Node3(l', a, m', b, r'), _ -> Node3(l, (k', v'), m, (k'', v''), Node3(l', a, m', b, r')), false
                    | Empty, _-> failwith "got empty after insert3 right"
            else if k = k' then
                Node3(l, (k', v), m, (k'', v''), r), false
            else if k = k'' then
                Node3(l, (k', v'), m, (k'', v), r), false
            else failwith "got an unexpected condition in insert"
    in 
    let t2, _ = insert_aux t (k, v) in t2

let rec search t k =
    match t with
        | Empty -> None
        | Node2(l, (k', v'), r) ->
            if k < k' then 
                search l k
            else if k > k' then
                search r k
            else Some v'
        | Node3(l, (k', v'), m, (k'', v''), r) -> 
            if k < k' then search l k
            else if k > k' && k < k'' then search m k
            else if k > k'' then search r k
            else if k = k' then Some v'
            else if k = k'' then Some v''
            else failwith "got an unexpected contidion in search"


let rec height = function
    | Empty -> 0
    | Node2(l, _, r) -> 1 + Int.max (height l) (height r)
    | Node3(l, _, m, _, r) -> 1 + Int.max (Int.max (height l) (height r)) (height m)

let rec uravnotezeno = function
    | Empty -> true
    | Node2(l, _, r) -> uravnotezeno l && uravnotezeno r && height l = height r
    | Node3(l, _, m, _, r) -> uravnotezeno l && uravnotezeno m && uravnotezeno r && height l = height m && height m = height r

let t = Empty
let _ = assert (height t = 0)
let _ = assert (uravnotezeno t)

let t = insert t (1, 1)
let _ = assert (height t = 1)
let _ = assert ((search t 1) = (Some 1))
let _ = assert (uravnotezeno t)

let t = insert t (2, 2)
let _ = assert (height t = 1)
let _ = assert ((search t 1) = (Some 1))
let _ = assert ((search t 2) = (Some 2))
let _ = assert (uravnotezeno t)

let t = insert t (3, 3)
let _ = assert ((search t 3) = (Some 3))
let _ = assert (uravnotezeno t)

let t = insert t (4, 3)
let _ = assert ((search t 4) = (Some 3))
let _ = assert (uravnotezeno t)

let t = insert t (5, 3)
let _ = assert ((search t 5) = (Some 3))
let _ = assert (uravnotezeno t)

let t = insert t (6, 3)
let _ = assert ((search t 6) = (Some 3))
let _ = assert (uravnotezeno t)

let t = insert t (7, 3)
let _ = assert ((search t 7) = (Some 3))
let _ = assert (uravnotezeno t)

let t = insert t (8, 3)
let _ = assert ((search t 8) = (Some 3))
let _ = assert (uravnotezeno t)

let t = insert t (9, 3)
let _ = assert ((search t 9) = (Some 3))
let _ = assert (uravnotezeno t)

let t = insert t (10, 3)
let _ = assert ((search t 10) = (Some 3))
let _ = assert (uravnotezeno t)