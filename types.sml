(* task1 : ('a -> 'b) -> 'a -> 'b *)
fun task1 f a = f a

(* task2 : ('a -> bool) -> 'a -> ('a -> 'b) -> (unit -> 'b) -> 'b *)
fun task2 f a sc fc = 
        if f a then sc a
        else fc ()


(* task3 : ('a -> 'b) -> 'a list -> ('b list -> 'c) -> 'c *)
fun task3 f [] c = c []
 |  task3 f (x::xs) c = task3 f xs (fn L => c (f x :: L))


