(* sum : int list -> int
 * REQUIRES: true
 * ENSURES: sum [x1, ..., xn] = x1 + ... + xn
 *)
val sum : int list -> int = foldr op+ 0


(* won'tStarve :
 *   int ->
 *   int ->
 *   int list ->
 *   (int list list -> 'a) ->
 *   (unit -> 'a) ->
 *   'a
 * REQUIRES: pots >= 0 and time >= 0 and for all x in curries, x > 0
 * ENSURES: won'tStarve pots time curries sc fc ==>
 *  sc D if there exists D such that concat D is a permutation of curries
 *  and length D = pots and for all d in D, sum d <= time.
 *  fc () otherwise.
 *)
(* 
fun intlistconcat ([]:int list list) : int list = []
 |  intlistconcat ([]::ys) = intlistconcat(ys)
 |  intlistconcat ((x::xs)::ys) = x::(intlistconcat(xs::ys))

fun findmax ([] : int list) (acc : int) : int = acc
 |  findmax (x::xs) acc = if x > acc then findmax xs x else findmax xs acc


fun cancelelement (x : int, done : int list, [] : int list) : int list = []
|   cancelelement (x, done, n::ns) = 
    if n = x then done@ns
    else cancelelement (x, done@[n], ns)

fun cancelapply ([] : int list list, x : int) : int list list= []
 |  cancelapply ((n::ns), x) = cancelelement (x, [], n) :: cancelapply(ns, x)

fun findsublists ([] : int list, acc : int list list) : int list list = acc
  | findsublists (x::xs, []) =  findsublists(xs, (x::xs)::[xs])
  | findsublists (x::xs, acc) =  findsublists(xs, acc@cancelapply(acc,x))

fun findx ([] : int list) (a : int) : bool = false
 |  findx (x::xs) a = if a = x then true else findx xs a

fun partitionsuccess ([] : int list) ([] : int list) : bool = true
 |  partitionsuccess curries [] = true
 |  partitionsuccess curries (x::xs) = if findx curries x then partitionsuccess curries xs else false *)
(* 
fun won'tStarve
  (pots : int)
  (time : int)
  (curries : int list)
  (sc : int list list -> 'a)
  (fc : unit -> 'a)
  : 'a = let 
           fun pL L scL fcL = if (length L = pots) andalso ((length (intlistconcat L)) = (length curries)) andalso (partitionsuccess (intlistconcat L) curries) andalso ((findmax (map sum L) 0) <= time) then scL L else fcL ()
           fun pR R scR fcR = scR ()
           fun scn (LJ, ()) = sc LJ
           val A = findsublists (curries, [])
          in 
            findPartition A pL pR scn fc
          end *)

  fun won'tStarve
  (0 : int)
  (time : int)
  ([] : int list)
  (sc : int list list -> 'a)
  (fc : unit -> 'a)
  : 'a = sc []
  | won'tStarve
  (pots : int)
  (time : int)
  ([] : int list)
  (sc : int list list -> 'a)
  (fc : unit -> 'a)
  : 'a = won'tStarve (pots-1) time  [] (fn reslist => sc ([]::reslist)) fc
  | won'tStarve
  (0 : int)
  (time : int)
  (curries : int list)
  (sc : int list list -> 'a)
  (fc : unit -> 'a)
  : 'a = fc ()
  | won'tStarve
  (pots : int)
  (time : int)
  (curries : int list)
  (sc : int list list -> 'a)
  (fc : unit -> 'a)
  : 'a = let 
          fun pL L scL fcL = if sum L <= time then scL L else fcL ()
          fun scn (L, R) =  sc (L::R)
          fun pR R scR fcR = won'tStarve (pots-1) time R (fn reslist => scR reslist) fcR
         in 
          findPartition curries pL pR scn fc 
         end 

(* (more than one possible answer here) *)
val sc = SOME
val fc = fn () => NONE
(* val SOME [[10, 40], [20], [30]] = won'tStarve 3 50 [10, 20, 30, 40] sc fc *)
val NONE = won'tStarve 2 40 [20, 20, 30, 40] sc fc
(* val SOME [[40],[20,20],[20]] = won'tStarve 3 40 [20, 20, 20, 40] sc fc *)
(* val SOME [[40],[20,20],[20]] = won'tStarve 3 50 [20, 20, 20, 40] sc fc *)
val NONE = won'tStarve 2 50 [20, 20, 20, 40] sc fc
val SOME [[20,30,40],[60],[]] = won'tStarve 3 90 [20, 30, 60, 40] sc fc
val NONE = won'tStarve 0 90 [20, 30, 60, 40] sc fc





val sc = SOME
val fc = fn () => NONE
val SOME [[10,20],[30],[40]] = won'tStarve 3 50 [10, 20, 30, 40] sc fc
val NONE = won'tStarve 2 40 [20, 20, 30, 40] sc fc
val SOME [[10],[],[]] = won'tStarve 3 50 [10] sc fc
val SOME [[10,30,70,5],[110],[20,40],[80],[],[]] = won'tStarve 6 120 [10,30,70,5,110,20,40,80] sc fc
val NONE = won'tStarve 0 25 [1] sc fc
val NONE = won'tStarve 4 100 [30,50,70,99,1,0,0,0,12,110] sc fc
val SOME [] = won'tStarve 0 0 [] sc fc
val SOME [] = won'tStarve 0 10 [] sc fc
val SOME [[0,0,0,0,0,0,0,0,0,0],[],[],[],[]] = won'tStarve 5 0 [0,0,0,0,0,0,0,0,0,0] sc fc
val SOME [[8800,12,20,1,0,0],[],[],[],[],[],[]] = won'tStarve 7 8848 [8800,12,20,1,0,0] sc fc
val SOME [[8848]] = won'tStarve 1 8848 [8848] sc fc

fun sc a = a
fun fc () = []
val [[50],[50],[50],[50]] = won'tStarve 4 50 [50,50,50,50] sc fc
val [[20,30],[50],[50],[50]] = won'tStarve 4 50 [20,30,50,50,50] sc fc
val [] = won'tStarve 5 50 [30,30,30,30,30,30] sc fc
val [] = won'tStarve 5 40 [20,20,20,20,30,30,30,30,30,30] sc fc
val [[99],[]] = won'tStarve 2 100 [99] sc fc
val [] = won'tStarve 0 50 [100] sc fc
val [] = won'tStarve 100 0 [1,1,1,1,1] sc fc
val [] = won'tStarve 0 0 [] sc fc
val [[1]] = won'tStarve 1 100 [1] sc fc


