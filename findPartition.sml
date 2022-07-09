(* findPartitionV1 :
 *  'e list ->
 *  ('e list -> 'l option) ->
 *  ('e list -> 'r option) ->
 *  ('l * 'r) option
 * REQUIRES: pL and pR are total
 * ENSURES: findPartitionV1 A pL pR ==>*
 *  SOME (evL, evR) if there exists a partition (L, R) of A
 *  such that pL accepts L with evL and pR accepts R with evR.
 *  NONE otherwise.
 *)


fun findPartitionHelper ([] : 'e list) (pL : 'e list -> 'l option) (pR : 'e list -> 'r option) (done : 'e list) (acc : 'e list) : ('l * 'r) option = 
                        (case (pL (done@[]), pR acc) of
                        (SOME L, SOME R) => SOME (L, R)
                      | (_, _) => NONE)
  | findPartitionHelper (x::xs) pL pR done acc = 
                        (case (pL (done@(x::xs)), pR acc) of
                        (SOME L, SOME R) => SOME (L, R)
                      | (_, _) => (case findPartitionHelper xs pL pR (done@[x]) acc of 
                                    SOME (L2, R2) => SOME (L2, R2)
                                  | NONE => findPartitionHelper xs pL pR done (acc@[x])))

fun findPartitionV1 (A : 'e list) (pL : 'e list -> 'l option) (pR : 'e list -> 'r option) : ('l * 'r) option = findPartitionHelper A pL pR [] []
                     
(* test cases: *)
val sum : int list -> int = foldr op+ 0
fun subsetSumV1 ( n : int) ( xs : int list ) : int list option =
    let
        val pL = fn L => if sum L = n then SOME L else NONE
        val pR = fn R => SOME R
        val res = findPartitionV1 xs pL pR
        fun extractL ( SOME ( partL , partR ) ) = SOME partL
          | extractL NONE = NONE
    in
        extractL res
    end

val SOME[1,2,3,4] = subsetSumV1 10 ([1,2,3,4])
val SOME[2,3,4] = subsetSumV1 9 [1,2,3,4]
(* val SOME[2,4] = subsetSumV1 6 [1,2,3,4] => it = SOME [1,2,3]*)
(* val SOME[3,4] = subsetSumV1 7 [1,2,3,4] => it = SOME [1,2,4]*)
val SOME[] = subsetSumV1 0 [1,2,3,4]
(* val SOME[3,1,2] = subsetSumV1 6 [1,3,1,2] => it = SOME [1,3,2]*)
val SOME[0,80] = subsetSumV1 80 [0,80]
(* val SOME [80] = subsetSumV1 80 [1,2,11,80,0,5,6,7,8,9,10] => it = SOME [80,0] *)
val SOME [1,80] = subsetSumV1 81 [1,2,11,80,10,20]
(* val SOME [3,2,3,2] = subsetSumV1 10 [2,3,2,3,2] =>  it = SOME [2,3,2,3] *)
(* val SOME [1,1,10,2] = subsetSumV1 14 [1,1,2,1,10,2] => it = SOME [1,1,2,10] *)
val SOME [1,10] = subsetSumV1 11 [1,1,2,1,10,2]
val SOME [] = subsetSumV1 0 [1,2,3,100]
val SOME [] = subsetSumV1 0 []
val NONE = subsetSumV1 1000000 [1,2,3,4,5,6,7,7,100]
val NONE = subsetSumV1 99 [1,2,3,4,5,6,7,7,100]
(* val SOME [4,7,7] = subsetSumV1 18 [1,2,3,4,5,6,7,7,100] => it = SOME [1,2,3,5,7] *)





val SOME [] = subsetSumV1 0 []
val SOME [] = subsetSumV1 0 [1,5,7,2,7,14,8848]
val SOME [1,8848] = subsetSumV1 8849 [1,5,7,2,7,14,8848]
val SOME [1,5,7,7] = subsetSumV1 20 [1,5,7,2,7,14,8848]
val NONE = subsetSumV1 ~1 [1,5,7,2,7,14,8848]
val SOME [0] = subsetSumV1 0 [1,5,7,0,2,7,14,8848]
val SOME [0,~12] = subsetSumV1 ~12 [0,12,~12,15,~8,122,150,210,~251]
val SOME [0,0,0,0,0,0,0,0,0,122,~122,150,~150,210,~210,213,~213,251,~251] = subsetSumV1 0 [0,0,0,0,0,0,0,0,0,122,  ~122,150,~150,210,~210,213,~213,251,~251]
val SOME [18100,~18100] = subsetSumV1 0
[15251,~15316,~10701,18100,11785,18240,~21355,~18100]
val NONE = subsetSumV1 8848
  [15251,~15316,~10701,18100,11785,18240,~21355,~18100]

val SOME [] = subsetSumV1 0 []
val NONE = subsetSumV1 1 []
val SOME [1] = subsetSumV1 1 [1]
val SOME [1,1] = subsetSumV1 2 [1,1]
val SOME [1,2] = subsetSumV1 3 [1,2,1]
val SOME [2,1] = subsetSumV1 3 [5,2,1]
val SOME [] = subsetSumV1 0 []
val NONE = subsetSumV1 1 []
val SOME [1] = subsetSumV1 1 [1]
val SOME([4, 7, 8]) = subsetSumV1 19 [~98, 4, 1, 7, 8]

(* findPartitionV2 :
 *  'e list ->
 *  ('e list -> 'l option) ->
 *  ('e list -> 'r option) ->
 *  ('l * 'r -> 'a) ->
 *  (unit -> 'a) ->
 *  'a
 * REQUIRES: pL and pR are total
 * ENSURES: findPartitionV2 A pL pR sc fc ==>*
 *  sc (evL, evR) if there exists a partition (L, R) of A
 *  such that pL accepts L with evL and pR accepts R with evR.
 *  fc () otherwise.
 *)
(* fun findPartitionV2Helper ([] : 'e list) (pL : 'e list -> 'l option) (pR : 'e list -> 'r option) (sc : 'l * 'r -> 'a) (fc : unit -> 'a) (done : 'e list) (acc : 'e list) : 'a = 
                          (case (pL (done), pR acc) of
                        (SOME L, SOME R) => sc (L, R)
                      | (_, _) => fc ())
 |  findPartitionV2Helper (x::xs) pL pR sc fc done acc =  findPartitionV2Helper xs pL pR (fn (L, R) => sc (L, R)) (fn () => (findPartitionV2Helper xs pL pR (fn (L, R) => sc (L, R)) fc done (acc@[x]))) (done@[x]) acc (*whether this is cps or not*)
    

fun findPartitionV2 (A : 'e list) (pL : 'e list -> 'l option) (pR : 'e list -> 'r option) (sc : 'l * 'r -> 'a) (fc : unit -> 'a) : 'a = findPartitionV2Helper A pL pR sc fc [] [] *)

fun findPartitionV2 ([] : 'e list) (pL : 'e list -> 'l option) (pR : 'e list -> 'r option) (sc : 'l * 'r -> 'a) (fc : unit -> 'a) : 'a = 
                    (case (pL [], pR []) of
                    (SOME L, SOME R) => sc (L, R)
                 |  _ => fc () )
 |  findPartitionV2 (x::xs) pL pR sc fc = findPartitionV2 xs (fn testlist => pL (x::testlist)) pR (fn (L, R) => sc (L, R)) 
                               (fn () => (findPartitionV2 xs pL (fn testlist => pR (x::testlist)) (fn (L, R) => sc (L, R)) fc))



(* test cases: *)
fun subsetSumV2 ( n : int) ( xs : int list ) : int list option =
  let
    val pL = fn L => if sum L = n then SOME L else NONE
    val pR = fn R => SOME R
    val sc = fn (l , r ) => SOME l
    val fc = fn () => NONE
  in
    findPartitionV2 xs pL pR sc fc
end
(* 
val SOME[1,2,3,4] = subsetSum 10 ([1,2,3,4])
val SOME[2,3,4] = subsetSum 9 [1,2,3,4]
(* val SOME[2,4] = subsetSum 6 [1,2,3,4] => it = SOME [1,2,3]*)
(* val SOME[3,4] = subsetSum 7 [1,2,3,4] => it = SOME [1,2,4]*)
val SOME[] = subsetSum 0 [1,2,3,4]
(* val SOME[3,1,2] = subsetSum 6 [1,3,1,2] => it = SOME [1,3,2]*)
val SOME[0,80] = subsetSum 80 [0,80]
(* val SOME [80] = subsetSum 80 [1,2,11,80,0,5,6,7,8,9,10] => it = SOME [80,0] *)
val SOME [1,80] = subsetSum 81 [1,2,11,80,10,20]
(* val SOME [3,2,3,2] = subsetSum 10 [2,3,2,3,2] =>  it = SOME [2,3,2,3] *)
(* val SOME [1,1,10,2] = subsetSum 14 [1,1,2,1,10,2] => it = SOME [1,1,2,10] *)
val SOME [1,10] = subsetSum 11 [1,1,2,1,10,2]
val SOME [] = subsetSum 0 [1,2,3,100]
val SOME [] = subsetSum 0 []
val NONE = subsetSum 1000000 [1,2,3,4,5,6,7,7,100]
val NONE = subsetSum 99 [1,2,3,4,5,6,7,7,100]
(* val SOME [4,7,7] = subsetSum 18 [1,2,3,4,5,6,7,7,100] => it = SOME [1,2,3,5,7] *)

 *)






val SOME [] = subsetSumV2 0 []
val SOME [] = subsetSumV2 0 [1,5,7,2,7,14,8848]
val SOME [1,8848] = subsetSumV2 8849 [1,5,7,2,7,14,8848]
val SOME [1,5,7,7] = subsetSumV2 20 [1,5,7,2,7,14,8848]
val NONE = subsetSumV2 ~1 [1,5,7,2,7,14,8848]
val SOME [0] = subsetSumV2 0 [1,5,7,0,2,7,14,8848]
val SOME [0,~12] = subsetSumV2 ~12 [0,12,~12,15,~8,122,150,210,~251]
val SOME [0,0,0,0,0,0,0,0,0,122,~122,150,~150,210,~210,213,~213,251,~251] =
  subsetSumV2 0 [0,0,0,0,0,0,0,0,0,122,~122,150,~150,210,~210,213,~213,251,~251]
val SOME [18100,~18100] = subsetSumV2 0
  [15251,~15316,~10701,18100,11785,18240,~21355,~18100]
val NONE = subsetSumV2 8848
    [15251,~15316,~10701,18100,11785,18240,~21355,~18100]

val SOME [] = subsetSumV2 0 []
val NONE = subsetSumV2 1 []
val SOME [1] = subsetSumV2 1 [1]
val SOME [1,1] = subsetSumV2 2 [1,1]
val SOME [1,2] = subsetSumV2 3 [1,2,1]
val SOME [2,1] = subsetSumV2 3 [5,2,1]
val SOME [] = subsetSumV2 0 []
val NONE = subsetSumV2 1 []
val SOME[1, 2, 3] = subsetSumV2 6 [~1, 1, ~5, 2, 3]




val pL = (fn a => if (a=[1,3,5,6]) then SOME 1 else NONE)
val pR = (fn a => if (a=[0,2,4,7,8]) then SOME 2 else NONE)
val NONE = findPartitionV1 [0,1,2,3,4,5,6,7] pL pR
val SOME (1,2) = findPartitionV1 [0,2,4,7,1,3,5,8,6] pL pR


(* findPartition :
 *  'e list ->
 *  ('e list -> ('l -> 'a) -> (unit -> 'a) -> 'a) ->
 *  ('e list -> ('r -> 'a) -> (unit -> 'a) -> 'a) ->
 *  ('l * 'r -> 'a) ->
 *  (unit -> 'a) ->
 *  'a
 * REQUIRES: pL and pR are CPS-total
 * ENSURES: findPartition A pL pR sc fc ==>
 *  sc (evL, evR) if there exists a partition (L, R) of A
 *  such that pL accepts L with evL and pR accepts R with evR.
 *  fc () otherwise.
 *)


(* 
fun findPartitionCPSHelper ([]: 'e list) (pL : 'e list -> ('l -> 'a) -> (unit -> 'a) -> 'a) (pR : 'e list -> ('r -> 'a) -> (unit -> 'a) -> 'a) (sc : 'l * 'r -> 'a) (fc : unit -> 'a) (done : 'e list) (acc : 'e list) : 'a = 
                           pL done (fn L => (pR acc (fn R => sc(L, R)) fc)) fc
  | findPartitionCPSHelper (x::xs) pL pR sc fc done acc =pL (done@(x::xs)) (fn L => (pR acc (fn R => sc (L, R)) (fn () => (findPartitionCPSHelper xs pL pR sc (fn () => findPartitionCPSHelper xs pL pR sc fc done (acc@[x])) (done@[x]) acc) ) ) ) (fn () => (findPartitionCPSHelper xs pL pR sc (fn () => findPartitionCPSHelper xs pL pR sc fc done (acc@[x])) (done@[x]) acc) )



(* pL (done@(x::xs)) (fn L => (pR acc (fn R => sc (L, R)) (fn () => (findPartitionCPSHelper (xs) pL pR sc fc done (acc@[x]))))) (fn () => (findPartitionCPSHelper (xs) pL pR sc fc done (acc@[x]))) *)

fun findPartition (A : 'e list) (pL : 'e list -> ('l -> 'a) -> (unit -> 'a) -> 'a) (pR : 'e list -> ('r -> 'a) -> (unit -> 'a) -> 'a) (sc : 'l * 'r -> 'a) (fc : unit -> 'a) : 'a = findPartitionCPSHelper A pL pR sc fc [] []
 *)

fun findPartition 
([] : 'e list) 
(pL : 'e list -> ('l -> 'a) -> (unit -> 'a) -> 'a) 
(pR : 'e list -> ('r -> 'a) -> (unit -> 'a) -> 'a) 
(sc : 'l * 'r -> 'a) 
(fc : unit -> 'a) : 'a = pL [] (fn L => (pR [] (fn R => sc (L, R)) fc) ) fc  
 | findPartition (x::xs) pL pR sc fc = findPartition xs (fn testlist => pL (x::testlist)) pR (fn (L, R) => sc (L, R))  
                               (fn () => (findPartition xs pL (fn testlist => pR (x::testlist)) (fn (L, R) => sc (L, R)) fc))  



val sum = foldr op+ 0

fun subsetSum (n : int) (xs : int list) : int list option =
  let
    fun pL L scL fcL = if sum L = n then scL L else fcL ()
    fun pR R scR fcR = scR ()
    fun sc (LJ, ()) = SOME LJ
    fun fc () = NONE
  in
    findPartition xs pL pR sc fc
  end

val SOME [] = subsetSum 0 [] 
val NONE = subsetSum 1 [] 
val SOME [1] = subsetSum 1 [1] 
val SOME [1,1] = subsetSum 2 [1,1]
val SOME [1,2] = subsetSum 3 [1,2,1]
val SOME [2,1] = subsetSum 3 [5,2,1]



val SOME[1,2,3,4] = subsetSum 10 ([1,2,3,4])
val SOME[2,3,4] = subsetSum 9 [1,2,3,4]
(* val SOME[2,4] = subsetSum 6 [1,2,3,4] => it = SOME [1,2,3]*)
(* val SOME[3,4] = subsetSum 7 [1,2,3,4] => it = SOME [1,2,4]*)
val SOME[] = subsetSum 0 [1,2,3,4]
(* val SOME[3,1,2] = subsetSum 6 [1,3,1,2] => it = SOME [1,3,2]*)
val SOME[0,80] = subsetSum 80 [0,80]
(* val SOME [80] = subsetSum 80 [1,2,11,80,0,5,6,7,8,9,10] => it = SOME [80,0] *)
val SOME [1,80] = subsetSum 81 [1,2,11,80,10,20]
(* val SOME [3,2,3,2] = subsetSum 10 [2,3,2,3,2] =>  it = SOME [2,3,2,3] *)
(* val SOME [1,1,10,2] = subsetSum 14 [1,1,2,1,10,2] => it = SOME [1,1,2,10] *)
val SOME [1,10] = subsetSum 11 [1,1,2,1,10,2]
val SOME [] = subsetSum 0 [1,2,3,100]
val SOME [] = subsetSum 0 []
val NONE = subsetSum 1000000 [1,2,3,4,5,6,7,7,100]
val NONE = subsetSum 99 [1,2,3,4,5,6,7,7,100]
(* val SOME [4,7,7] = subsetSum 18 [1,2,3,4,5,6,7,7,100] => it = SOME [1,2,3,5,7] *)


val SOME [] = subsetSum 0 []
val NONE = subsetSum 1 []
val SOME [1] = subsetSum 1 [1]
val SOME [1,1] = subsetSum 2 [1,1]
val SOME [1,2] = subsetSum 3 [1,2,1]
val SOME [2,1] = subsetSum 3 [5,2,1]
val SOME [] = subsetSum 0 [1,5,7,2,7,14,8848]
val SOME [1,8848] = subsetSum 8849 [1,5,7,2,7,14,8848]
val SOME [1,5,7,7] = subsetSum 20 [1,5,7,2,7,14,8848]
val NONE = subsetSum ~1 [1,5,7,2,7,14,8848]
val SOME [0] = subsetSum 0 [1,5,7,0,2,7,14,8848]
val SOME [0,~12] = subsetSum ~12 [0,12,~12,15,~8,122,150,210,~251]
val SOME [0,0,0,0,0,0,0,0,0,122,~122,150,~150,210,~210,213,~213,251,~251] = subsetSum 0 [0,0,0,0,0,0,0,0,0,122,    ~122,  150,~150,210,~210,213,~213,251,~251]



val SOME [18100,~18100] = subsetSum 0
[15251,~15316,~10701,18100,11785,18240,~21355,~18100]
val NONE = subsetSum 8848
  [15251,~15316,~10701,18100,11785,18240,~21355,~18100]
val SOME [] = subsetSum 0 []
val NONE = subsetSum 1 []
val SOME [1] = subsetSum 1 [1]
val SOME [1,1] = subsetSum 2 [1,1]
val SOME [1,2] = subsetSum 3 [1,2,1]
val SOME [2,1] = subsetSum 3 [5,2,1]
val SOME [] = subsetSum 0 []
val NONE = subsetSum 1 []