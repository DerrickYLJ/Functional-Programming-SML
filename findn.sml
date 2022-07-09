datatype 'a shrub = Leaf of 'a
                  | Branch of 'a shrub * 'a shrub

(* findOne : ('a -> bool) -> 'a shrub -> ('a -> 'b) -> (unit -> 'b) -> 'b
 * REQUIRES: p is total
 * ENSURES:  findOne p T sc fc ==> sc x if x is in T and p x ==> true.
 *           If no such x exists, this evalutes to fc () instead.
 *           If more than one such x exists,
 *           findOne p T sc fc evaluates the leftmost such x.
 *)
fun findOne (p : 'a -> bool) (Leaf(a) : 'a shrub) (sc : 'a -> 'b) (fc : unit -> 'b) : 'b = 
            if (p a) then sc a
            else fc ()
  | findOne p (Branch(L, R)) sc fc = findOne p L sc (fn () => (findOne p R sc fc))


(* test case *)
val T = Branch ( Leaf 1 , Leaf 2)
val p = fn x => x > 0
val sc = SOME
val fc = fn () => NONE
val SOME 1 = findOne p T sc fc
val p0 = fn x => x = 0
val p2 = fn x => x = 2
val SOME 2 = findOne p2 T sc fc
val NONE = findOne p0 T sc fc



(* findTwo : ('a -> bool) -> ('a * 'a -> bool) -> 'a shrub
 *           -> ('a * 'a -> 'b) -> (unit -> 'b) -> 'b
 * REQUIRES: p is total, eq is total, eq represents an equivalence relation
 * ENSURES:  findTwo p eq T sc fc ==> sc (x, y) if x and y are values in T s.t.
 *           p x ==> true and p y ==> true and eq (x,y) ==> false.
 *           If no such pair (x,y) exists, findTwo p T sc fc ==> fc ()
 *)

fun findTwo (p : 'a -> bool) (eq : 'a * 'a -> bool) (Leaf(a) : 'a shrub) (sc : 'a * 'a -> 'b) (fc : unit -> 'b) : 'b  = fc ()
 |  findTwo p eq (Branch(L, R)) sc fc = findOne p (Branch(L, R)) 
 (fn fir  => (findOne (fn x => ((p x) andalso (not (eq (fir, x))))) (Branch(L, R)) (fn sec => sc (fir, sec)) fc)) fc
    
val T1 = Branch ( Leaf 1 , Leaf 2)
val T2 = Branch ( Leaf 1 , Leaf 1)
val T3 = Branch(Branch(Leaf(1),Leaf(2)),Branch(Leaf(3),Leaf(4)))
val T4 = Branch(Branch(Leaf(1),Leaf(1)),Branch(Leaf(1),Leaf(4)))
val T5 = Branch(Branch(Branch(Leaf(1),Leaf(2)),Branch(Leaf(2),Leaf(3))),Branch(Branch(Leaf(3),Leaf(4)),Branch(Leaf(4),Leaf(5))))
val T6 = Branch(Branch(Branch(Leaf(1),Leaf(2)),Branch(Leaf(2),Leaf(3))),Branch(Branch(Leaf(3),Leaf(4)),Branch(Leaf(4),Leaf(3))))
val T7 = Branch(Branch(Branch(Leaf(1),Leaf(3)),Branch(Leaf(2),Leaf(3))),Branch(Branch(Leaf(3),Leaf(4)),Branch(Leaf(4),Leaf(3))))
val p1 = fn x => x > 0
val p2 = fn x => x = 1
val eq = op=
val sc = SOME
val fc = fn () => NONE
val SOME (1 , 2) = findTwo p1 eq T1 sc fc
val NONE = findTwo p2 eq T1 sc fc
val NONE = findTwo p1 eq T2 sc fc
            


(* findN : ('a -> bool) -> ('a * 'a -> bool) -> 'a shrub -> int
 *         -> ('a list -> 'b) -> (unit -> 'b) -> 'b
 * REQUIRES: n >= 0, p is total, eq is total,
 *           eq represents an equivalence relation
 * ENSURES: findN p eq T n sc fc ==> sc L if there exists
 *          a list L of length n s.t the elements in L are pairwise distinct
 *          by eq, and for each element x in L, p x ==> true.
 *          Otherwise evaluates to fc ().
 *)

fun findN (p : 'a -> bool) (eq : 'a * 'a -> bool) (T : 'a shrub)
          (n : int) (sc : 'a list -> 'b) (fc : unit -> 'b) =
  case n of
    0 => sc []
  | _ =>
      let
        
        fun success x = findN (fn y => ((p y) andalso (not (eq (x, y))))) eq T (n-1) (fn L => sc(x::L)) fc
      in
        findOne p T success fc
      end


val SOME [1,2,3,4] = findN p1 eq T3 4 sc fc
val NONE = findN p2 eq T3 4 sc fc
val SOME [1, 4] = findN p1 eq T4 2 sc fc
val SOME [1,2,3,4] = findN p1 eq T5 4 sc fc
val SOME [1,3,2,4] = findN p1 eq T7 4 sc fc

  (* fun findfalse (a, acc) = case (a, acc) of 
                                 (true, true) => true
                               | (_, _) => false *)
(* (fn L => (if ((foldr findfalse true (map (fn a => case eq (a, x) of true => false | false => true) L)) = true)  then (sc (x::L)) else fc ())) *)




val T = Branch (Leaf 1, Leaf 2)
val p = fn x => x > 0
val sc = SOME
val fc = fn () => NONE
val SOME 1 = findOne p T sc fc
val p0 = fn x => x = 0
val p2 = fn x => x = 2
val SOME 2 = findOne p2 T sc fc
val NONE = findOne p0 T sc fc
val TL = Branch(Branch(Branch(Branch(Branch(Leaf 1,Leaf 2),Leaf 3),Branch(Leaf 4,Leaf 5)),Branch(Leaf 6,Leaf 8848)),Branch((Leaf 0),Branch(Leaf ~8848,Leaf 9)))
val SOME ~8848 = findOne (fn x => x < 0) TL (sc) (fc)
val SOME 8848 = findOne (fn x => x mod 8848 = 0) TL sc fc
val SOME 2 = findOne (fn x => x mod 2 = 0) TL sc fc
val NONE = findOne (fn x => x - 100 = 0) TL sc fc
val SOME 9 = findOne (fn x => 3*3 = x) TL sc fc

val T1 = Branch (Leaf 1, Leaf 2)
val T2 = Branch (Leaf 1, Leaf 1)
val T1 = Branch(Branch(Leaf 1, Leaf 2), Leaf 4)
val T2 = Branch(Branch(Leaf(1),Leaf(7)),Branch(Leaf(1),Leaf(6)))
val bigT = Branch(Branch(Branch(Leaf(2),Leaf(4)),Branch(Leaf(6),Leaf(8))),Branch(Branch(Leaf(10),     Leaf(12)),Leaf(14)))
val T3 = Branch(Branch(Leaf(2),Leaf(4)),Branch(Leaf(6),Leaf(8)))
val T4 = Branch(Leaf(2),Leaf(4))
val repT = Branch(Branch(Leaf(1),Leaf(1)),Branch(Leaf(6),Leaf(8)))
val smallT = Leaf(3)

val p0 = fn x => x = 1
val p1 = fn x => x mod 2 = 0
val p2 = fn x => x > 10
val p3 = fn x => x > 12
val p4 = fn x => x < 3
val p5 = fn x => x = 2 orelse x = 14
val p6 = fn x => x < 6

val NONE = findOne p0 T3 sc fc
val NONE = findOne p0 T3 sc fc
val SOME 1 = findOne p0 T2 sc fc
val SOME 2 = findOne p1 T1 sc fc
val SOME 2 = findOne p1 bigT sc fc

(* test cases *)
val T1 = Branch (Leaf 1,Leaf 1)
val eq = op =
val SOME (1,2) = findTwo p eq T sc fc
val NONE = findTwo (fn x => x = 1) eq T sc fc
val NONE = findTwo p eq T1 sc fc
val SOME (3,6) = findTwo (fn x => x mod 3 = 0) eq TL sc fc
val SOME (8848,~8848) = findTwo (fn x => Int.abs(x) = 8848) eq TL sc fc
val NONE = findTwo (fn x => x = 0) eq TL sc fc
val TL' = Branch(Branch(Branch(Branch(Branch(Leaf 2,Leaf 2),Leaf 3),Branch(Leaf 4,Leaf 5)),Branch(Leaf 6,Leaf   8848)),Branch((Leaf 0),Branch(Leaf ~8848,Leaf 9)))
val SOME (2,4) = findTwo (fn x => x mod 2 = 0) eq TL' sc fc
val TL'' = Branch(Branch(Branch(Branch(Branch(Leaf 2,Leaf 2),Leaf 3),Branch(Leaf
4,Leaf 3)),Branch(Leaf 6,Leaf 8848)),Branch((Leaf 0),Branch(Leaf ~8848,Leaf 9)))
val SOME (3,6) = findTwo (fn x => x mod 3 = 0) eq TL'' sc fc
val SOME (3,6) = findTwo (fn x => x mod 3 = 0) eq TL' sc fc
val TL''' = Branch(Branch(Branch(Branch(Branch(Leaf 2,Leaf 2),Leaf 3),Branch(Leaf
  4,Leaf 3)),Branch(Leaf 3,Leaf 8848)),Branch((Leaf 0),Branch(Leaf ~8848,Leaf 9)))
val SOME (3,0) = findTwo (fn x => x mod 3 = 0) eq TL''' sc fc
val eq = op=

val SOME(2, 4) = findTwo p1 eq bigT sc fc
val SOME(2, 4) = findTwo p1 eq T4 sc fc
val NONE = findTwo p1 eq smallT sc fc
val SOME(12, 14) = findTwo p2 eq bigT sc fc
val NONE = findTwo p3 eq bigT sc fc
val NONE = findTwo p4 eq repT sc fc
val SOME(2, 14) = findTwo p5 eq bigT sc fc
val T1 = Branch (Leaf 1, Leaf 2)
val T2 = Branch (Leaf 1, Leaf 1)
val p1 = fn x => x > 0
val p2 = fn x => x = 1
val eq = op=
val sc = SOME
val fc = fn () => NONE
val SOME (1, 2) = findTwo p1 eq T1 sc fc
val NONE = findTwo p2 eq T1 sc fc
val NONE = findTwo p1 eq T2 sc fc
val NONE = findTwo p2 eq T2 sc fc
val T=Branch(Leaf 1, Branch(Leaf 2, Branch(Branch(Leaf 3, Leaf
4),Branch(Branch(Leaf 5, Leaf 6),Leaf 7))))
val sc = (fn a => a)
val fc = (fn () => [])
val [] = findN p1 eq T 8 sc fc

val T = Branch (Leaf 1, Leaf 2)
val p = fn x => x > 0
val sc = SOME
val fc = fn () => NONE
val SOME 1 = findOne p T sc fc
val p0 = fn x => x = 0
val p2 = fn x => x = 2
val SOME 2 = findOne p2 T sc fc
val NONE = findOne p0 T sc fc
val T = Branch(Leaf 1, Branch(Leaf 2, Branch(Leaf 3, Leaf 4)))
val p = fn x => x>3
val p1 = fn x => x<4
val SOME 4 =findOne p T sc fc
val SOME 1 = findOne p1 T sc fc
val SOME [2] = findN p1 eq T3 1 sc fc
val NONE = findN p6 eq repT 2 sc fc
val p2 = fn x => x > 10
val SOME [12,14] = findN p2 eq bigT 2 sc fc

