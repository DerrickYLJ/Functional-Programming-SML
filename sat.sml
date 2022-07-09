datatype prop = Const of bool
              | Var of string
              | And of prop * prop
              | Or of prop * prop
              | Not of prop

type assignment = string * bool


(* subst : assignment * prop -> prop
 * REQUIRES: true
 * ENSURES: subst ((c, b), p) ==>* p' such that
 *  - p' does not contain c
 *  - p' is equivalent to p except all instances of c have been replaced with
 *    True if b is true and False if b is false.
 *)
fun subst ((c, b), Var c') = if c = c' then Const b else Var c'
  | subst ((c, b), And (p1, p2)) = And (subst ((c, b), p1), subst ((c, b), p2))
  | subst ((c, b), Or (p1, p2)) = Or (subst ((c, b), p1), subst ((c, b), p2))
  | subst ((c, b), Not p) = Not (subst ((c, b), p))
  | subst (_, p) = p

(* subst_all : prop -> assignment list -> prop
 * REQUIRES: all strings in asgns are unique
 * ENSURES: subst_all p asgns evaluates to a proposition with all
 *  instances of variables in asgns replaced with the Const True or Const False,
 *  according to their corresponding booleans in asgns.
 *)
val subst_all = foldl subst

(* try_eval : prop -> (bool -> 'a) -> (string -> 'a) -> 'a
 * REQUIRES: true
 * ENSURES: if p contains no variables,
 *  then try_eval p sc fc ==>* sc b where b is the truth value of p.
 *  Otherwise, try_eval p sc fc ==>* fc c where c is the leftmost variable in p.
 *)
fun try_eval (p : prop) (sc : bool -> 'a) (fc : string -> 'a) : 'a =
      case p of 
      Const(b) => sc b
    | Var(s) => fc s
    | And(p1, p2) => try_eval p1 (fn res1 => (try_eval p2 (fn res2 => sc (res1 andalso res2)) fc)) fc
    | Or(p1, p2) => try_eval p1 (fn res1 => (try_eval p2 (fn res2 => sc (res1 orelse res2)) fc)) fc
    | Not p3 => try_eval p3 (fn res => sc (not res)) fc

val sc = fn b => (SOME b , NONE)
val fc = fn c => (NONE , SOME c)
val (SOME false , NONE) = try_eval (And (Not (Const true), Const true)) sc fc

val (NONE , SOME "a") = try_eval (And (Not (Var "a"), Var "b")) sc fc
val (NONE , SOME "a") = try_eval ( Or ( Const true , Var "a") ) sc fc
(* sat : prop -> (assignment list -> 'a) -> (unit -> 'a) -> 'a
 * REQUIRES: true
 * ENSURES: if there exists some value asgns such that
 *  try_eval (subst_all p asgns) (fn x => x) (fn _ => false) ==>* true,
 *  then sat p s k ==>* s asgns.
 *  Otherwise, sat p s k ==>* k ().
 *)
fun sat (p : prop) (sc : assignment list -> 'a) (fc : unit -> 'a) : 'a =
     try_eval p (fn firres => if firres then sc [] else fc ()) 
     (fn var => (sat (subst ((var, true),p)) (fn L => sc ((var, true)::L)) (fn () => (sat (subst ((var, false),p)) (fn L => sc ((var, false)::L)) fc))))



val sc = SOME
val fc = fn () => NONE
val NONE = sat ( And (Not ( Var "a") ,Var "a") ) sc fc
val SOME [("a", true )] = sat ( Or (And (Not ( Var "a") ,Var "a") ,Var "a")) sc fc



fun atLeastK (_ : prop list) (0 : int) : prop = Const true
    | atLeastK [] _ = Const false
    | atLeastK (p::ps) k = Or(And(p, atLeastK ps (k-1)), atLeastK ps k)
  
  
  fun atMostK (P : prop list) (k : int) : prop = atLeastK (map Not P) (length P - k)
  
  fun exactlyK (P : prop list) (k : int) = And(atLeastK P k, Not(atLeastK P (k+1)))

val sc = SOME
val fc = fn () => NONE
val NONE = sat (And(Not(Var "a"),Var "a")) sc fc
val SOME [("a",true)] = sat (Or(And(Not (Var "a"),Var "a"),Var "a")) sc fc
val SOME [] = sat (Const true) sc fc
val NONE = sat (Const false) sc fc
val NONE = sat (And(Not (Const false),Or (Not (Const true),Const false))) sc fc
val t1 = exactlyK  ([Var "Nuo naozi buhao",Var "Ge Qinglin naozi buhao", Const
true, Const false, And (Const true,Var "123"), Or (Var "nima",Var "aiai"), Not
(Var" ")]) 6
val sc = fn x => x
val fc = fn () => [("impossible",false)]
val k1 = sat t1 sc fc
val sc' = fn x => x
val fc' = fn _ => false
val true = try_eval (subst_all t1 k1) sc' fc'
val t11 = exactlyK  ([Var "Nuo naozi buhao",Var "Ge Qinglin naozi buhao", Const
  true, Const false, And (Const true,Var "123"), Or (Var "nima",Var "aiai"), Not
  (Var" ")]) 8

val k11 = sat t11 sc fc
val false = try_eval (subst_all t11 k11) sc' fc'
val t12 = exactlyK  ([Var "Nuo naozi buhao",Var "Ge Qinglin naozi buhao", Const
    true, Const false, And (Const true,Var "123"), Or (Var "nima",Var "aiai"), Not
    (Var" ")]) 4
val k12 = sat t12 sc fc
val true = try_eval (subst_all t12 k12) sc' fc'
val t13 = exactlyK  ([Var "Nuo naozi buhao",Var "Ge Qinglin naozi buhao", Const
      true, Const false, And (Const true,Var "123"), Or (Var "nima",Var "aiai"), Not
      (Var" ")]) 12
val k13 = sat t13 sc fc
val false = try_eval (subst_all t13 k13) sc' fc'
val t14 = exactlyK  ([Var "Nuo naozi buhao",Var "Ge Qinglin naozi buhao", Const
      true, Const false, And (Const true,Var "123"), Or (Var "nima",Var "aiai"), Not
      (Var" ")]) 9
val k13 = sat t13 sc fc
val false = try_eval (subst_all t13 k13) sc' fc'

val t2 = exactlyK ([Var "Chishi",Or (Var "heniao",Var "naozi"),Or (Const true,Var
"danzi"), Or (Const true,Const false), Or (Const false, Const true), Or (Const
false, Var "Iliano chishi"), And (Const false,Const false),And (Const false,Var
"yeji"), And (Const true,Const true), Not (Const true), Not (Const false), Not
(Var "Iliano shabi"),Var "mlgb", Var "Iliano Cervesato", Var "Holo"]) 8
val k2 = sat t2 sc fc
val true = try_eval (subst_all t2 k2) sc' fc'
val t21 = exactlyK ([Var "Chishi",Or (Var "heniao",Var "naozi"),Or (Const true,Var
  "danzi"), Or (Const true,Const false), Or (Const false, Const true), Or (Const
  false, Var "Iliano chishi"), And (Const false,Const false),And (Const false,Var
  "yeji"), And (Const true,Const true), Not (Const true), Not (Const false), Not
  (Var "Iliano shabi"),Var "mlgb", Var "Iliano Cervesato", Var "Holo"]) 6
val k21 = sat t21 sc fc

val true = try_eval (subst_all t21 k21) sc' fc'
val t22 = exactlyK ([Var "Chishi",Or (Var "heniao",Var "naozi"),Or (Const true,Var
    "danzi"), Or (Const true,Const false), Or (Const false, Const true), Or (Const
    false, Var "Iliano chishi"), And (Const false,Const false),And (Const false,Var
    "yeji"), And (Const true,Const true), Not (Const true), Not (Const false), Not
    (Var "Iliano shabi"),Var "mlgb", Var "Iliano Cervesato", Var "Holo"]) 3
val k22 = sat t22 sc fc
val false = try_eval (subst_all t22 k22) sc' fc'

val sc = SOME
val fc = fn () => NONE
val NONE = sat (And (Not (Var "a"),Var "a")) sc fc
val SOME [("a", true)] = sat (Or (And (Not (Var "a"),Var "a"),Var "a")) sc fc
val p = And(And(And(Var "a",Var "b"),Not(Var "b")),Or(Or(Var "b",Var "c"),Not (Var "a")))
val p1 = And(And(Or(Var "a",Var "b"),Not(Var "b")),Or(Or(Var "b",Var "c"),Not (Var "a")))
val NONE =sat p sc fc
val SOME [("a",true),("b",false),("c",true)] = sat p1 sc fc

(* test cases for try_eval *)
val sc = fn b => (SOME b, NONE)
val fc = fn c => (NONE, SOME c)
val (SOME false, NONE) = try_eval (And(Not(Const true), Const true)) sc fc

val (NONE, SOME "a") = try_eval (And(Not(Var "a"), Var "b")) sc fc
val (NONE, SOME "a") = try_eval (Or(Const true, Var "a")) sc fc
val (NONE, SOME "a") = try_eval (Or(And(Const true, Var "a"), Var "b")) sc fc
val (SOME true, NONE) = try_eval (Or(And(Not(Const true), Const false), Const true)) sc fc
