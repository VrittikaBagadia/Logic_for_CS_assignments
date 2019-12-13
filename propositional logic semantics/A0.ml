type prop = T 
		| F 
		| L of string 	
		| Not of prop 
		| And of (prop*prop) 
		| Or of (prop*prop)
		| Impl of (prop*prop)
		| Iff of (prop*prop);;

let max n1 n2 = if n1 > n2 then n1 else n2;;

(* height of syntax tree of proposition *)
let rec ht p = match p with
		T -> 1
		| F -> 1
		| L(p1) -> 1
		| Not(p1) -> 1 + (ht p1)
		| And(p1,p2) -> 1 + (max (ht p1) (ht p2))
		| Or(p1,p2) -> 1 + (max (ht p1) (ht p2))
		| Impl(p1,p2) -> 1 + (max (ht p1) (ht p2))
		| Iff (p1,p2) -> 1 + (max (ht p1) (ht p2));;

(* size of syntax tree of proposition *)
let rec size p = match p with
		T -> 1
		| F -> 1
		| L(p1) -> 1
		| Not(p1) -> 1 + (size p1)
		| And(p1,p2) -> 1 + (size p1) + (size p2)
		| Or(p1,p2) -> 1 + (size p1) + (size p2)
		| Impl(p1,p2) -> 1 + (size p1) + (size p2)
		| Iff (p1,p2) -> 1 + (size p1) + (size p2);;


(* returns true if symbol found in list a *)
let rec find_element sym a = match a with
	([]) -> (false)
	|(x::xs)-> (if x = sym then true else find_element sym xs);; 

(* union of two lists *)
let rec app l1 l2 = match l1 with
	[] -> l2
	|(x::xs) -> (if (find_element x l2) then (app xs l2) else (app xs (x::l2)));;

(* returns set of propositional letters *)
let rec letters p = match p with
		T -> []
		| F -> []
		| L(s) -> [s]
		| Not(p1) -> letters p1
		| And(p1,p2) -> app (letters p1) (letters p2)
		| Or(p1,p2) -> app (letters p1) (letters p2)
		| Impl(p1,p2) -> app (letters p1) (letters p2)
		| Iff(p1,p2) -> app (letters p1) (letters p2);;

(* checks equality of propositions *)
let rec check_equality p1 p2 = match (p1,p2) with
		(T,T) -> true
		| (F,F) -> true
		| (L(s1),L(s2)) -> if (s1=s2) then true else false
		| (Not(x1),Not(x2)) -> check_equality x1 x2
		| (And(x1,x2),And(x3,x4)) -> (check_equality x1 x3) && (check_equality x2 x4)
		| (Or(x1,x2), Or(x3,x4)) -> (check_equality x1 x3) && (check_equality x2 x4)
		| (Impl(x1,x2),Impl(x3,x4)) -> (check_equality x1 x3) && (check_equality x2 x4)
		| (Iff(x1,x2),Iff(x3,x4)) -> (check_equality x1 x3) && (check_equality x2 x4)
		| _ -> false;;

let rec add_lists l1 l2 = match l1 with
		[] -> l2
		| (x::xs) -> add_lists xs (x::l2);;

(* looks for position of p1 in p2 *)
let rec prop_pos p1 p2 till_now = match p2 with
		T -> if (check_equality p1 p2) then [till_now] else []
		| F -> if (check_equality p1 p2) then [till_now] else []
		| L(x) -> if (check_equality p1 p2) then [till_now] else [] 
		| Not(p) -> if (check_equality p1 p2) then [till_now] else (prop_pos p1 p (0::till_now))
		| And(p3,p4) -> if (check_equality p1 p2) then [till_now] else (add_lists (prop_pos p1 p3 (0::till_now)) (prop_pos p1 p4 (1::till_now)))
		| Or(p3,p4) -> if (check_equality p1 p2) then [till_now] else (add_lists (prop_pos p1 p3 (0::till_now)) (prop_pos p1 p4 (1::till_now)))
		| Impl(p3,p4) -> if (check_equality p1 p2) then [till_now] else (add_lists (prop_pos p1 p3 (0::till_now)) (prop_pos p1 p4 (1::till_now)))
		| Iff(p3,p4) -> if (check_equality p1 p2) then [till_now] else (add_lists (prop_pos p1 p3 (0::till_now)) (prop_pos p1 p4 (1::till_now)));;

exception NotSubProp;;
(* returns a list of all paths to p1 in p2 *)
let subprop_at p1 p2 = match (prop_pos p1 p2 []) with
		[] -> raise NotSubProp
		| x -> x;;

let implies p1 p2 = match (p1, p2) with
		(true, false) -> false
		| _ -> true;;

let iff p1 p2 = match (p1,p2) with
		(true, true) -> true
		| (false, false) -> true
		| _ -> false;;

exception NotFound;;
(* semantic function using standard truth table of connectives *)
let rec truth p rho = match p with
		| T -> true
		| F -> false
		| L(s) -> rho s
		| Not(p1) -> not (truth p1 rho)
		| And(p1,p2) -> (truth p1 rho) && (truth p2 rho)
		| Or(p1,p2) -> (truth p1 rho) || (truth p2 rho)
		| Impl(p1,p2) -> implies (truth p1 rho) (truth p2 rho)
		| Iff(p1,p2) -> iff (truth p1 rho) (truth p2 rho);;

(* eliminates impl and iff from proposition *)
let rec eliminate p = match p with
		| T -> T
		| F -> F
		| L(s) -> L(s)
		| Not(p1) -> Not(eliminate p1)
		| And(p1,p2) -> And(eliminate p1, eliminate p2)
		| Or(p1,p2) -> Or(eliminate p1, eliminate p2)
		| Impl(p1,p2) -> Or(Not(eliminate p1), eliminate p2)
		| Iff(p1,p2) -> Or(And(eliminate p1, eliminate p2), And(Not(eliminate p1),Not(eliminate p2)));;

(* deals with nots in proposition whose impl and iff have been removed *)
let rec nnf2 p = match p with
		T -> T
		| F -> F
		| L(s) -> L(s)
		| Not(T) -> F
		| Not(F) -> T
		| Not(L(s)) -> p
		| Not(Not p1) -> nnf2 p1
		| Not(And(p1,p2)) -> Or(nnf2 (Not(p1)), nnf2 (Not(p2)))
		| Not(Or(p1,p2)) -> And(nnf2 (Not(p1)), nnf2 (Not(p2)))
		| And(p1,p2) -> And(nnf2 p1, nnf2 p2)
		| Or(p1, p2) -> Or(nnf2 p1, nnf2 p2);;
	
let nnf p = nnf2 (eliminate p);;

(* will be called only on nnf form *)
let rec any_and p = match p with	
		T -> false
		| F -> false
		| L(s) -> false 
		| Not(p1) -> any_and p1
		| And(p1,p2) -> true
		| Or(p1,p2) -> (match (any_and p1, any_and p2) with 
			(false,false) -> false
			|_ -> true);;

(* will be called only on nnf form *)
let rec any_or p = match p with	
		T -> false
		| F -> false
		| L(s) -> false
		| Not(p1) -> any_or p1
		| Or(p1,p2) -> true
		| And(p1,p2) -> (match (any_or p1, any_or p2) with 
			(false,false) -> false
			|_ -> true);;

let rec dnf2 p = match p with
		| T -> T
		| F -> F
		| L(s) -> L(s)
		| Not(p1) -> Not(dnf2 p1)
		| Or(p1, p2) -> Or (dnf2 p1, dnf2 p2)
		| And (p1, Or(p2,p3)) -> Or( dnf2 (And(p1,p2)), dnf2 (And(p1,p3)))
		| And (Or(p1,p2), p3) -> Or( dnf2 (And(p1,p3)), dnf2 (And(p2,p3)))
		| And( p1, p2) -> if (any_or p) then dnf2 (And(dnf2 p1, dnf2 p2)) else And(p1,p2);;

let dnf p = dnf2 (nnf p);;

let rec cnf2 p = match p with
		| T -> T
		| F -> F
		| L(s) -> L(s)
		| Not(p1) -> Not(cnf2 p1)
		| And(p1, p2) -> And (cnf2 p1, cnf2 p2)
		| Or(p1, And(p2,p3)) -> And ( cnf2 (Or(p1,p2)), cnf2 (Or(p1,p3)) )
		| Or(And(p1,p2), p3) -> And ( cnf2 (Or(p1,p3)), cnf2 (Or(p2,p3)) )
		| Or(p1,p2) -> if (any_and p) then cnf2 (Or( cnf2 p1, cnf2 p2)) else Or(p1,p2);;

let cnf p = cnf2 (nnf p);;

 (* ------------------------------ EXAMPLES ------------------------------- *)

let rhoTTT var = match var with
		"p" -> true
		| "q" -> true
		| "r" -> true
		| _ -> false;;

let rhoTFT var = match var with
		"p" -> true
		| "q" -> false
		| "r" -> true
		| _ -> false;;

let rhoFTT var = match var with
		"p" -> false
		| "q" -> true
		| "r" -> true
		| _ -> false;;

let rhoFFT var = match var with
		"p" -> false
		| "q" -> false
		| "r" -> true
		| _ -> false;;

let rhoTTF var = match var with
		"p" -> true
		| "q" -> true
		| "r" -> false
		| _ -> false;;

let rhoFTF var = match var with
		"p" -> false
		| "q" -> true
		| "r" -> false
		| _ -> false;;

(* -------------- TESTING STARTING FUNCTIONS --------------- *)
let prop = Not(Iff(Or(L("p"),L("q")),Or(L("q"),L("p"))));;
(* let height = ht prop;;
let sizee = size prop;;
let alphas = letters prop;;
let s1 = subprop_at T prop;; *)

(* val height : int = 4
val sizee : int = 8
val alphas : string list = ["q"; "p"]
Exception: NotSubProp. *)

(* -------------- TAUTOLOGY --------------- *)
let prop1 = Or(Or(L("p"),L("q")),And(Not(L("p")),Not(L("q"))));; 
let ht1 = ht prop1;;
let size1 = size prop1;;
let alphas = letters prop1;;
let nnf1 = nnf prop1;;
let dnf1 = dnf prop1;;
let cnf1 = cnf prop1;;
let a1 = truth prop1 rhoTTT ;; (* val a1 : bool = true *)
let a2 = truth prop1 rhoTFT;; (* val a2 : bool = true *)
let a3 = truth prop1 rhoFTT ;; (* val a3 : bool = true *)
let a4 = truth prop1 rhoFFT;; (* val a4 : bool = true *)
let a5 = truth nnf1 rhoFFT;; (* val a5 : bool = true *)
let a6 = truth cnf1 rhoTTT ;; (* val a6 : bool = true *)
let a7 = truth dnf1 rhoTFT ;; (* val a7 : bool = true *)

(* --------------- CONTRADICTION --------------- *)
let prop2 = And(Not(Impl(L("p"),Impl(L("q"),L("p")))),Or(And(L("r"),L("q")),L("p")));;
let nnf2 = nnf prop2;;
let dnf2 = dnf prop2;;
let cnf2 = cnf prop2;;
let b1 = truth prop2 rhoTTT;; (* val b1 : bool = false *)
let b2 = truth prop2 rhoTTF;; (* val b2 : bool = false *)
let b3 = truth prop2 rhoFFT;; (* val b3 : bool = false *)
let b4 = truth nnf2 rhoFFT;; (* val b4 : bool = false *)
let b5 = truth nnf2 rhoFTF;; (* val b5 : bool = false *)
let b6 = truth dnf2 rhoTTF;; (* val b6 : bool = false *)
let b7 = truth cnf2 rhoFTF;; (* val b7 : bool = false *)

(* --------------- CONTINGENCY --------------- *)
let prop3 = And(And(Or(L("p"),L("q")),Or(L("q"),L("r"))),And(Impl(L("p"),L("q")),Iff(L("p"),L("r"))));;
let c1 = truth prop3 rhoTTT;;   		(* val c1 : bool = true *)
let c2 = truth (nnf prop3) rhoTTT;;
let c3 = truth (dnf prop3) rhoTTT;;
let c4 = truth (cnf prop3) rhoTTT;;
let c5 = truth prop3 rhoFFT;;   		(*  val c5 : bool = false *)
let c6 = truth (nnf prop3) rhoFFT;;
let c7 = truth (dnf prop3) rhoFFT;;
let c8 = truth (cnf prop3) rhoFFT;;
let c9 = truth prop3 rhoFTF;;			(* val c9 : bool = true *)
let c10 = truth (nnf prop3) rhoFTF;;	
let c11 = truth (dnf prop3) rhoFTF;;
let c12 = truth (cnf prop3) rhoFTF;;
let c13 = truth prop3 rhoFTT;;			(* val c13 : bool = false *)
let c14 = truth (nnf prop3) rhoFTT;;
let c15 = truth (dnf prop3) rhoFTT;;
let c16 = truth (cnf prop3) rhoFTT;;

(* --------------- CONTRADICTION --------------- *)
let prop4 = Not(Iff(Or(L("p"),L("q")),Or(L("q"),L("p"))));;
let d1 = truth prop4 rhoTTT;;   		(* val d1 : bool = false *)
let d2 = truth (nnf prop4) rhoTTT;;
let d3 = truth (dnf prop4) rhoTTT;;
let d4 = truth (cnf prop4) rhoTTT;;
let d5 = truth prop4 rhoTFT;;   		(*  val d5 : bool = false *)
let d6 = truth (nnf prop4) rhoTFT;;
let d7 = truth (dnf prop4) rhoTFT;;
let d8 = truth (cnf prop4) rhoTFT;;
let d9 = truth prop4 rhoFTT;;			(* val d9 : bool = false *)
let d10 = truth (nnf prop4) rhoFTT;;	
let d11 = truth (dnf prop4) rhoFTT;;
let d12 = truth (cnf prop4) rhoFTT;;
let d13 = truth prop4 rhoFFT;;			(* val d13 : bool = false *)
let d14 = truth (nnf prop4) rhoFFT;;
let d15 = truth (dnf prop4) rhoFFT;;
let d16 = truth (cnf prop4) rhoFFT;;

(* --------------- CONTINGENCY --------------- *)
let prop5 = Or(Or(And(L("p"),L("q")), L("s")), Not(And(L("r"),L("q"))));;
let e1 = truth prop5 rhoTTT;;   		(* val e1 : bool = true *)
let e2 = truth (nnf prop5) rhoTTT;;
let e3 = truth (dnf prop5) rhoTTT;;
let e4 = truth (cnf prop5) rhoTTT;;
let e5 = truth prop5 rhoFFT;;   		(*  val e5 : bool = true *)
let e6 = truth (nnf prop5) rhoFFT;;
let e7 = truth (dnf prop5) rhoFFT;;
let e8 = truth (cnf prop5) rhoFFT;;
let e9 = truth prop5 rhoFTF;;			(* val e9 : bool = true *)
let e10 = truth (nnf prop5) rhoFTF;;	
let e11 = truth (dnf prop5) rhoFTF;;
let e12 = truth (cnf prop5) rhoFTF;;
let e13 = truth prop5 rhoFTT;;			(* val e13 : bool = false *)
let e14 = truth (nnf prop5) rhoFTT;;
let e15 = truth (dnf prop5) rhoFTT;;
let e16 = truth (cnf prop5) rhoFTT;;

(* --------------- TAUTOLOGY --------------- *)
let prop6 = Impl(Impl( Impl( L("p"), L("q")), L("p")), L("p"));;
let f1 = truth prop6 rhoTTT;;   		(* val f1 : bool = true *)
let f2 = truth (nnf prop6) rhoTTT;;
let f3 = truth (dnf prop6) rhoTTT;;
let f4 = truth (cnf prop6) rhoTTT;;
let f5 = truth prop6 rhoFFT;;   		(*  val f5 : bool = true *)
let f6 = truth (nnf prop6) rhoFFT;;
let f7 = truth (dnf prop6) rhoFFT;;
let f8 = truth (cnf prop6) rhoFFT;;
let f9 = truth prop6 rhoFTF;;			(* val f9 : bool = true *)
let f10 = truth (nnf prop6) rhoFTF;;	
let f11 = truth (dnf prop6) rhoFTF;;
let f12 = truth (cnf prop6) rhoFTF;;
let f13 = truth prop6 rhoTFT;;			(* val f13 : bool = true *)
let f14 = truth (nnf prop6) rhoTFT;;
let f15 = truth (dnf prop6) rhoTFT;;
let f16 = truth (cnf prop6) rhoTFT;;

				