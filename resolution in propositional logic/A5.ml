open List;;
type variable = Var of string;;
type symbol = Sym of string;;
type term = V of variable| Node of symbol*(term list);;

(* signature *)
type pair = Pair of (symbol*int);;
type signature = List of pair list;;

(* returns true if symbol found in list a *)
let rec find_element sym a = match a with
	([]) -> (false)
	|(x::xs)-> (if x = sym then true else find_element sym xs);; 

(* returns true if a list of pairs is a valid signature *)
let rec check li acc = match li with (Pair(s,n)::xs)->
	(if n<0 then false else (if (find_element s acc) then false else (if xs=[] then true else check xs (s::acc))));;

(* returns true only if there is atleast one symbol with 0 arity *)
let rec check0arity li  = match li with
	[] -> false
	| (Pair(s,n)::xs)-> (if n=0 then true else (check0arity xs));;

let check_sig sign = match sign with List(l)-> 
	(check l [])&&(check0arity l);;

(* CHECK WELL FORMED TERM *)

exception Not_Found;;
let rec foldl func l a = match l with
	([])-> (a)
	|(x::xs)-> foldl func xs (func x a);;

let ands a b = match (a,b) with
	(true,true) -> true
	|_-> false;;

(* to find arrity of a symbol from given signature (which is assumed to be non empty ) *)
let rec arr sign sym = match sign with List(l)->
(
	match l with (Pair(s,n)::xs) -> (if s=sym then n else (if xs=[] then (raise Not_Found) else (arr (List(xs)) sym))) 
);;

let rec wfterm sign t = match t with
	V(var)-> true
	| Node(sym,l)-> (if ((length l)!=(arr sign sym)) then false else (foldl ands (map (wfterm sign) l) true));;

(* These functions are written assuming well formed term as parameter *)
let rec ht term = match term with
	V(var) -> 0
	| Node(sym,l)-> (if (length l = 0) then 0 else (1 + (foldl max (map ht l) 0)));;

let add n1 n2 = n1+n2;;
let rec size term = match term with
	V(var) -> 1
	| Node(sym,l) -> (if (length l = 0) then 1 else (1+ (foldl add (map size l) 0)));;

(* union of two lists *)
let rec app l1 l2 = match l1 with
	[] -> l2
	|(x::xs) -> (if (find_element x l2) then (app xs l2) else (app xs (x::l2)));;

let rec vars term = match term with
	V(var) -> [var]
	| Node(sym,l) -> (if l=[] then [] else foldl app (map vars l) []);;

(* substitution represented as a hash table*)
open Hashtbl;;

(* apply substitution s to term t *)
let rec subst s t = match t with
	V(var) -> (if (mem s var) then (find s var) else (V(var)))
	| Node(sym,l) -> (Node(sym, (map (subst s) l)));;

(* applies substitution s1 to b and adds the new term as value of key a *)
let func new_table s a b = (add new_table a (subst s b));;
				 
(* adds a b if not already in new_table *)
let func2 new_table a b = (if ((mem new_table a)=false) then add new_table a b );;

(* compose - takes two substitutions and returns their composition which is a new hash table *)
let compose s s1 s0 = 	(iter (func s s1) s0;
						 iter (func2 s) s1;
							s
						);;

let s0 = create 124;;			(* hash table 1 *)
add s0 (Var("x")) (V(Var("y")));;
add s0 (Var("z")) (Node(Sym("Plus"),[(Node(Sym("1"),[]));(V(Var("y")))]));;
(* add s0 (Var("y")) (Node(Sym("Plus"),[V(Var("x"));V(Var("z"))]));; *)
let s1 = create 124;;			(* hash table 2 *)
add s1 (Var("y")) (V(Var("u")));;
add s1 (Var("z")) (V(Var("x")));;
add s1 (Var("x")) (V(Var("t")));;
let s = create 124;;						
let com_sub = compose s s1 s0;;

exception NOT_UNIFIABLE;;
(* let fn a b = (a,b);; *)
(* type mgu_result = Hashtable of (variable, term) Hashtbl.t | NOT_UNIFIABLE;; *)

let rec mgu s t1 t2 = match (t1,t2) with
	(V(var1),V(var2)) -> ((if (not (var1 = var2)) then add s var1 (V(var2)));
							s
						 )
	| (V(var1), Node(sym,l)) -> (	(match (List.length l) with
									 0 -> ((add s var1 (Node(sym,l))))
									| _ -> (if (find_element var1 (vars (Node(sym,l)))) then (raise NOT_UNIFIABLE) else (add s var1 (Node(sym,l)))));

									s
							    )
	| (Node(sym,l),V(var1)) -> (	(match (List.length l) with
									 0 -> ((add s var1 (Node(sym,l))))
									| _ -> (if (find_element var1 (vars (Node(sym,l)))) then (raise NOT_UNIFIABLE) else (add s var1 (Node(sym,l)))));

									s
							    )
	| (Node(sym1,l1), Node(sym2,l2)) -> 
	(
		if (not(sym1 = sym2)) then raise NOT_UNIFIABLE
		else
		(
			match (l1,l2) with
			([],[])-> s 	(* return s *)			
			|(x1::xs1,x2::xs2)-> (mgu (compose (create 124) (mgu (create 124) (subst s x1) (subst s x2)) s) ((Node(sym1,xs1))) ((Node(sym2,xs2))))

		)

	);;

(* returns empty hashtable for both identical terms and ununifiable terms *)
let unifiable t1 t2 = 
	try mgu (create 24) t1 t2
	with NOT_UNIFIABLE -> (create 24);; 

(* ------------------------------  RESOLUTION  -------------------------------- *)

type literal = P of term | N of term;;
type clause = literal list;;

let rec remove_literal c l a = match c with (x::xs)-> (if (x=l) then a@xs else (remove_literal xs l (x::a)));;

let subst_literal s lit = match lit with
	P(l) -> P(subst s l)
	| N(l) -> N(subst s l);;

(* assuming l1 l2 are unifiable *)
let one_step_resolution c1 c2 lit1 lit2 = match (lit1,lit2) with
	(P(l1),N(l2)) -> (let s = (mgu (create 124) l1 l2) in (app (map (subst_literal s) (remove_literal c1 lit1 [])) (map (subst_literal s) (remove_literal c2 lit2 []))))
	| (N(l1),P(l2)) -> (let s = (mgu (create 124) l1 l2) in (app (map (subst_literal s) (remove_literal c1 lit1 [])) (map (subst_literal s) (remove_literal c2 lit2 []))));;

let opposite_literals lit1 lit2 = match (lit1, lit2) with
	(P(Node(s1,l1)),N(Node(s2,l2))) -> (if (s1=s2) then 
								(if (Node(s1,l1)=Node(s2,l2)) then true else (let s = (unifiable (Node(s1,l1)) (Node(s2,l2))) in if (length s)=0 then false else true)) else false)
	| (N(Node(s1,l1)),P(Node(s2,l2))) -> (if (s1=s2) then 
								(if (Node(s1,l1)=Node(s2,l2)) then true else (let s = (unifiable (Node(s1,l1)) (Node(s2,l2))) in if (length s)=0 then false else true)) else false)
	| _ -> false;;

let rec func1 literal clause acc = match clause with 
	[] -> acc
	| (x::xs) -> (if (opposite_literals literal x) then (func1 literal xs ((literal,x)::acc)) else (func1 literal xs acc));;

(* returns list of pairs of opposite_literals in clauses c1, c2 *)
let rec unifiable_literals c1 c2 acc = match c1 with 
	[] -> acc
	| (x::xs) -> unifiable_literals xs c2 ((func1 x c2 [])@acc);;

let rec choose_clauses_helper clause clause_list chosen_already = match clause_list with 
	[] -> []
	| (x::xs) -> if (find_element (clause,x) chosen_already) then (choose_clauses_helper clause xs chosen_already) else (let temp = (unifiable_literals clause x []) in if temp=[] then (choose_clauses_helper clause xs chosen_already) else [(clause,x)]);;

let rec choose_clauses clause_list chosen_already = match clause_list with
	[x] -> []
	| [] -> []
	| (x::xs) -> (let temp = (choose_clauses_helper x xs chosen_already) in 
					if (temp = []) then (choose_clauses xs chosen_already)
					else temp
					);;
	(* choose_clauses_helper x xs chosen_already;; *)

(* returns a list of all resolved clauses; lis is list of oppposite literals *)
let rec resolution_helper c1 c2 lis acc = match lis with
									[] -> acc
									| ((l1,l2)::xs) -> resolution_helper c1 c2 xs ((one_step_resolution c1 c2 l1 l2)::acc);;

let rec empty_clause_present lis = match lis with
	[] -> false
	| (x::xs) -> if (x = []) then true else (empty_clause_present xs);;
						
exception Cant_Prove_Unsatisfiable;;
exception Unsatisfiable;;
let rec run clause_list resolved = (
								let temp = (choose_clauses clause_list resolved) in match temp with 
								[] -> raise Cant_Prove_Unsatisfiable
								| [(c1,c2)] -> (
													let litlist = (unifiable_literals c1 c2 []) in 
													let resolved_clauses = (resolution_helper c1 c2 litlist []) in
													if (empty_clause_present resolved_clauses) then raise Unsatisfiable else
													(run (app clause_list resolved_clauses) ((c1,c2)::resolved))
												)
							);;

(* EXAMPLE 1 *)
let a = Node(Sym("A"),[]);;
let h = Node(Sym("H"),[]);;
let m = Node(Sym("M"),[]);;
let i = Node(Sym("I"),[]);;
let c1 = [N(a);P(h)];;
let c2 = [N(h)];;
let c3 = [N(i);P(h)];;
let c4 = [P(m);P(a)];;
let c5 = [N(m);P(i)];;
let cl = [c1;c2;c3;c4;c5];;


(* EXAMPLE 2 *)
let x1 = N(Node(Sym("x"),[]));;
let x2 = P(Node(Sym("x"),[]));;
let x = [[x1];[x2]];;
(* run x [];; *)

(* EXAMPLE 3 *)
let c1 = [N(Node(Sym("p"),[])) ; P(Node(Sym("q"),[]))];;
let c2 = [N(Node(Sym("q"),[])) ; P(Node(Sym("p"),[]))];;
let c3 = [P(Node(Sym("p"),[])) ; P(Node(Sym("q"),[]))];;
let c4 = [N(Node(Sym("p"),[])) ; N(Node(Sym("q"),[]))];;
let c = [c1;c2;c3;c4];;
(* run c [];; *)

(* EXAMPLE 4 *)
let l1 = N(Node(Sym("loves"),[V(Var("x"));V(Var("y"))]));;
let l2 = P(Node(Sym("loves"),[V(Var("y"));V(Var("z"))]));;
let l = [[l1];[l2]];;
(* run l [];; *)

(* EXAMPLE 5 *)
let c1 = [P(Node(Sym("f"),[V(Var("x1"));V(Var("x2"));V(Var("x3"))])) ; N(Node(Sym("g"),[V(Var("y1"));V(Var("y2"))]))];;
let c2 = [N(Node(Sym("f"),[V(Var("y1"));V(Var("y2"));V(Var("y3"))])) ; N(Node(Sym("g"),[V(Var("x1"));V(Var("x2"))]))];;
let c3 = [P(Node(Sym("g"),[V(Var("z1"));V(Var("z2"))]))];;
let c_ = [c1;c2;c3];;

(* EXAMPLE 6 *)
let p = Node(Sym("P"),[]);;
let q = Node(Sym("Q"),[]);;
let l = Node(Sym("L"),[]);;
let m = Node(Sym("M"),[]);;
let a = Node(Sym("A"),[]);;
let b = Node(Sym("B"),[]);;
let cl1 = [N(p);P(q)];;
let cl2 = [N(l);N(m);P(p)];;
let cl3 = [N(b);N(l);P(m)];;
let cl4 = [N(a);N(p);P(l)];;
let cl5 = [N(a);N(b);P(l)];;
let cl6 = [P(a)];;
let cl7 = [P(b)];;
let cl8 = [N(q)];;
let cl9 = [P(q)];;
let clauses = [cl1;cl2;cl3;cl4;cl5;cl6;cl7;cl8;cl9];;

(* YES, it will terminate *)

