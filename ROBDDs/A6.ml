(* Paper implemented: http://www.cs.utexas.edu/~isil/cs389L/bdd.pdf *)
open Hashtbl;;
type prop = T 
		| F 
		| L of int 	
		| Not of prop 
		| And of (prop*prop) 
		| Or of (prop*prop)
		| Impl of (prop*prop)
		| Iff of (prop*prop);;
(* -------------------------- NNF, CNF, DNF -------------------------- *)

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

(* ---------------------------------------------------------------------- *)
type node = Node of (int*int*int);; 	(* variable_index, l, h *)
	
let hashH = create 124;;
let hashT = create 124;;

let get_from_node u str = match u with 
	Node(x1,x2,x3) -> (match str with 
					"var" -> x1
					| "low" -> x2
					| _ -> x3
				);;

let mk hashH hashT nodeU = if ((get_from_node nodeU "low") = (get_from_node nodeU "high")) then (get_from_node nodeU "low") 
				else if (mem hashH nodeU) then (find hashH nodeU) 
				else 
				( 
					let new_no = (Hashtbl.length hashT) in
					(add hashT new_no nodeU);
					(add hashH nodeU new_no);
					new_no
				);;

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
		| L(s) -> (List.nth rho (s-1)) 	(* find index of s in ordered_var list and then get assignment in rho *)
		| Not(p1) -> not (truth p1 rho)
		| And(p1,p2) -> (truth p1 rho) && (truth p2 rho)
		| Or(p1,p2) -> (truth p1 rho) || (truth p2 rho)
		| Impl(p1,p2) -> implies (truth p1 rho) (truth p2 rho)
		| Iff(p1,p2) -> iff (truth p1 rho) (truth p2 rho);;

let init table n = (
				(replace table 0 (Node(n+1,-1,-1)));
				(replace table 1 (Node(n+1,-1,-1)));
				);;

(* rho is a list *)
let rec build_helper hashH hashT prop_main i rho n =
	if (i > n) then (let x = (truth prop_main rho) in if x=true then 1 else 0)
	else 
	(let v0 = (build_helper hashH hashT prop_main (i+1) (rho@[false]) n) in 
		let v1 = (build_helper hashH hashT prop_main (i+1) (rho@[true]) n) in 
		(mk hashH hashT (Node(i,v0,v1))));;  

let build prop n t h =
	(init t (max n ((get_from_node (find t 0) "var")-1)));
	build_helper h t prop 1 [] n;;

let rec app u1 u2 op g t h = 
	if (mem g (u1,u2)) then (find g (u1,u2)) else
	if ((u1=0 || u1=1) && (u2=0 || u2=1)) then (let u = (op u1 u2) in ((add g (u1,u2) u); u)) else
	if ( (get_from_node (find t u1) "var") = (get_from_node (find t u2) "var") ) then 
		(let u = (mk h t ( Node( (get_from_node (find t u1) "var") , (app (get_from_node (find t u1) "low") (get_from_node (find t u2) "low") op g t h) , (app (get_from_node (find t u1) "high") (get_from_node (find t u2) "high") op g t h) ) ))
			in (add g (u1,u2) u); u 
		) else
	if ( (get_from_node (find t u1) "var") < (get_from_node (find t u2) "var") ) then 
		(let u = (mk h t ( Node( (get_from_node (find t u1) "var") , (app (get_from_node (find t u1) "low") u2 op g t h) , (app (get_from_node (find t u1) "high") u2 op g t h) ) ))
			in (add g (u1,u2) u); u 
		) 
	else
	(* if ( (get_from_node (find t u1) "var") > (get_from_node (find t u2) "var") ) then  *)
		(let u = (mk h t ( Node( (get_from_node (find t u2) "var") , (app u1 (get_from_node (find t u2) "low") op g t h) , (app u1 (get_from_node (find t u2) "high") op g t h) ) ))
			in (add g (u1,u2) u); u 
		);;

let apply u1 u2 op t h = app u1 u2 op (create 124) t h;;

let rec restrict u j b t h = 
	if ((get_from_node (find t u) "var") > j) then u else 
	if ((get_from_node (find t u) "var") < j) then (mk h t (Node( (get_from_node (find t u) "var") , ( restrict (get_from_node (find t u) "low") j b t h) , (restrict (get_from_node (find t u) "high") j b t h) ))) else
	if (b=0) then (restrict (get_from_node (find t u) "low") j b t h)
	else (restrict (get_from_node (find t u) "high") j b t h);;

let rec find_variables_num prop = match prop with
		T -> 0
		| F -> 0
		| L(s) -> s
		| Not(p1) -> find_variables_num p1
		| And(p1,p2) -> (max (find_variables_num p1) (find_variables_num p2))
		| Or(p1,p2) -> (max (find_variables_num p1) (find_variables_num p2))
		| Impl(p1,p2) -> (max (find_variables_num p1) (find_variables_num p2))
		| Iff(p1,p2) -> (max (find_variables_num p1) (find_variables_num p2));;

exception Unsatisfiable;;
let rec anysat u t h = 
	if (u = 0) then raise Unsatisfiable else
	if (u = 1) then [] else
	if ((get_from_node (find t u) "low")=0) then ((get_from_node (find t u) "var"),1)::(anysat (get_from_node (find t u) "high") t h)
	else ((get_from_node (find t u) "var"),0)::(anysat (get_from_node (find t u) "low") t h);;

let rec add_to_all element lis = match lis with
	[] -> []
	| (x::xs) -> (element::x)::(add_to_all element xs);;

let rec allsat u t h = 
	if (u=0) then []
	else if (u=1) then [[]] 
	else
		(add_to_all ((get_from_node (find t u) "var"),0) (allsat (get_from_node (find t u) "low") t h)) @ (add_to_all ((get_from_node (find t u) "var"),1) (allsat (get_from_node (find t u) "high") t h));;

let rec pow2 n ans = if (n=0) then ans else (pow2 (n-1) (2*ans));;

let rec count u t = 
	if (u=0) then 0
	else if (u=1) then 1
	else 
	( 
		let nodeU = (find t u) in 
		(pow2 ((get_from_node (find t (get_from_node nodeU "low")) "var") - (get_from_node nodeU "var") -1) 1)*(count (get_from_node nodeU "low") t) 
		+ (pow2 ((get_from_node (find t (get_from_node nodeU "high")) "var") - (get_from_node nodeU "var") -1) 1)*(count (get_from_node nodeU "high") t)
	);;

let satcount u t = (count u t)*(pow2 ((get_from_node (find t u) "var")-1) 1);;

let rec simplify d u t h = 
	if (d=0) then 0
	else if (u<=1) then u
	else if (d=1) then (mk h t (Node((get_from_node (find t u) "var"),(simplify d (get_from_node (find t u) "low") t h),(simplify d (get_from_node (find t u) "high") t h))))
	else if ((get_from_node (find t d) "var") = (get_from_node (find t u) "var")) then
	(
		if ((get_from_node (find t d) "low")=0) then (simplify (get_from_node (find t d) "high") (get_from_node (find t u) "high") t h)
		else if ((get_from_node (find t d) "high")=0) then (simplify (get_from_node (find t d) "low") (get_from_node (find t u) "low") t h)
		else (mk h t (Node( (get_from_node (find t u) "var") , (simplify (get_from_node (find t d) "low") (get_from_node (find t u) "low") t h) , (simplify (get_from_node (find t d) "high") (get_from_node (find t u) "high") t h) )))
	)
	else if ((get_from_node (find t d) "var") < (get_from_node (find t u) "var")) then
		(mk h t (Node( (get_from_node (find t d) "var") , (simplify (get_from_node (find t d) "low") u t h) , (simplify (get_from_node (find t d) "high") u t h) )))
	else 
		(mk h t (Node( (get_from_node (find t u) "var") , (simplify d (get_from_node (find t u) "low") t h) , (simplify d (get_from_node (find t u) "high") t h) )));;

(* --------------------------TESTING -------------------------- *)
let vx1 = L(1);;
let vx2 = L(2)
let vx3 = L(3);;

let p0 = Iff(vx1, vx2);;
let p1 = Or(p0,vx3);;
let p2 = Or(vx2,vx3);;
let np1 = Not(p1);;

(* compute NNF, CNF of p1 and Not(p1) *)
let p1' = nnf(p1);;
let p1'' = cnf(p1);;
let np1' = nnf(np1);;
let np1'' = cnf(np1);;

(* build ROBDDs *)
let h1 = create 124;; 
let t1 = create 124;;
(* init t1 0;; *)
add t1 0 (Node(1,-1,-1));;
add t1 1 (Node(1,-1,-1));;
let tt = build T 0 t1 h1;;			(* val tt : int = 1 *)
let tf = build F 0 t1 h1;;			(* val tf : int = 0 *)
let tvx1 = build vx1 (find_variables_num vx1) t1 h1;;
let tp2 = build p2 (find_variables_num p2) t1 h1;;
let tp0 = build p0 (find_variables_num p0) t1 h1;;
let tp1 = build p1 (find_variables_num p1) t1 h1;;
let tp1' = build p1' (find_variables_num p1') t1 h1;;
let tp1'' = build p1'' (find_variables_num p1'') t1 h1;;
let tnp1 = build np1 (find_variables_num np1) t1 h1;;
let tnp1' = build np1' (find_variables_num np1') t1 h1;;
let tnp1'' = build np1'' (find_variables_num np1'') t1 h1;;

(* Testcase #1 *)
tp1 == tp1';;
tp1 == tp1'';;
tnp1 == tnp1';;
tnp1 == tnp1'';;

(* Testcase #2 *)
let and_op x1 x2 = if (x1=1 && x2=1) then 1 else 0;;
let or_op x1 x2 = if (x1=0 && x2=0) then 0 else 1;;
let tplanp1 = apply tp1 tnp1 and_op t1 h1;;	   (* val tplanp1 : int = 0 *)
tplanp1 == tf;;						(* bool = true *)
let tp1onp1 = apply tp1 tnp1 or_op t1 h1;;		(* val tp1onp1 : int = 1 *)
tp1onp1 == tt;;						(* bool = true *)

(* Testcase #3 *)
let tp1rv30 = restrict tp1 3 0 t1 h1;;
tp1rv30 == tp0;;
let tp1rv31 = restrict tp1 3 1 t1 h1;;
tp1rv31 == tt;;

(* Testcase #4 *)
satcount tp1 t1;;	(* int = 6 *)
anysat tp1 t1 h1;;  (* [(1, 0); (2, 0)] i.e. any of the above *)
allsat tp1 t1 h1;;
(* 4 solutions:
[[(1, 0); (2, 0)]; 
[(1, 0); (2, 1); (3, 1)]; 
[(1, 1); (2, 0); (3, 1)];
[(1, 1); (2, 1)]] 
*)

(* Testcase #5 *)
let tstp2tp1 = simplify tp2 tp1 t1 h1;;
tstp2tp1 == tt;;
let tstvx1tp1 = simplify tvx1 tp1 t1 h1;;
tstvx1tp1 == tp2;;


