open List;;
open Hashtbl;;

type prop = T 
		| F 
		| L of string 	
		| Not of prop 
		| And of (prop*prop) 
		| Or of (prop*prop)
		| Impl of (prop*prop)
		| Iff of (prop*prop);;

type assignment = A of (prop*bool);;
type node = Node of (prop*bool*bool*bool*int list);; 	(* 2st bool for explored, 3nd for closed *)
type tree = Tree of node * tree list * assignment list;;
type proof = Tableau of tree | Assignment of assignment list;;

exception NotImplemented;;

let rec member key mapping = match mapping with
	[] -> false
	| (A(p,b)::xs) -> (if (p=key) then true else (member key xs));;

let rec size treeRoot = match treeRoot with
		Tree(n,[],a) -> 1
		| Tree(n,[x;x2],a) -> 1 + size(x) + size(x2)
		| Tree(n,[x],a) -> 1 + size(x);;

let rec findIn key mapping = match mapping with
	(A(p,b)::xs) -> (if (p=key) then b else (findIn key xs));;

let rec push_alpha toAdd treeRoot = match treeRoot with 
		Tree(Node(p,b,n1,n2,l), [], x) -> (if (n2=true) then treeRoot else 
											match toAdd with Node(p2,b2,n12,n22,l2) -> 
											(
												if (member p2 x)=false then Tree(Node(p,b,n1,n2,l), [Tree(Node(p2,b2,n12,n22,l@[0]),[],A(p2,b2)::x)], x)
											else
												if (findIn p2 x)=b2 then Tree(Node(p,b,n1,n2,l), [Tree(Node(p,b,n12,n22,l@[0]),[],x)], x)	
												else Tree(Node(p,b,n1,n2,l), [Tree(Node(p2,b2,n12,true,l@[0]),[],x)], x)	
											))
		| Tree(Node(p,b,n1,n2,l), children, x) -> if (n2=true) then treeRoot else Tree(Node(p,b,n1,n2,l), List.map (push_alpha toAdd) children, x);;

let rec push_beta toAdd1 toAdd2 treeRoot = match treeRoot with
		Tree(Node(p,b,n1,n2,l), [], x) -> if (n2=true) then treeRoot else 
										(match (toAdd1,toAdd2) with (Node(p1,b1,n11,n21,l1),Node(p2,b2,n12,n22,l2)) -> 
										(
											if ((member p1 x)=false && (member p2 x)=false) then Tree(Node(p,b,n1,n2,l), [Tree(Node(p1,b1,n11,n21,l@[0]),[],A(p1,b1)::x);Tree(Node(p2,b2,n12,n22,l@[1]),[],A(p2,b2)::x)], x)
										else
											if ((member p1 x)=false && (findIn p2 x)=b2) then Tree(Node(p,b,n1,n2,l), [Tree(Node(p1,b1,n11,n21,l@[0]),[],A(p1,b1)::x);Tree(Node(p2,b2,n12,n22,l@[1]),[],x)], x)
										else
											if ((member p1 x)=false && (findIn p2 x)=not b2) then Tree(Node(p,b,n1,n2,l), [Tree(Node(p1,b1,n11,n21,l@[0]),[],A(p1,b1)::x);Tree(Node(p2,b2,n12,true,l@[1]),[],x)], x)
										else
											if ((findIn p1 x)=b1 && (member p2 x)=false) then Tree(Node(p,b,n1,n2,l), [Tree(Node(p1,b1,n11,n21,l@[0]),[],x);Tree(Node(p2,b2,n12,n22,l@[1]),[],A(p2,b2)::x)], x)
										else
											if ((findIn p1 x)=b1 && (findIn p2 x)=b2) then Tree(Node(p,b,n1,n2,l), [Tree(Node(p1,b1,n11,n21,l@[0]),[],x);Tree(Node(p2,b2,n12,n22,l@[1]),[],x)], x)
										else
											if ((findIn p1 x)=b1 && (findIn p2 x)=(not b2)) then Tree(Node(p,b,n1,n2,l), [Tree(Node(p1,b1,n11,n21,l@[0]),[],x);Tree(Node(p2,b2,n12,true,l@[1]),[],x)], x)
										else 
											if ((findIn p1 x)=(not b1) && (member p2 x)=false) then Tree(Node(p,b,n1,n2,l), [Tree(Node(p1,b1,n11,true,l@[0]),[],x);Tree(Node(p2,b2,n12,n22,l@[1]),[],A(p2,b2)::x)], x)
										else 
											if ((findIn p1 x)=(not b1) && (findIn p2 x)=b2) then Tree(Node(p,b,n1,n2,l), [Tree(Node(p1,b1,n11,true,l@[0]),[],x);Tree(Node(p2,b2,n12,n22,l@[1]),[],x)], x)
										else
											Tree(Node(p,b,n1,n2,l), [Tree(Node(p1,b1,n11,true,l@[0]),[],x);Tree(Node(p2,b2,n12,true,l@[1]),[],x)], x)
										))
											(* Tree(Node(p,b,n1,n2,l), [Tree(Node(p1,b1,n11,n21,l@[0]),[]); Tree(Node(p2,b2,n12,n22,l@[1]),[])]) ) *)
		| Tree(Node(p,b,n1,n2,l), children, x) -> if (n2=true) then treeRoot else Tree(Node(p,b,n1,n2,l), List.map (push_beta toAdd1 toAdd2) children, x);;

(* identifies alpha type nodes which are prefereanly expanded before beta type *)
let rec toExpandFirst myNode = match myNode with
		Node(And(p1,p2), true, n1, n2, l) -> true
		| Node(Or(p1,p2),false,n1, n2, l) -> true
		| Node(Impl(p1,p2), false, n1, n2, l) -> true
		| Node(T,b,n1,n2,l) -> true
		| Node(F,b,n1,n2,l) -> true
		| Node(L(s),b,n1,n2,l) -> true
		| _ -> false;;

let rec step_develop toFind treeRoot = match treeRoot with
		Tree(Node(p,b,n1,n2,l), children, mapping) -> if (l=toFind) then (match (p,b) with 
											 (T,true) -> Tree(Node(p,b,true,n2,l), children,mapping)
											 | (F, false) -> Tree(Node(p,b,true,n2,l), children,mapping)
											 | (T, false) -> Tree(Node(p,b,true,false,l), children,mapping)
											 | (F, true) -> Tree(Node(p,b,true,false,l), children,mapping)
											 | (L(s), b) -> if (member (L(s)) mapping) then (if (findIn (L(s)) mapping)=b then Tree(Node(p,b,true,n2,l), children,mapping) else Tree(Node(p,b,true,false,l), children,mapping)) else Tree(Node(p,b,true,n2,l),children,A(p,b)::mapping)
											 (* Tree(Node(p,b,true,n2,l), children,mapping) *)
											 | (Not(p1), b1) -> push_alpha (Node(p1,(not b1),false,n2,l)) (Tree(Node(p,b,true,n2,l),children,mapping))
											 | (And(p1,p2), false) -> push_beta (Node(p1,false,false,n2,[])) (Node(p2,false,false,n2,[])) (Tree(Node(p,b,true,n2,l),children,mapping))
											 | (Or(p1,p2), true) -> push_beta (Node(p1,true,false,n2,[])) (Node(p2,true,false,n2,[])) (Tree(Node(p,b,true,n2,l),children,mapping))
											 | (Impl(p1,p2), true) -> push_beta (Node(p1,false,false,n2,[])) (Node(p2,true,false,n2,[])) (Tree(Node(p,b,true,n2,l),children,mapping))
											 | (And(p1,p2), true) -> push_alpha (Node(p1,true,false,n2,[])) (push_alpha (Node(p2,true,false,n2,[])) (Tree(Node(p,b,true,n2,l), children,mapping)))
											 | (Or(p1,p2), false) -> push_alpha (Node(p1,false,false,n2,[])) (push_alpha (Node(p2,false,false,n2,[])) (Tree(Node(p,b,true,n2,l), children,mapping)))
											 | (Impl(p1,p2), false) -> push_alpha (Node(p1,true,false,n2,[])) (push_alpha (Node(p2,false,false,n2,[])) (Tree(Node(p,b,true,n2,l), children,mapping)))
											 | (Iff(p1,p2), false) -> push_beta (Node(And(p1,Not(p2)),false,false,n2,[])) (Node(And(Not(p1),p2),false,false,n2,[])) (Tree(Node(p,b,true,n2,l),children,mapping))
											 | (Iff(p1,p2), true) -> push_beta (Node(And(p1,p2),true,false,n2,[])) (Node(And(Not(p1),Not(p2)),true,false,n2,[])) (Tree(Node(p,b,true,n2,l),children,mapping))
											 |_ ->raise NotImplemented)
											else Tree(Node(p,b,n1,n2,l), (List.map (step_develop toFind) children), mapping);;

(* returns first alpha type unexplored node if any *)
let rec firstPass treeRoot = match treeRoot with
	Tree(Node(p,b,n1,n2,l),[],ass) -> if (n1=false && n2=false && (toExpandFirst (Node(p,b,n1,n2,l)))) then [l] else []
	| Tree(Node(p,b,n1,n2,l),[x],ass) -> if (n1=false && n2=false && toExpandFirst (Node(p,b,n1,n2,l))) then [l] else firstPass x
	| Tree(Node(p,b,n1,n2,l), [x1;x2],ass) -> if (n1=false && n2=false && toExpandFirst (Node(p,b,n1,n2,l))) then [l] else (if firstPass x1 = [] then firstPass x2 else firstPass x1);; 

(* returns first unexplored and not contradicted node if any *)
let rec secondPass treeRoot = match treeRoot with
	Tree(Node(p,b,n1,n2,l),[],ass) -> if (n1=false && n2 = false) then [l] else []
	| Tree(Node(p,b,n1,n2,l),[x],ass) -> if (n1=false && n2=false) then [l] else (secondPass x)
	| Tree(Node(p,b,n1,n2,l), [x1;x2],ass) -> if (n1=false && n2=false) then [l] else (if (secondPass x1) = [] then (secondPass x2) else (secondPass x1));;

exception AllExplored;;
let select_node treeRoot = (match firstPass treeRoot with
	[] -> (match (secondPass treeRoot) with [x] -> x| _->[])
	| [x] -> x);;
(* 
let rec contrad_path_helper mapping treeRoot = match treeRoot with
	Tree(Node(p,b,n1,n2,l), children) -> if (n2=true) then treeRoot else 
										(if (member p mapping)=false then (Tree(Node(p,b,n1,n2,l), (List.map (contrad_path_helper (A(p,b)::mapping)) children))) else 
										(if (findIn p mapping)=b then (Tree(Node(p,b,n1,n2,l), (map (contrad_path_helper mapping) children))) else 
										 Tree(Node(p,b,n1,true,l), children) ));; *)

(* let contrad_path treeRoot = contrad_path_helper [] treeRoot;; *)
(* 
let rec foldl func l a = match l with
	[] -> a
	| (x::xs) -> foldl func xs ((func x)::a);;
 *)

(* function for detecting contradiction on path and pushing up contradictions *)
let rec contrad_path treeRoot = match treeRoot with
	Tree(Node(p,b,n1,true,l),children,mapping) -> treeRoot
	| Tree(Node(p,b,n1,n2,l),[],mapping) -> treeRoot
	| Tree(Node(p,b,n1,n2,l),[x],mapping) -> (match (contrad_path x) with 
												Tree(Node(p1,b1,n11,true,l1),ch,assg) -> Tree(Node(p,b,n1,true,l),[contrad_path x],mapping)
												|_ -> Tree(Node(p,b,n1,n2,l),[x],mapping))
	| Tree(Node(p,b,n1,n2,l),[x1;x2],mapping) -> (match ((contrad_path x1),(contrad_path x2)) with 
													(Tree(Node(p1,b1,n11,true,l1),ch,assg), Tree(Node(p2,b2,n12,true,l2),ch2,assg2) )-> Tree(Node(p,b,n1,true,l),[(contrad_path x1);(contrad_path x2)],mapping)
													|_ -> Tree(Node(p,b,n1,n2,l),[x1;x2],mapping));;

let rec run treeRoot = (let l = select_node treeRoot in if (l=[]) then treeRoot else (run (contrad_path (step_develop (select_node treeRoot) treeRoot)) ));;

(* function for picking up truth assignments of letters from mapping *)
let rec truth_assignments x a = match x with
	[] -> a
	| ((A(L(s),b))::ys) -> truth_assignments ys ((A(L(s),b))::a)
	| (y::ys) -> truth_assignments ys a;;

(* function for finding assignments from fully developed tree *)
let rec find_assignments_helper treeRoot acc = match treeRoot with
	Tree(Node(p,b,n1,true,l),children,x) -> acc
	| Tree(Node(p,b,n1,n2,l),[],x) -> (truth_assignments x [])::acc
	| Tree(Node(p,b,n1,n2,l),[c],x) -> find_assignments_helper c acc
	| Tree(Node(p,b,n1,n2,l),[c1;c2],x) -> (find_assignments_helper c1 (find_assignments_helper c2 acc));;
	(* | Tree(Node(p,b,n1,n2,l),children,x) -> foldl find_assignments children [];; *)

let find_assignments treeRoot = find_assignments_helper (run treeRoot) [];;

let check_tautology p = (let table = run (Tree(Node(p,false,false,false,[0]),[],[])) in let ass = find_assignments_helper table [] in if (ass=[]) then Tableau(table) else Assignment(hd ass));;

let check_contradiction p = (let table = run (Tree(Node(p,true,false,false,[0]),[],[])) in let ass = find_assignments_helper table [] in if (ass=[]) then Tableau(table) else Assignment(hd ass));;

let rec valid_tableau_helper myTableau givenTableau = if (size myTableau) > (size givenTableau) then false
										else if ((size myTableau = size givenTableau) &&  (myTableau = givenTableau)) then true 
										else let l = select_node myTableau in if (l=[]) then false else valid_tableau_helper ( contrad_path (step_develop l myTableau) ) givenTableau;;

let rec valid_tableau givenTableau = match givenTableau with
	Tree(Node(p,b,n1,n2,[0]),l1,l2) -> valid_tableau_helper (Tree(Node(p,b,false,false,[0]),[],[])) givenTableau;;

let p = And(L("s"), Not(L("s")));;
let root = Tree(Node(p, true, false, false, [0]), [], []);;
let tableau = run root;;

(* EXAMPLES *)
let p = And(L("s"), Not(L("s")));;
check_tautology p;;
check_contradiction p;;
let r1 = Tree(Node(p,true,false,false,[0]), [], []);;
find_assignments r1;;
(* let r2 = Tree(Node(p,false, false, false, [0]), [], []);; *)

let p2 = Impl(L("q"),Impl(L("q"),L("p")));;
check_tautology p2;;  (* proof = Assignment [A (L "q", true); A (L "p", false)] *)
check_contradiction p2;; 	(* proof = Assignment [A (L "q", false)] *)

let pR = Impl((Impl(Not(L("p")),Not(L("q")))),(Impl(Impl(Not(L("p")),L("q")),L("p"))));;
check_contradiction pR;;		(* proof = Assignment [A (L "q", true); A (L "p", false)] *)
check_tautology pR;;
(* let tR1 = Tree(Node(pR, true, false, false, [0]), [], []);; *)
(* let tR2 = Tree(Node(pR, false, false, false, [0]), [], []);; *)

let pS = Impl( Impl (L("p"), Impl(L("q"), L("r"))), Impl( Impl(L("p"), L("q")), Impl(L("p"), L("r")) ));;
check_contradiction pS;; 		(* proof = Assignment [A (L "p", true); A (L "r", false); A (L "q", true)] *)
check_tautology pS;;
let tS1 = Tree(Node(pS, true, false, false, [0]), [], []);;
find_assignments tS1;;
(* - : assignment list list =
[[A (L "p", true); A (L "r", false); A (L "q", true)];
 [A (L "q", false); A (L "p", true)]; [A (L "p", false)]; [A (L "r", true)]] *)

let pK = Impl ( L("p"), Impl(L("q"), L("p")));;
check_tautology pK;;
check_contradiction pK;;		(* proof = Assignment [A (L "p", false)] *)
let tK1 = Tree(Node(pK, true, false, false, [0]), [], []);;
find_assignments tK1;;
(* - : assignment list list =
[[A (L "p", false)]; [A (L "q", false)]; [A (L "p", true)]] *)

let t1 = run tK1;;
let t2 = tK1;;
valid_tableau_helper t1 t2;;		(* bool = false *)
valid_tableau_helper t2 t1;;		(* bool = true *)
valid_tableau t1;;					(* bool = true *)
