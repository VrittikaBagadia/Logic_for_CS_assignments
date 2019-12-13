exception Normalised;;
exception Invalid_Input;;
exception InvalidProoftree;;
exception NotFound;;
type prop = T 
		| F 
		| L of string 	
		| Not of prop 
		| And of (prop*prop) 
		| Or of (prop*prop)
		| Impl of (prop*prop)
		| Iff of (prop*prop);;

type ndprooftree = 
		Leaf of string * prop list * prop
		| Node of string * prop list * prop * ndprooftree list| Normalised1;;

let rec member li value = match li with 
		[] -> false
		| (x::xs) -> (if (x=value) then true else (member xs value));;

let rec union li1 li2 = match li2 with
		[] -> li1
		| (x::xs) -> if (member li1 x) then (union li1 xs) else (union (x::li1) xs);;

let rec same1 l1 l2 = match l2 with
		[] -> true
		| (x::xs) -> if (member l1 x) then (same1 l1 xs) else false;;

(* returns true if 2 lists are same *)
let same l1 l2 = (same1 l1 l2) && (same1 l2 l1);;

let ruleIn tree = match tree with
		Leaf(s,g,p) -> s
		| Node(s,g,p,l) -> s;;

let propIn tree = match tree with 
		Leaf(s,l,p) -> p
		| Node(s,l,p,prooftree_list) -> p;;

let gammaIn tree = match tree with 
		Leaf(s,l,p) -> l
		| Node(s,l,p,prooftree_list) -> l;;

let rec find_rpair_helper tree = match tree with
		Leaf(s,g,p) -> []
		| Node("ImpE",g,p,[t1;t2]) -> if (((ruleIn t1) = "ImpI" && (propIn t1)=Impl((propIn t2),p)) || ((ruleIn t2) = "ImpI" && (propIn t2)=Impl((propIn t1),p))) then [tree] else (find_rpair_helper t1)@(find_rpair_helper t2)
		| Node("AndEL",g,p,[t1]) -> if (ruleIn t1) = "AndI" then [tree] else (find_rpair_helper t1)
		| Node("AndER",g,p,[t1]) -> if (ruleIn t1) = "AndI" then [tree] else (find_rpair_helper t1)
		| Node("OrE",g,p,[t1;t2;t3]) -> if ((propIn t1)=p && (propIn t2)=p && ((ruleIn t3)="OrIL"||(ruleIn t3)="OrIR")) || ((propIn t2)=p && (propIn t3)=p && ((ruleIn t1)="OrIL"||(ruleIn t1)="OrIR")) || ((propIn t1)=p && (propIn t3)=p && ((ruleIn t2)="OrIL"||(ruleIn t2)="OrIR")) then [tree] else (find_rpair_helper t1)@(find_rpair_helper t2)@(find_rpair_helper t3)
		| Node("ImpI", g, Impl(p,q), [t1]) -> find_rpair_helper t1
		| Node("AndI",g,And(p,q),[t1;t2]) -> (find_rpair_helper t1) @ (find_rpair_helper t2)
		| Node("OrIL",g,Or(p,q),[t1]) -> (find_rpair_helper t1)
		| Node("OrIR",g,Or(p,q),[t1]) -> (find_rpair_helper t1)
		| Node("NotI",g,p,[t1]) -> (find_rpair_helper t1)
		| Node("NotClassical",g,p,[t1]) -> (find_rpair_helper t1);;

let find_rpair_t tree = (let res = (find_rpair_helper tree) in if (res = []) then Normalised1 else (List.hd res));;
let find_rpair tree = (let x = (find_rpair_t tree) in if x=Normalised1 then raise Normalised else x);;

let p1 = And(L("x"), Or(L("x"),L("y")));;
let gamma = [L("x")];;
let tree1 = Node("ImpI",[], Impl(L("x"),p1), [Node("AndI",gamma,p1,[ Leaf("Hyp",gamma,L("x")) ; Node("OrIL",gamma,Or(L("x"),L("y")),[Leaf("Hyp",gamma,L("x"))]) ])]);;
(* find_rpair tree1;;		 *)
(* Exception: Normalised. *)


let rec findprooftree prooflist prop = match prooflist with
	[] -> raise NotFound
	| (x::xs) -> if (propIn x) = prop then x else findprooftree xs prop;; 

let rec inList prooflist prop = match prooflist with
	[] -> false
	| (x::xs) -> if (propIn x) = prop then true else inList xs prop;;

let rec graft_helper tree treelist gamma = match tree with
		Leaf("Hyp",g,p) -> if (inList treelist p) then (findprooftree treelist p) else tree
		| Leaf(s,g,p) -> Leaf(s,gamma,p)
		| Node("NotClassical",g,p,[t1]) -> Node("NotClassical",gamma,p,[graft_helper t1 treelist (union gamma [Not(p)])])
		| Node("ImpI",g,Impl(p,q),[t1]) -> Node("ImpI",gamma,Impl(p,q),[graft_helper t1 treelist (union gamma [p])])
		| Node("OrE",g,r,[t1;t2;t3]) -> if (((propIn t1)=r)=false) then
										(
											match (propIn t1) with Or(p,q) ->
											if (member (gammaIn t2) p) && (member (gammaIn t3) q) then Node("OrE",gamma,r,[(graft_helper t1 treelist gamma);(graft_helper t2 treelist (union gamma [p]));(graft_helper t3 treelist (union gamma [q]))])
											else if (member (gammaIn t2) q) && (member (gammaIn t3) p) then Node("OrE",gamma,r,[(graft_helper t1 treelist gamma);(graft_helper t2 treelist (union gamma [q]));(graft_helper t3 treelist (union gamma [p]))])
											else raise InvalidProoftree 
										)
										else if (((propIn t2)=r)=false) then
										(
											match (propIn t2) with Or(p,q) ->
											if (member (gammaIn t1) p) && (member (gammaIn t3) q) then Node("OrE",gamma,r,[(graft_helper t1 treelist (union gamma [p]));(graft_helper t2 treelist gamma);(graft_helper t3 treelist (union gamma [q]))])
											else if (member (gammaIn t1) q) && (member (gammaIn t3) p) then Node("OrE",gamma,r,[(graft_helper t1 treelist (union gamma [q]));(graft_helper t2 treelist gamma);(graft_helper t3 treelist (union gamma [p]))])
											else raise InvalidProoftree 
										)
										else if (((propIn t3)=r)=false) then
										(
											match (propIn t3) with Or(p,q) ->
											if (member (gammaIn t1) p) && (member (gammaIn t2) q) then Node("OrE",gamma,r,[(graft_helper t1 treelist (union gamma [p]));(graft_helper t2 treelist (union gamma [q]));(graft_helper t3 treelist gamma)])
											else if (member (gammaIn t1) q) && (member (gammaIn t2) p) then Node("OrE",gamma,r,[(graft_helper t1 treelist (union gamma [q]));(graft_helper t2 treelist (union gamma [p]));(graft_helper t3 treelist gamma)])
											else raise InvalidProoftree 
										)
										else raise InvalidProoftree
		| Node(dowale,g,r,[t1;t2]) -> Node(dowale, g, r, [(graft_helper t1 treelist gamma);(graft_helper t2 treelist gamma)])
		| Node(ekwala,g,r,[t1]) -> Node(ekwala, g, r, [(graft_helper t1 treelist gamma)]);;

let graft tree treelist = if (treelist = []) then tree else graft_helper tree treelist (gammaIn (List.hd treelist));;

let simplify_helper tree1 tree2 = graft tree1 [tree2];;

let simplify1 tree = match tree with 
		Node("AndEL",g,r,[Node("AndI",g_,And(p,q),[t1;t2])]) -> if (propIn t1)=p then t1 else if (propIn t2)=p then t2 else raise Invalid_Input
		| Node("AndER",g,r,[Node("AndI",g_,And(p,q),[t1;t2])]) -> if (propIn t1)=q then t1 else if (propIn t2)=q then t2 else raise Invalid_Input
		| Node("ImpE",g,r,[t1;t2]) -> (
										if (propIn t1)=Impl((propIn t2),r) then
										( if r=(propIn t2) then t2 else (match t1 with Node("ImpI",g_,p,[t_]) -> (simplify_helper t_ t2)))
										else
										( if r=(propIn t1) then t1 else (match t2 with Node("ImpI",g_,p,[t_]) -> (simplify_helper t_ t1)))
										)

		(* | Node("ImpE",g,r,[Node("ImpI",g_,Impl(p,q),[t1]);t2]) -> if (propIn t2)=r then t2 else (simplify_helper t1 t2) *)
		(* | Node("ImpE",g,r,[t2;Node("ImpI",g_,Impl(p,q),[t1])]) -> if (propIn t2)=r then t2 else (simplify_helper t1 t2) *)
		| Node("OrE",g,r,[Node("OrIL",g_,Or(p,q),[t1]);t2;t3]) -> if (member (gammaIn t2) p) then (simplify_helper t2 t1) else (simplify_helper t3 t1)
		| Node("OrE",g,r,[Node("OrIR",g_,Or(p,q),[t1]);t2;t3]) -> if (member (gammaIn t2) q) then (simplify_helper t2 t1) else (simplify_helper t3 t1)
		| _ -> raise Invalid_Input;;

let rec replace tree_to_replace new_tree tree = match tree with
	Leaf(s,g,p) -> if (tree = tree_to_replace) then new_tree else tree
	| Node(s,g,p,l) -> if (tree = tree_to_replace) then new_tree else Node(s,g,p,(List.map (replace tree_to_replace new_tree) l));;

let rec normalise tree = (let x = (find_rpair_t tree) in if x=Normalised1 then tree else normalise (replace x (simplify1 x) tree));;

let rec valid_ndprooftree tree = match tree with
		Leaf("Hyp", l, p) -> if (member l p) then true else false
		| Leaf("TI", l, p) -> if (p=T) then true else false
		| Node("ImpI", l, Impl(p,q), [t1]) -> (match t1 with 
												Leaf(s,l1,p1) -> if ((p1 = q) && (same l1 (union l [p]))) then true else false
												| Node(s,l1,p1,plist) -> if ((p1 = q) && (same l1 (union l [p]))) then (valid_ndprooftree t1) else false)
		| Node("ImpE",l,q,[t1;t2]) -> let p1 = (propIn t1) in let p2 = (propIn t2) in 
										if (p1 = Impl(p2,q)) then (same l (gammaIn t1)) && (same l (gammaIn t2))
										else if (p2 = Impl(p1,q)) then (same l (gammaIn t1)) && (same l (gammaIn t2))
										else false
		| Node("AndI",l,And(p,q),[t1;t2]) -> if ((same l (gammaIn t1)) && (same l (gammaIn t2)))=false then false else
											( if (propIn t1 = p) && (propIn t2 = q) then (valid_ndprooftree t1)&&(valid_ndprooftree t2)
											  else if (propIn t1 = q) && (propIn t2 = p) then (valid_ndprooftree t1)&&(valid_ndprooftree t2)
											  else false
											)
		| Node("AndEL",l,p,[t1]) -> if (same l (gammaIn t1))=false then false else (match (propIn t1) with
										And(p,q) -> (valid_ndprooftree t1)
										| _-> false)
		| Node("AndER",l,q,[t1]) -> if (same l (gammaIn t1))=false then false else (match (propIn t1) with
										And(p,q) -> (valid_ndprooftree t1)
										| _-> false)
		| Node("OrIL",l,Or(p,q),[t1]) -> if (same l (gammaIn t1))=false then false else if (propIn t1)=p then (valid_ndprooftree t1) else false
		| Node("OrIR",l,Or(p,q),[t1]) -> if (same l (gammaIn t1))=false then false else if (propIn t1)=q then (valid_ndprooftree t1) else false
		| Node("OrE",l,r,[t1;t2;t3]) -> if (propIn t1)=r && (propIn t2)=r then if (same l (gammaIn t3))=false then false else
											(match (propIn t3) with
											| Or(p,q) -> if ((same (gammaIn t1) (union l [p])) && (same (gammaIn t2) (union l [q]))) then ((valid_ndprooftree t1)&&(valid_ndprooftree t2)&&(valid_ndprooftree t3))
														 else if ((same (gammaIn t1) (union l [q])) && (same (gammaIn t2) (union l [p]))) then ((valid_ndprooftree t1)&&(valid_ndprooftree t2)&&(valid_ndprooftree t3))
														 else false
											| _ -> false)
										else if (propIn t2)=r && (propIn t3)=r then if (same l (gammaIn t1))=false then false else
											(match (propIn t1) with
											| Or(p,q) -> if ((same (gammaIn t2) (union l [p])) && (same (gammaIn t3) (union l [q]))) then ((valid_ndprooftree t1)&&(valid_ndprooftree t2)&&(valid_ndprooftree t3))
														 else if ((same (gammaIn t2) (union l [q])) && (same (gammaIn t3) (union l [p]))) then ((valid_ndprooftree t1)&&(valid_ndprooftree t2)&&(valid_ndprooftree t3))
														 else false
											| _ -> false)
										else if (propIn t1)=r && (propIn t3)=r then if (same l (gammaIn t2))=false then false else
											(match (propIn t2) with
											| Or(p,q) -> if ((same (gammaIn t1) (union l [p])) && (same (gammaIn t3) (union l [q]))) then ((valid_ndprooftree t1)&&(valid_ndprooftree t2)&&(valid_ndprooftree t3))
														 else if ((same (gammaIn t1) (union l [q])) && (same (gammaIn t3) (union l [p]))) then ((valid_ndprooftree t1)&&(valid_ndprooftree t2)&&(valid_ndprooftree t3))
														 else false
											| _ -> false)
										else false
		| Node("NotI",l,p,[t1]) -> (same l (gammaIn t1)) && ((propIn t1)=F) && (valid_ndprooftree t1)
		| Node("NotClassical",l,p,[t1]) -> (same (union l [Not(p)]) (gammaIn t1)) && ((propIn t1)=F) && (valid_ndprooftree t1)
		| _-> false;;


(* ----------  TESTING  ---------- *)

let gamma = [L("p");L("r");L("q")];;
let a = Leaf("Hyp",gamma,L("r"));;
let b = Leaf("Hyp",gamma,L("p"));;
let c = Node("OrIL",gamma,Or(L("p"),L("q")),[b]);;
(* let d = Node(gamma, L("r"), Oe(L("p"), L("q"), L("r")), c, a, a);; *)
let d = Node("OrE",gamma,L("r"),[c;a;a]);;

valid_ndprooftree d;;
let h = find_rpair d;;
let i = simplify1 h;;
valid_ndprooftree i;;
normalise d;;

let gamma = [L("p");Impl(L("p"), L("q"));L("y");Impl(L("p"), L("x"))];;
let a = Leaf("Hyp",gamma,L("p"));;
let b = Node("OrIL",gamma,Or(L("p"),L("q")),[a]);;
let c = Leaf("Hyp",gamma,L("y"));;
let d = Leaf("Hyp",L("q")::gamma, L("y"));;
let e = Node("OrE",gamma,L("y"),[b;c;d]);;		(* here is a major*)
let f = Leaf("Hyp",gamma,Impl(L("p"),L("x")));;
let g = Leaf("Hyp",gamma,L("p"));;
let h = Node("ImpE",gamma,L("x"),[f;g]);;
let i = Node("ImpI",gamma,Impl(L("y"),L("x")),[h]);;
let j = Node("ImpE",gamma,L("x"),[i;e]);;
valid_ndprooftree j;;
let ans = (normalise j);;
valid_ndprooftree (ans);;
(* find_rpair ans;; *)


