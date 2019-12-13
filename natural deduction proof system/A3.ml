open List;;
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
		| Node of string * prop list * prop * ndprooftree list;;

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

let propIn tree = match tree with 
		Leaf(s,l,p) -> p
		| Node(s,l,p,prooftree_list) -> p;;

let gammaIn tree = match tree with 
		Leaf(s,l,p) -> l
		| Node(s,l,p,prooftree_list) -> l;;

(* used in prune_helper1 - lis is list of gammas  *)
let rec foldl lis acc = match lis with
	[] -> acc
	| (x::xs) -> foldl xs (union acc x);;

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

let rec pad del tree = match tree with
		Leaf(s,gamma,p) -> Leaf(s,(union gamma del),p)
		| Node(s,gamma,p,prooftree_list) -> Node(s, (union gamma del), p, (map (pad del) prooftree_list));;

let rec prune_helper1 acc tree = match tree with
		Leaf("Hyp",gamma,p) -> [p]
		| Leaf("TI",gamma,p) -> []
		| Node(s,gamma,p,prooftree_list) -> foldl (map (prune_helper1 []) prooftree_list) acc;;

let rec intersection l1 l2 acc = match l2 with
	[] -> acc
	| (x::xs) -> if (member l1 x) then (intersection l1 xs (x::acc)) else (intersection l1 xs acc);;

exception InvalidProoftree;;

let rec prune_hepler2 gamma tree = match tree with
		Leaf(s,g,p) -> Leaf(s,gamma,p)
		| Node("NotClassical",g,p,[t1]) -> Node("NotClassical",gamma,p,[prune_hepler2 (union gamma [Not(p)]) t1])
		| Node("ImpI",g,Impl(p,q),[t1]) -> Node("ImpI",gamma,Impl(p,q),[prune_hepler2 (union gamma [p]) t1])
		| Node("OrE",g,r,[t1;t2;t3]) -> if (((propIn t1)=r)=false) then
										(
											match (propIn t1) with Or(p,q) ->
											if (member (gammaIn t2) p) && (member (gammaIn t3) q) then Node("OrE",gamma,r,[(prune_hepler2 gamma t1);(prune_hepler2 (union gamma [p]) t2);(prune_hepler2 (union gamma [q]) t3)])
											else if (member (gammaIn t2) q) && (member (gammaIn t3) p) then Node("OrE",gamma,r,[(prune_hepler2 gamma t1);(prune_hepler2 (union gamma [q]) t2);(prune_hepler2 (union gamma [p]) t3)])
											else raise InvalidProoftree 
										)
										else if (((propIn t2)=r)=false) then
										(
											match (propIn t2) with Or(p,q) ->
											if (member (gammaIn t1) p) && (member (gammaIn t3) q) then Node("OrE",gamma,r,[(prune_hepler2 (union gamma [p]) t1);(prune_hepler2 gamma t2);(prune_hepler2 (union gamma [q]) t3)])
											else if (member (gammaIn t1) q) && (member (gammaIn t3) p) then Node("OrE",gamma,r,[(prune_hepler2 (union gamma [q]) t1);(prune_hepler2 gamma t2);(prune_hepler2 (union gamma [p]) t3)])
											else raise InvalidProoftree 
										)
										else if (((propIn t3)=r)=false) then
										(
											match (propIn t3) with Or(p,q) ->
											if (member (gammaIn t1) p) && (member (gammaIn t2) q) then Node("OrE",gamma,r,[(prune_hepler2 (union gamma [p]) t1);(prune_hepler2 (union gamma [q]) t2);(prune_hepler2 gamma t3)])
											else if (member (gammaIn t1) q) && (member (gammaIn t2) p) then Node("OrE",gamma,r,[(prune_hepler2 (union gamma [q]) t1);(prune_hepler2 (union gamma [p]) t2);(prune_hepler2 gamma t3)])
											else raise InvalidProoftree 
										)
										else raise InvalidProoftree
		| Node(s,g,p,l) -> Node(s,gamma,p,(map (prune_hepler2 gamma) l));;

let prune tree = prune_hepler2 (intersection (prune_helper1 [] tree) (gammaIn tree) []) tree;;

let rec findprooftree prooflist prop = match prooflist with
	[] -> raise NotFound
	| (x::xs) -> if (propIn x) = prop then x else findprooftree xs prop;; 

let rec inList prooflist prop = match prooflist with
	[] -> false
	| (x::xs) -> if (propIn x) = prop then true else inList xs prop;;

(* inserts appropriate proof tree on all assumption nodes and given gamma on other proof trees *)
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

let graft tree treelist = if (treelist = []) then tree else graft_helper tree treelist (gammaIn (List.hd treelist));;


let p1 = And(L("x"), Or(L("x"),L("y")));;
let gamma = [L("x")];;
let tree1 = Node("ImpI",[], Impl(L("x"),p1), [Node("AndI",gamma,p1,[ Leaf("Hyp",gamma,L("x")) ; Node("OrIL",gamma,Or(L("x"),L("y")),[Leaf("Hyp",gamma,L("x"))]) ])]);;
valid_ndprooftree tree1;;			    (* bool = true *)
prune tree1;;
let padtree1 = pad [L("p");L("q")] tree1;;
valid_ndprooftree padtree1;;			(*  bool = true *)
let tree2 = prune padtree1;;

let p = Impl(L("q"),L("p"));;
let tree2 = Node("ImpI",[p],Impl(L("p"),p),[Leaf("Hyp", [p], p)]);;			
valid_ndprooftree tree2		(* : bool = false *)

let tree3 = Node("ImpI",[p],Impl(L("p"),p),[Leaf("Hyp", [L("p");p], p)]);;
valid_ndprooftree tree3 	(*  bool = true *)

let t_ = Node("ImpI", [L("p")], p, [Leaf("Hyp",[L("p");L("q")],L("p"))]);;
let graft_test_1 = graft tree3 [t_];;
