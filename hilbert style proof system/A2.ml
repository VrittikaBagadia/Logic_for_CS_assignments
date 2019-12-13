exception NotFound;;
type prop = T 
		| F 
		| L of string 	
		| Not of prop 
		| And of (prop*prop) 
		| Or of (prop*prop)
		| Impl of (prop*prop)
		| Iff of (prop*prop);;

type hprooftree = 
		Leaf of prop list * prop * string
		| MP of prop list * prop * hprooftree * hprooftree;;

let rec member li value = match li with 
		[] -> false
		| (x::xs) -> (if (x=value) then true else (member xs value));;

let rec union li1 li2 = match li2 with
		[] -> li1
		| (x::xs) -> if (member li1 x) then (union li1 xs) else (union (x::li1) xs);;

let rec same1 l1 l2 = match l2 with
		[] -> true
		| (x::xs) -> if (member l1 x) then (same1 l1 xs) else false;;

let same l1 l2 = (same1 l1 l2) && (same1 l2 l1);;

let rec remove_prop_from_gamma gamma prop acc = match gamma with 
		[] -> raise NotFound
		| x::xs -> if (x=prop) then acc@xs else (remove_prop_from_gamma xs prop (x::acc));;

(* root prop p and leaves p1 p2  *)
let mpprops p p1 p2 = 
	if (p1=Impl(p2,p)) then true else if (p2=Impl(p1,p)) then true else false;;

let rec valid_hprooftree tree = match tree with
		Leaf(l,p,s) -> 
		(
			match s with
			"A" -> (member l p)
			| "K" -> (match p with 
						Impl(p1,Impl(q1,p2)) -> if (p2=p1) then true else false
						|_ -> false
					)
			| "S" -> (match p with
						Impl( Impl(p1,Impl(q1,r1)), Impl( Impl(p2,q2), Impl(p3,r2))) -> if ((p1=p2) && (p1=p3) && (q1=q2) && (r1=r2)) then true else false
						|_-> false	
					)
			| "R" -> ( match p with
						Impl( Impl(Not(p1),Not(q1)), Impl(Impl(Not(p2),q2), p3)) -> if ((p1=p2) && (p1=p3) && (q1=q2)) then true else false
						|_ -> false
					)
		)
		| MP(l,p,t1,t2) -> 
		(
			match (t1,t2) with
			(Leaf(l1,p1,s1), Leaf(l2,p2,s2)) -> if ((same l1 l) && (same l2 l)) then (mpprops p p1 p2) && (valid_hprooftree t2) && (valid_hprooftree t1)
												else false
			|(Leaf(l1,p1,s), MP(l2,p2,tr1,tr2)) -> if ((same l1 l) && (same l2 l)) then (mpprops p p1 p2) && (valid_hprooftree t2) && (valid_hprooftree t1)
												else false
			|(MP(l1,p1,tr1,tr2), Leaf(l2,p2,s)) -> if ((same l1 l) && (same l2 l)) then (mpprops p p1 p2) && (valid_hprooftree t2) && (valid_hprooftree t1)
												else false
			|(MP(l1,p1,tre1,tre2), MP(l2,p2,tr1,tr2)) -> if ((same l1 l) && (same l2 l)) then (mpprops p p1 p2) && (valid_hprooftree t2) && (valid_hprooftree t1)
												else false
		);;

let rec pad tree props = match tree with 
		Leaf(l,p,s) -> Leaf((union l props),p,s)
		| MP(l,p,t1,t2) -> MP((union l props), p, (pad t1 props), (pad t2 props));;

(* finds the finite subset by looking at all assumption nodes *)
let rec prune_helper1 tree acc = match tree with 
		Leaf(l,p,"A") -> if (member acc p) then acc else (p::acc)
		| Leaf(l,p,s) -> acc
		| MP(l,p,t1,t2) -> prune_helper1 t1 (prune_helper1 t2 acc);;

(* replaces all gamma by a new given gamma *)
let rec replace_gamma tree del = match tree with
		Leaf(l,p,s) -> Leaf(del,p,s)
		| MP(l,p,t1,t2) -> MP(del,p,(replace_gamma t1 del),(replace_gamma t2 del));;

let rec prune tree = replace_gamma tree (prune_helper1 tree []);;

(* finds proof tree corresponding to a prop from a list of proof trees *)
let rec find_prooftree prop treelist = match treelist with
		[] -> raise NotFound
		| Leaf(l,p,s)::xs -> if (p=prop) then Leaf(l,p,s) else (find_prooftree prop xs)
		| MP(l,p,t1,t2)::xs -> if (p=prop) then MP(l,p,t1,t2) else (find_prooftree prop xs);;

(* finds gamma for non assumption proof trees *)
let graft_helper treelist = match treelist with
		[] -> []
		| Leaf(l,p,s)::xs -> l
		| MP(l,p,t1,t2)::xs -> l;;

(* inserts appropriate proof tree on all assumption nodes and given gamma on other proof trees *)
let rec graft_helper2 tree treelist gamma = match tree with
		Leaf(l,p,"A") -> find_prooftree p treelist
		| Leaf(l,p,s) -> Leaf(gamma, p, s)
		| MP(l,p,t1,t2) -> MP(gamma,p,(graft_helper2 t1 treelist gamma),(graft_helper2 t2 treelist gamma));;

let rec graft tree treelist = graft_helper2 tree treelist (graft_helper treelist);;

(* when p = q *)
let dedthm_heper2 tree p gamma = 
	MP(gamma,Impl(p,p),
		Leaf(gamma,Impl(p,Impl(L("A") ,p)),"K"), 
		MP(gamma, Impl(Impl(p,Impl(L("A") ,p)),Impl(p,p)), 
			Leaf(gamma,Impl(p,Impl(Impl( L("A"),p),p)),"K"),
			Leaf(gamma, (Impl( (Impl( p , Impl( Impl(L("A") ,p), p) )) , (Impl( Impl(p,Impl(L("A"),p)), Impl(p,p))) )), "S")	
	));;

let propIn tree = match tree with
	Leaf(g,p,s) -> p
	| MP(g,p,t1,t2) -> p;;

let gammaIn tree = match tree with
	Leaf(g,p,s) -> g
	| MP(g,p,t1,t2) -> g;;

let rightTreeinMP tree1 tree2 q = match (tree1, tree2) with
		(Leaf(g1,p1,s1),Leaf(g2,p2,s2)) -> if p1=Impl(p2,q) then tree2 else tree1
		|(Leaf(g1,p1,s1),MP(g2,p2,t1,t2)) -> if p1=Impl(p2,q) then tree2 else tree1
		|(MP(g1,p1,t1,t2),Leaf(g2,p2,s2)) -> if p1=Impl(p2,q) then tree2 else tree1
		|(MP(g1,p1,t1,t2),MP(g2,p2,t12,t22)) -> if p1=Impl(p2,q) then tree2 else tree1;;

let rec dedthm_heper1 tree p gamma = match tree with 
	Leaf(gammaold, q, s) ->	if (q=p) then (dedthm_heper2 tree p gamma) else (MP(gamma,Impl(p,q), Leaf(gamma,(Impl(q,Impl(p,q))),"K") , Leaf(gamma,q,s)))
	| MP(gammaold, q, t1, t2) -> if (q=p) then dedthm_heper2 tree p gamma else (
		if (t2 = rightTreeinMP t1 t2 q) then ((let r = (propIn t2) in (
		MP(gamma, Impl(p,q), MP(gamma, Impl(Impl(p,r),Impl(p,q)), (Leaf(gamma, Impl( Impl(p,Impl(r,q)) , Impl( Impl(p,r) , Impl(p,q) ) ) , "S")), (dedthm_heper1 t1 p gamma) ), (dedthm_heper1 t2 p gamma))
	)))
	else
	(let r = (propIn t1) in (
		MP(gamma, Impl(p,q), MP(gamma, Impl(Impl(p,r),Impl(p,q)), (Leaf(gamma, Impl( Impl(p,Impl(r,q)) , Impl( Impl(p,r) , Impl(p,q) ) ) , "S")), (dedthm_heper1 t2 p gamma) ), (dedthm_heper1 t1 p gamma))
	))
	);;

let dedthm p tree = dedthm_heper1 tree p (remove_prop_from_gamma (gammaIn tree) p []);;

(* EXAMPLES *)

let prop1 = Impl(L("p"),Impl(L("q"),L("r")));;
let prop2 = Impl(Impl(L("p"),L("q")),Impl(L("p"),L("r")));;
let tree1S = Leaf([], Impl(prop1,prop2), "S");;
let tree2S = Leaf([], Impl(prop1,prop2), "K");;
valid_hprooftree tree1S;;   (* bool = true *)
valid_hprooftree tree2S;;	(* bool = false *)

let tree1A = Leaf( [L("p")], L("p"), "A");;
let tree2A = Leaf( [L("p")], L("q"), "A");;
valid_hprooftree tree1A;;   (* bool = true *)
valid_hprooftree tree2A;;	(* bool = false *)

let treeMP1 = MP([], L("q"), Leaf([Impl(L("p"),L("q"))], Impl(L("p"),L("q")), "A") ,tree1A);;
valid_hprooftree treeMP1;;		(* bool = false *)

let gamma = [Impl(L("p"),L("q"));L("p")];;
let t1 = Leaf(gamma, Impl(L("p"),L("q")), "A");;
let t2 = Leaf( gamma, L("p"), "A");;
let treeMP2 = MP(gamma,L("q"),t1,t2);;
valid_hprooftree treeMP2;;		 (* bool = true *)

let treeMP3 = MP(gamma,L("q"),t2,t1);;
valid_hprooftree treeMP3;;		 (* bool = true *)


valid_hprooftree (Leaf(gamma, Impl(Impl(Not(prop1),Not(prop2)),Impl(Impl(Not(prop1),prop2), prop1)), "R"));;

valid_hprooftree (Leaf([],Impl(L("p"),Impl(L("q"),L("p"))),"K"));;    (* bool = true *)

let tree1 = Leaf([],L("p"),"A");;
valid_hprooftree tree1;;			(* bool = false *)
let padtree1 = pad tree1 [L("p");L("q")];;
valid_hprooftree padtree1;;			(*  bool = true *)
let tree2 = prune padtree1;;


let ded_test1 = dedthm (L("p")) (Leaf([L("p");L("q")],L("q"),"A"));;
let pIMPp = dedthm (L("p")) (Leaf([L("p");L("q")], L("p"), "A"));;
valid_hprooftree pIMPp;;	   	 (* bool = true *)	

let tree1 = Leaf([Impl(L("p"),L("p"))], Impl(L("p"),L("p")), "A");;
let graft_test = graft tree1 [pIMPp];;
