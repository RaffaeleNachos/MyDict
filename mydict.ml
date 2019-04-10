type ide = string;;

type exp = (*tipi di dato*)
	| Eint of int 
	| Estring of string
	| Ebool of bool 
	| Den of ide 
	| Prod of exp * exp 
	| Sum of exp * exp 
	| Diff of exp * exp 
	| Eq of exp * exp 
	| Minus of exp 
	| IsZero of exp 
	| Or of exp * exp 
	| And of exp * exp 
	| Not of exp 
	| Ifthenelse of exp * exp * exp 
	| Let of ide * exp * exp (*nomefun,corpo,bodylet*)
	| Fun of ide * exp 
	| FunCall of exp * exp 
	| Letrec of ide * ide * exp * exp (*nomefun,parametro,corpo,bodylet*)
	| Dict of (ide * exp) list  (*definisco il dizionario come una lista di coppie identificatore valore*)
	| SelectDict of exp * ide (* dizionario, label *)
	| AddDict of exp * ide * exp (* dict, label, valore*)
	| UpdateDict of exp * ide * exp (* dict, label, nuovo valore*)
	| RmDict of exp * ide (* dict, label *)
	| ClearDict of exp (* dict *)
	| ApplyOverDict of exp * exp;; (* funzione dict*)

(*ambiente polimorfo*)
type 't env = (string * 't) list;; (*contiene valori*)

let emptyenv (x : 't) = [("",x)];;

let rec applyenv ((r : 't env), (i : ide)) = match r with
	| [(_,e)] -> e
	| (i1,e1)::xs -> if i=i1 then e1 else applyenv (xs,i)
	| [] -> failwith ("not present in this amb");;

let bind (r : 't env) (i : ide) (v : 't) = (i,v)::r;;

(*tipi esprimibili*)
type evT = 
	| Int of int 
	| String of string
	| Bool of bool 
	| Unbound 
	| FunVal of evFun 
	| DictVal of (ide * evT) list
	| RecFunVal of ide * evFun (*nomefun,par,corpo,ambiente dove è stata dichiarata*)
and evFun = ide * exp * evT env;;

let typecheck (s : string) (v : evT) : bool = match s with
	| "int" -> (match v with
					| Int(_) -> true 
					| _ -> false)
	| "string" -> (match v with
					| String(_) -> true 
					| _ -> false)
	| "bool" -> (match v with
					|Bool(_) -> true 
					| _ -> false) 
	| _ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
			(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
			(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
			(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
			(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   		Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
			Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
			(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
			(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
			| Bool(true) -> Bool(false) 
			| Bool(false) -> Bool(true))
	else failwith("Type error");;

(* aux fun per dict *)

let rec lookupdict dict label =
	match dict with
		| [] -> failwith("not found in dict")
		| (x,y)::xs -> if (label = x) then y else lookupdict xs label;;

let rec member lista label =
	match lista with
		| [] -> false
		| (x,y)::xs -> if (label = x) then true else member xs label;;
	
let rec removeDup dict =
	match dict with
		| [] -> []
		| (x,y)::xs -> if (member xs x) then removeDup xs else (x,y)::removeDup xs;;

let rec updatelab lista label nval =
	match lista with
		| [] -> []
		| (x,y)::xs -> if (label = x) then (x,nval)::updatelab xs label nval else (x,y)::updatelab xs label nval;;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	| Eint n -> Int n 
	| Estring s -> String s
	| Ebool b -> Bool b 
	| IsZero a -> iszero (eval a r) 
	| Den i -> applyenv (r,i) 
	| Eq(a, b) -> eq (eval a r) (eval b r) 
	| Prod(a, b) -> prod (eval a r) (eval b r) 
	| Sum(a, b) -> sum (eval a r) (eval b r) 
	| Diff(a, b) -> diff (eval a r) (eval b r) 
	| Minus a -> minus (eval a r) 
	| And(a, b) -> et (eval a r) (eval b r) 
	| Or(a, b) -> vel (eval a r) (eval b r) 
	| Not a -> non (eval a r) 
	| Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") 
	| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) 
	| Fun(i, a) -> FunVal(i, a, r) (*il valore di una funzione è una chiusura*) 
	| FunCall(f, eArg) -> (*scoping statico*)
		let fClosure = (eval f r) in
			(match fClosure with
				| FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) 
				| RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in (*valuto il parametro attuale nell'ambiente del chiamante*)
						let rEnv = (bind fDecEnv g fClosure) in (*nuovo ambiente esteso con il binding tra il nome della funzione (g) e la sua chiusura ricorsiva*)
							let aEnv = (bind rEnv arg aVal) in (*nuovo ambiente contenente la chiusura ricorsiva esteso con il binding tra il parametro formale e l'ambiente dove è valutato il parametro attuale*)
								eval fBody aEnv (*valuto il body del let nell'ultimo ambiente calcolato*)
				| _ -> failwith("non functional value")) 
	| Letrec(f, i, fBody, letBody) ->
        		let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                								eval letBody r1
                								(*valuto il body del let in un ambiente r1 che è l'ambiente dove prima 
                								ho fatto il binding tra il nome della funzione e la sua chiusura RICORSIVA*)
	| Dict(dict) -> let thisdict = removeDup dict 
										in DictVal(evalDict thisdict r)
	| SelectDict(thisdict,lab) -> 
		(match (eval thisdict r) with
			| DictVal(mydict) -> lookupdict mydict lab
			| _ -> failwith("wrong value"))
	| AddDict(thisdict,lab,valx) ->
		(match (eval thisdict r) with
			| DictVal(mydict) -> if (member mydict lab) then failwith("etichetta già presente") else DictVal((lab,(eval valx r))::mydict)
			| _ -> failwith("wrong value"))
	| UpdateDict(thisdict,lab,newval) -> 
		(match (eval thisdict r) with
			| DictVal(mydict) -> if (member mydict lab) then DictVal(updatelab mydict lab (eval newval r)) else failwith("etichetta non presente")
			| _ -> failwith("wrong value"))
	| RmDict(thisdict,lab) ->
		(match (eval thisdict r) with
			| DictVal(mydict) -> DictVal(removeElem mydict lab)
			| _ -> failwith("wrong value"))
	| ClearDict(thisdict) ->
		(match (eval thisdict r) with
			| DictVal(mydict) -> DictVal([])
			| _ -> failwith("wrong value"))
	| ApplyOverDict(funx,thisdict) ->
		(match (eval thisdict r) with
			| DictVal(mydict) -> DictVal(applyFun mydict funx r)
			| _ -> failwith("wrong value"))
	and evalDict (dict : (ide * exp) list) (r : evT env) = 
				(match dict with 
					| [] -> []
					| (x,y)::xs -> (x, eval y r) :: evalDict xs r)
	and removeElem (dict : (ide * evT) list) (lab : ide) = 
				(match dict with
					| [] -> []
					| (x,y)::xs -> if (lab = x) then (removeElem xs lab) else (x,y)::(removeElem xs lab))
	and applyFun (dict : (ide * evT) list) (funx : exp) (r : evT env) =
				(match dict with
					| [] -> []
					| (x,y)::xs ->  (x, (dictFunCall funx y r) )::(applyFun xs funx r))
	and dictFunCall (funx : exp) (y : evT) (r : evT env) =
				let fClosure = (eval funx r) in
					(match fClosure with
						| FunVal(arg, fBody, fDecEnv) -> 
							eval fBody (bind fDecEnv arg y) 
						| RecFunVal(g, (arg, fBody, fDecEnv)) -> (* non valuto il parametro attuale nell'ambiente del chiamante perchè già un evT*)
								let rEnv = (bind fDecEnv g fClosure) in (*nuovo ambiente esteso con il binding tra il nome della funzione (g) e la sua chiusura ricorsiva*)
									let aEnv = (bind rEnv arg y) in (*nuovo ambiente contenente la chiusura ricorsiva esteso con il binding tra il parametro formale e l'ambiente dove è valutato il parametro attuale*)
										eval fBody aEnv (*valuto il body del let nell'ultimo ambiente calcolato*)
						| _ -> failwith("non functional value"));;

(* ============================= * test interprete base * ============================= *)

(* definisco ambiente vuoto*)
let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 1)), Eint 3);;

eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;

eval e2 env0;;

let e3 = Letrec("fact","n",Ifthenelse(Eq(Den("n"),Eint(0)),Eint(1),Prod(Den("n"),FunCall(Den("fact"),Diff(Den("n"),Eint(1))))),FunCall(Den("fact"),Eint(3)));;

eval e3 env0;;

(* ============================= * test dizionario * ============================= *)

let my_empty_dict = Dict([]);;

let my_dict = Dict([("name", Estring "raffaele");("matricola", Eint 549220)]);;

eval my_dict env0;;

(* nel caso di etichette uguali nella creazione viene tenuta l'ultima definizione *)
let my_dictwithcopies = Dict([("name", Estring "raffaele");("matricola", Eint 549220);("matricola", Eint 549222)]);;

eval my_dictwithcopies env0;;

let savemyname = SelectDict(my_dict,"name");;

eval savemyname env0;;

let savemyfreshman = SelectDict(my_dict,"matricola");;

eval savemyfreshman env0;;

let my_dict1 = AddDict(my_dict,"eta'", Eint 22);;

eval my_dict1 env0;;

(* aggiungo una etichetta già presente *)

let my_dictupdate = AddDict(my_dict,"name", Estring "francesco");;

(* exception *)
eval my_dictupdate env0;;

let my_dictupdate = UpdateDict(my_dict,"name", Estring "francesco");;

eval my_dictupdate env0;;

(* aggiorno una etichetta non presente *)
let my_dictupdate = UpdateDict(my_dict,"cognome", Estring "rossi");;

(* exception *)
eval my_dictupdate env0;;

let my_dict2 = RmDict(my_dict1, "name");;

eval my_dict2 env0;;

let my_dict3 = ClearDict(my_dict2);;

eval my_dict3 env0;;

let funtodict = ApplyOverDict(Fun("x", Sum(Den "x", Eint 1)),my_dict2);;

eval funtodict env0;;

(* Type Error per ApplyOverDict su tipi errati *)
let numstrdict = Dict([("name", Estring "raffaele");("matricola", Eint 549220)]);;

eval numstrdict env0;;

let typerr = ApplyOverDict(Fun("x", Sum(Den "x", Eint 1)),numstrdict);;

(* Exception *)
eval typerr env0;;