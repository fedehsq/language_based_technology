(* 
  Programming language that contains primitive operations, functions and Read and Send methods: these two operations aren't implemented, they are used only to
  do inlining.
  
  The security policy to be guaranteed is NO SEND AFTER READ.
*)

(* Language values *)
type expr =
 | CstI of int
 | CstB of bool
 | Var of string
 | Let of string * expr * expr (* string, value to associate to string, body of let *)
 | Prim of string * expr * expr
 | If of expr * expr * expr (* check, then, else *)
 | Fun of string * expr (* formal parameter, function body *)
 | Call of expr * expr (* function, actual parameter *)
 | Read of string (* file to read from*)
 | Send of expr * string;; (* operations, file to write to *)
 
(* environment is a list of pairs (ide, value) *)
type 'v env = (string * 'v) list;;

(* check if var has an associated value in the environment env *)
let rec lookup env x =
   match env with
   | []        -> failwith (x ^ " not found")
   | (y, v)::r -> if x=y then v else lookup r x;;

(* 
  Possible runtime values are integers or closures. Booleans are represented as integers (0 -> false, 1 -> true)

  type value =
  | Int of int
  | Closure of string * expr * value env;; (param, function body, declaration env)
  
*)

(* 
  The language is extended the aim of the work is to do inlining of the security automata that represent the EM. 
  The following type iexpr means "intermediate expr" and it is needed by the compiler in the backend environment, not by the programmer.
*)

type iexpr =
 | CstI of int
 | CstB of bool
 | Var of string
 | Let of string * iexpr * iexpr
 | Prim of string * iexpr * iexpr
 | If of iexpr * iexpr * iexpr
 | Fun of string * iexpr
 | Call of iexpr * iexpr
 | Read of string
 | Send of iexpr * string
 | Abort of string (* error message *)
 | GLet of iexpr * iexpr (* global var, expr. where the global var could be modified *)
 | GVar;; (* global var *)
 
 type ivalue =
 | Int of int
 | Closure of string * iexpr * ivalue env;;
 
 type gstate = GState of int;; (* global state *)
 
 (* 
  Intermediate interpreter that takes as parameters an expression to evaluate {e}, the environment {env} and the global state {g} and it will return
  a pair ({ivalue{, {global state}).
  
  This interpreter is in the backend, same as type iexpr.
 *)
 
 let rec ieval (e : iexpr) (env : ivalue env) (g : gstate) : ivalue * gstate  =
   match e with
   | CstI i -> (Int i, g)
   | CstB b -> (Int (if b then 1 else 0), g)
   | Var x  -> (lookup env x, g)
   | Prim(ope, e1, e2) ->
     let (v1, g') = ieval e1 env g in
     let (v2, g'') = ieval e2 env g' in 
     begin
     match (ope, v1, v2) with
     | ("*", Int i1, Int i2) -> (Int (i1 * i2), g'')
     | ("+", Int i1, Int i2) -> (Int (i1 + i2), g'')
     | ("-", Int i1, Int i2) -> (Int (i1 - i2), g'')
     | ("=", Int i1, Int i2) -> (Int (if i1 = i2 then 1 else 0), g'')
     | ("<", Int i1, Int i2) -> (Int (if i1 < i2 then 1 else 0), g'')
     |  _ -> failwith "unknown primitive or wrong type"
     end
   | Let(x, eRhs, letBody) ->
     let (xVal, g') = ieval eRhs env g in
     let letEnv = (x, xVal) :: env in
     ieval letBody letEnv g'
   | If(e1, e2, e3) ->
     begin
     match ieval e1 env g with
     | (Int 0, g') -> ieval e3 env g'
     | (Int _, g') -> ieval e2 env g'
     | _     -> failwith "eval If"
     end
   | Fun(x,fBody) -> (Closure(x, fBody, env), g)
   | Call(eFun, eArg) ->
     let (fClosure, _) = ieval eFun env g in
     begin
     match fClosure with
     | Closure (x, fBody, fDeclEnv) ->
       let (xVal, g') = ieval eArg env g in
       let fBodyEnv = (x, xVal) :: fDeclEnv
       in ieval fBody fBodyEnv g'
     | _ -> failwith "eval Call: not a function"
     end
   | Read(_) -> (Int 0, g)
   | Send(x, _) -> let (_, g') = ieval x env g in (Int 1, g')
   | Abort msg -> failwith msg
   | GLet(letVal, letBody) -> let (xVal, _) = ieval letVal env g 
   								in begin match xVal with 
   									| Int(i) -> ieval letBody env (GState i)
   									| _ -> failwith "eval Call: not an integer"
   								end
   | GVar -> begin match g with
   			 	    | GState(i) -> (Int(i), g)
   			     end;;
   
   
type state = int;;
type symbol = iexpr;;

(*   
  Definition of the security automata 

  (s0, s1, delta, msg) 
*)
type nfa = state * state * (state * symbol -> state option) * string;;

(* type 'a option = None | Some of 'a;; *)

(* Inlining of the security automata into the expression e *)
let inlineNfa (s0, s1, delta, msg) e = 
	If(Prim("=", GVar, CstI s0), 
		begin match (delta(s0,e)) with
			| Some s -> GLet(CstI s, e)
			| None -> Abort(msg)
		end, 
		begin match (delta(s1,e)) with 
			| Some s -> GLet(CstI s, e)
			| None -> Abort(msg)
		end)

(* Compile a specific program with the security automata, doing inlining thanks to inlineNfa function *)
let rec comp (sa : nfa) (p : expr) : iexpr = 
  match p with
	| CstI i -> CstI i
	| CstB b -> CstB b
	| Var x -> inlineNfa sa (Var x)
	| Prim(ope, e1, e2) -> inlineNfa sa (Prim(ope, (comp sa e1), (comp sa e2)))
	| Let(x, e1, e2) -> Let(x, (comp sa e1), (comp sa e2))
	| If(e1, e2, e3) -> inlineNfa sa (If((comp sa e1), (comp sa e2), (comp sa e3)))
	| Fun(x, e) -> Fun(x, (comp sa e))
	| Call(f, a) -> inlineNfa sa (Call((comp sa f), (comp sa a)))
	| Read s -> inlineNfa sa (Read s)
	| Send(e, s) -> inlineNfa sa (Send((comp sa e), s));;

(* Interpreter *)
let eval (e : expr) (env : ivalue env) (sa : nfa) : ivalue = 
  match sa with 
	| (initialState, _, _, _) -> let (result, _) = ieval (comp sa e) env (GState initialState) in result;;

(* Transition function of the security automata.
   This function expresses the security policy.
*)
let myDelta (s, e) = 
  match (s, e) with
	| (0, Read _) -> Some 1
	| (0, _) -> Some 0
	| (1, Send(_, _)) -> None 
	| (1, _) -> Some 1
	| _ -> None;;
	
(* Security automata *)
let mySa : nfa = (0, 1, myDelta, "send after read detected");;
  
(**
  This is what happens in the backend when the compiler compiles the following code, called safeProgram.
  
let x = 0 in send(x, file1)

compiled into
g = 0;
let x = 0 in (if g = 0 then g := 0; send(x, file1)
              else abort)
*)
let safeProgram : expr = Let("x", CstI 0, Send(Var "x", "file1"));;
eval safeProgram [] mySa;; 

(**
  This is what happens in the backend when the compiler compiles the following code, called unsafeProgram.
  
let x = read(file2) in send(x, file1)

compiled into
g = 0;
let x = (if g = 0 then g := 1; read(file2)
         else abort) in (if g = 0 then g := 0; send(x, file1)
                         else abort);
*)
let unsafeProgram : expr = Let("x", Read("file2"), Send(Var "x", "file1"));;
eval unsafeProgram [] mySa;;
