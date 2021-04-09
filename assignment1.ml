(* ---- DECLARATION OF TYPES ---- *)

(* security permissions *)
type permission = 
  | None
  | Read
  | Write
  | Permission of permission * permission;; (* list of permission *)

(* expressions of language *)
type exp = 
  | Enone
  | Eint of int
  | Ebool of bool
  | Estring of string
  | Elist of exp (* Eitem or None*)
  | Eitem of exp * exp (* element and something other or None *)
  | Var of string
  | Plus of exp * exp (* + of Int * Int *)
  | Minus of exp * exp (* - of Int * Int *)
  | Mul of exp * exp (* * of Int * Int *)
  | Div of exp * exp (* / of Int * Int *)
  | Greater of exp * exp (* e1 > e2 *)
  | Minor of exp * exp (* e1 < e2 *)
  | Equals of exp * exp (* e1 == e2 *)
  | Concat of exp * exp (* s1 ^ s2 *)
  | Cons of exp * exp (* x::xs * *)
  | IfThenElse of exp * exp * exp (* "guardia", then, else *)
  (* The following builder permits to give a name to an exp *)
  | LetIn of string * exp * exp  (* ide, value to associate to ide, body of let 
  i.e y (ide) = 5 (exp) in y + x (exp)  *)
  (* Fun is anonymous => it hasn't a name! 'ide' is the formal parameter!
  i.e f(x) = x + 1  => x is the formal parameter, x + 1 is the body *)
  (* formal parameter with function body and permissions *)
  | Fun of string * exp * permission  
  (* name to assign to fun exp, new permission(s), 
  exp in which evaluate es: let f x = x + x in f 5;; *)
  | EnableIn of string * exp * permission * exp 
  (* name to assign to fun exp, permission(s) to remove, 
  exp in which evaluate es: let f x = x + x in f 5;; *)
  | DisableIn of string * exp * permission * exp 
  | Call of exp * exp;; (* Fun with acutal parameter *)

(* I have defined a new syntactic type for the primitive construct that checks
the permissions of functions rather than inserting it in exp 
because the idea is that in this way it is invisible to the programmer.*)
type iexp = 
  | Check of exp;; (* exp must be Fun *)

(* environment is a couple list of ide with their value *)
type 'v env = (string * 'v)list;; 

(* language values *)
type value =
  | None
  | Int of int
  | Bool of bool
  | String of string
  | List of value (* List(Item(Eint 5, None)) *)
  | Item of value * value (* Item(Eint 5, None)) => List item or tuple!*)
  | Closure of string * exp * value env;; (* formal param, body, env *)

(* ---- DECLARATION OF FUNCTIONS ---- *)

(* associate var with value to env *)
let bind (var: string) (value: value) (env: 'v env) =
  (var, value)::env;;

(* It checks if var has a associated value in the environment env  *)
let rec lookup (env: 'v env) (var: string) : value = 
  match env with
  | [] -> failwith(var ^ " not found")
  | (ide, value)::envs -> if (ide = var) then value else lookup envs var;;

(* basic operations *)
let calculator (op: string) (x: value) (y: value): value =
    begin match (op, x, y) with
    | ("+", Int x, Int y) -> Int (x + y)
    | ("-", Int x, Int y) -> Int (x - y)
    | ("*", Int x, Int y) -> Int (x * y)
    | ("/", Int x, Int y) -> Int (x / y)
    | (">", Int x, Int y) -> Bool (x > y)
    | ("<", Int x, Int y) -> Bool (x < y)
    | ("==", Int x, Int y) -> Bool (x = y)
    | ("==", Bool x, Bool y) -> Bool (x = y)
    | ("==", String x, String y) -> Bool (x = y)
    | ("^", String x, String y) -> String (x ^ y)
    | ("::", _x, Item(y, z)) -> (* check if x will be inserted as head *)
      begin match x with
      | Item _ -> failwith("Not a :: operation!")
      | None -> failwith("Not a :: operation!")
      | _x -> Item(x, Item (y, z))
      end
    | (_, _, _) -> failwith("Not yet implemented")
    end;;

(* given a permission needed from a function, check if it can be granted 
matching them with the global ones *)
let rec check_one_permission (cp: permission) (gp: permission) : bool =
  match gp with
  | Permission(p, pgs) ->
    if p = cp then true else check_one_permission cp pgs
  | p -> if cp = p then true else false;;
    
(* given the permissions needed from a function, check if them can be granted 
  matching them with the global ones *)
let rec check_all_permission (cp: permission) (gp: permission) : bool =
  match cp with
  (* Needed more than one permission by the function *)
  | Permission(cp, cps) ->
    (* check if the current requested permission is granted *)
    if check_one_permission cp gp then 
      check_all_permission cps gp 
    else 
      false
  | p -> if p = None then true else check_one_permission p gp;;

(* given a particular permission, remove it matching it with the global ones *)
let rec remove_one_permission(cp: permission) (gp: permission) : permission =
  match gp with
  | Permission(p, pgs) ->
    if p = cp then pgs else Permission(pgs, remove_one_permission cp pgs)
  | p -> if p = cp then None else p


(* given the permissions needed, check if them can be granted 
  matching them with the global ones *)
let rec remove_permission (cp: permission) (gp: permission) : permission =
  match cp with
  (* Needed more than one permission by the function *)
  | Permission(cp, cps) ->
    remove_permission (remove_one_permission cp gp) cps
  | p -> remove_one_permission p gp (* devo matchare p con il primo di gp *)

(* error message for missed permissions *)
let print_error (cp: permission) (gp: permission) : string = 
  let rec print_error (cp: permission) (fail_message : string) : string =
    match cp with
    | None -> ""
    | Read -> fail_message ^ "Read can't be executed"
    | Write -> fail_message ^ "Write can't be executed"
    | Permission(p, ps) ->
      begin match p with
      | Read ->
        if not(check_one_permission Read gp) then
          print_error ps ("Read, " ^ fail_message)
        else 
          print_error ps fail_message
      | Write ->
        if not(check_one_permission Write gp) then
          print_error ps ("Write, " ^ fail_message)
        else 
          print_error ps fail_message
      | _ ->  print_error ps fail_message
      end
    in print_error cp "";;

(* 
represents the security manager who checks whether the permissions
requested by the function are granted; 
in the event of a positive outcome, it returns the closure, 
otherwise it raises an exception.
*)
let ieval (iexp: iexp) (gp: permission) (env: 'v env): value =
  match iexp with
  | Check(exp) -> 
    begin match exp with
    | Fun(var, body, p) -> 
      if check_all_permission p gp then 
        Closure(var, body, env) 
      else 
        failwith(print_error p gp)
    | _ -> failwith("Type error")
    end;;

  (* for debugging *)
  let rec print_permission (p: permission) : unit =
  match p with
  | Write -> print_string("Write")
  | Read -> print_string("Read")
  | None -> print_string("None")
  | Permission(cp, cps) -> 
    begin match cp with
    | Write -> print_string("Write"); print_permission cps
    | Read -> print_string("Read"); print_permission cps
    | None -> print_string("None"); print_permission cps
    | _ -> print_permission cps
  end;;

(* interpreter *)
let rec eval (exp: exp) (env: 'v env) (gp: permission): value = match exp with
  | Enone -> None
  | Eint x -> Int x
  | Ebool b -> Bool b
  | Estring s -> String s
  | Elist l ->
    begin match eval l env gp with
    | Item(x, y) -> List(Item(x, y))
    | None -> List(None)
    | _ -> failwith("Wrong List declaration")
    end
  | Eitem(x, y) -> (* check if 2nd elem is Item or Enone!*)
    begin match y with 
    | Enone -> Item(eval x env gp, eval y env gp)
    | Eitem(_, _) -> Item(eval x env gp, eval y env gp)
    | _ -> failwith("Wrong Item declarations")
    end
  | Var(x) -> lookup env x
  | IfThenElse(guardia, t, e) -> 
      begin match eval guardia env gp with
      | Bool b -> if b then eval t env gp else eval e env gp
      | _ -> failwith("not a valid statement")
      end 
  | Plus(x, y) -> calculator "+" (eval x env gp) (eval y env gp)
  | Minus(x, y) -> calculator "-" (eval x env gp) (eval y env gp)
  | Mul(x, y) -> calculator "*" (eval x env gp) (eval y env gp)
  | Div(x, y) -> calculator "/" (eval x env gp) (eval y env gp)
  | Greater(x, y) -> calculator ">" (eval x env gp) (eval y env gp)
  | Minor(x, y) -> calculator "<" (eval x env gp) (eval y env gp)
  | Equals(x, y) -> calculator "==" (eval x env gp) (eval y env gp)
  | Concat(x, y) -> calculator "^" (eval x env gp) (eval y env gp)
  | Cons(x, xs) -> calculator "::" (eval x env gp) (eval xs env gp)
  | LetIn(ide, value, body) ->
      (* "calculate" value ... *)
      let v = eval value env gp in 
      (* ... and bind this value to the ide for creating new env 
      (new value on the stack).. *)
      let new_env = bind ide v env in
      (* ... and use it in the body *)
      eval body new_env gp
  (* define functions*)
  (* ---- WARNING ----
      var isn't the name of function! It is the argument, 
      the formal parameter of function!
      i.e f (x) = x + 1   =>  var is x! Not the name of function! 
      For naming a function we must use the builder LetIn! 
      *)
  | Fun(_, _, _) -> ieval (Check(exp)) gp env (* security manager *)
  | EnableIn(ide, f, p, body) -> 
    let ep = Permission(gp, p) in (* extend gloabl permissions *)
    let v = eval f env ep in (* evaluate f with new global permissions *)
    begin match v with 
    (* check if v is a closure, bind ide to f,
       and use the new env with extended perms in the body *)
    | Closure(_, _, _) -> eval body (bind ide v env) ep
    | _ -> failwith("Type error")
    end
  | DisableIn(ide, f, p, body) -> 
    let ep = remove_permission p gp in (* restrict global permissions *)
    let v = eval f env ep in (*  evaluate f with restricted global permissions *)
    begin match v with 
    (* check if v is a closure, bind ide to f,
       and use the new env with restricted perms in the body *)
    | Closure(_, _, _) -> eval body (bind ide v env) ep
    | _ -> failwith("Type error")
    end
  (* Call a function f with p actual parameter i.e f(x) = x + 1 => f(5) = 6 *)
  | Call(f, actual_param) -> 
      let func = eval f env gp in
      begin match func with
      | Closure(formal_param, body, decl_env) -> 
        (* evaluate the ACTUAL param in the current environment *)
        let a_p = eval actual_param env gp in
        (* BIND THE FORMAL PARAMETER TO THE ACTUAL ONE AND ADD THEM TO DECL ENV! *)
        let new_env = bind formal_param a_p decl_env in
        (* calculate the functions with the extened env! *)
        eval body new_env gp
      | _ -> failwith("not a function")
      end;;
    

(* raise an exception because permissions requested by f are not enabled *)
eval 
  (Call(Fun("x", Plus(Var("x"), Eint 5), Read), Var "y"))
  (bind "y" (Int 10) []) 
  None;;

(* return the result because permissions requested by f are enabled *)
eval 
  (Call(Fun("x", Plus(Var("x"), Eint 5), Permission(Read, Write)), Var "y"))
  (bind "y" (Int 10) []) 
  (Permission(Read, Write));;

(* raise an exception because permissions requested by second f are not enabled *)
eval 
  (Call(Fun("x", Plus(Var("x"), Eint 5), Read),
   Call(Fun("z", Plus(Var("z"), Eint 5), Permission(Read, Write)), Var("y"))))
  (bind "y" (Int 10) []) 
  Read;;
  
(* global permissions granted only Read, but in this execution the special permission 
Write is added to the global one, so the function can be called *)
eval
  (EnableIn("f", (* name to bind to the function *)
  Fun("x", Plus(Var("x"), Var "y"), Permission(Read, Write)), (* function definition *)
  Write, (* new permission to grant *)
  Call(Var "f", Var "y"))) (* where to evaluate the function *)
  (bind "y" (Int 10) []) (* environment *)
  Read;; (* global permissions *)

(* global permissions granted only Read, but in this execution the special permission 
Write is added to the global one, so the second function can be called *)
eval 
  (Call(Fun("x", Plus(Var("x"), Eint 5), Read),
  EnableIn("f", (* name to bind to the function *)
  Fun("x", Plus(Var("x"), Var "y"), Permission(Read, Write)), (* function definition *)
  Write, (* new permission to grant *)
  Call(Var "f", Var "y"))))
  (bind "y" (Int 10) []) 
  Read;;

(* global permissions granted Write | Read, which are such that requested by function
but in this execution the special permission Write is not granted anymore, 
so f can't be called *)
eval
  (DisableIn("f", (* name to bind to the function *)
  Fun("x", Plus(Var("x"), Var "y"), Permission(Read, Write)), (* function definition *)
  Write, (* permission to remove *)
  Call(Var "f", Var "y"))) (* where to evaluate the function *)
  (bind "y" (Int 10) []) (* environment *)
  (Permission(Write, Read));; (* global permissions *)