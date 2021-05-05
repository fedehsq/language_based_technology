
(*
DFA
• A deterministic ﬁnite automaton M is a 5tuple, (Q, Σ, δ, q0, F), consisting of
– a ﬁnite set of states (Q)
– a ﬁnite set of input symbols called the alphabet (Σ)
– a transition function (δ : Q × Σ → Q)
– a start state (q0 ∈ Q)
– a set of accepti ng states (F ⊆ Q)
*)

(* Respresents states of dfa as int *)
type state = int;;

(* Represents symbols (alphabet) as a char *)
type symbol = char;;

(* transaction function delta *)
type transition = state * symbol * state;;

(* description of dfa *)
type dfa = {
  states : state list;
  sigma : symbol list;
  start : state;
  transitions : transition list;
  accepting : state list;
};;

(* Auxiliary Functions *)
(* To dereference a record, use the dot notation *)
let states (dfa : dfa) = dfa.states;;
let alphabet (dfa : dfa) = dfa.sigma;;
let start (dfa : dfa) = dfa.start;;
let transitions (dfa : dfa) = dfa.transitions;;
let acceptings (dfa : dfa) = dfa.accepting;;

(* This is a function that takes in a DFA as input, and adds a transition.
*)

(* "with" evaluates to a new record of the same type as X, and whose 
fields are initialized to the same as those in X, except the ones
which are listed after the "with", which are initialized to those
given values.
*)
let addTransition t dfa = { 
  dfa with transitions = t::dfa.transitions 
};;

(*
explode takes a string `s`, and turns it into its individual
characters. This way we can run the DFA on the string "101"
without explicitly writing ['1';'0';'1']
*)
let explode s =
  let rec expl i l =
    if i < 0 
      then l 
      (* s.[i] returns the ith element of s as a char *)
    else expl (i - 1) (s.[i] :: l) in 
   (* String.length s returns the length of s *)
      expl (String.length s - 1) [];;

(* 
another helper function that checks whether a list contains an
element *)
let rec contains e l =
  match l with
  | [] -> false
  | hd::tl -> if hd = e then true else contains e tl;;


(*
Checking DFA Acceptance
• Attempt 1: we might keep a (mutable) 
variable that keeps track of what state the
DFA is currently at, and then updates the state depending on that.
*)
let check_accepts str dfa =
  (* Get the list of symbols. *)
  let symbols = explode str in
    (* If I'm at state {state}, where do I go on {symbol}? *)
    let transition state symbol =
      let rec find_state l =
        match l with
        | (s1, sym, s2)::tl ->
          if (s1 = state && symbol = sym) then s2 else find_state tl
        | _ -> failwith "no next state" 
      in find_state dfa.transitions      
    in let final_state = 
      let rec h symbol_list =
        match symbol_list with
        | [hd] -> (transition dfa.start hd)
        | hd::tl -> (transition (h tl) hd)
        | _ -> failwith "empty list of symbols"
      in h (List.rev symbols) in
        if (contains final_state dfa.accepting) then 
          true 
        else false;;


(* Example: no write after read *)
let d : dfa = { 
  states = [0; 1; 2];
  sigma = ['r';'w'];
  start = 0;
  transitions =
    [(0, 'r', 1);
    (0, 'w', 0);
    (1, 'w', 2);
    (1, 'r', 1);
    (2, 'r', 2);
    (2, 'w', 2)];
  accepting = [0; 1]
};;

check_accepts "rrrrrw" d;;