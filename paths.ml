(* paths.ml - Claire Le Goues (June 2014)
 * generates paths through a C file 
 *)

(* fixme: clean this mess up, make calling convention (order in which state is
   passed for example) consistent *)
open Utils
open Cil

type z3Decision =
    Definitely_True
  | Definitely_False
  | Maybe

type decisionInfo =
    {
      decision : z3Decision;
      exp2 : Cil.exp ;
      ast1 : Z3.ast;
      ast2 : Z3.ast
    }

type symexp = Cil.exp

type path_exploration = 
  | Exploring_Block of Cil.block 
  | Exploring_Statement of Cil.stmt  
  | Exploring_Done 

type path_step = 
  | Statement of Cil.stmt
  | Assume of symexp

type path = path_step list 

(* sigma: "symbolic register file" mapping variable names to expressions *)
(* possible fixme: add globals lazily, as we run into them *)
type state = 
{
  sigma : Cil.exp StringMap.t ;
  mu : (symexp * symexp) list ;
  formals : Cil.varinfo StringMap.t ;
  locals : Cil.varinfo StringMap.t ;
  globals : Cil.varinfo StringMap.t ;
  visited : IntSet.t ;
  path : path_step list ;
  expset : StringSet.t 
}

let empty_state () =
{
  sigma = StringMap.empty;
  mu = [] ;
  formals = StringMap.empty ;
  locals = StringMap.empty ;
  globals = StringMap.empty ;
  visited = IntSet.empty ;
  path = [];
  expset = StringSet.empty
}

(*
 * Each worklist element is a five-tuple: 
 * (1) the current state, including path visited so far
 * (2) the current place to explore
 * (3) nn - where to go if the current exploration terminates normally  -- if we're
 * done exploring the inside of a then branch, for example, we should fall
 * through and explore whatever came after the if.
 * (4) where to go if the current exploration is "break;" 
 * (5) where to go if the current exploration is "continue;" 
 *)

module type PathExp = 
sig
  type t

  val empty : t

  val nn : t -> path_exploration list
  val nb : t -> path_exploration list list
  val nc : t -> path_exploration list list 

  val newp : path_exploration list -> path_exploration list list -> path_exploration list list -> t
  val newnn : t -> path_exploration list -> t
end

module PathExp = struct
  type t = path_exploration list * path_exploration list list * path_exploration list list
  let empty = [],[],[]
  let nn (nn,_,_) = nn
  let nb (_,nb,_) = nb
  let nc (_,_,nc) = nc
  let newp nn nb nc = (nn,nb,nc)
  let newnn (_,nb,nc) nn = (nn,nb,nc)
end

(* tracks visitors manipulated in an assumption or assignment statement *)
class noteVarVisitor (varset : Cil.varinfo StringMap.t ref) = object
  inherit nopCilVisitor
  method vvrbl v = 
    varset := StringMap.add v.vname v !varset ;
    DoChildren
end 


(*
 * Look up a variable in the symbolic state. For example, if we know that
 * [x=10] and [y=z+3] and we lookup "y", we expect to get "z+3" out.  Doesn't
 * look in symbolic memory file; that's handle by "select", below.
 * Not sure how fields should work, though; I suspect that should be done here...
 *)
let lookup (sigma : Cil.exp StringMap.t) (variable : Cil.exp) : Cil.exp =
  let found = match variable with
  | Lval(Var(va),NoOffset) -> 
    begin
      try
        Some(StringMap.find va.vname sigma)
      with Not_found -> 
        None
    end 
  | Lval(Var(va),Field(fi,NoOffset)) -> 
    begin
      try
        Some(StringMap.find (va.vname ^"."^fi.fname) sigma)
      with Not_found -> None
    end
  | Lval(_,Field(_)) -> None (* complicated field accesses *)
  | Lval(Mem(exp),NoOffset) -> None (* cannot handle memory access *) 
  | Lval(lhost,Index(_)) -> None (* cannot handle array index *) 
  | _ -> None (* not a variable *) 
  in 
  match found with
  | Some(answer) -> answer
  | None -> variable 
      

(*
 * Rewrite an expression based on the current symbolic state.  For example,
 * if we know that [x=10] and [y=z+3] and we lookup "sin(x+y)", we expect
 * to get "sin(10+z+3)". 
 *)
class substituteVisitor sigma = object
  inherit nopCilVisitor
  method vexpr e = 
    ChangeDoChildrenPost(e,(fun e ->
      lookup sigma e
    ))
end 


(* returns a new state in which 'value' has been written to memory heap
 * location 'address' *)
let update_memory state address value =
  { state with mu = (address,value) :: state.mu }

(* The usual state update: sigma[variable_name := new_value] *) 
let assign state varname new_value =
  {state with sigma = StringMap.add varname new_value state.sigma }

let already_visited state stmt =
  IntSet.mem stmt.sid state.visited 

let mark_as_visited old_state stmt = 
  { old_state with visited = IntSet.add stmt.sid old_state.visited } 


(* We will often need to make a fresh symbolic value that we know nothing
 * about (this is like the \forall x. ... in the notes) ... "fresh_value"
 * does that for us *) 
let value_counter = ref 0 
let fresh_value ?va () = 
  let str = 
    match va with
    | None -> "|" 
    | Some(va) -> "|" ^ va.vname 
  in
  let c = !value_counter in
    incr value_counter ;
    let va1 = makeVarinfo false (Printf.sprintf "%s%d" str c) (TVoid([])) in
      Lval(Var(va1),NoOffset)


(* this function throws away all information we have about the values 
 * of local variables and heap values -- this is typically a conservative
 * "option of last resort" when something happens that we don't know how to
 * model *) 
(* FIXME: wackiness wrt variables implicated and state of solver, maybe??
   possible fixme: multiple contexts, and solver.reset, might be good here/in
   some places.
*)
let throw_away_state old_state =
  let new_sigma = StringMap.mapi (fun old_key old_val -> 
    fresh_value () 
  ) old_state.sigma in
  { old_state with sigma = new_sigma ; mu = [] } 

(* In Z3, boolean-valued and integer-valued expressions are different
 * (i.e., have different _Sort_s). CIL does not have this issue. *) 
let is_binop exp = 
  match exp with 
  | UnOp(LNot,_,_) 
  | BinOp(Lt,_,_,_) 
  | BinOp(Le,_,_,_) 
  | BinOp(Gt,_,_,_) 
  | BinOp(Ge,_,_,_) 
  | BinOp(Eq,_,_,_) 
  | BinOp(Ne,_,_,_) 
  | BinOp(BAnd,_,_,_) (* fixme: POSSIBLY TOTALLY WRONG *)
  | BinOp(BXor,_,_,_)
  | BinOp(BOr,_,_,_)
  | BinOp(LAnd,_,_,_)
  | BinOp(LOr,_,_,_)
    -> true
  | _ -> false

let flip_binop = function
  | Lt -> Ge | Gt -> Le | Le -> Gt | Ge -> Lt | Eq -> Ne | Ne -> Eq  
  | _ -> failwith "unflippable binop"
let is_flippable = function
  | Lt | Gt | Le | Ge | Eq | Ne -> true
  | _ -> false
let flip_exp exp = 
  match exp with
  | BinOp(b,e1,e2,t) when is_flippable b -> BinOp(flip_binop b, e1,e2,t)
  | UnOp(LNot,exp,t) -> exp
  | _ -> UnOp(LNot,exp,(Cil.typeOf exp))

  (* returns the symbolic C/CIL expression associated with 'true' or
   * 'false'. Recall that in C we have "false == 0" and "true <> 0". *)
let se_of_bool b = match b with
  | true -> Const(CInt64(Int64.one,IInt,None))
  | false -> Const(CInt64(Int64.zero,IInt,None))

(* convenience symbolic C/CIL expression.  *)
let zero_exp = se_of_bool false

(* possible fixme: limit number of paths? *)
(** @param target_fundec method to enumerate paths in 
    @return paths path through target_fundec
*) 
let path_enumeration labelht (target_fundec : Cil.fundec) : (state list) =

  let enumerated_paths = ref [] in
  let note_path (s : state) = enumerated_paths := s :: !enumerated_paths in 

  (* convenience/helpful stuff for deciding stuff *)
(*  let ctx = Z3.mk_context [("model", "false")] in *)
  let ctx = Z3.mk_context [] in 
  let int_sort = Z3.mk_int_sort ctx in
  let bool_sort = Z3.mk_bool_sort ctx in
  let zero_ast = Z3.mk_int ctx 0 int_sort in 
  let solver = Z3.mk_solver ctx in

  (* Every time we encounter the same C variable "foo" we want to map
   * it to the same Z3 node. We use a hash table to track this.  *) 
  (* fixme: think about whether I want to clear this out when I pop the solver
     stack, for example? I don't think so, but think about it anyway *)
  let symbol_ht = Hashtbl.create 255 in
  let var_to_ast str = 
    try
      Hashtbl.find symbol_ht str 
    with _ -> 
      let sym = Z3.mk_string_symbol ctx str in
      (* Possible FIXME: currently we assume all variables are integers. *)
      let ast = Z3.mk_const ctx sym int_sort in 
        Hashtbl.replace symbol_ht str ast ;
        ast
  in 

  (* if we run into an expression type we can't handle, we also want to make a
     constant, but since we're not tracking anything about them, we don't assume
     they should map to the same node.  Possibly a mistake *)
  let fresh_int_ast exp = 
    let expstr = exp_str exp in
    let sym = Z3.mk_string_symbol ctx expstr in
      Z3.mk_const ctx sym int_sort
  in
  (* I strongly believe this is the correct way to handle this particular
     problem, but if there's weirdness encountered later this wouldn't be a bad
     place to look *)
  let fresh_bool_ast exp = 
    let expstr = exp_str exp in
    let sym = Z3.mk_string_symbol ctx expstr in
      Z3.mk_const ctx sym bool_sort
  in

  (* convert CIL expression to Z3 ast node. possible fixme: there are other many
     integers/constants/characters/constructs/etc that could be handled here,
     at least with more precision (see, for example, our treatment of
     characters just as integers *) 
  let rec exp_to_ast exp = 
(*    let _ = debug "Converting [%s]\n" (exp_str exp) in
    let res = *)
    match exp with
    | Const(CInt64(i,_,_)) -> Z3.mk_int ctx (Int64.to_int i) int_sort
    | Const(CChr(c)) -> Z3.mk_int ctx (Char.code c) int_sort

    | Const(_) -> fresh_int_ast exp (* fixme: not handling reals, enums, strings, etc
                                       right now *)
  (* this should be fine, because anything that's been defined along the path so
     far should have already been substituted in before we ever called
     exp_to_ast *)
    | Lval(Var(va),NoOffset) -> var_to_ast va.vname 
    | Lval(_) -> fresh_int_ast exp
    | UnOp(Neg,e,_) -> Z3.mk_unary_minus ctx (exp_to_ast e) 
    | UnOp(LNot,e,_) when is_binop e -> Z3.mk_not ctx (exp_to_ast e) 
    | UnOp(LNot,e,_) -> Z3.mk_eq ctx (exp_to_ast e) (zero_ast) 
    | BinOp(PlusA,e1,e2,_) -> Z3.mk_add ctx [| exp_to_ast e1; exp_to_ast e2|]
    | BinOp(MinusA,e1,e2,_) -> Z3.mk_sub ctx [| exp_to_ast e1; exp_to_ast e2|]
    | BinOp(Mult,e1,e2,_) -> Z3.mk_mul ctx [| exp_to_ast e1; exp_to_ast e2|]
    | BinOp(Div,e1,e2,_) -> 
      let ast2 = exp_to_ast e2 in 
      let not_div_by_zero = Z3.mk_distinct ctx [| zero_ast ; ast2 |] in 
        Z3.solver_assert ctx solver not_div_by_zero  ; 
        Z3.mk_div ctx (exp_to_ast e1) ast2 
    | BinOp(Mod,e1,e2,_) -> Z3.mk_mod ctx (exp_to_ast e1) (exp_to_ast e2) 
    | BinOp(Lt,e1,e2,_) -> Z3.mk_lt ctx (exp_to_ast e1) (exp_to_ast e2) 
    | BinOp(Le,e1,e2,_) -> Z3.mk_le ctx (exp_to_ast e1) (exp_to_ast e2) 
    | BinOp(Gt,e1,e2,_) -> Z3.mk_gt ctx (exp_to_ast e1) (exp_to_ast e2) 
    | BinOp(Ge,e1,e2,_) -> Z3.mk_ge ctx (exp_to_ast e1) (exp_to_ast e2) 
    | BinOp(Eq,e1,e2,_) -> Z3.mk_eq ctx (exp_to_ast e1) (exp_to_ast e2) 
    | BinOp(LAnd,e1,e2,_) -> Z3.mk_and ctx [| exp_to_ast e2 ; exp_to_ast e2 |]
    | BinOp(LOr,e1,e2,_) -> Z3.mk_or ctx [| exp_to_ast e2; exp_to_ast e2 |] 
    | BinOp(Ne,e1,e2,_) -> 
      let e1' = exp_to_ast e1 in
      let e2' = exp_to_ast e2 in 
        Z3.mk_distinct ctx [| e1' ; e2' |] 
    | CastE(_,e) -> exp_to_ast e (* Possible FIXME: (int)(3.1415) ? *) 
    | BinOp(BAnd,e1,e2,_) 
    | BinOp(BXor,e1,e2,_) 
    | BinOp(BOr,e1,e2,_) -> fresh_bool_ast exp
  (* addrof, startof, alignof, sizeof, etc., are not explicitly handled *) 
    | _ -> fresh_int_ast exp
(*    in
      debug "looks like: [%s]\n" (Z3.ast_to_string ctx res);
      debug "has sort: [%s]\n" (Z3.sort_to_string ctx (Z3.get_sort ctx res));
      res*)
  in

(* adding stuff to path *)
  let update_path_vars toadd visitCilWhichever state = 
    let ans = ref (StringMap.empty) in
    let _ = visitCilWhichever (new noteVarVisitor ans) toadd in
      StringMap.fold (fun variable_name vinfo state -> 
        (* possible fixme: it's OK that this doesn't special-handle fields, right? *)
        let state' = 
          if not (StringMap.mem variable_name state.sigma) then 
            let new_value = Lval(Var(makeVarinfo false ("_" ^ variable_name) 
                                       (TVoid [])),NoOffset) 
            in
              assign state variable_name new_value 
          else state
        in
          if vinfo.vglob then
            { state' with globals = StringMap.add variable_name vinfo state'.globals } 
          else state')
        !ans state
  in
  let add_stmt_to_path stmt state = 
    let state = update_path_vars stmt visitCilStmt state in
      {state with path = (Statement(stmt)) :: state.path }
  in

  let rec assume state exp ast : state = 
    let expstr = exp_str exp in
      if StringSet.mem expstr state.expset then state
      else begin
        let state = update_path_vars exp visitCilExpr state in
        let state = 
          {state with path = Assume(exp) :: state.path; 
            expset = StringSet.add expstr state.expset} in
          state
      end
  and canon_exp state exp = 
    let exp' = eval state exp in
  (* two options.  One, catch the exception and assume that this is the
     problem, or two, special handle every one we run into.  I think two is
     good to start to make sure there aren't any legit cases where this
     *isn't* the solution, and then replace it with one once that's
     established. *)
    let rec convexp exp =
      match exp with
        Lval(_) | Const(_) | SizeOfE(_) | SizeOfStr(_) | SizeOf(_) | AddrOf(_) -> BinOp(Ne,exp,zero_exp,intType)
      | CastE(_,e) -> convexp e
      | _ -> exp 
    in
      convexp exp'
  and eval state exp =
  (* precondition: we assume exp has already been canonicalized *)
    let sv = new substituteVisitor state.sigma in 
    let exp = visitCilExpr sv exp in
    let rec innereval state exp =
    (* McCarthy's Select Memory Axiom *) 
      let rec select lst read_addr = 
        match lst with
        | [] -> fresh_value () 
        | (written_addr, written_value) :: earlier_writes -> begin 
        (* I *believe* that if branch handling does all the pushing/popping
           necessary here.  *)
          let cilexp1 =  BinOp(Eq,read_addr, written_addr, TInt(IInt,[])) in
          let decision = decide state cilexp1 in
            match decision.decision with
              Definitely_True -> written_value
            | Definitely_False -> select earlier_writes read_addr
            | Maybe -> fresh_value ()
        end in
        match exp with
        | Lval(Mem(read_addr),NoOffset) -> select state.mu (innereval state read_addr)
        | Lval(Var(va),Index(i,NoOffset)) -> select state.mu exp
        | UnOp(unop,ce,tau) -> UnOp(unop, innereval state ce, tau) 
        | BinOp(bop,ce1,ce2,tau) -> begin
          match bop, (innereval state ce1), (innereval state ce2) with
          | PlusA, Const(CInt64(i1,ik1,_)), Const(CInt64(i2,_,_)) -> 
            Const(CInt64(Int64.add i1 i2, ik1, None))
          | MinusA, Const(CInt64(i1,ik1,_)), Const(CInt64(i2,_,_)) ->
            Const(CInt64(Int64.sub i1 i2, ik1, None))
          | Mult, Const(CInt64(i1,ik1,_)), Const(CInt64(i2,_,_)) ->
            Const(CInt64(Int64.mul i1 i2, ik1, None))
          | Shiftlt, Const(CInt64(i1,ik1,_)), Const(CInt64(i2,_,_)) ->
            Const(CInt64(Int64.shift_left i1 (Int64.to_int i2), ik1, None))
          | Shiftrt, Const(CInt64(i1,ik1,_)), Const(CInt64(i2,_,_)) ->
            Const(CInt64(Int64.shift_right i1 (Int64.to_int i2), ik1, None))
          | Lt, Const(CInt64(i1,ik1,_)), Const(CInt64(i2,_,_)) ->
            se_of_bool (i1 < i2) 
          | Le, Const(CInt64(i1,ik1,_)), Const(CInt64(i2,_,_)) ->
            se_of_bool (i1 <= i2) 
          | Gt, Const(CInt64(i1,ik1,_)), Const(CInt64(i2,_,_)) ->
            se_of_bool (i1 > i2) 
          | Ge, Const(CInt64(i1,ik1,_)), Const(CInt64(i2,_,_)) ->
            se_of_bool (i1 >= i2) 
          | x, y, z -> BinOp(x,y,z,tau)
        end 
        | CastE(_,ce) -> innereval state ce
        | x -> x
    in
      innereval state exp
  and decide state exp1 =
    let exp2 = flip_exp exp1 in

    let exp1' = canon_exp state exp1 in
    let exp2' = canon_exp state exp2 in
(*
      debug "deciding: %s\n" (exp_str exp1');
      debug "(flipped: %s)\n" (exp_str exp2');
*)
    Z3.solver_push ctx solver;
      List.iter (fun p -> 
        match p with Assume(exp) -> 
          let cexp = canon_exp state exp in
(*            debug "ASSUME: %s\n" (exp_str cexp);*)
          let aexp = exp_to_ast cexp in
            Z3.solver_assert ctx solver aexp
      | Statement (s)  -> () (*debug "STMT(%s)\n" (stmt_str s)*)) state.path;


    let ast1 = exp_to_ast exp1' in
    let ast2 = exp_to_ast exp2' in
    let one_solve ast  = (*Z3.L_UNDEF*)
      Z3.solver_push ctx solver;
      Z3.solver_assert ctx solver ast;
      let res = Z3.solver_check ctx solver in
(*      let _ =  match res with
          Z3.L_TRUE -> debug "true\n" 
        | Z3.L_FALSE -> debug "false\n"
        | Z3.L_UNDEF -> debug "undef\n"
      in
      let _ =
        try 
          let m = Z3.solver_get_model ctx solver in 
            debug "model:\n%s\n" (Z3.model_to_string ctx m) ;
        with _ -> ()
      in*)
        Z3.solver_pop ctx solver 1; res 
    in
    let decision1 = one_solve ast1 in
    let decision2 = one_solve ast2 in
      Z3.solver_pop ctx solver 1;
    let z3dec = 
      match decision1,decision2 with
        Z3.L_TRUE,Z3.L_FALSE -> Definitely_True
      | Z3.L_FALSE,Z3.L_TRUE ->  Definitely_False
      | _,_ -> Maybe
    in
      {decision=z3dec;exp2=exp2; ast1=ast1; ast2=ast2 }
  (* fixme: consider using preexisting z3 predicates that check against things
     like over/underflow etc? *)
  in
(* evaluates an instruction in a given state. Returns either Some(new_state)
 * if symex should continue or None if we should stop, which we do after
 * calling exit(1) or through a decidedly null function pointer (could also
 * check division by 0, etc, if we wanted) *) 
  let rec handle_instr i state = 
    match i with
    | Set((Var(va),NoOffset),rhs,_) -> 
      let evaluated_rhs = eval state rhs in
        (Some(assign state va.vname evaluated_rhs))
    | Set((Var(va),Field(fi,NoOffset)),rhs,_) -> (* simple field access *)
      let evaluated_rhs = eval state rhs in 
        (Some(assign state (va.vname ^"."^fi.fname) evaluated_rhs))
    | Set((Var(va),Index(index,NoOffset)), rhs,_) -> 
    (* simple array indexing *)
      let evaluated_index = eval state index in
      let evaluated_rhs = eval state rhs in
      let lvalexp = Lval(Var(va),Index(evaluated_index,NoOffset)) in
        (Some(update_memory state lvalexp evaluated_rhs))
    | Call(retval_option, (Lval(Var(va),NoOffset)), args, loc) -> 
      if va.vname = "exit" then None 
      else begin 
        match retval_option with
        | None -> (Some state)
        | Some(lv) -> 
        (* function calls can return anything *) 
          let fv = fresh_value ~va () in 
            handle_instr (Set(lv,fv,loc)) state
      end 
    | Call(retval_option, function_ptr_exp, args, location) -> 
    (* fixme: call through function pointer!  do you want to fix this? Probably
       not. But it's not clear that throwing away all state will work properly,
       so consider coming back to this. *) 
      (Some (throw_away_state state))
    | Set((Mem(ptr_exp),NoOffset),new_val,location) -> 
      let ptr_exp = eval state ptr_exp in 
      let new_val = eval state new_val in 
      let state = update_memory state (ptr_exp) (new_val) in 
      (* if a path continues after *p = 5, then p must be non-null *) 
      let exp1 = BinOp(Ne,ptr_exp,(se_of_bool false),TInt(IInt,[])) in
      let decision = decide state exp1 in 
        if decision.decision = Definitely_False then None
        else Some(assume state exp1 decision.ast1)
    | Set(_,new_val,location) -> (Some (throw_away_state state ))
  (* unexpected assignment, punting *) 
    | Asm(_) -> (* seriously, fuck inline asm *) (Some state)
  in

(* initialize state. Formals start out undefined *)
  let state = 
    lfoldl (fun state formal ->
      let state' = assign state formal.vname (fresh_value ~va:formal ()) in
        { state' with formals = StringMap.add formal.vname formal state'.formals })
      (empty_state ()) target_fundec.sformals 
  in
  let state =
  (* locals start out at zero *)
    List.fold_left (fun state local ->
      let state' = assign state local.vname zero_exp in
        { state' with locals = StringMap.add local.vname local state'.locals })
      state target_fundec.slocals 
  in

  let rec dfs_path_enum state here (explore : PathExp.t) =
    let add_to_worklist state where (explore : PathExp.t) =
      match where with
        Exploring_Statement(s) when (already_visited state s) ->
          dfs_path_enum state (Exploring_Done) explore
      | _ -> dfs_path_enum state where explore
    in
    let give_up state = 
    (* At various times we will stop exploring along a path but we'll still
     * want to report it; we don't need to do any of the symbolic execution
     * stuff --- collect all variables and assign them arbitrary values, etc
     * --- because this is the end of the path *)
      dfs_path_enum state (Exploring_Done) (PathExp.empty)
    in
      match here with 
      | Exploring_Done -> begin 
        match (PathExp.nn explore) with
        | [] -> note_path state
        | first :: rest -> add_to_worklist state first (PathExp.newnn explore rest)  
      end 
      | Exploring_Block(b) -> begin
        match b.bstmts with
        | [] -> add_to_worklist state (Exploring_Done) explore
        | first :: rest -> 
          let followup = (Exploring_Block { b with bstmts = rest }) in 
          let explore' = PathExp.newnn explore (followup :: (PathExp.nn explore)) in
            add_to_worklist state (Exploring_Statement(first)) explore'
      end 
      | Exploring_Statement(s) when not (already_visited state s) -> 
        begin
          let state = mark_as_visited state s in
            match s.skind with
            | Block(b) -> add_to_worklist state (Exploring_Block b) explore
            | TryFinally _ | TryExcept _ -> give_up state (* Microsoft C Extensions *) 
            | Goto(stmtref,_) ->
              let stmt = !stmtref in
                if Hashtbl.mem labelht stmt.sid then 
                  add_to_worklist state (Exploring_Statement stmt) explore
                else 
              give_up state
            | Return _ -> 
              (* possible FIXME: it's not clear to me whether we should eval or not *)
(*              let eopt' = 
                match eopt with
                  Some(e) -> Some(eval state e) 
                | None -> None 
              in
              let s' = { s with skind = Return(eopt',loc) } in*)
              let state' = add_stmt_to_path s state in
                add_to_worklist state' (Exploring_Done) (PathExp.empty)
            | Switch(exp1,block,stmts,_) -> 
              let lval = eval state exp1 in
              
              (* we only jump to (exploring) labeled statements; we do it this way
                 instead of walking the list of labeled statements that CIL
                 constructs for us so we can find the rest of the stmts in the
                 list/block that come after a given labeled statement *)
            let is_labeled stmt = 
              List.exists (fun label ->
                match label with Case _ | Default _ -> true
                | _ -> false) stmt.labels 
            in
            let rec process_switch state stmts =
              match stmts with
                stmt :: rest when (is_labeled stmt) ->
                  let where = Exploring_Statement(stmt) in
                  let nn = PathExp.nn explore in
                  let nb = PathExp.nb explore in
                  let nc = PathExp.nc explore in 
                  let nn' = (Exploring_Block{ block with bstmts = rest }) :: nn in
                  let nb' = nn :: nb in
                  let nc' = ([]) :: nc in
                  let explore' = PathExp.newp nn' nb' nc' in
                  let rec handle_labels state labels = 
                    match labels with
                      Case(exp2,_) :: rest_of_labels -> begin
                        let exp1 = BinOp(Eq,lval,exp2,intType) in
                        let decision = decide state exp1 in 
                          Z3.solver_push ctx solver;
                          match decision.decision with
                            Definitely_True ->
                              let state = assume state exp1 decision.ast1 in
                                add_to_worklist state where explore';
                                Z3.solver_pop ctx solver 1;
                                false
                          | Definitely_False ->
                            let state = assume state decision.exp2 decision.ast2 in
                              ignore(handle_labels state rest_of_labels); true
                          | Maybe -> 
                            add_to_worklist (assume state exp1 decision.ast1) where explore';
                            Z3.solver_pop ctx solver 1; 
                            Z3.solver_push ctx solver;
                            ignore(handle_labels (assume state decision.exp2 decision.ast2) rest_of_labels);
                            Z3.solver_pop ctx solver 1;
                            true
                      end
                    | Default _ :: rest_of_labels -> 
                      add_to_worklist state where explore'; false
                    | _ :: rest_of_labels -> handle_labels state rest_of_labels
                    | [] -> false
                  in  
                    if (handle_labels state stmt.labels) then
                      process_switch state rest
                    else ()
              | stmt :: rest -> process_switch state rest
              | [] -> ()
            in
              process_switch state block.bstmts 
          | Break _ -> begin
            match (PathExp.nb explore), (PathExp.nc explore) with 
            | b_hd :: b_tl , c_hd :: c_tl -> 
              add_to_worklist state (Exploring_Done) (PathExp.newp b_hd b_tl c_tl)
            | _, _ -> failwith "Break with no enclosing loop or switch structure.  This should be impossible"
          end 

          | Continue _ -> begin 
            match (PathExp.nb explore), (PathExp.nc explore) with 
            | b_hd :: b_tl , c_hd :: c_tl -> 
              add_to_worklist state (Exploring_Done) (PathExp.newp c_hd b_tl c_tl)
            | _, _ -> failwith "Continue with no enclosing loop structure.  This should be impossible"
          end 

          | Instr il ->
            let stateopt = 
              List.fold_left (fun stateopt instr ->
                match stateopt with
                  None -> None
                | Some(state) -> handle_instr instr state 
              ) (Some state) il
            in
              begin
                match stateopt with
                | None -> note_path state 
                | Some(state) ->
                  let state = add_stmt_to_path s state in
                    add_to_worklist state (Exploring_Done) explore;
              end
          | If(exp,then_branch,else_branch,_) -> 
            let process_branch exp ast branch =
              let state = assume state exp ast in
                add_to_worklist state (Exploring_Block(branch)) explore
            in
            let decision = decide state exp in 
(*              debug "processing {%s}\n" (stmt_str s);*)
              begin
(*              Z3.solver_push ctx solver; *) (* possible fixme: do we need these pushes/pops? *)
              match decision.decision with
                Definitely_True -> (* else is impossible *)
(*                  debug "else is impossible\n\n";*)
                  process_branch exp decision.ast1 then_branch;
(*                  Z3.solver_pop ctx solver 1*)
              | Definitely_False -> (* then is impossible *)
(*debug "then is impossible\n\n";*)
                process_branch decision.exp2 decision.ast2 else_branch;
(*                Z3.solver_pop ctx solver 1*)
              | Maybe -> 
(*debug "either is possible\n\n";*)
                process_branch exp decision.ast1 then_branch;
(*                Z3.solver_pop ctx solver 1;
                Z3.solver_push ctx solver;*)
                process_branch decision.exp2 decision.ast2 else_branch;
(*                Z3.solver_pop ctx solver 1*)
              end
          | Loop(loop_block,_,break_opt,continue_opt) -> 
            (* In CIL, while (b) { c } becomes
             *
             * while (1) {
             *   if (!b) break; 
             *   c;
             * } 
             *
             * Thus all Loops are the equivalent of "while true". *)  
            let nn = PathExp.nn explore in
            let nb = PathExp.nb explore in
            let nc = PathExp.nc explore in
            let explore' = 
              PathExp.newp (here :: nn) (nn :: nb)  ((here :: nn) :: nc)
            in
              add_to_worklist state (Exploring_Block loop_block) explore'
      end 
    | Exploring_Statement(s) -> 
      add_to_worklist state (Exploring_Done) explore
  in
    (* start enumerating at the first line of the function body. *) 

    dfs_path_enum state (Exploring_Block(target_fundec.sbody)) (PathExp.empty);

  (* We prepended statements to the front of paths, so we have to
   * reverse them to get the right history order. *) 
  let paths = List.map (fun state -> {state with path = List.rev state.path })
    (List.rev !enumerated_paths) in
  let print_vars vars vtyp =
    StringMap.iter (fun vname vinfo ->
      let typstr = cil_type_to_str vinfo.vtype in 
        Printf.printf "%s(%s%s)\n" vtyp typstr vname)
      vars 
  in
    debug "Paths: \n"; 
    List.iter 
      (fun state ->
        print_vars state.globals "GLOBAL";
        print_vars state.formals "FORMAL";
        print_vars state.locals "LOCAL"; 
        List.iter 
          (fun step ->
            match step with
              Assume(e) -> 
                debug "\tASSUME(%s)\n" (exp_str e)
            | Statement(s) -> debug "\tSTMT(%s)\n" (stmt_str s)
          ) state.path;
        debug "\n";
      ) paths;
  debug "path_enumeration: %s: %d path(s) enumerated\n" 
    target_fundec.svar.vname 
    (List.length paths) ;
  paths 
