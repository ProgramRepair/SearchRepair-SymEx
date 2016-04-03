(*
 * transform.ml - Claire Le Goues
 * April 2015
 * Small utility to transform the IntroClass benchmarks so we can handle code
 * with printfs.
 * This is fairly specific to the IC code and the experiment we're setting up
 * with it, YMMV on applying it to anything more complicated.  *)

open Utils
open Cil

let cregexp = Str.regexp_string "%c" 
(* making more than one variable is probably a bad idea, but I thought I
   probably should make my code at least moderately robust to that
   possibility *)
let varcount = ref 0

let new_local fd t =
  let varname = Printf.sprintf "printf_tmp%d" !varcount in
  let _ = incr varcount in 
  Cil.makeLocalVar fd varname t

let is_printf = function
  | Lval(Var(varinfo),_) when varinfo.vname = "printf" -> true
  | _ -> false 

(* everyVisitor turns lists of instructions within a single statement into
   multiple statements with stmtkind instr, each of which contains a
   single-element list.  It is remarkably useful.  This visitor also counts
   return statements as part of a sanity check. *)
class everyVisitor sane = object
  inherit nopCilVisitor

  val mutable num_returns = 0

  method vfunc fd = num_returns <- 0; DoChildren

  method vstmt s =
    match s.skind with
      Return _ -> 
        if num_returns > 0 then sane := false;
        num_returns <- num_returns + 1;
        DoChildren
    | _ -> DoChildren

  method vblock b = 
    ChangeDoChildrenPost(b,(fun b ->
      let stmts = List.map (fun stmt ->
        match stmt.skind with
        | Instr([]) -> [stmt] 
        | Instr(first :: rest) -> 
          stmt.skind <- Instr([first]);
          stmt :: List.map (fun instr -> mkStmtOneInstr instr ) rest 
        | other -> [ stmt ] 
      ) b.bstmts in
      let stmts = List.flatten stmts in
        { b with bstmts = stmts } 
    ))
end 

(* this visitor counts printfs after the initial set in a program to support the
   grade transformation in its attempt to figure out which type of
   transformation it's suppose to apply *)
class countPrintfs 
  num_printfs
  num_simple_unguarded_printfs 
  num_simple_guarded_printfs 
  num_complex_unguarded_printfs 
  num_complex_guarded_printfs = 
object
  inherit nopCilVisitor
  val mutable in_condition = false 
  val mutable start_counting = false

  method vstmt stmt =
      match stmt.skind with 
      | If(_) -> 
        let old_in = in_condition in 
          start_counting <- true;
          ChangeDoChildrenPost((in_condition <- true; stmt), 
                               (fun s -> in_condition <- old_in; s))
      | Instr([Call(_,fn,arglist,_)]) when is_printf fn && start_counting -> begin
        incr num_printfs;
        let complex = (List.length arglist) > 1 in
          if in_condition then
            if complex then
              incr num_complex_guarded_printfs
            else 
              incr num_simple_guarded_printfs
          else 
            if complex then
              incr num_complex_unguarded_printfs
            else 
              incr num_simple_unguarded_printfs;
          DoChildren
      end
      | _ -> DoChildren

end

(* printfs is a hashbtbl mapping format strings to useful info that we need to
   replace the printf calls: the statement id corresponding to the original
   printf (to be replaced with an assignment), the exp corresponding to the
   printf function, and the variable used as an argument (necessary for the
   assignment) *)
class findPrintfsSimple printfs formatstr printf_exp = object
  inherit nopCilVisitor

  val mutable in_condition = false 

  method vstmt stmt =
    match stmt.skind with 
    | If(_) -> 
      let old_in = in_condition in 
        ChangeDoChildrenPost((in_condition <- true; stmt), 
                             (fun s -> in_condition <- old_in; s))
    | Instr([Call(_,fn,[(Const(CStr(str))); arg],_)]) when 
        in_condition && is_printf fn ->
        (* these are calls to printf that print out an integer.  We will replace
           it with an assignment that stores the printed integer, which will
           then be printed at the end. *)
      begin
        if !formatstr <> "" && str <> !formatstr then 
          abort "too many different format strings being used in printfs; transformation impossible.  Use the original instead";
        formatstr := str;
        printf_exp := Some(fn);
        Hashtbl.add printfs stmt.sid arg;
          DoChildren
      end
    | Instr([Call(_,fn,[(Const(CStr(s)))],_)]) when 
        in_condition && is_printf fn ->
    (*  these are calls to simple printfs; we will replace it with an
        asssignment that stores the printed string, which will then be printed
        at the end *)
      Hashtbl.add printfs stmt.sid (Const(CStr(s)));
          printf_exp := Some(fn);
          DoChildren
    | _ -> DoChildren
      
end

(* res_ht maps statement ids to the expression that is originally printed (and
   will be saved instead.  integer for median, string for string-based grade).
   The tmp is the new variable we use to store intermediate results and that
   eventually gets printed at the end of the function *)
class transformPrintfsSimple printf_info construct_printf tmp = object
  inherit nopCilVisitor 

  val mutable inserted = true

  method vstmt s = 
    match s.skind with
    | Return _ when inserted ->
      let printf = construct_printf !currentLoc in
      let printf = mkStmt (Instr[printf]) in
      let b = Block({battrs = []; bstmts = [printf;s]}) in
        ChangeTo(mkStmt b )
    | _ -> 
      if Hashtbl.mem printf_info s.sid then begin
        let arg = Hashtbl.find printf_info s.sid in
        let newSet = Set((Var(tmp),NoOffset), arg, !currentLoc) in
          inserted <- true;
          ChangeTo(mkStmt (Instr([newSet])))
      end else DoChildren
end


let transform_simple formatstr tmp fd  = begin
  let printf_info = Hashtbl.create 10 in
  let printf_fn_tmp = ref None in
  let _ = 
    ignore(visitCilFunction (new findPrintfsSimple printf_info formatstr printf_fn_tmp) fd)
  in
    match !printf_fn_tmp with
      Some(fn) ->   
        let construct_printf loc = 
          Call(None, fn, [Const(CStr(!formatstr)); Lval(Var(tmp),NoOffset)], loc) 
        in
          visitCilFunction (new transformPrintfsSimple printf_info construct_printf tmp) fd
    | None -> fd
end 

(* there are two possibilities with grade: the students either used an
   intermediate variable to store the grade and then used it with a format
   string in one printf in the end, or had multiple printfs, no extra arguments,
   guarded by if checks. This handles the first case. *)
class findPrintfsGradeChar printfs assignments charinfo = object
  inherit nopCilVisitor

  val mutable in_condition = false 

  method vstmt stmt =
    let has_character_typ = function
        TInt(IChar,_) | TInt(ISChar,_) | TInt(IUChar,_) -> true
      | _ -> false
    in
      match stmt.skind with 
      | If(_) -> 
        let old_in = in_condition in 
          ChangeDoChildrenPost((in_condition <- true; stmt), 
                               (fun s -> in_condition <- old_in; s))
      | Instr([Set((Var(vinfo),NoOffset),exp,_)]) 
          (* assigning a letter grade to a character variable to be used in a
             later printout. will replace this assignment of a character with an
             assignment to a string that comprises the entire string that is
             ultimately printed out *)
          when in_condition && (not vinfo.vglob) && (has_character_typ vinfo.vtype) -> 
          Hashtbl.add assignments stmt.sid (vinfo,exp);
          Hashtbl.add charinfo vinfo.vname (vinfo, "");
          DoChildren
      | Instr([Call(_,fn,[(Const(CStr(str))); (Lval(Var(carvar),_))],_)]) when 
          (* printing out a string, filling in a character from a previous
             assignment.  Will be replaced with a printf that prints a single
             string variable *)
          is_printf fn && (Hashtbl.mem charinfo carvar.vname)  ->
          Hashtbl.replace charinfo carvar.vname (carvar,str);
          Hashtbl.replace printfs stmt.sid fn;
          DoChildren
      | _ -> DoChildren
end

class transformPrintfsGradeChar printfs charinfo assignments tmp = object
  inherit nopCilVisitor

  method vstmt s = 
    let rec getCharE = function
      | Const(CChr(c)) -> Some(c)
      | Lval((Mem(e),_)) 
      | SizeOfE(e)
      | AlignOfE(e)
      | UnOp(_,e,_)
      | CastE(_,e) -> getCharE e
      | _ -> None
    in
    if Hashtbl.mem printfs s.sid then begin
      let funvar = Hashtbl.find printfs s.sid in
      let newstr = Const(CStr("%s")) in
      let newCall = Call(None, funvar, [newstr;Lval(Var(tmp),NoOffset)],!currentLoc) in
        ChangeTo(mkStmt (Instr[newCall]))
    end else if Hashtbl.mem assignments s.sid then begin
      let vinfo,exp = Hashtbl.find assignments s.sid in
      let carvar,formatstr = Hashtbl.find charinfo vinfo.vname in
        match (Str.split cregexp formatstr),(getCharE exp) with
          [frst;scnd],Some(char) ->             
            let newString = Printf.sprintf "%s%c%s" frst char scnd in
            let newSet = Set((Var(tmp),NoOffset), Const(CStr(newString)), !currentLoc) in
            let instr = Instr([newSet]) in
              ChangeTo(mkStmt instr)
        | _,_ -> DoChildren
    end else DoChildren

end

let guess_transform fd = begin
  let num_printfs = ref 0 in
  let num_simple_unguarded_printfs = ref 0 in
  let num_simple_guarded_printfs = ref 0 in
  let num_complex_unguarded_printfs = ref 0 in
  let num_complex_guarded_printfs = ref 0 in
    ignore(visitCilFunction 
             (new countPrintfs num_printfs
                num_simple_unguarded_printfs 
                num_simple_guarded_printfs 
                num_complex_unguarded_printfs 
                num_complex_guarded_printfs) fd);
    if !num_complex_unguarded_printfs = 1 &&
      !num_complex_unguarded_printfs = !num_printfs then "grade_character"
    else if !num_simple_guarded_printfs = !num_printfs then "grade_string"
  else "can't do it"

end

let transform_grade fd = begin
  match guess_transform fd with
    "grade_character" -> begin
      let printf_info = Hashtbl.create 10 in
      let assignment_info = Hashtbl.create 10 in
      let char_info = Hashtbl.create 10 in
      let _ =
        ignore(visitCilFunction (new findPrintfsGradeChar printf_info assignment_info char_info) fd)
      in
      let tmp = new_local fd Cil.charPtrType in
        visitCilFunction 
          (new transformPrintfsGradeChar
             printf_info 
             char_info 
             assignment_info 
             tmp) fd
    end
  | "grade_string" -> 
    transform_simple (ref "%s") (new_local fd Cil.charPtrType) fd
  | _ -> abort "couldn't guess appropriate transform for grade; use original instead"
end

let transform_type = ref "simple"
let funname = ref ""

let options = [
  "--type", Arg.Set_string transform_type,
  "X transformation type.  Options: simple, grade.  Default: simple";
  "--fun", Arg.Set_string funname,
  "X apply transformation just to function X.  Default: none, so whole file";
]

let load_check_process_file filename =
  match filename with
    "" -> abort "transform: specify a pre-preprocessed C file\n" 
  | _ -> begin
    Cil.useLogicalOperators := true;
    Cil.insertImplicitCasts := false;
    let file = load_c_file filename in 

    (* by default, instructions like assignments and calls to printf are grouped
       into single statements (the Instr statement).  We want to find the
       printfs separately, so we separate lists of instructions into single
       statements, before numbering (below).  This also sanity-checks the number
       of return statements in the program (to save us a second visiting
       pass). *)
    let sane = ref true in
      ignore(visitCilFileSameGlobals (new everyVisitor sane) file);
      if not !sane then 
        abort "cannot sensibly transform this program; too many return statements.  Use the original instead\n";

      Cfg.computeFileCFG(file);
      file
  end

let main () = begin
  let filename = ref "" in
  let _ =
    Arg.parse (Arg.align options) (fun f -> filename := f) "Simple C program printf transformer\n"
  in
  let file = load_check_process_file !filename in 

  let rec process_fundecs globals = 
    match globals with
    | GFun(fd, loc) :: tl when
        !funname = "" || !funname = fd.svar.vname ->
      let transform = 
        match !transform_type with
          "simple" -> transform_simple (ref "") (new_local fd Cil.intType)
        | "grade" -> transform_grade
        | x -> 
          debug "transform: unrecognized transform type %s.  Options: simple, complex.\n" x;
          exit 1
      in

        GFun((transform fd), loc) :: (process_fundecs tl)
    | hd :: tl -> hd :: (process_fundecs tl)
    | _ -> []
  in
  let file = { file with globals = process_fundecs file.globals } in
    dumpFile printer stdout "string" file 
end ;;

main () ;;
