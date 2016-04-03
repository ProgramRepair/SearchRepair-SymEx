(*
 * main.ml - Claire Le Goues
 * June 2014
 * adapted from starter code stolen from Wes Weimer's Graduate Programming
 * Languages class (as of at least a couple years ago...who knows when he last
 * taught it?)
 * probably totally different by the time you look at it...
 * I think I've done this before, wish I remembered where so I wouldn't have to
 * refind all the same bugs that I *know* are in here...
 * 
 * Comments from original code:
 * Test Input Generation Project 
 *
 * Summary: Given a C file, produce a suite of test inputs for that file
 *        such that branch coverage is maximized. 
 *
 * Input: A filename for a pre-processed, instrumented C file. This file
 *        is typically obtained via the "make test" Makefile target or
 *        the "instrument" utility. 
 *        example: test/simple-1/simple-1.i
 *
 * Output: Create a series of C files test0001.c, test0002.c, etc., 
 *        in that same directory. Each has main() defined to call
 *        the last function defined in the input file with the 
 *        goal of visiting every labeled statement. 
 *
 * High-Level Approach: 
 *  Step 1 -- generate straight-line paths of statements and "assumes"
 *  Step 2 -- symbolically execute those paths  
 *  Step 3 -- generate constraints from symex states
 *  Step 4 -- solve those constraints (obtaining values for variables)
 *  Step 5 -- convert constraint solutions into test inputs
 *
 * Many places in this code are annotated with "Possible FIXME", indicating
 * an area that might be expanded in a student project. 
 *)
open Utils
open Cil
open Paths

(* FIXME: don't generate paths for stuff in system header files *)

let foo () = 
(* in what is the strangest failure mode I have ever seen, if I delete this
   function definition (and specifically the call to mk_datatypes), Z3
   experiences an internal error on mk_context in paths.ml.  Thus, I leave it
   in, but I have no explanation for why I need it, given that this function is
   never called. *)
  ignore(Z3.mk_datatypes (Z3.mk_context []) (fun x -> None))

class collectLabeledStatementVisitor ht = object
  inherit nopCilVisitor

  method vstmt s = 
    List.iter (fun l -> match l with
      Label(lbl, _, false) -> Hashtbl.add ht s.sid ()
    | _ -> ()) s.labels;
    DoChildren

end

(**********************************************************************
 * Main Driver
 *
 * We accept the program to test as the only command-line argument. We
 * emit the test cases in the same directory as the program source. Try
 * "make test" and "make eval" to run this automatically on the provided
 * tests. 
 *)

let main () = begin
  if Array.length Sys.argv < 2 then begin 
    debug "pathgen: specify a pre-preprocessed C file\n" ;
    exit 1 
  end ; 
  let filename = Sys.argv.(1) in 
  let funname = ref "" in
    if Array.length Sys.argv > 2 then begin
      funname :=  (Sys.argv.(2))
    end;
    Cil.insertImplicitCasts := false;
(*    Cil.useLogicalOperators := true;*)
  let file = load_c_file filename in 
    let rec process_fundecs globals paths = 
      match globals with
      | GFun(fd, loc) :: tl when
          !funname = "" || !funname = fd.svar.vname ->
        let glob = GFun(fd, loc) in
          debug "Processing: %s\n" fd.svar.vname;
          Simplify.doGlobal glob; (* convert to ssa *)
          (* We want each statement to have a unique statement ID, so we'll call
           * cfgFun.  Note that we used to call computeFileCFG above, but
           * because Simplify introduces new statements, we have to do it after
           * converting to SSA.  *)
                    ignore(Cfg.cfgFun fd);
          let labelht = Hashtbl.create 10 in
            ignore(visitCilGlobal  (new collectLabeledStatementVisitor labelht) glob);
          debug "post process:\n";
          dumpGlobal printer stdout glob;
          flush stdout;
          let new_paths = path_enumeration labelht fd in
          let paths' = new_paths @ paths in
            process_fundecs tl paths'
      | hd :: tl -> process_fundecs tl paths
      | [] -> paths
    in
    let all_paths = process_fundecs file.globals [] in
      Printf.printf "Number of paths generated: %d\n" (List.length all_paths)


end ;;
main () ;;

(* tigen.ml: end of file *) 
