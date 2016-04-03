(*
 * Graduate Programming Languages - Wes Weimer
 *
 * Test Input Generation Project - Global Utilities
 *
 * All of the real action happens in "tigen.ml". 
 *)
open Cil

let printer = Cilprinter.noLineCilPrinter
let stmt_str stmt = Pretty.sprint ~width:80 (printStmt printer () stmt) 
let exp_str exp = Pretty.sprint ~width:80 (printExp printer () exp) 
let instr_str instr = Pretty.sprint ~width:80 (printInstr printer () instr)

(* 
 * This "debugging output" function behaves just like printf(), but it also
 * flushes the output buffer so that you'll always see all of your output,
 * even if the program terminates abnormally. 
 *)
let debug fmt = 
  let k result = begin
    output_string stdout result ; 
    flush stdout ; 
  end in
  Printf.kprintf k fmt 

let abort fmt = 
  debug fmt ;
  exit 1 

(* 
 * Load, lex and parse and pre-processed C-language file (typically a .i
 * file obtained by "gcc -E" or "gcc -save-temps") into a Cil.file abstract
 * syntax tree data structure.
 *)
let load_c_file (filename : string) : Cil.file = 
  Frontc.parse filename () 

(*
 * Pretty-print a Cil expression as a string. Handy for debugging. 
 *)
let cil_exp_to_str (e : Cil.exp) : string = 
  Pretty.sprint ~width:80 (d_exp () e) 

let cil_type_to_str (t : Cil.typ) : string = 
  Pretty.sprint ~width:80 (d_type () t)

(* 
 * returns the first N elements of the given list 
 *) 
let rec first_nth lst n =  
  if n < 1 then [] 
  else match lst with
  | [] -> []
  | hd :: tl -> hd :: (first_nth tl (pred n))


module OrderedString =
  struct
    type t = string
    let compare = compare
  end
module StringMap = Map.Make(OrderedString)
module StringSet = Set.Make(OrderedString)

module OrderedInt =
  struct
    type t = int
    let compare = compare
  end
module IntMap = Map.Make(OrderedInt)
module IntSet = Set.Make(OrderedInt)

let lfoldl = List.fold_left

let hadd = Hashtbl.add 

let ht_find ht key new_val = 
  try 
    Hashtbl.find ht key 
  with Not_found -> 
    let newval = new_val () in
      hadd ht key newval; newval

let get_opt = function
  | Some(s) -> s
  | None -> failwith "Unexpected None to get_opt"
