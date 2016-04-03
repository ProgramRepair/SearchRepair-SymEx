open Cil

let load_c_file (filename : string) : Cil.file = 
  Frontc.parse filename () 

let _  = begin
  let filename = Sys.argv.(1) in 
  let file = load_c_file filename in 
    ()

end ;;

(* tigen.ml: end of file *) 
