(* prover.ml - Claire Le Goues (June 2014)
 * interface/signature for calls to the theorem prover
 * mostly to abstract out the z3 details until I get it building/running on, for
 * example, os x *)

module type Prover = 
  sig
    val init : unit -> unit
end

module StubProver =
struct
  let init () = ()

end

module Z3Prover = 
struct
  let init () =
    Z3.toggle_warning_messages true 
end
