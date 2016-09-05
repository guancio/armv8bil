signature mainLib =
sig
  include Abbrev

  val lift_program : (string * term) list -> thm
(* ------------------------------------------------------------------------- *)
end
