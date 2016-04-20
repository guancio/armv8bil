signature arm8bilInstructionLib =
sig
  include Abbrev

  val tc_gen_goal      : term -> 'a list -> thm -> term -> term -> term

  val tc_one_instruction2_by_bin : string -> term -> term -> thm
  val tc_one_instruction2        : string quotation -> term -> term -> thm
(* ------------------------------------------------------------------------- *)
end
