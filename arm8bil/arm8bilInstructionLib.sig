signature arm8bilInstructionLib =
sig
  include Abbrev

  val sim_invariant_def: thm
  val does_match : term -> term -> bool
   val align_conversion_thm : thm

  val tc_gen_goal      : term -> 'a list -> thm -> term -> term -> term

  val tc_one_instruction_goal :string -> term -> term -> term * thm list * thm * term
   val tc_one_instruction2_by_bin : string -> term -> term -> thm
  val tc_one_instruction2        : string quotation -> term -> term -> thm
(* ------------------------------------------------------------------------- *)
end
