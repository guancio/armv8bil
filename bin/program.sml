HOL_Interactive.toggle_quietdec();
open HolKernel boolLib bossLib Parse;
open lcsymtacs utilsLib;
open wordsLib blastLib;
open state_transformerTheory updateTheory arm8Theory;
open stateTheory;
open lcsymtacs arm8_stepTheory;
open state_transformerSyntax;
open arm8_stepLib;
open proofTools arithTheory;
open bilTheory arm8bilTheory;
open arm8bilLib;
open arm8stepbilLib;
open arm8bilInstructionLib;
open mainLib;
HOL_Interactive.toggle_quietdec();
 

val ops = 
 [("d10103ff", ``0w:word64``), ("f9000fe0", ``4w:word64``),
  ("f9000be1", ``8w:word64``), ("f90007e2", ``12w:word64``),
  ("b90007e3", ``16w:word64``), ("b9003bff", ``20w:word64``),
  ("14000009", ``24w:word64``)];
val thm = lift_program(ops);
print_thm thm;

