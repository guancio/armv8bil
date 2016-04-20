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
HOL_Interactive.toggle_quietdec();


(* 0000000000000000 <internal_mul>: *)
val instructions = [
"d10103ff","f9000fe0","f9000be1","f90007e2","b90007e3","b9003bff","14000009",
"b9803be0","d37ff800","f94007e1","8b000020","7900001f","b9403be0","11000400",
"b9003be0","b94007e0","531f7801","b9403be0","6b00003f","54fffe8c","b94007e0",
"51000400","b9003fe0","14000043","b9803fe0","d37ff800","f9400fe1","8b000020",
"79400000","53003c00","f90017e0","f9001bff","b94007e0","51000400","b9003be0",
"1400002a","b9803be0","d37ff800","f9400be1","8b000020","79400000","53003c01",
"f94017e0","9b007c20","f9401be1","8b000020","f9001be0","b9403fe1","b9403be0",
"0b000020","93407c00","91000400","d37ff800","f94007e1","8b000020","79400000",
"53003c00","f9401be1","8b000020","f9001be0","b9403fe1","b9403be0","0b000020",
"93407c00","91000400","d37ff800","f94007e1","8b000020","f9401be1","53003c21",
"79000001","f9401be0","d350fc00","f9001be0","b9403be0","51000400","b9003be0",
"b9403be0","6b1f001f","54fffaaa","b9803fe0","d37ff800","f94007e1","8b000020",
"f9401be1","53003c21","79000001","b9403fe0","51000400","b9003fe0","b9403fe0",
"6b1f001f","54fff78a","910103ff","d65f03c0"
];

List.foldl (fn (code, pc) =>
  let val _ = print "******************************\n"
      val _ = print (String.concat ["Lifting instruction: ", code, "\n"])
  in
    (let val th = tc_one_instruction2_by_bin code pc ``\x.x<+0x100000w:word64``;   
     in print_thm th ; print "\n" end
     handle _ => print "-------FAILURE-------\n");
     ((snd o dest_eq o concl o EVAL) ``^pc+4w``)
  end
) ``0w:word64`` instructions;

