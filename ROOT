session "Isabelle_DOF" = HOL + 
  theories [document = false]
    (* Foo *)
    (* Bar *)
  theories
    Isa_DOF



(*
 Bit
 Bits
 Boolean_Algebra
 Code_Abstract_Nat
 Code_Target_Nat
 Code_Target_Int
 Misc_Numeric
 Misc_Typedef
 Code_Target_Numeral
 Bit_Representation
 Bits_Bit
 Phantom_Type
 RegExp
 Word_Miscellaneous
 Bits_Int
 Cardinality
 Isa_MOF
 Numeral_Type
 Bool_List_Representation
 Type_Length
 Word
 Isa_DOF
 CENELEC_50126
*)

session "HOL-Analysis-AutoCorres" = "HOL-Analysis" +
  theories [document=false]
    "autocorres-1.3/autocorres/AutoCorres"


session "Odo" = "HOL-Analysis-AutoCorres" +
  description {* The Toplevel Requirement Documents of the Odometrie Service *}
  options [document = pdf,document_variants="document:outline=/proof,/ML",document_output=output,quick_and_dirty]
  theories [document=false]
    "ontology_support/CENELEC_50126"
    "Real"
    "~~/src/HOL/Word/Word"
    "Monads"
    "Assert"
  theories
    "Odo_ReqAna"
    "Odo_Design"
  document_files
     "root.tex"
     "root.bib"
     "main.tex"
     "titlepage.tex"

(* examples of s.th. more complex: 
session "HOL-TestGen" (main) = "HOL-TestGenLib" +
  description {* HOL-TestGen *}
  theories 
    "codegen_fsharp/Code_String_Fsharp"
    "codegen_fsharp/Code_Char_chr_Fsharp"
    "codegen_fsharp/Code_Integer_Fsharp" 
    "codegen_fsharp/Code_Char_Fsharp"
    "Testing"
    "IOCO"
*)
