session "Isabelle_DOF-Ontologies" = "Isabelle_DOF" + 
  options  [document = pdf, document_output = "output", document_build = dof]
  directories
    "CC_v3_1_R5"
    "Conceptual"
    "small_math"
    "CENELEC_50128"
  theories
    "document_setup"
    "document_templates"
    "CC_v3_1_R5/CC_v3_1_R5"
    "CC_v3_1_R5/CC_terminology"  
    "Conceptual/Conceptual"
    "small_math/small_math"
    "CENELEC_50128/CENELEC_50128"
    "CENELEC_50128/CENELEC_50128_Documentation"
  document_files
    "root.bib"
    "lstisadof-manual.sty"
    "preamble.tex"
    "figures/antiquotations-PIDE.png"
    "figures/srac-as-es-application.png"
    "figures/srac-definition.png"
