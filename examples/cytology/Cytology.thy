theory Cytology
  imports "Isabelle_DOF.scholarly_paper"
begin

text\<open>A small example ontology for demonstration purposes.
     The presentation follows closely: \<^url>\<open>https://www.youtube.com/watch?v=URUJD5NEXC8\<close>.\<close>


datatype protein = filaments | motor_proteins | rna |dna |nucleolus


onto_class organelles =   description :: string

onto_class ribosomes = organelles +       description :: string
   
onto_class mytochondria = organelles +    description :: string

onto_class golgi_apparatus = organelles + description :: string

onto_class lysosome = organelles + description :: string


text\<open>the control center of the cell:\<close>
onto_class nucleus = organelles +  
       description :: string
       components  :: "protein list" <= "[nucleolus]" 

definition is_nucleus 
  where "is_nucleus org \<equiv>  \<exists> tg d ta da . org  =  nucleus.make tg d ta da"
find_theorems (300) name:"Cytology" name:"nucleus"


onto_class cell = 
    name             :: string
    membrane         :: string   <= "\<open>The outer boundary of the cell\<close>"
    cytoplasm        :: string   <= "\<open>The outer boundary of the cell\<close>"
    cytoskeleton     :: string   <= "\<open>includes the thread-like microfilaments\<close>"
    genetic_material :: "protein list" <= "[rna, dna]"

text\<open>Cells are devided into two categories: \<^emph>\<open>procaryotic\<close> cells (unicellular organisms some 
bacteria) without a substructuring in organelles and \<^emph>\<open>eucaryotic\<close> cells, as occurring in 
pluricellular organisms\<close>

onto_class procaryotic_cells = cell +
    name :: string

onto_class eucaryotic_cells = cell + 
    organelles :: "organelles list"
(*
invariant has_nucleus :: "\<lambda>\<sigma>::eucaryotic_cells. \<exists> org \<in> set (organelles \<sigma>). is_nucleus org"
*)
 
end
