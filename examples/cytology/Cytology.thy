theory Cytology
  imports "Isabelle_DOF.scholarly_paper"
begin

text\<open>A small example ontology for demonstration purposes.
     The presentation follows closely: \<^url>\<open>https://www.youtube.com/watch?v=URUJD5NEXC8\<close>.\<close>


datatype protein = filaments | motor_proteins | rna |dna |nucleolus

type_synonym desc = "string"

onto_class organelles   =   description :: desc

onto_class ribosomes    = organelles +    description :: desc
   
onto_class mytochondria = organelles +    description :: desc

onto_class golgi_apparatus = organelles + description :: desc

onto_class lysosome    = organelles +     description :: desc

text\<open>the control center of the cell:\<close>
onto_class nucleus = organelles +  
       description :: desc
       components  :: "protein list" <= "[nucleolus]" 

(* Not so nice construction to mimick inheritance on types useds in attribute positions. *)
datatype organelles' = mk\<^sub>r\<^sub>i\<^sub>b\<^sub>o\<^sub>s\<^sub>o\<^sub>m\<^sub>e\<^sub>s     (get_ribosomes:ribosomes)
                     | mk\<^sub>m\<^sub>y\<^sub>t\<^sub>o\<^sub>c\<^sub>h\<^sub>o\<^sub>n\<^sub>d\<^sub>r\<^sub>i\<^sub>a   (get_mytochondria:mytochondria)
                     | mk\<^sub>g\<^sub>o\<^sub>l\<^sub>g\<^sub>i\<^sub>_\<^sub>a\<^sub>p\<^sub>p\<^sub>a\<^sub>r\<^sub>a\<^sub>t\<^sub>u\<^sub>s (get_golgi_apparatus: golgi_apparatus)
                     | mk\<^sub>l\<^sub>y\<^sub>s\<^sub>o\<^sub>s\<^sub>o\<^sub>m\<^sub>e      (get_lysosome : lysosome)
                     | mk\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s       (get_nucleus : nucleus)

fun is\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s where "is\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s (mk\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s X) = True" | "is\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s ( _) = False"


definition is\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s 
  where "is\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s org \<equiv>  \<exists> tg d ta da . org  =  nucleus.make tg d ta da"
find_theorems (300) name:"Cytology" name:"nucleus"


onto_class cell = 
    name             :: string
    membrane         :: desc   <= "\<open>The outer boundary of the cell\<close>"
    cytoplasm        :: desc   <= "\<open>The liquid in the cell\<close>"
    cytoskeleton     :: desc   <= "\<open>includes the thread-like microfilaments\<close>"
    genetic_material :: "protein list" <= "[rna, dna]"

text\<open>Cells are devided into two categories: \<^emph>\<open>procaryotic\<close> cells (unicellular organisms some 
bacteria) without a substructuring in organelles and \<^emph>\<open>eucaryotic\<close> cells, as occurring in 
pluricellular organisms\<close>

onto_class procaryotic_cells = cell +
    name :: string

onto_class eucaryotic_cells = cell + 
    organelles :: "organelles' list"
    invariant has_nucleus :: "\<lambda>\<sigma>::eucaryotic_cells. \<exists> org \<in> set (organelles \<sigma>). is\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s org"
    \<comment>\<open>Cells must have at least one nucleus. However, this should be executable.\<close>

find_theorems (70)name:"eucaryotic_cells"
find_theorems name:has_nucleus

value "is\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s (mk\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s X)"

term \<open>eucaryotic_cells.organelles\<close>

value \<open>(eucaryotic_cells.organelles(eucaryotic_cells.make X Y Z Z Z [] 3 []))\<close>
value \<open>has_nucleus_inv(eucaryotic_cells.make X Y Z Z Z [] 3 [])\<close>


end
