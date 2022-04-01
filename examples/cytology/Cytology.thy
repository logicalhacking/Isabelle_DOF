theory Cytology
  imports "Isabelle_DOF.scholarly_paper"
begin

text\<open>A small example ontology for demonstration purposes.
     The presentation follows closely: \<^url>\<open>https://www.youtube.com/watch?v=URUJD5NEXC8\<close>.\<close>


datatype protein = filaments | motor_proteins | rna | dna |nucleolus

type_synonym desc = "string"

onto_class organelles   =   description :: desc

find_theorems (60) name:"organelles"

term "Cytology.organelles.make"

onto_class ribosomes    = organelles +    description :: desc
   
onto_class mytochondria = organelles +    description :: desc

onto_class golgi_apparatus = organelles + description :: desc

onto_class lysosome    = organelles +     description :: desc

text\<open>the control center of the cell:\<close>
onto_class nucleus = organelles +  
       description :: desc
       components  :: "protein list" <= "[nucleolus]" 

(* Not so nice construction to mimick inheritance on types useds in attribute positions. *)
datatype organelles' = upcast\<^sub>r\<^sub>i\<^sub>b\<^sub>o\<^sub>s\<^sub>o\<^sub>m\<^sub>e\<^sub>s     (get_ribosomes:ribosomes)
                     | upcast\<^sub>m\<^sub>y\<^sub>t\<^sub>o\<^sub>c\<^sub>h\<^sub>o\<^sub>n\<^sub>d\<^sub>r\<^sub>i\<^sub>a   (get_mytochondria:mytochondria)
                     | upcast\<^sub>g\<^sub>o\<^sub>l\<^sub>g\<^sub>i\<^sub>_\<^sub>a\<^sub>p\<^sub>p\<^sub>a\<^sub>r\<^sub>a\<^sub>t\<^sub>u\<^sub>s (get_golgi_apparatus: golgi_apparatus)
                     | upcast\<^sub>l\<^sub>y\<^sub>s\<^sub>o\<^sub>s\<^sub>o\<^sub>m\<^sub>e      (get_lysosome : lysosome)
                     | upcast\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s       (get_nucleus : nucleus)

fun is\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s where "is\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s (upcast\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s X) = True" | "is\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s ( _) = False"
(* ... *)
fun downcast\<^sub>r\<^sub>i\<^sub>b\<^sub>o\<^sub>s\<^sub>o\<^sub>m\<^sub>e\<^sub>s 
  where "downcast\<^sub>r\<^sub>i\<^sub>b\<^sub>o\<^sub>s\<^sub>o\<^sub>m\<^sub>e\<^sub>s (upcast\<^sub>r\<^sub>i\<^sub>b\<^sub>o\<^sub>s\<^sub>o\<^sub>m\<^sub>e\<^sub>s X) = X" | "downcast\<^sub>r\<^sub>i\<^sub>b\<^sub>o\<^sub>s\<^sub>o\<^sub>m\<^sub>e\<^sub>s _ = undefined"
fun downcast\<^sub>m\<^sub>y\<^sub>t\<^sub>o\<^sub>c\<^sub>h\<^sub>o\<^sub>n\<^sub>d\<^sub>r\<^sub>i\<^sub>a 
  where "downcast\<^sub>m\<^sub>y\<^sub>t\<^sub>o\<^sub>c\<^sub>h\<^sub>o\<^sub>n\<^sub>d\<^sub>r\<^sub>i\<^sub>a (upcast\<^sub>m\<^sub>y\<^sub>t\<^sub>o\<^sub>c\<^sub>h\<^sub>o\<^sub>n\<^sub>d\<^sub>r\<^sub>i\<^sub>a X) = X" | "downcast\<^sub>m\<^sub>y\<^sub>t\<^sub>o\<^sub>c\<^sub>h\<^sub>o\<^sub>n\<^sub>d\<^sub>r\<^sub>i\<^sub>a _ = undefined"
fun downcast\<^sub>g\<^sub>o\<^sub>l\<^sub>g\<^sub>i\<^sub>_\<^sub>a\<^sub>p\<^sub>p\<^sub>a\<^sub>r\<^sub>a\<^sub>t\<^sub>u\<^sub>s 
  where "downcast\<^sub>g\<^sub>o\<^sub>l\<^sub>g\<^sub>i\<^sub>_\<^sub>a\<^sub>p\<^sub>p\<^sub>a\<^sub>r\<^sub>a\<^sub>t\<^sub>u\<^sub>s (upcast\<^sub>g\<^sub>o\<^sub>l\<^sub>g\<^sub>i\<^sub>_\<^sub>a\<^sub>p\<^sub>p\<^sub>a\<^sub>r\<^sub>a\<^sub>t\<^sub>u\<^sub>s X) = X" | "downcast\<^sub>g\<^sub>o\<^sub>l\<^sub>g\<^sub>i\<^sub>_\<^sub>a\<^sub>p\<^sub>p\<^sub>a\<^sub>r\<^sub>a\<^sub>t\<^sub>u\<^sub>s _ = undefined"
fun downcast\<^sub>l\<^sub>y\<^sub>s\<^sub>o\<^sub>s\<^sub>o\<^sub>m\<^sub>e 
  where "downcast\<^sub>l\<^sub>y\<^sub>s\<^sub>o\<^sub>s\<^sub>o\<^sub>m\<^sub>e (upcast\<^sub>l\<^sub>y\<^sub>s\<^sub>o\<^sub>s\<^sub>o\<^sub>m\<^sub>e X) = X" | "downcast\<^sub>l\<^sub>y\<^sub>s\<^sub>o\<^sub>s\<^sub>o\<^sub>m\<^sub>e _ = undefined"
fun downcast\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s 
  where "downcast\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s (upcast\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s X) = X" | "downcast\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s _ = undefined"




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
    \<comment> \<open>Cells must have at least one nucleus. However, this should be executable.\<close>

find_theorems (70)name:"eucaryotic_cells"
find_theorems name:has_nucleus

value "is\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s (mk\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s X)"

term \<open>eucaryotic_cells.organelles\<close>

value \<open>(eucaryotic_cells.organelles(eucaryotic_cells.make X Y Z Z Z [] 3 []))\<close>

value \<open>has_nucleus_inv(eucaryotic_cells.make X Y Z Z Z [] 3 [])\<close>

value \<open>has_nucleus_inv(eucaryotic_cells.make X Y Z Z Z [] 3 
                         [upcast\<^sub>n\<^sub>u\<^sub>c\<^sub>l\<^sub>e\<^sub>u\<^sub>s (nucleus.make a b c d [])])\<close>



end
