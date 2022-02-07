theory Mapped_PILIB_Ontology
  imports "Isabelle_DOF.Isa_DOF"


begin


define_shortcut* hol      \<rightleftharpoons> \<open>HOL\<close>
                 isabelle \<rightleftharpoons> \<open>Isabelle/HOL\<close>
                 dof      \<rightleftharpoons> \<open>Isabelle/DOF\<close>
                 LaTeX    \<rightleftharpoons> \<open>LaTeX\<close>
                 html     \<rightleftharpoons> \<open>HTML\<close>
                 csp      \<rightleftharpoons> \<open>CSP\<close>      \<comment>\<open>obsolete\<close>
                 holcsp   \<rightleftharpoons> \<open>HOL-CSP\<close>  \<comment>\<open>obsolete\<close> 

text\<open>
The following example is extract from this reference : 
CONTEXT-EXPLICATION IN CONCEPTUAL ONTOLOGIES: PLIB ONTOLOGIES AND THEIR USE FOR INDUSTRIAL DATA
Special issue of JAMS - Journal of Advanced Manufacturing Systems
By GUY PIERRA
\<close>

term\<open>fold (+) S 0\<close>  

definition sum 
  where "sum S = (fold (+) S 0)"

  
datatype Hardware_Type = 
  Motherboard | 
  Expansion_Card | 
  Storage_Device | 
  Fixed_Media | 
  Removable_Media |
  Input_Device |
  Output_Device


text\<open>Reference Ontology\<close>

onto_class Resource =
  name :: string

onto_class Electronic = Resource +
  provider :: string
  manufacturer :: string

onto_class Component = Electronic +
  mass :: int
  dimensions :: "int list" 

onto_class Simulation_Model = Electronic +
  type :: string

onto_class Informatic = Resource +
  description :: string

onto_class Hardware = Informatic +
  type :: Hardware_Type
  mass :: int
  composed_of :: "Component list" 
  invariant c2 :: "mass \<sigma> = sum(map Component.mass (composed_of \<sigma>))"

onto_class R_Software = Informatic +
  version :: int


text\<open>
\<^dof> framework does not assume that all documents reference the same ontology. 
Each document may build its local ontology without any external reference. 
It may also build it based upon one or several reference ontologies (i.e., standard ones). 
\<close>


text\<open>Local Ontology\<close>

onto_class Item =
  name :: string

onto_class Product = Item +
  serial_number :: int
  provider :: string
  mass :: int

onto_class Computer_Software = Item +
  version :: int

onto_class Electronic_Component = Product +
  dimensions :: "int set"

onto_class Computer_Hardware = Product +
  type :: Hardware_Type
  composed_of :: "Product list" 
  invariant c1 :: "Product.mass \<sigma> = sum(map Product.mass (composed_of \<sigma>))"


text\<open>
The relationship between the local ontology and the reference one is formalised using a morphism function. 
More precisely, a class of a local ontology may be described as a consequence of a transformation applied
to one or several other class(es) defined in other ontologies. This means that each instance of the former can be 
computed from one or more instances of the latter. 
\<close>

definition Item_to_Resource_morphism
  where "Item_to_Resource_morphism (\<sigma>::'a Item_scheme) =
        \<lparr> 
          Resource.tag_attribute = 0::int , 
          Resource.name = name \<sigma>
        \<rparr>" 

definition Product_to_Component_morphism
  where "Product_to_Component_morphism (\<sigma>::'a Product_scheme) =
        \<lparr> 
          Resource.tag_attribute = 1::int ,
          Resource.name = name \<sigma> ,
          Electronic.provider  = Product.provider \<sigma> ,
          Electronic.manufacturer  = '''' ,
          Component.mass = Product.mass \<sigma> ,
          Component.dimensions = []
        \<rparr>" 

definition Computer_Hardware_to_Hardware_morphism
  where "Computer_Hardware_to_Hardware_morphism (\<sigma>::'a Computer_Hardware_scheme) =
        \<lparr>  
          Resource.tag_attribute = 2::int ,
          Resource.name = name \<sigma> ,
          Informatic.description = ''no description'', 
          Hardware.type = Computer_Hardware.type \<sigma> ,
          Hardware.mass = mass \<sigma> ,
          Hardware.composed_of = map Product_to_Component_morphism (Computer_Hardware.composed_of \<sigma>)
        \<rparr>" 


text\<open>
Thanks to the morphism relationship, the obtained class may either import properties (definitions are preserved) 
or map properties (the properties are different but are semantically equivalent) that are defined in the referenced class(es). 
It may also define additional properties.
\<close>

text\<open>Now we check that the invariant is preserved through the morphism:\<close>

lemma inv_c1_preserved :
  "c1_inv \<sigma> \<Longrightarrow> c2_inv (Computer_Hardware_to_Hardware_morphism \<sigma>)"
  unfolding c2_inv_def c1_inv_def Computer_Hardware_to_Hardware_morphism_def  
  by auto


lemma Computer_Hardware_to_Hardware_morphism_total :
  "Computer_Hardware_to_Hardware_morphism ` ({X::Computer_Hardware. c1_inv X}) \<subseteq> ({X::Hardware. c2_inv X})"
  using inv_c1_preserved 
  by auto

declare[[invariants_checking]]
declare[[invariants_checking_with_tactics]]

text*[c1::Component, mass=4]\<open>\<close>
text*[c2::Component, mass=4]\<open>\<close>

text*[h1::Hardware, mass=8, composed_of="[@{Component \<open>c1\<close>},@{Component \<open>c2\<close>}]"]\<open>\<close>
text*[h2::Hardware, mass=8, composed_of="[@{Component \<open>c1\<close>},@{Component \<open>c2\<close>}]"]\<open>\<close>

value*\<open>
sum (map Component.mass [@{Component \<open>c1\<close>},@{Component \<open>c2\<close>}])
\<close>

value*\<open>
@{Hardware \<open>h1\<close>} = @{Hardware \<open>h2\<close>}
\<close>

end