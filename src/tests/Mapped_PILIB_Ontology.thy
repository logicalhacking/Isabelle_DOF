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

text\<open>
\<^dof> framework does not assume that all documents reference the same ontology. 
Each document may build its local ontology without any external reference. 
It may also build it based upon one or several reference ontologies (i.e., standard ones). 

The relationship between the local ontology and the reference one is formalised using a morphism function. 
More precisely, a class of a local ontology may be described as a consequence of a transformation applied
to one or several other class(es) defined in other ontologies. This means that each instance of the former can be 
computed from one or more instances of the latter. 
\<close>

(* Reference Ontology *)
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
  invariant c1 :: "mass \<sigma> = sum(map Component.mass (composed_of \<sigma>))"

onto_class R_Software = Informatic +
  version :: int

text\<open>
To illustrate this process, we use the reference ontology (considered as a standard) described in the listing X, defining the Resource, Electronic, Component,
Informatic, Hardware and Software concepts (or classes). Each class contains a set of attributes or properties and some local invariants. 

In our example, we focus on the Hardware class containing a mass attribute and composed of a list of components with a mass attribute formalising 
the mass value of each component. The Hardware class also contains a local invariant ''c1'' to define a constraint linking the global mass of a Hardware 
object with the masses of its own components.  
\<close>

(* Local Ontology *)
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
  invariant c2 :: "Product.mass \<sigma> = sum(map Product.mass (composed_of \<sigma>))"

text\<open>
For the needs of our document, we have defined a simple ontology to classify Software and Hardware objects.
This ontology is described in listing X and defines the Item, Product, Computer_Software and Computer_Hardware concepts.
As for the reference ontology, we focus on the Computer_Hardware class defined as a list of products characterised by their mass value. 
This class contains a local invariant to guarantee that its own mass value equals the sum of all the masses of the products composing the object.
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
To check the coherence of our local ontology, we define some  transformation rules as a mapping applied to one or several 
other class(es) described in the reference ontology.
\<close>


text\<open>
Thanks to the morphism relationship, the obtained class may either import properties (definitions are preserved) 
or map properties (the properties are different but are semantically equivalent) that are defined in the referenced class(es). 
It may also define additional properties.

As shown by our example, the structure of a (user) ontology may be quite different from the one of a standard ontology she references. 
\<close>

text\<open>Now we check that the invariant is preserved through the morphism:\<close>

lemma inv_c2_preserved :
  "c2_inv \<sigma> \<Longrightarrow> c1_inv (Computer_Hardware_to_Hardware_morphism \<sigma>)"
  unfolding c1_inv_def c2_inv_def Computer_Hardware_to_Hardware_morphism_def  
  by auto

lemma Computer_Hardware_to_Hardware_morphism_total :
  "Computer_Hardware_to_Hardware_morphism ` ({X::Computer_Hardware. c2_inv X}) \<subseteq> ({X::Hardware. c1_inv X})"
  using inv_c2_preserved 
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