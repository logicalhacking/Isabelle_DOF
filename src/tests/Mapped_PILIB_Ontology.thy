theory Mapped_PILIB_Ontology
  imports "Isabelle_DOF.Isa_DOF"

begin

text\<open>
The following example is extract from this reference : 
CONTEXT-EXPLICATION IN CONCEPTUAL ONTOLOGIES: PLIB ONTOLOGIES AND THEIR USE FOR INDUSTRIAL DATA
Special issue of JAMS - Journal of Advanced Manufacturing Systems
By GUY PIERRA
\<close>

text\<open>Local Ontology\<close>

onto_class Item =
  item_name :: string

onto_class Product = Item +
  serial_number :: int
  provider :: string
  mass :: int

onto_class U_Software = Item +
  version :: int

onto_class Electronic_Component = Product +
  dimensions :: "int set"
  
datatype Hardware_Type = 
  Motherboard | 
  Expansion_Card | 
  Storage_Device | 
  Fixed_Media | 
  Removable_Media |
  Input_Device |
  Output_Device

onto_class Computer_Hardware = Product +
  type :: Hardware_Type
  composed_of :: "Product set" 

text\<open>Reference Ontology\<close>

onto_class Resource =
  resource_name :: string

onto_class Electronic = Resource +
  provider :: string
  manufacturer :: string

onto_class Component = Electronic +
  mass :: int
  dimensions :: "int set" 

onto_class Simulation_Model = Electronic +
  type :: string

onto_class Informatic = Resource +
  att :: string 
  
onto_class Hardware = Informatic +
  type :: Hardware_Type
  mass :: int
  composed_of :: "Component set" 
  
onto_class R_Software = Informatic +
  version :: int


text\<open>

Isa_DOF framework does not assume that all documents reference the same ontology. 
Each document may build its local ontology without any external reference. 
It may also build it based upon one or several reference ontologies (i.e., standard ones). 

The relationship between the local ontology and the reference one is formalised using a morphism function. 
More precisely, a class of a local ontology may be described as a consequence of a transformation applied
to one or several other class(es) defined in other ontologies. This means that each instance of the former can be 
computed from one or more instances of the latter. 

Thanks to the morphism relationship, the obtained class may either import properties (definitions are preserved) 
or map properties (the properties are different but are semantically equivalent) that are defined in the referenced class(es). 
It may also define additional properties.
\<close>

definition Item_to_Resource_morphism
  where "Item_to_Resource_morphism (\<sigma>::'a Item_scheme) =
        \<lparr> tag_attribute = 0::int
          , resource_name = item_name \<sigma>
        \<rparr>" 


definition U_Software_to_R_Software_morphism
  where "U_Software_to_R_Software_morphism (\<sigma>::'a U_Software_scheme) =
        \<lparr> tag_attribute = 1::int
          , resource_name = Item.item_name \<sigma>
          , att = ''''
          , version = U_Software.version \<sigma>
        \<rparr>" 


end