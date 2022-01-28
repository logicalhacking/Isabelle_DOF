theory Mapped_PILIB_Ontology
  imports "Isabelle_DOF.Isa_DOF"

begin

text\<open>User Ontology\<close>

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