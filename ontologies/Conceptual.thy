theory Conceptual
  imports "../Isa_Dof"
begin
  
doc_class A =
   x :: "string"  

doc_class B =
   y :: "string list"          <= "[]"

doc_class C = B +
   z :: "A option"             <= None

datatype enum = X1 | X2 | X3
   
doc_class D = B +
   a1 :: enum                  <= "X2"
   a2 :: int                   <= 0

doc_class F  = 
   r :: "thm list"
   b :: "(A \<times> B) set"   <= "{}"

doc_class M = 
   trace :: "(A + C + D + F) list"
   where "A . (C | D)* . [F]"
     
end     