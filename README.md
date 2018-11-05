# talkdepzip
Dependently Typed Zippers over Dependent-Data-Type-Embedded DSLs

# Abstract
GADT (AKA Dependent-Data-Type) embedded DSLs have the advantage of being type-checked by the meta-language and are very easy to 
interpret. Unfortunately most people working with these DSLs know the difficulty involved when one wishes to transform part 
of the syntax tree. This talk proposes a method to address that issue through the introduction of a Huet Zipper implemented 
with dependent types. The talk will start by briefly introducing the concepts of dependent types (GADTs, pi types, and 
sigma types), along with a brief refresher on GADT-Embedded (HOAS) DSLs, before moving on to discuss the details of the 
zipper implementation proper in Idris. This talk aims to showcase how dependent types can be applied in interesting ways to 
tackle some otherwise difficult problems.
