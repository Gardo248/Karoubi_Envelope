#############################################################################
##
##                  KaroubiEnvelope package
##
##  Copyright 2018, Maxime Flin, Université Paris Diderot
##  	      	    Daniel Juteau, Université Paris Diderot
##
#! @Chapter Karoubi Envelope of a Category
##
#############################################################################

#! Let $\mathbf{A}$ be a category.
#! We denote its Karoubi envelope by $\mathbf{K(A)}$.

####################################
##
#! @Section GAP Categories
##
####################################

#! @Description
#! The GAP category of objects in the
#! Karoubi envelope of a category.
#! @Arguments object
DeclareCategory( "IsKaroubiObject",
                 IsCapCategoryObject );

#! @Description
#! The GAP category of morphisms in the
#! Karoubi envelope of a category.
#! @Arguments object
DeclareCategory( "IsKaroubiMorphism",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Attributes
##
####################################

#! @Description
#! The argument is an object $a$ in the Karoubi envelope of a category.
#! The output is its underlying object in the original category.
#! @Returns an object in $\mathbf{A}$
#! @Arguments a
#TODO Why not an attribute?
DeclareOperation( "UnderlyingObject",
                  [ IsKaroubiObject ] );                  
		  
#! @Description
#! The argument is an object $a$ in the Karoubi envelope of a category.
#! The output is the idempotent of the underlying object
#! in the original category.
#! @Returns a morphism in $\mathbf{A}$
#! @Arguments a
DeclareAttribute( "Idempotent",
                  IsKaroubiObject );

#! @Description
#! The argument is a morphism $f$ in the Karoubi envelope of a category.
#! The output is the underlying morphism
#! in the original category.
#! @Returns a morphism in $\mathbf{A}$
#! @Arguments a
DeclareAttribute( "UnderlyingMorphism",
                  IsKaroubiMorphism );

#! @Description
#! The argument is a Karoubi envelope $C = \mathbf{K(A)}$.
#! The output is $\mathbf{A}$.
#! @Returns a category
#! @Arguments C
DeclareAttribute( "UnderlyingCategory",
                  IsCapCategory );


####################################
##
#! @Section Properties
##
####################################

#! @Description
#! The argument is a Karoubi object $a$.
#! The output is <C>true</C> if the underlying morphism is the identity,
#! so that $a$ can be considered as an object of the original category.
#! Otherwise the output is <C>false</C>.
#! @Returns a boolean
#! @Arguments a
DeclareProperty( "IsFullObject",
                  IsKaroubiObject );


####################################
##
#! @Section Operations
##
####################################

#! @Description
#! The argument is an idempotent $e:a\rightarrow a$ of the Karoubi envelope $\mathbf{K(A)}$.
#! The output is the universal objet that splits $e$
#! @Returns an object in $\mathbf{K(A)}$
#! @Arguments e
DeclareOperation( "UniversalSplitObject",
                  [ IsKaroubiMorphism ] );

#! @Description
#! The argument is an idempotent $e:a\rightarrow a$ of the Karoubi envelope $\mathbf{K(A)}$.
#! TODO
#! @Returns an morphism in $\mathbf{K(A)}$
#! @Arguments e
DeclareOperation( "UniversalMorphismIntoSplit",
                  [ IsKaroubiMorphism ] );

#! @Description
#! The argument is an idempotent $e:a\rightarrow a$ of the Karoubi envelope $\mathbf{K(A)}$.
#! TODO
#! @Returns an object in $\mathbf{K(A)}$
#! @Arguments e
DeclareOperation( "UniversalMorphismFromSplit",
                  [ IsKaroubiMorphism ] );


####################################
##
#! @Section Constructors
##
####################################


#! @Description
#! The argument is an idempotent $e:a\rightarrow a$.
#! The output is the object in the Karoubi envelope $\mathbf{K(A)}$
#! @Returns an object in $\mathbf{K(A)}$
#! @Arguments e
DeclareOperation( "KaroubiObject",
                  [ IsCapCategoryMorphism ] );

#! @Description
#! The arguments are $a\in\mathbf{K(A)}$, $b\in\mathbf{K(A)}$
#! and a morphism $f:a\rightarrow b$.
#! The output is the morphism in the Karoubi envelope $\mathbf{K(A)}$
#! @Returns an object in $\mathrm{Hom}_\mathbf{K(A)}(A, B)$
#! @Arguments a, b and f
DeclareOperation( "KaroubiMorphism",
                  [ IsCapCategoryObject, IsCapCategoryMorphism, IsCapCategoryObject ] );


#! @Description
#! The argument is a category $\mathbf{A}$.
#! The output is the Karoubi envelope  $\mathbf{K(A)}$.
#! @Returns a category
#! @Arguments A
DeclareAttribute( "KaroubiEnvelope",
                  IsCapCategory );


