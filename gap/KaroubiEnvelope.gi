#############################################################################
##
##                  KaroubiEnvelope package
##
##  Copyright 2018, Maxime Flin, Université Paris Diderot
##  	      	    Daniel Juteau, Université Paris Diderot
##
##
#############################################################################

LoadPackage( "AttributeCategoryForCAP" );

DeclareRepresentation( "IsKaroubiObjectRep",
        IsCapCategoryObject and IsKaroubiObject and IsAttributeStoringRep,
        [ ] );

DeclareRepresentation( "IsKaroubiMorphismRep",
        IsCapCategoryMorphism and IsKaroubiMorphism and IsAttributeStoringRep,
	[ ] );

####################################
#
# families and types:
#
####################################

# new families:
BindGlobal( "TheFamilyOfKaroubiObjects",
        NewFamily( "TheFamilyOfKaroubiObjects" ) );

BindGlobal( "TheFamilyOfKaroubiMorphisms",
        NewFamily( "TheFamilyOfKaroubiMorphisms" ) );

BindGlobal( "TheTypeOfKaroubiObjects",
        NewType( TheFamilyOfKaroubiObjects,
                IsKaroubiObjectRep ) );

BindGlobal( "TheTypeOfKaroubiMorphisms",
        NewType( TheFamilyOfKaroubiMorphisms,
		 IsKaroubiMorphismRep ) );


InstallMethod ( IsIdempotent,
	        [ IsCapCategoryMorphism ],
    function (f)
    return IsCongruentForMorphisms( PreCompose(f, f), f );
end);

####################################
##
## Attributes
##
####################################


InstallMethod( Idempotent,
	       [ IsKaroubiObject ],
    function ( obj )
         return ObjectAttributesAsList( obj )[1];
end);

InstallMethod( UnderlyingObject,
	       [ IsKaroubiObject ],
  UnderlyingCell );

InstallMethod( UnderlyingMorphism,
	       [ IsKaroubiMorphism ],
  UnderlyingCell );

# InstallMethod( UnderlyingCategory,
# 	       [ IsKaroubiCategory ],
#     function ( obj )
#         return UnderlyingCell( obj );
# end);

InstallMethod( IsFullObject,
	       [ IsKaroubiObject ],
    function ( obj )
        return Idempotent( obj ) = IdentityMorphism(UnderlyingObject(obj));
end);


####################################
##
## Operations
##
####################################


InstallMethod( UniversalSplitObject,
	       [ IsKaroubiMorphism ],
    function ( obj )
        return KaroubiObject( UnderlyingMorphism( obj ) );
end);

InstallMethod( UniversalMorphismIntoSplit,
	       [ IsKaroubiMorphism ],
    function (f)
    local e, r;
    e := Idempotent(Source(f));
    r := UnderlyingMorphism(f);
    return KaroubiMorphism(Source(f), PreCompose(e, r), KaroubiObject(r));
end);

InstallMethod( UniversalMorphismFromSplit,
	       [ IsKaroubiMorphism ],
    function (f)
    local e, r;
    e := Idempotent(Source(f));
    r := UnderlyingMorphism(f);
    return KaroubiMorphism(KaroubiObject(r), PreCompose(r, e), Source(f));
end);

####################################
##
## Constructors
##
####################################

InstallMethod( KaroubiEnvelope,
               [ IsCapCategory ],
               
  function( category )
    local karoubi_envelope, category_weight_list, structure_record, zero_object, triple, mor_const, obj_const;
    
    if not IsFinalized( category ) then
        Error( "category must be finalized" );
        return;
    fi;

    karoubi_envelope := CreateCapCategory( Concatenation( "Karoubi envelope of ", Name( category ) ) );

    structure_record := rec(
      underlying_category := category,
      category_with_attributes := karoubi_envelope
    );

    structure_record.object_type := TheTypeOfKaroubiObjects;
    structure_record.morphism_type := TheTypeOfKaroubiMorphisms;

    triple := EnhancementWithAttributes( structure_record );
    obj_const := triple[2];
    mor_const := triple[3];

    ##
    InstallMethod( KaroubiObject,
    		   [ IsCapCategoryMorphism ],
        function (idempotent)
	return obj_const(Source(idempotent), [idempotent]);
    end);

    InstallMethod( KaroubiMorphism,
    		   [ IsCapCategoryObject, IsCapCategoryMorphism, IsCapCategoryObject ],
        function (a, f, b)
	return mor_const(a, f, b);
    end);

    ##
    AddIsWellDefinedForObjects( karoubi_envelope,
        function( karoubi_envelope, object )
	local idem;
	idem := Idempotent(object);
        
        return IsWellDefinedForObjects( UnderlyingCell(object) ) and
	       IsWellDefinedForMorphisms( idem ) and
	       IsIdempotent( idem );
        
    end );

    AddIsWellDefinedForMorphisms( karoubi_envelope,
        function( mor )
	local e, f, p;
	e := Idempotent(Source(mor));
	f := Idempotent(Range(mor));
	p := UnderlyingCell(mor);
        
        return IsWellDefinedForMorphisms( UnderlyingCell(mor) ) and
	       IsCongruentForMorphisms( p, PreCompose(f, PreCompose(p, e)));
    end );

    ##
    AddIsEqualForObjects( karoubi_envelope,
        function( obj_1, obj_2 )
        return IsEqualForMorphisms( Idempotent(obj_1), Idempotent(obj_2) );
    end );

    AddIsEqualForMorphisms( karoubi_envelope,
        function( morphism_1, morphism_2 )
        return IsEqualForMorphisms( UnderlyingCell( morphism_1 ), UnderlyingCell( morphism_2 ) );
    end );

    AddIsCongruentForMorphisms( karoubi_envelope,
        function (m1, m2)
	return IsCongruentForMorphisms( UnderlyingCell(m1), UnderlyingCell(m2));
    end);

    ##
    AddIdentityMorphism( karoubi_envelope,
        function (obj)
	return KaroubiMorphism(obj, Idempotent(obj), obj);
    end);

    category_weight_list := category!.derivations_weight_list;

    if CurrentOperationWeight(category_weight_list, "ZeroObject") < infinity then
        AddZeroObject( karoubi_envelope,
	    function ()
	    return KaroubiObject(IdentityMorphism(ZeroObject(category)));
	end);
    fi;

    if CurrentOperationWeight(category_weight_list, "KernelObject") < infinity then
        AddKernelEmbedding( karoubi_envelope,
	    function (mor)
	    local e, ker, f, h;
	    f := UnderlyingMorphism(mor);
	    h := KernelEmbedding(f);
	    ker := KaroubiObject(IdentityMorphism(KernelObject(f)));
	    e := Idempotent(Source(mor));
	    return KaroubiMorphism(ker, PreCompose(h, e), Source(mor));
	end);


        AddKernelLift( karoubi_envelope,
	    function (mor, tmor)
	    local e, q, f, k, ker, phi;
	    phi := UnderlyingMorphism(mor);
	    f := UnderlyingMorphism(tmor);
	    e := Idempotent(Source(mor));
	    q := Idempotent(Source(tmor));
	    k := KernelEmbedding(phi);
	    ker := KaroubiObject(IdentityMorphism(Source(k)));
	    return KaroubiMorphism(Source(tmor), PreCompose(k, q), ker);
	end);
    fi;

    if CurrentOperationWeight(category_weight_list, "DirectSum") < infinity then
        AddDirectSum( karoubi_envelope,
	    function (obj_list)
	    return KaroubiObject(IdentityMorphism(DirectSum(List(obj_list, o -> UnderlyingObject(o)))));
	end);
    fi;

    Finalize( karoubi_envelope );
    return karoubi_envelope;
end );


