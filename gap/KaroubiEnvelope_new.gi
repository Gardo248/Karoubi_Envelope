InstallMethod( KaroubiEnvelope,
    "for a CAP category",
    [ IsCapCategory ],
    function( C )
    local KarEnvC;

    KarEnvC := CreateCapCategoryWithDataTypes(
        Concatenation( "KaroubiEnvelope(", Name( C ), ")" ),
        IsKaroubiEnvelope,
        IsKaroubiObject,
        IsKaroubiMorphism,
        IsCapCategoryTwoCell,
        CapJitDataTypeOfMorphismOfCategory( C ),
        CapJitDataTypeOfMorphismOfCategory( C ),
    fail );

    #note: I set the source category C as the Underlying category of the output category KarEnvC
    SetUnderlyingCategory( KarEnvC, C );
     
    #Q: Is this a good definition? I will postpone the check that the morphism is an idempotent inside the IsWellDefinedForObject.
    #Q: Should I eliminate the datum of the source of the idempotent? Perhaps turn it into an operation.  
    AddObjectConstructor( KarEnvC,
        function( KarEnvC, idempotent )
        return CreateCapCategoryObjectWithAttributes( KarEnvC, IdempotentDatum, idempotent );
        # option with the datum of the source inside the object datum:
        # return CreateCapCategoryObjectWithAttributes( KarEnvC, IdempotentDatum, idempotent, UnderlyingSourceOfIdempotent, Source(idempotent) );
    end );

    AddObjectDatum( KarEnvC,
        function ( KarEnvC, obj )
            return IdempotentDatum ( obj );
    end );

#not much interesting idea: 
# In case I want to separate the datum of the underlying object (the source of the idempotent) from the constructor, I can do it in this way, adding the attribute "UnderlyingObjectForKaroubiObjects" in the declaration file
    # InstallMethod(UnderlyingObjectForKaroubiObjects,
    #             [ IsKaroubiObject ],
    #     function (obj)
    #     return Source( IdempotentDatum (obj) );
    # end);

    if CanCompute( C, "IsCongruentForMorphisms" ) then
        AddIsWellDefinedForObjects( KarEnvC,
            function ( KarEnvC, obj )
                local C, e;
                C := UnderlyingCategory( KarEnvC );
                e := IdempotentDatum ( obj );
                return IsCongruentForMorphisms( C, PreCompose( C, e, e ), e );
            end );
    fi;

    #Q: is it better to use IsCongruentForMorphisms or IsEqualForMorphisms?
    #The point is that Cap is functional and so I have to assure that equal inputs gives equal outputs!
    AddIsEqualForObjects( KarEnvC,
            function ( KarEnvC, obj1, obj2 )
                local C, e1, e2;
                C := UnderlyingCategory( KarEnvC );
                e1 := IdempotentDatum( obj1 );
                e2 := IdempotentDatum( obj2 );
                return IsEqualForMorphisms( C, e1, e2 );
            end );
 
    AddMorphismConstructor( KarEnvC,
            function ( KarEnvC, s, morph, t )
                return CreateCapCategoryMorphismWithAttributes( KarEnvC, s, t, UnderlyingMorphismDatum, morph );
            end );

    AddMorphismDatum( KarEnvC,
        function ( KarEnvC, morph )
            return UnderlyingMorphismDatum ( morph );
    end );

    if CanCompute( C, "IsEqualForMorphisms" ) then
        AddIsEqualForMorphisms( KarEnvC,
                function ( KarEnvC, morphism1, morphism2 )
                    local C, mor1, mor2;
                    C := UnderlyingCategory( KarEnvC );
                    mor1 := UnderlyingMorphismDatum ( morphism1 );
                    mor2 := UnderlyingMorphismDatum ( morphism2 );
                    return IsEqualForMorphisms( C, mor1, mor2 );
                end );
    fi;
    
        # Remember: these functions always assume that the morphisms are
        # indeed parallel.
    if CanCompute( C, "IsCongruentForMorphisms" ) then
        AddIsCongruentForMorphisms( KarEnvC,
            function ( KarEnvC, morphism1, morphism2 )
                local C, f1, f2;
                C := UnderlyingCategory( KarEnvC );
                f1 := UnderlyingMorphismDatum ( morphism1 );
                f2 := UnderlyingMorphismDatum ( morphism2 );
                return IsCongruentForMorphisms( C, f1, f2 );
            end );
    fi;

    if CanCompute( C, "IsWellDefinedForMorphismsWithGivenSourceAndRange" ) and CanCompute( C, "IsCongruentForMorphisms" ) and CanCompute( C, "IsWellDefinedForObjects" ) then
            AddIsWellDefinedForMorphisms( KarEnvC,
                function ( KarEnvC, f )
                    local C, f_u, s_u, t_u, e_s, e_t;
                    C := UnderlyingCategory( KarEnvC );
                    f_u := UnderlyingMorphismDatum( f );
                    e_s := IdempotentDatum( Source( f ) );
                    e_t := IdempotentDatum( Target ( f ) );
                    s_u := Source ( e_s );
                    t_u := Source ( e_t );
                    return IsWellDefinedForMorphismsWithGivenSourceAndRange( C, s_u, f_u, t_u ) and IsWellDefinedForObjects( C, s_u ) and
                    IsWellDefinedForObjects( C, t_u ) and IsCongruentForMorphisms( f_u, PreCompose( e_s, PreCompose( f_u, e_t ) ) );
                end );
        fi;

    AddIdentityMorphism( KarEnvC,
            function ( KarEnvC, object )
                local C, idempotent;
                C := UnderlyingCategory( KarEnvC );
                idempotent := IdempotentDatum( object ) ;
                return MorphismConstructor( KarEnvC, object, idempotent, object );
            end );

    AddPreCompose( KarEnvC,
            function ( KarEnvC, f, g )
                #    f     g
                # x --> y --> z
                local C, x, z, f_under, g_under;
                C := UnderlyingCategory( KarEnvC );
                x := Source( f ) ;
                z := Target( g );
                f_under := UnderlyingMorphismDatum( f );
                g_under := UnderlyingMorphismDatum( g );
                return MorphismConstructor( KarEnvC, x, PreCompose( C, f_under, g_under ), z );
            end );

    #note: from now on we implement the preservation of structures of the underlying category C

    #note: preservation of monoidal structure
    if HasIsMonoidalCategory( C ) and IsMonoidalCategory( C ) then
        SetIsMonoidalCategory( KarEnvC, true );

        if CanCompute( C, "TensorUnit" ) then 
            #note: tensor unit
            AddTensorUnit( KarEnvC,
            function( KarEnvC )
                local C, unit, id_unit;
                C := UnderlyingCategory( KarEnvC );
                unit := TensorUnit( C );
                id_unit := IdentityMorphism( C, unit );
                return ObjectConstructor( KarEnvC, id_unit );
            end );
        fi; 

        if CanCompute( C, "TensorProductOnMorphisms" ) then
            #note: tensor product on objects
            AddTensorProductOnObjects( KarEnvC,
            function ( KarEnvC, x, y )
                local C, e_x, e_y;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                e_y := IdempotentDatum( y );
                return ObjectConstructor( KarEnvC, TensorProductOnMorphisms( C, e_x, e_y ) );
            end );

            #note: tensor product on morphisms
            AddTensorProductOnMorphismsWithGivenTensorProducts( KarEnvC,
            function ( KarEnvC, source, phi1, phi2, target )
                local C, phi1_under, phi2_under;
                C := UnderlyingCategory( KarEnvC );
                phi1_under := UnderlyingMorphismDatum( phi1 );
                phi2_under := UnderlyingMorphismDatum( phi2 );
                return MorphismConstructor( KarEnvC, source, TensorProductOnMorphisms( C, phi1_under, phi2_under ), target );
            end );
        fi;

        #note: left unitor
        if CanCompute( C, "LeftUnitor") then
            AddLeftUnitorWithGivenTensorProduct( KarEnvC, 
            function( KarEnvC, x, one_times_x )
                local C, Karunit, e_x, under_x, leftunitor_under;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source(e_x);
                leftunitor_under := LeftUnitor( under_x );
                return MorphismConstructor( KarEnvC, one_times_x, leftunitor_under, x );
            end );
        fi;

        #note: inverse of left unitor
        if CanCompute( C, "LeftUnitorInverse") then
            AddLeftUnitorInverseWithGivenTensorProduct( KarEnvC, 
            function( KarEnvC, x, one_times_x )
                local C, Karunit, e_x, under_x, leftunitorinv_under;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source(e_x);
                leftunitorinv_under := LeftUnitorInverse( under_x );
                return MorphismConstructor( KarEnvC, x, leftunitorinv_under, one_times_x );
            end );
        fi;

        #note: right unitor
        if CanCompute( C, "RightUnitor") then
            AddRightUnitorWithGivenTensorProduct( KarEnvC, 
            function( KarEnvC, x, x_times_one )
                local C, Karunit, e_x, under_x, rightunitor_under;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source(e_x);
                rightunitor_under := RightUnitor( under_x );
                return MorphismConstructor( KarEnvC, x_times_one, rightunitor_under, x );
            end );
        fi;

        #note: inverse of right unitor
        if CanCompute( C, "RightUnitorInverse") then
            AddRightUnitorInverseWithGivenTensorProduct( KarEnvC, 
            function( KarEnvC, x, x_times_one )
                local C, Karunit, e_x, under_x, rightunitorinv_under;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source(e_x);
                rightunitorinv_under := RightUnitorInverse( under_x );
                return MorphismConstructor( KarEnvC, x, rightunitorinv_under, x_times_one );
            end );
        fi;

        #note: associator from right to left
        if CanCompute( C, "AssociatorRightToLeft" ) then
            AddAssociatorRightToLeftWithGivenTensorProducts( KarEnvC, 
            function( KarEnvC, source, x, y, z, target )
                #source = x otimes ( y otimes z )
                #target = ( x otimes y ) otimes z 
                local C, e_x, e_y, e_z, under_x, under_y, under_z;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source( e_x );
                e_y := IdempotentDatum( y );
                under_y := Source( e_y );
                e_z := IdempotentDatum( z );
                under_z := Source( e_z );
                return MorphismConstructor( KarEnvC, source, AssociatorRightToLeft( under_x, under_y, under_z ), target );
            end );
        fi;

        #note: associator from left to right
        if CanCompute( C, "AssociatorLeftToRight" ) then
            AddAssociatorLeftToRightWithGivenTensorProducts( KarEnvC, 
            function( KarEnvC, source, x, y, z, target )
                #source = ( x otimes y ) otimes z 
                #target = x otimes ( y otimes z )
                local C, e_x, e_y, e_z, under_x, under_y, under_z;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source( e_x );
                e_y := IdempotentDatum( y );
                under_y := Source( e_y );
                e_z := IdempotentDatum( z );
                under_z := Source( e_z );
                return MorphismConstructor( KarEnvC, source, AssociatorLeftToRight( under_x, under_y, under_z ), target );
            end );
        fi;
    fi;

    
    

    #TODO: check in example/test file that righ unitor and its inverse are effectively inverses, same for the left one

    #preservation of pre-additive structure

    #TODO: set the fact that, if C is a preadditive cat, then also its Karoubi envelope is. At the moment the code IsAbCategory( kar ) give an error
    
    if ( HasIsAbCategory( C ) and IsAbCategory( C ) ) then
        SetIsAbCategory( KarEnvC, true );

        #note: zero morphism between any two objects in KarEnvC
        if CanCompute( C, "ZeroMorphism" ) then
            AddZeroMorphism( KarEnvC,
            function( KarEnvC, x, y )
                local C, e_x, e_y, under_x, under_y;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                e_y := IdempotentDatum( y );
                under_x := Source( e_x );
                under_y := Source( e_y );
                return MorphismConstructor( KarEnvC, x, ZeroMorphism( under_x, under_y ), y );
            end );
        fi;

        #note: addition for morphisms
        #TODO: add in the example/test file a check that the congruence is compatible with the addition
        if CanCompute( C, "AdditionForMorphisms" ) then
            AddAdditionForMorphisms( KarEnvC, 
            function( KarEnvC, phi1, phi2)
                local C, s, t, phi1_under, phi2_under;
                C := UnderlyingCategory( KarEnvC );
                s := Source( phi1 );
                t := Target( phi1 );
                phi1_under := UnderlyingMorphismDatum( phi1 );
                phi2_under := UnderlyingMorphismDatum( phi2 );
                return MorphismConstructor( KarEnvC, s, AdditionForMorphisms( phi1_under, phi2_under ), t );
            end );
        fi;

        #note: additive inverse for morphisms
        if CanCompute( C, "AdditiveInverseForMorphisms" ) then
            AddAdditiveInverseForMorphisms( KarEnvC, 
            function( KarEnvC, phi)
                local C, s, t, phi_under;
                C := UnderlyingCategory( KarEnvC );
                s := Source( phi );
                t := Target( phi );
                phi_under := UnderlyingMorphismDatum( phi );
                return MorphismConstructor( KarEnvC, s, AdditiveInverseForMorphisms( phi_under ), t );
            end );
        fi;
    fi;

    #note: preservation of zero object

    if HasIsCategoryWithZeroObject( C ) and IsCategoryWithZeroObject( C ) then
        SetIsCategoryWithZeroObject( KarEnvC, true );

        if CanCompute( C, "ZeroObject" ) then
            AddZeroObject(  KarEnvC, 
            function( KarEnvC )
                local C, zero_C;
                C := UnderlyingCategory( KarEnvC );
                zero_C := ZeroObject( C );
                return ObjectConstructor( KarEnvC, IdentityMorphism( zero_C ) );
            end );
        fi; 

        if CanCompute( C, "UniversalMorphismFromZeroObject" ) then
            AddUniversalMorphismFromZeroObjectWithGivenZeroObject( KarEnvC,
            function( KarEnvC, x, zero )
                local C, e_x, under_x;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source( e_x );
                return MorphismConstructor( KarEnvC, zero, UniversalMorphismFromZeroObject( under_x ), x );
            end );

            if CanCompute( C, "UniversalMorphismIntoZeroObject" ) then
            AddUniversalMorphismIntoZeroObjectWithGivenZeroObject( KarEnvC,
            function( KarEnvC, x, zero )
                local C, e_x, under_x;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source( e_x );
                return MorphismConstructor( KarEnvC, zero, UniversalMorphismIntoZeroObject( under_x ), x );
            end );
        fi;
        fi;
    fi;

    #Q: is it correct? Is there something I didn't considered?
    #Q: is it enough to implement the coproduct, and then the product is obtained conjugating with the opposite category?
    #Q: it is possible that we can compute the coproduct only for some objects in the category. In this case, is the precondition CanCompute("Coproduct") the right check or there is a better check to do?
    #note: preservation of coproducts

    if CanCompute( C, "Coproduct" ) and CanCompute( C, "UniversalMorphismFromCoproductWithGivenCoproduct" ) and CanCompute( C, "InjectionOfCofactorOfCoproductWithGivenCoproduct" ) then
        AddCoproduct( KarEnvC,
        function( KarEnvC, L )
            local C, e_L, under_L, coprod_under_L, idempotent_of_coproduct;
            C := UnderlyingCategory( KarEnvC );
            e_L := List( L, x -> IdempotentDatum( x ) );
            under_L := List( e_L, e_x -> Source( e_x ) );
            coprod_under_L := Coproduct( C, under_L );
            idempotent_of_coproduct := UniversalMorphismFromCoproduct( C, under_L, coprod_under_L,
                                List( [ 1 .. Length( under_L ) ], k -> PreCompose( C, e_L[k], InjectionOfCofactorOfCoproductWithGivenCoproduct( C, under_L, k, coprod_under_L ) ) ) );
            return ObjectConstructor( KarEnvC, idempotent_of_coproduct );
        end );

        AddInjectionOfCofactorOfCoproductWithGivenCoproduct( KarEnvC,
        function( KarEnvC, L, k, coprod )
            local C, e_L, under_L, under_coprod;
            C := UnderlyingCategory( KarEnvC );
            e_L := List( L, x -> IdempotentDatum( x ) );
            under_L := List( e_L, e_x -> Source( e_x ) );
            under_coprod := Source( IdempotentDatum( coprod ) );
            return MorphismConstructor( KarEnvC, L[k], PreCompose( C, e_L[k], UniversalMorphismFromCoproductWithGivenCoproduct( C, under_L, k, under_coprod ) ), coprod ); 
        end );

        AddUniversalMorphismFromCoproductWithGivenCoproduct( KarEnvC,
        function( KarEnvC, L, z, tao, coprod )
            local C, e_L, under_L, under_tao, e_z, under_z, under_coprod;
            C := UnderlyingCategory( KarEnvC );
            e_L := List( L, x -> IdempotentDatum( x ) );
            under_L := List( e_L, e_x -> Source( e_x ) );
            under_tao := List( tao, phi -> UnderlyingMorphismDatum( phi ) );
            e_z := IdempotentDatum( z );
            under_z := Source( e_z );
            under_coprod := Source( IdempotentDatum( coprod ) );
            #note: the element phi = under_tao[k] in under_tao are morphism commuting with the idempotents, i.e. PreCompose( Precompose( e_z, phi ), e_L[k] ) 
        return MorphismConstructor( KarEnvC, coprod, UniversalMorphismFromCoproductWithGivenCoproduct( C, under_L, under_z, under_tao, under_coprod ), z );
        end );
    fi;

    #note: preservation of structures to be implemented in case we need them

    if HasIsEnrichedOverCommutativeRegularSemigroup( C ) and IsEnrichedOverCommutativeRegularSemigroup( C ) then
        SetIsEnrichedOverCommutativeRegularSemigroup( KarEnvC, true );
    fi;

    if HasIsCategoryWithTerminalObject( C ) and IsCategoryWithTerminalObject( C ) then
        SetIsCategoryWithTerminalObject( KarEnvC, true );
    fi;

    if HasIsCategoryWithInitialObject( C ) and IsCategoryWithInitialObject( C ) then
        SetIsCategoryWithInitialObject( KarEnvC, true );
    fi;

    if HasIsAdditiveMonoidalCategory( C ) and IsAdditiveMonoidalCategory( C ) then
        SetIsAdditiveMonoidalCategory( KarEnvC, true );
    fi;

    # if Has( C ) and ( C ) then
    #     Set( KarEnvC, true );
    # fi;

    Finalize( KarEnvC );
  
    return KarEnvC;
end );