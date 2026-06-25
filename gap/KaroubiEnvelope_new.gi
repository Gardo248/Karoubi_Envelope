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
      
    AddObjectConstructor( KarEnvC,
        function( KarEnvC, idempotent )
            return CreateCapCategoryObjectWithAttributes( KarEnvC, IdempotentDatum, idempotent );
        end );

    AddObjectDatum( KarEnvC,
        function ( KarEnvC, obj )
            return IdempotentDatum ( obj );
    end );

    if CanCompute( C, "IsCongruentForMorphisms" ) then
        AddIsWellDefinedForObjects( KarEnvC,
            function ( KarEnvC, obj )
                local C, e;
                C := UnderlyingCategory( KarEnvC );
                e := IdempotentDatum( obj );
                return IsCongruentForMorphisms( C, PreCompose( C, e, e ), e );
            end );
    fi;

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

    #TODO: check in example/test file that righ unitor and its inverse are effectively inverses, same for the left one

    #note: preservation of pre-additive structure
    
    if HasIsAbCategory( C ) and IsAbCategory( C ) then
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

    #TODO: add preservation of enrichment
    if HasIsEnrichedOverCommutativeRegularSemigroup( C ) and IsEnrichedOverCommutativeRegularSemigroup( C ) then
        SetIsEnrichedOverCommutativeRegularSemigroup( KarEnvC, true );
    fi;

    #todo: add the if hasiscocartesian and is cocartesian then...
    #todo: if it is additive then derive the product and coproduct directly, else if it is cartesian or cocartesian derive it separately, also the zeroobject will be in the else stuff
    if HasIsAdditiveCategory( C ) and IsAdditiveCategory( C ) then
        SetIsAdditiveCategory( KarEnvC, true  );
        #TODO: write the preservation of additive structure

        #we define the zero object for additive category
        if CanCompute( C, "ZeroObject" ) then
            AddZeroObject(  KarEnvC, 
            function( KarEnvC )
                local C, zero_C;
                C := UnderlyingCategory( KarEnvC );
                zero_C := ZeroObject( C );
                return ObjectConstructor( KarEnvC, IdentityMorphism( C, zero_C ) );
            end );
        fi; 

        if CanCompute( C, "UniversalMorphismFromZeroObjectWithGivenZeroObject" ) then
            AddUniversalMorphismFromZeroObjectWithGivenZeroObject( KarEnvC,
            function( KarEnvC, x, zero )
                local C, e_x, under_x, under_zero;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source( e_x );
                under_zero := Source( IdempotentDatum( zero ) );
                return MorphismConstructor( KarEnvC, zero, UniversalMorphismFromZeroObjectWithGivenZeroObject( C, under_x, under_zero ), x );
            end );
        fi;

        if CanCompute( C, "UniversalMorphismIntoZeroObjectWithGivenZeroObject" ) then
            AddUniversalMorphismIntoZeroObjectWithGivenZeroObject( KarEnvC,
            function( KarEnvC, x, zero )
                local C, e_x, under_x, under_zero;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source( e_x );
                under_zero := Source( IdempotentDatum( zero ) );
                return MorphismConstructor( KarEnvC, zero, UniversalMorphismIntoZeroObjectWithGivenZeroObject( C, under_x, under_zero ), x );
            end );
        fi;
    else
        #note: preservation of coproducts
        #TODO: have a look to CoproductFunctorial... and to MorphismBetweenCoproducts (ToolsForCategoricalTowers)
        if HasIsCocartesianCategory( C ) and IsCocartesianCategory( C ) then
            SetIsCocartesianCategory( KarEnvC, true  );
            if CanCompute( C, "Coproduct" ) and CanCompute( C, "UniversalMorphismFromCoproductWithGivenCoproduct" ) and CanCompute( C, "InjectionOfCofactorOfCoproductWithGivenCoproduct" ) then
                AddCoproduct( KarEnvC,
                function( KarEnvC, L )
                    local C, e_L, under_L, coprod_under_L, idempotent_of_coproduct;
                    C := UnderlyingCategory( KarEnvC );
                    e_L := List( L, x -> IdempotentDatum( x ) );
                    under_L := List( e_L, e_x -> Source( e_x ) );
                    coprod_under_L := Coproduct( C, under_L );
                    idempotent_of_coproduct := CoproductFunctorialWithGivenCoproducts( C, coprod_under_L,
                                    List( [ 1 .. Length( under_L ) ], k -> PreCompose( C, e_L[k], InjectionOfCofactorOfCoproductWithGivenCoproduct( C, under_L, k, coprod_under_L ) ) ),
                                    coprod_under_L );
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
        elif HasIsCartesianCategory( C ) and IsCartesianCategory( C ) then
        SetIsCartesianCategory( KarEnvC, true  );
        #TODO: add preservation of products
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
                    return ObjectConstructor( KarEnvC, IdentityMorphism( C, zero_C ) );
                end );
            fi; 

            if CanCompute( C, "UniversalMorphismFromZeroObjectWithGivenZeroObject" ) then
                AddUniversalMorphismFromZeroObjectWithGivenZeroObject( KarEnvC,
                function( KarEnvC, x, zero )
                    local C, e_x, under_x, under_zero;
                    C := UnderlyingCategory( KarEnvC );
                    e_x := IdempotentDatum( x );
                    under_x := Source( e_x );
                    under_zero := Source( IdempotentDatum( zero ) );
                    return MorphismConstructor( KarEnvC, zero, UniversalMorphismFromZeroObjectWithGivenZeroObject( C, under_x, under_zero ), x );
                end );
            fi;

            if CanCompute( C, "UniversalMorphismIntoZeroObjectWithGivenZeroObject" ) then
                AddUniversalMorphismIntoZeroObjectWithGivenZeroObject( KarEnvC,
                function( KarEnvC, x, zero )
                    local C, e_x, under_x, under_zero;
                    C := UnderlyingCategory( KarEnvC );
                    e_x := IdempotentDatum( x );
                    under_x := Source( e_x );
                    under_zero := Source( IdempotentDatum( zero ) );
                    return MorphismConstructor( KarEnvC, zero, UniversalMorphismIntoZeroObjectWithGivenZeroObject( C, under_x, under_zero ), x );
                end );
            fi;
        else
            if HasIsCategoryWithTerminalObject( C ) and IsCategoryWithTerminalObject( C ) then
                SetIsCategoryWithTerminalObject( KarEnvC, true );

            elif HasIsCategoryWithInitialObject( C ) and IsCategoryWithInitialObject( C ) then
                SetIsCategoryWithInitialObject( KarEnvC, true );
            fi;
        fi;
    fi;


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

        if CanCompute( C, "TensorProductOnMorphismsWithGivenTensorProducts" ) and CanCompute( C, "TensorProductOnObjects" ) then
            #note: tensor product on objects
            AddTensorProductOnObjects( KarEnvC,
            function ( KarEnvC, x, y )
                local C, e_x, e_y, under_x, under_y, under_xy;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source( e_x );
                e_y := IdempotentDatum( y );
                under_y := Source( e_y );
                under_xy := TensorProductOnObjects( C, under_x, under_y );
                return ObjectConstructor( KarEnvC, TensorProductOnMorphismsWithGivenTensorProducts( C, under_xy, e_x, e_y, under_xy ) );
            end );

            #note: tensor product on morphisms
            AddTensorProductOnMorphismsWithGivenTensorProducts( KarEnvC,
            function ( KarEnvC, source, phi1, phi2, target )
                local C, under_phi1, under_phi2, under_source, under_target;
                C := UnderlyingCategory( KarEnvC );
                under_phi1 := UnderlyingMorphismDatum( phi1 );
                under_phi2 := UnderlyingMorphismDatum( phi2 );
                under_source := Source( IdempotentDatum( source ) );
                under_target := Source( IdempotentDatum( target ) );
                return MorphismConstructor( KarEnvC, source, TensorProductOnMorphismsWithGivenTensorProducts( C, under_source, under_phi1, under_phi2, under_target ), target );
            end );
        fi;

        #note: left unitor
        if CanCompute( C, "LeftUnitorWithGivenTensorProduct") then
            AddLeftUnitorWithGivenTensorProduct( KarEnvC, 
            function( KarEnvC, x, one_times_x )
                local C, Karunit, e_x, under_x, under_one_times_x, leftunitor_under;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source(e_x);
                under_one_times_x := Source( IdempotentDatum( one_times_x ) );
                leftunitor_under := LeftUnitorWithGivenTensorProduct( C, under_x, under_one_times_x );
                return MorphismConstructor( KarEnvC, one_times_x, leftunitor_under, x );
            end );
        fi;

        #note: inverse of left unitor
        if CanCompute( C, "LeftUnitorInverseWithGivenTensorProduct") then
            AddLeftUnitorInverseWithGivenTensorProduct( KarEnvC, 
            function( KarEnvC, x, one_times_x )
                local C, Karunit, e_x, under_x, under_one_times_x, leftunitorinv_under;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source(e_x);
                under_one_times_x := Source( IdempotentDatum( one_times_x ) );
                leftunitorinv_under := LeftUnitorInverseWithGivenTensorProduct( under_x );
                return MorphismConstructor( KarEnvC, x, leftunitorinv_under, one_times_x );
            end );
        fi;

        #note: right unitor
        if CanCompute( C, "RightUnitorWithGivenTensorProduct") then
            AddRightUnitorWithGivenTensorProduct( KarEnvC, 
            function( KarEnvC, x, x_times_one )
                local C, Karunit, e_x, under_x_times_one, under_x, rightunitor_under;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source(e_x);
                under_x_times_one := Source( IdempotentDatum( x_times_one ) );
                rightunitor_under := RightUnitorWithGivenTensorProduct( C, under_x, under_x_times_one );
                return MorphismConstructor( KarEnvC, x_times_one, rightunitor_under, x );
            end );
        fi;

        #note: inverse of right unitor
        if CanCompute( C, "RightUnitorInverseWithGivenTensorProduct") then
            AddRightUnitorInverseWithGivenTensorProduct( KarEnvC, 
            function( KarEnvC, x, x_times_one )
                local C, Karunit, e_x, under_x, under_x_times_one, rightunitorinv_under;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source(e_x);
                under_x_times_one := Source( IdempotentDatum( x_times_one ) );
                rightunitorinv_under := RightUnitorInverseWithGivenTensorProduct( C, under_x, under_x_times_one );
                return MorphismConstructor( KarEnvC, x, rightunitorinv_under, x_times_one );
            end );
        fi;

        #note: associator from right to left
        if CanCompute( C, "AssociatorRightToLeftWithGivenTensorProducts" ) then
            AddAssociatorRightToLeftWithGivenTensorProducts( KarEnvC, 
            function( KarEnvC, source, x, y, z, target )
                #source = x otimes ( y otimes z )
                #target = ( x otimes y ) otimes z 
                local C, e_x, e_y, e_z, under_x, under_y, under_z, under_source, under_target;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source( e_x );
                e_y := IdempotentDatum( y );
                under_y := Source( e_y );
                e_z := IdempotentDatum( z );
                under_z := Source( e_z );
                under_source := Source( IdempotentDatum( source ) );
                under_target := Source( IdempotentDatum( target ) );
                return MorphismConstructor( KarEnvC, source, AssociatorRightToLeftWithGivenTensorProducts( C, under_source, under_x, under_y, under_z, under_target ), target );
            end );
        fi;

        #note: associator from left to right
        if CanCompute( C, "AssociatorLeftToRightWithGivenTensorProducts" ) then
            AddAssociatorLeftToRightWithGivenTensorProducts( KarEnvC, 
            function( KarEnvC, source, x, y, z, target )
                #source = ( x otimes y ) otimes z 
                #target = x otimes ( y otimes z )
                local C, e_x, e_y, e_z, under_x, under_y, under_z, under_source, under_target;
                C := UnderlyingCategory( KarEnvC );
                e_x := IdempotentDatum( x );
                under_x := Source( e_x );
                e_y := IdempotentDatum( y );
                under_y := Source( e_y );
                e_z := IdempotentDatum( z );
                under_z := Source( e_z );
                under_source := Source( IdempotentDatum( source ) );
                under_target := Source( IdempotentDatum( target ) );
                return MorphismConstructor( KarEnvC, source, AssociatorLeftToRightWithGivenTensorProducts( C, under_source, under_x, under_y, under_z, under_target ), target );
            end );
        fi;
        
        if HasIsAdditiveMonoidalCategory( C ) and IsAdditiveMonoidalCategory( C ) then
            SetIsAdditiveMonoidalCategory( KarEnvC, true );
        fi;
    fi;

    # if Has( C ) and ( C ) then
    #     Set( KarEnvC, true );
    # fi;

    Finalize( KarEnvC );
  
    return KarEnvC;
end );