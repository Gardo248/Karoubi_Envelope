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
                    local C, f_u, under_s, under_t, e_s, e_t;
                    C := UnderlyingCategory( KarEnvC );
                    f_u := UnderlyingMorphismDatum( f );
                    e_s := IdempotentDatum( Source( f ) );
                    e_t := IdempotentDatum( Target ( f ) );
                    under_s := Source ( e_s );
                    under_t := Source ( e_t );
                    return IsWellDefinedForMorphismsWithGivenSourceAndRange( C, under_s, f_u, under_t ) and IsWellDefinedForObjects( C, under_s ) and
                    IsWellDefinedForObjects( C, under_t ) and IsCongruentForMorphisms( f_u, PreCompose( e_s, PreCompose( f_u, e_t ) ) );
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
                local C, x, z, under_f, under_g;
                C := UnderlyingCategory( KarEnvC );
                x := Source( f ) ;
                z := Target( g );
                under_f := UnderlyingMorphismDatum( f );
                under_g := UnderlyingMorphismDatum( g );
                return MorphismConstructor( KarEnvC, x, PreCompose( C, under_f, under_g ), z );
            end );

    #from now on we implement the preservation of structures of the underlying category C
    #preservation of pre-additive structure
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

        #we define the universal morphism from the zero object into any other object of the category
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

        #we define the universal morphism from any object of the category into the zero object
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

        if CanCompute( C, "DirectSum" ) and CanCompute( C, "DirectSumFunctorialWithGivenDirectSums" ) and 
        CanCompute( C, "InjectionOfCofactorOfDirectSumWithGivenDirectSum" ) and CanCompute( C, "UniversalMorphismFromDirectSumWithGivenDirectSum" ) and 
        CanCompute( C, "ProjectionInFactorOfDirectSumWithGivenDirectSum" ) and CanCompute( C, "UniversalMorphismIntoDirectSumWithGivenDirectSum" ) then

            #we define the direct sum of a list of objects in the Karoubi envelope relying on the direct sum of the underlying category C
            AddDirectSum( KarEnvC,
            #Q: in the case of the direct sum, I could define the k-th element defining the idempotent of the direct sum either as Precompose( C, e_L[k], InjectionOfCofactorOfDirectSumWithGivenDirectSum( C, under_L, k, dirsum_under_L ) ) ) or as Precompose( C, ProjectionInFactorOfDirectSumWithGivenDirectSum( C, under_L, k, dirsum_under_L ), e_L[k] ) ). I believe that the two are both equal to the morphism Precompose( C, ProjectionInFactorOfDirectSumWithGivenDirectSum( C, under_L, k, dirsum_under_L ), Precompose( C, e_L[k], InjectionOfCofactorOfDirectSumWithGivenDirectSum( C, under_L, k, dirsum_under_L ) ) ) ). Is it smart to use this form in the implementation? It allows you not to choose between one or the other, but makes the code more complicated
            function( KarEnvC, L )
                local C, e_L, under_L, dirsum_under_L, idempotent_of_dirsum;
                C := UnderlyingCategory( KarEnvC );
                e_L := List( L, x -> IdempotentDatum( x ) );
                under_L := List( e_L, e_x -> Source( e_x ) );
                dirsum_under_L := DirectSum( C, under_L );
                idempotent_of_dirsum := DirectSumFunctorialWithGivenDirectSums( C, dirsum_under_L, e_L, dirsum_under_L );
                return ObjectConstructor( KarEnvC, idempotent_of_dirsum );
            end );

            #we define the injection into the direct sum of a list of objects
            AddInjectionOfCofactorOfDirectSumWithGivenDirectSum( KarEnvC,
            function( KarEnvC, L, k, dirsum )
                local C, e_L, under_L, under_dirsum;
                C := UnderlyingCategory( KarEnvC );
                e_L := List( L, x -> IdempotentDatum( x ) );
                under_L := List( e_L, e_x -> Source( e_x ) );
                under_dirsum := Source( IdempotentDatum( dirsum ) );
                return MorphismConstructor( KarEnvC, L[k], PreCompose( C, e_L[k], InjectionOfCofactorOfDirectSumWithGivenDirectSum( C, under_L, k, under_dirsum ) ), dirsum ); 
            end );

            #we define the universal morphism from the direct sum of a list of objects induced by a list of morphisms into an object z
            AddUniversalMorphismFromDirectSumWithGivenDirectSum( KarEnvC,
            function( KarEnvC, L, z, tao, dirsum )
                local C, e_L, under_L, under_tao, e_z, under_z, under_dirsum;
                C := UnderlyingCategory( KarEnvC );
                e_L := List( L, x -> IdempotentDatum( x ) );
                under_L := List( e_L, e_x -> Source( e_x ) );
                under_tao := List( tao, phi -> UnderlyingMorphismDatum( phi ) );
                e_z := IdempotentDatum( z );
                under_z := Source( e_z );
                under_dirsum := Source( IdempotentDatum( dirsum ) );
                #mathematically it is true that this morphism is a well defined morphism in KarEnvC
                return MorphismConstructor( KarEnvC, dirsum, UniversalMorphismFromDirectSumWithGivenDirectSum( C, under_L, under_z, under_tao, under_dirsum ), z );
            end );

            #we define the projection from the direct sum of a list of objects
            AddProjectionInFactorOfDirectSumWithGivenDirectSum( KarEnvC,
            function( KarEnvC, L, k, dirsum )
                local C, e_L, under_L, under_dirsum;
                C := UnderlyingCategory( KarEnvC );
                e_L := List( L, x -> IdempotentDatum( x ) );
                under_L := List( e_L, e_x -> Source( e_x ) );
                under_dirsum := Source( IdempotentDatum( dirsum ) );
                return MorphismConstructor( KarEnvC, dirsum, PreCompose( C, ProjectionInFactorOfDirectSumWithGivenDirectSum( C, under_L, k, under_dirsum ), e_L[k] ), L[k] ); 
            end );

            #we define the universal morphism into the direct sum of a list of objects induced by a list of morphisms from an object z
            AddUniversalMorphismIntoDirectSumWithGivenDirectSum( KarEnvC,
            function( KarEnvC, L, z, tao, dirsum )
                local C, e_L, under_L, under_tao, e_z, under_z, under_dirsum;
                C := UnderlyingCategory( KarEnvC );
                e_L := List( L, x -> IdempotentDatum( x ) );
                under_L := List( e_L, e_x -> Source( e_x ) );
                under_tao := List( tao, phi -> UnderlyingMorphismDatum( phi ) );
                e_z := IdempotentDatum( z );
                under_z := Source( e_z );
                under_dirsum := Source( IdempotentDatum( dirsum ) );
                #mathematically it is true that this morphism is a well defined morphism in KarEnvC
                return MorphismConstructor( KarEnvC, z, UniversalMorphismIntoDirectSumWithGivenDirectSum( C, under_L, under_z, under_tao, under_dirsum ), dirsum );
            end );
        fi;
        
    else
        #preservation of cocartesian structure
        if HasIsCocartesianCategory( C ) and IsCocartesianCategory( C ) then

            SetIsCocartesianCategory( KarEnvC, true  );
            #TODO: complete the cocartesian structure

            if CanCompute( C, "Coproduct" ) and CanCompute( C, "UniversalMorphismFromCoproductWithGivenCoproduct" ) and
            CanCompute( C, "InjectionOfCofactorOfCoproductWithGivenCoproduct" ) and CanCompute( C, "CoproductFunctorialWithGivenCoproducts" ) then

                AddCoproduct( KarEnvC,
                function( KarEnvC, L )
                    local C, e_L, under_L, coprod_under_L, idempotent_of_coproduct;
                    C := UnderlyingCategory( KarEnvC );
                    e_L := List( L, x -> IdempotentDatum( x ) );
                    under_L := List( e_L, e_x -> Source( e_x ) );
                    coprod_under_L := Coproduct( C, under_L );
                    idempotent_of_coproduct := CoproductFunctorialWithGivenCoproducts( C, coprod_under_L, e_L, coprod_under_L );
                    return ObjectConstructor( KarEnvC, idempotent_of_coproduct );
                end );

                AddInjectionOfCofactorOfCoproductWithGivenCoproduct( KarEnvC,
                function( KarEnvC, L, k, coprod )
                    local C, e_L, under_L, under_coprod;
                    C := UnderlyingCategory( KarEnvC );
                    e_L := List( L, x -> IdempotentDatum( x ) );
                    under_L := List( e_L, e_x -> Source( e_x ) );
                    under_coprod := Source( IdempotentDatum( coprod ) );
                    return MorphismConstructor( KarEnvC, L[k], PreCompose( C, e_L[k], InjectionOfCofactorOfCoproductWithGivenCoproduct( C, under_L, k, under_coprod ) ), coprod ); 
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
        fi;

        #preservation of cartesian structure
        if HasIsCartesianCategory( C ) and IsCartesianCategory( C ) then

            SetIsCartesianCategory( KarEnvC, true );

            if CanCompute( C, "DirectProduct" ) and CanCompute( C, "UniversalMorphismIntoDirectProductWithGivenDirectProduct" ) and
            CanCompute( C, "ProjectionInFactorOfDirectProductWithGivenDirectProduct" ) and CanCompute( C, "DirectProductFunctorialWithGivenDirectProducts" ) then

                AddDirectProduct( KarEnvC,
                function( KarEnvC, L )
                    local C, e_L, under_L, dirprod_under_L, idempotent_of_dirproduct;
                    C := UnderlyingCategory( KarEnvC );
                    e_L := List( L, x -> IdempotentDatum( x ) );
                    under_L := List( e_L, e_x -> Source( e_x ) );
                    dirprod_under_L := DirectProduct( C, under_L );
                    idempotent_of_dirproduct := DirectProductFunctorialWithGivenDirectProducts( C, dirprod_under_L, e_L, dirprod_under_L );
                    return ObjectConstructor( KarEnvC, idempotent_of_dirproduct );
                end );

                AddProjectionInFactorOfDirectProductWithGivenDirectProduct( KarEnvC,
                function( KarEnvC, L, k, dirprod )
                    local C, e_L, under_L, under_dirprod;
                    C := UnderlyingCategory( KarEnvC );
                    e_L := List( L, x -> IdempotentDatum( x ) );
                    under_L := List( e_L, e_x -> Source( e_x ) );
                    under_dirprod := Source( IdempotentDatum( dirprod ) );
                    return MorphismConstructor( KarEnvC, dirprod, PreCompose( C, ProjectionInFactorOfDirectProductWithGivenDirectProduct( C, under_L, k, under_dirprod ), e_L[k] ), L[k] ); 
                end );

                AddUniversalMorphismIntoDirectProductWithGivenDirectProduct( KarEnvC,
                function( KarEnvC, L, z, tao, dirprod )
                    local C, e_L, under_L, under_tao, e_z, under_z, under_dirprod;
                    C := UnderlyingCategory( KarEnvC );
                    e_L := List( L, x -> IdempotentDatum( x ) );
                    under_L := List( e_L, e_x -> Source( e_x ) );
                    under_tao := List( tao, phi -> UnderlyingMorphismDatum( phi ) );
                    e_z := IdempotentDatum( z );
                    under_z := Source( e_z );
                    under_dirprod := Source( IdempotentDatum( dirprod ) );
                    return MorphismConstructor( KarEnvC, z, UniversalMorphismIntoDirectProductWithGivenDirectProduct( C, under_L, under_z, under_tao, under_dirprod ), dirprod );
                end );
            fi;
        fi;

        #preservation of zero object
        if HasIsCategoryWithZeroObject( C ) and IsCategoryWithZeroObject( C ) then

            SetIsCategoryWithZeroObject( KarEnvC, true );

            #we define the zero object
            if CanCompute( C, "ZeroObject" ) then
                AddZeroObject( KarEnvC, 
                function( KarEnvC )
                    local C, zero_C;
                    C := UnderlyingCategory( KarEnvC );
                    zero_C := ZeroObject( C );
                    return ObjectConstructor( KarEnvC, IdentityMorphism( C, zero_C ) );
                end );
            fi; 

            #we define the universal morphism from the zero object into any other object of the category
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

            #we define the universal morphism from any object of the category into the zero object
            if CanCompute( C, "UniversalMorphismIntoZeroObjectWithGivenZeroObject" ) then

                AddUniversalMorphismIntoZeroObjectWithGivenZeroObject( KarEnvC,
                function( KarEnvC, x, zero )
                    local C, e_x, under_x, under_zero;
                    C := UnderlyingCategory( KarEnvC );
                    e_x := IdempotentDatum( x );
                    under_x := Source( e_x );
                    under_zero := Source( IdempotentDatum( zero ) );
                    return MorphismConstructor( KarEnvC, x, UniversalMorphismIntoZeroObjectWithGivenZeroObject( C, under_x, under_zero ), zero );
                end );
            fi;
        else
            #preservation of the terminal object
            if HasIsCategoryWithTerminalObject( C ) and IsCategoryWithTerminalObject( C ) then

                SetIsCategoryWithTerminalObject( KarEnvC, true );

                #we define the terminal object
                if CanCompute( C, "TerminalObject" ) then
                    AddTerminalObject( KarEnvC, 
                    function( KarEnvC )
                        local C, terminal_C;
                        C := UnderlyingCategory( KarEnvC );
                        terminal_C := TerminalObject( C );
                        return ObjectConstructor( KarEnvC, IdentityMorphism( C, terminal_C ) );
                    end );
                fi;

                #we define the universal morphism from any object of the category into the terminal object
                if CanCompute( C, "UniversalMorphismIntoTerminalObjectWithGivenTerminalObject" ) then
                    AddUniversalMorphismIntoTerminalObjectWithGivenTerminalObject( KarEnvC,
                    function( KarEnvC, x, terminal )
                        local C, e_x, under_x, under_terminal;
                        C := UnderlyingCategory( KarEnvC );
                        e_x := IdempotentDatum( x );
                        under_x := Source( e_x );
                        under_terminal := Source( IdempotentDatum( terminal ) );
                        return MorphismConstructor( KarEnvC, x, UniversalMorphismIntoTerminalObjectWithGivenTerminalObject( C, under_x, under_terminal ), terminal );
                    end );
                fi;
            fi;

            if HasIsCategoryWithInitialObject( C ) and IsCategoryWithInitialObject( C ) then

                SetIsCategoryWithInitialObject( KarEnvC, true );

                #we define the initial object
                if CanCompute( C, "InitialObject" ) then
                    AddInitialObject( KarEnvC, 
                    function( KarEnvC )
                        local C, initial_C;
                        C := UnderlyingCategory( KarEnvC );
                        initial_C := InitialObject( C );
                        return ObjectConstructor( KarEnvC, IdentityMorphism( C, initial_C ) );
                    end );
                fi; 

                #we define the universal morphism from the initial object into any other object of the category
                if CanCompute( C, "UniversalMorphismFromInitialObjectWithGivenInitialObject" ) then
                    AddUniversalMorphismFromInitialObjectWithGivenInitialObject( KarEnvC,
                    function( KarEnvC, x, initial )
                        local C, e_x, under_x, under_initial;
                        C := UnderlyingCategory( KarEnvC );
                        e_x := IdempotentDatum( x );
                        under_x := Source( e_x );
                        under_initial := Source( IdempotentDatum( initial ) );
                        return MorphismConstructor( KarEnvC, initial, UniversalMorphismFromInitialObjectWithGivenInitialObject( C, under_x, under_initial ), x );
                    end );
                fi;

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