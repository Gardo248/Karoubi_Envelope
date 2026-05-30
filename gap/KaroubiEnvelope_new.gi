InstallMethod( KaroubiEnvelope,
    "for a CAP category",
    [IsCapCategory],
    function ( C )
    local KarEnvC;

    KarEnvC := CreateCapCategoryWithDataTypes(
        Concatenation("KaroubiEnvelope(", Name(C), ")" ),
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
    AddObjectConstructor(KarEnvC,
        function( cat, idempotent )
        return CreateCapCategoryObjectWithAttributes( cat, IdempotentDatum, idempotent );
        # option with the datum of the source inside the object datum:
        # return CreateCapCategoryObjectWithAttributes( cat, IdempotentDatum, idempotent, UnderlyingSourceOfIdempotent, Source(idempotent) );
    end);

    AddObjectDatum( KarEnvC,
        function ( cat, obj )
            return IdempotentDatum ( obj );
    end);

#not much interesting idea: 
# In case I want to separate the datum of the underlying object (the source of the idempotent) from the constructor, I can do it in this way, adding the attribute "UnderlyingObjectForKaroubiObjects" in the declaration file
    # InstallMethod(UnderlyingObjectForKaroubiObjects,
    #             [ IsKaroubiObject ],
    #     function (obj)
    #     return Source( IdempotentDatum (obj) );
    # end);

    if CanCompute( C, "IsCongruentForMorphisms" ) then
        AddIsWellDefinedForObjects( KarEnvC,
            function ( cat, obj )
                local C, e;
                C := UnderlyingCategory( cat );
                e := IdempotentDatum ( obj );
                return IsCongruentForMorphisms( C, PreCompose( C, e, e ), e );
            end );
    fi;

    #Q: is it better to use IsCongruentForMorphisms or IsEqualForMorphisms?
    #The point is that Cap is functional and so I have to assure that equal inputs gives equal outputs!
    AddIsEqualForObjects( KarEnvC,
            function ( cat, obj1, obj2 )
                local C, e1, e2;
                C := UnderlyingCategory( cat );
                e1 := IdempotentDatum( obj1 );
                e2 := IdempotentDatum( obj2 );
                return IsEqualForMorphisms( C, e1, e2 );
            end );
 
    AddMorphismConstructor( KarEnvC,
            function ( cat, s, morph, t )
                return CreateCapCategoryMorphismWithAttributes( cat, s, t, UnderlyingMorphismDatum, morph);
            end );

    AddMorphismDatum(KarEnvC,
        function ( cat, morph )
            return UnderlyingMorphismDatum ( morph );
    end);

    if CanCompute( C, "IsEqualForMorphisms" ) then
        AddIsEqualForMorphisms( KarEnvC,
                function ( cat, morphism1, morphism2 )
                    local C, mor1, mor2;
                    C := UnderlyingCategory( cat );
                    mor1 := UnderlyingMorphismDatum ( morphism1 );
                    mor2 := UnderlyingMorphismDatum ( morphism2 );
                    return IsEqualForMorphisms(C, mor1, mor2 );
                end );
    fi;
    
        # Remember: these functions always assume that the morphisms are
        # indeed parallel.
    if CanCompute( C, "IsCongruentForMorphisms" ) then
        AddIsCongruentForMorphisms( KarEnvC,
            function ( cat, morphism1, morphism2 )
                local C, f1, f2;
                C := UnderlyingCategory( cat );
                f1 := UnderlyingMorphismDatum ( morphism1 );
                f2 := UnderlyingMorphismDatum ( morphism2 );
                return IsCongruentForMorphisms(C, f1, f2 );
            end );
    fi;

    if CanCompute( C, "IsWellDefinedForMorphismsWithGivenSourceAndRange" ) and CanCompute( C, "IsCongruentForMorphisms" ) and CanCompute( C, "IsWellDefinedForObjects" ) then
            AddIsWellDefinedForMorphisms( KarEnvC,
                function ( cat, f )
                    local C, f_u, s_u, t_u, e_s, e_t;
                    C := UnderlyingCategory( KarEnvC );
                    f_u := UnderlyingMorphismDatum( f );
                    e_s := IdempotentDatum( Source( f ) );
                    e_t := IdempotentDatum( Target ( f ) );
                    s_u := Source ( e_s );
                    t_u := Source ( e_t );
                    return IsWellDefinedForMorphismsWithGivenSourceAndRange( C, s_u, f_u, t_u ) and IsWellDefinedForObjects( C, s_u ) and IsWellDefinedForObjects( C, t_u ) and IsCongruentForMorphisms( f_u, PreCompose( e_s, PreCompose( f_u, e_t ) ) );
                end );
        fi;

    AddIdentityMorphism( KarEnvC,
            function ( cat, object )
                local C, idempotent;
                C := UnderlyingCategory( cat );
                idempotent := IdempotentDatum( object ) ;
                return MorphismConstructor( cat, object, idempotent, object );
            end );

    AddPreCompose( KarEnvC,
            function ( cat, f, g )
                #    f     g
                # x --> y --> z
                local C, x, z, f_under, g_under;
                C := UnderlyingCategory( cat );
                x := Source( f ) ;
                z := Target( g );
                f_under := UnderlyingMorphismDatum( f );
                g_under := UnderlyingMorphismDatum( g );
                return MorphismConstructor( cat, x, PreCompose( C, f_under, g_under ), z );
            end );

    #Q: do I have to add manually: if CanCompute... then AddIsMonomorphism, AddIsEpimorphism, AddIsIsomorphism, AddIsSplitMonomorphism, AddInverseMorphism,  AddCoproduct, AddInitialObject, AddTerminalObject, AddDirectProduct, ecc...

    #Q: should I add something like the essential image of the underlying category? Should I add the formal splitting of an element in this essential image? Should I implement a proof (maybe in the example file) that in KarEnvC all the idempotent splits?

    #note: from now on we implement the preservation of structures of the underlying category C, I will not suppose that the upper category has the structure, I always ask if "the underlying cat has the structure S" then I define S over KarEnvC
    #Q: is it correct to ask if CanCompute( C, "TensorProductOnObjects" )? Should I ask something like if IsMonoidalCategory(C) then ..., maybe in one external if

    #note: preservation of monoidal structure
    if CanCompute( C, "TensorUnit" ) then 
        #note: tensor unit
        AddTensorUnit( KarEnvC,
        function( cat )
            local C, unit, id_unit;
            C := UnderlyingCategory( cat );
            unit := TensorUnit( C );
            id_unit := IdentityMorphism( unit );
            return ObjectConstructor( cat, id_unit );
        end );
    fi; 

    if CanCompute( C, "TensorProductOnMorphisms" ) then
        #note: tensor product on objects
        AddTensorProductOnObjects( KarEnvC,
        function (cat, x, y )
            local C, e_x, e_y;
            C := UnderlyingCategory( cat );
            e_x := IdempotentDatum( x );
            e_y := IdempotentDatum( y );
            return ObjectConstructor( cat, TensorProduct(e_x, e_y) );
        end );

        #note: tensor product on morphisms
        AddTensorProductOnMorphisms( KarEnvC,
        function (cat, phi1, phi2 )
            local C, phi1_under, phi2_under, s1, s2, t1, t2;
            C := UnderlyingCategory( cat );
            s1 := Source( phi1 );
            s2 := Source( phi2 );
            t1 := Target( phi1 );
            t2 := Target( phi2 );
            phi1_under := UnderlyingMorphismDatum( phi1 );
            phi2_under := UnderlyingMorphismDatum( phi2 );
            return MorphismConstructor( cat, TensorProduct( s1, s2 ), TensorProduct( phi1_under, phi2_under ), TensorProduct ( t1, t2 ) );
        end );
    fi;

    #note: left unitor
    if CanCompute( C, "LeftUnitor") then
        AddLeftUnitor( KarEnvC, 
        function( cat, x )
            local C, Karunit, e_x, under_x, leftunitor_under;
            C := UnderlyingCategory( cat );
            Karunit := TensorUnit( cat );
            e_x := IdempotentDatum( x );
            under_x := Source(e_x);
            leftunitor_under := LeftUnitor( under_x );
            return MorphismConstructor( cat, TensorProduct( Karunit, x ), leftunitor_under, x );
        end );
    fi;

    #note: inverse of left unitor
    if CanCompute( C, "LeftUnitorInverse") then
        AddLeftUnitorInverse( KarEnvC, 
        function( cat, x )
            local C, Karunit, e_x, under_x, leftunitorinv_under;
            C := UnderlyingCategory( cat );
            Karunit := TensorUnit( cat );
            e_x := IdempotentDatum( x );
            under_x := Source(e_x);
            leftunitorinv_under := LeftUnitorInverse( under_x );
            return MorphismConstructor( cat, x, leftunitorinv_under, TensorProduct( Karunit, x ) );
        end );
    fi;

    #note: right unitor
    if CanCompute( C, "RightUnitor") then
        AddRightUnitor( KarEnvC, 
        function( cat, x )
            local C, Karunit, e_x, under_x, rightunitor_under;
            C := UnderlyingCategory( cat );
            Karunit := TensorUnit( cat );
            e_x := IdempotentDatum( x );
            under_x := Source(e_x);
            rightunitor_under := RightUnitor( under_x );
            return MorphismConstructor( cat, TensorProduct( x, Karunit ), rightunitor_under, x );
        end );
    fi;

    #note: inverse of right unitor
    if CanCompute( C, "RightUnitorInverse") then
        AddRightUnitorInverse( KarEnvC, 
        function( cat, x )
            local C, Karunit, e_x, under_x, rightunitorinv_under;
            C := UnderlyingCategory( cat );
            Karunit := TensorUnit( cat );
            e_x := IdempotentDatum( x );
            under_x := Source(e_x);
            rightunitorinv_under := RightUnitorInverse( under_x );
            return MorphismConstructor( cat, x, rightunitorinv_under, TensorProduct( x, Karunit ) );
        end );
    fi;

    #note: associator from right to left
    if CanCompute( C, "AssociatorRightToLeft" ) then
        AddAssociatorRightToLeft( cat, 
        function(cat, x, y, z)
            local C, e_x, e_y, e_z, under_x, under_y, under_z;
            C := UnderlyingCategory( cat );
            e_x := IdempotentDatum( x );
            under_x := Source( e_x );
            e_y := IdempotentDatum( y );
            under_y := Source( e_y );
            e_z := IdempotentDatum( z );
            under_z := Source( e_z );
            return MorphismConstructor( cat, TensorProduct( x, TensorProduct( y, z ) ), AssociatorRightToLeft( under_x, under_y, under_z ), TensorProduct( TensorProduct( a, b ), c ) );
        end );
    fi;

    #note: associator from left to right
    if CanCompute( C, "AssociatorLeftToRight" ) then
        AddAssociatorLeftToRight( cat, 
        function(cat, x, y, z)
            local C, e_x, e_y, e_z, under_x, under_y, under_z;
            C := UnderlyingCategory( cat );
            e_x := IdempotentDatum( x );
            under_x := Source( e_x );
            e_y := IdempotentDatum( y );
            under_y := Source( e_y );
            e_z := IdempotentDatum( z );
            under_z := Source( e_z );
            return MorphismConstructor( cat, TensorProduct( TensorProduct( a, b ), c ), AssociatorLeftToRight( under_x, under_y, under_z ), TensorProduct( x, TensorProduct( y, z ) ) );
        end );
    fi;

    #TODO: check in example/test file that righ unitor and its inverse are effectively inverses, same for the left one

    #Q: how can I find the documentation related to a specific structure such as AbCategory and so on?

    #preservation of pre-additive structure
    #Q: Is it enough to build the structure of sums and differences of morphisms? Do I have to define the zero object and the zero morphism? Is the zero morphism a universal morphism (i.e. the zero morph in the zero obj) or it is a "contructor" such that for every two objects build the zero morph between the two objcets?
    #Q: do I have to say somehow that, if C is preadditive, then KarEnvC is preadditive? Is it "if IsAbCategory(C)" the right way to do it?
    if IsAbCategory( C ) then
        #note: zero morphism between any two objects in KarEnvC
        if CanCompute( C, "ZeroMorphism" ) then
            AddZeroMorphism( KarEnvC,
            function( cat, x, y )
                local C, e_x, e_y, under_x, under_y;
                C := UnderlyingCategory( cat );
                e_x := IdempotentDatum( x );
                e_y := IdempotentDatum( y );
                under_x := Source( e_x );
                under_y := Source( e_y );
                return MorphismConstructor( cat, x, ZeroMorphism( under_x, under_y ) y );
            end)
        fi;

        #note: addition for morphisms
        #TODO: add in the example/test file a check that the congruence is compatible with the addition
        if CanCompute( C, "AdditionForMorphism" ) then
            AddAdditionForMorphism( KarEnvC, 
            function( cat, phi1, phi2)
                local C, s, t, phi1_under, phi2_under;
                C := UnderlyingCategory( cat );
                s := Source( phi1 );
                t := Target( phi1 );
                phi1_under := UnderlyingMorphismDatum( phi1 );
                phi2_under := UnderlyingMorphismDatum( phi2 );
                return MorphismConstructor( cat, s, AdditionForMorphism( phi1_under, phi2_under ), t );
            end)
        fi;

        #note: additive inverse for morphisms
        if CanCompute( C, "AdditiveInverseForMorphism" ) then
            AddAdditionForMorphism( KarEnvC, 
            function( cat, phi)
                local C, s, t, phi_under;
                C := UnderlyingCategory( cat );
                s := Source( phi1 );
                t := Target( phi1 );
                phi_under := UnderlyingMorphismDatum( phi );
                return MorphismConstructor( cat, s, AdditiveInverseForMorphism( phi1_under, phi2_under ), t );
            end)
        fi;
    fi;


return KarEnvC;
end);