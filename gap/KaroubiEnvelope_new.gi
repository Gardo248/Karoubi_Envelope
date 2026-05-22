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
        function(cat, idempotent)
        return CreateCapCategoryObjectWithAttributes( cat, IdempotentDatum, idempotent );
        # option with the datum of the source inside the object datum:
        # return CreateCapCategoryObjectWithAttributes( cat, IdempotentDatum, idempotent, UnderlyingSourceOfIdempotent, Source(idempotent) );
    end);

    AddObjectDatum(KarEnvC,
        function (cat, obj)
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

                return IsCongruentForMorphisms( C, e1, e2 );
            end );
 
    AddMorphismConstructor( KarEnvC,
            function ( cat, s, morph, t )

                return CreateCapCategoryMorphismWithAttributes( cat, s, t, UnderlyingMorphismDatum, morph);
            end );

    AddMorphismDatum(KarEnvC,
        function (cat, morph)
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

    #Q: there is this line of code inside the old file, what do it does? Do I have to add it, in some other form?
    #category_weight_list := category!.derivations_weight_list;
    #Q:Then he add manually a lot of methods lime kernelobject, zeroObject, KernelLift
    #Q: should I add something like the essential image of the underlying category? Should I add the formal splitting of an element in this essential image? Should I implement a proof (maybe in the example file) that in KarEnvC all the idempotent splits?



return KarEnvC;
end);