InstallMethod(
    "for a CAP category",
    [IsCapCategory],
    function ( C )
    local KarEnvC;

    #Q: in principle the datum of the object/morphism in the Karoubi envelope is only a morphism in the underlying category, but we also have conditions. As I understand CAP right now, I have to put such conditions on the constructor for objects/morphisms.
    KarEnvC := CreateCapCategoryWithDataTypes(
        Concatenation("KaroubiEnvelope(", Name(C), ")" ),
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
        function(KarEnvC, idempotent)
        return CreateCapCategoryObjectWithAttributes( KarEnvC, IdempotentDatum, idempotent, UnderlyingSourceOfIdempotent, Source(idempotent) )
    end);

    #Q: clarify exactly what is the purpose of this
    AddObjectDatum(KarEnvC,
        function (KarEnvC, obj)
        return IdempotentDatum ( obj );
    end);

#not much interesting idea: 
# In case I want to separate the datum of the underlying object (the source of the idempotent) from the constructor, I can do it in this way, adding the attribute "UnderlyingObjectForKaroubiObjects" in the declaration file
    # InstallMethod(UnderlyingObjectForKaroubiObjects,
    #             [ IsKaroubiObject ],
    #     function (obj)
    #     return Source( IdempotentDatum (obj) );
    # end);

    if CanCompute( C, "IsWellDefinedForObjects" ) then
        AddIsWellDefinedForObjects( KarEnvC,
            function ( KarEnvC, obj )
                local C, e;
                C := UnderlyingCategory( KarEnvC );
                e := IdempotentDatum ( obj );

                return IsCongruentForMorphisms( C, PreCompose(e, e), e );
            end );
    fi;

    #Q: is it better to use IsCongruentForMorphisms or IsEqualForMorphisms?
    AddIsEqualForObjects( KarEnvC,
            function ( KarEnvC, obj1, obj2 )
                local KarEnvC, l1, l2;
                C := UnderlyingCategory( KarEnvC );
                e1 := IdempotentDatum( obj1 );
                e2 := IdempotentDatum( obj2 );

                return IsCongruentForMorphisms( C, e1, e2 );
            end );
 
    AddMorphismConstructor( KarEnvC,
            function ( KarEnvC, s, morph, t )

                return CreateCapCategoryMorphismWithAttributes( KarEnvC, s, t, UnderlyingMorphismDatum, morph);
            end );

    AddMorphismDatum(KarEnvC,
        function (KarEnvC, morph)
        return UnderlyingMorphismDatum ( morph );
    end);

    AddIsEqualForMorphisms( KarEnvC,
            function ( KarEnvC, morphism1, morphism2 )
                local C, mor1, mor2;
                C := UnderlyingCategory( KarEnvC );
                mor1 := UnderlyingMorphismDatum ( morphism1 );
                mor2 := UnderlyingMorphismDatum ( morphism2 );
                return(IsEqualForMorphisms(C, mor1, mor2 ));
            end );

        # Remember: these functions always assume that the morphisms are
        # indeed parallel.
    AddIsCongruentForMorphisms( KarEnvC,
        function ( KarEnvC, morphism1, morphism2 )
            local C, mor1, mor2;
            C := UnderlyingCategory( KarEnvC );
            f1 := UnderlyingMorphismDatum ( morphism1 );
            f2 := UnderlyingMorphismDatum ( morphism2 );
            return(IsCongruentForMorphisms(C, f1, f2 ));
        end );

    if CanCompute( C, "IsWellDefinedForMorphisms" ) then
            AddIsWellDefinedForMorphisms( KarEnvC,
                function ( KarEnvC, f )
                    local C, f_l, s_l, t_l;
                    C := UnderlyingCategory( IC );
                    f_u := UnderlyingMorphismDatum( f );
                    e_s := IdempotentDatum( Source( f ) );
                    e_t := IdempotentDatum( Target ( f ) );
                    s_u := Source ( e_s );
                    t_u := Source ( e_t );
                    return IsWellDefinedForMorphismsWithGivenSourceAndRange( C, s_u, f_u, t_u ) and IsCongruentForMorphisms( f, PreCompose( e_s, PreCompose( f, e_t ) ) );
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

    #Q: do I have to add manually: if CanCompute... then AddIsMonomorphism, AddIsEpimorphism, AddIsIsomorphism, AddIsSplitMonomorphism, AddInverseMorphism,  AddCoproduct, AddInitialObject, AddTerminalObject, AddDirectProduct, ecc...

    #Q: there is this line of code inside the old file, what do it does? Do I have to add it, in some other form?
    #category_weight_list := category!.derivations_weight_list;
    #Q:Then he add manually a lot of methods lime kernelobject, zeroObject, KernelLift
    #Q: should I add something like the essential image of the underlying category? Should I add the formal splitting of an element in this essential image? Should I implement a proof (maybe in the example file) that in KarEnvC all the idempotent splits?




end)