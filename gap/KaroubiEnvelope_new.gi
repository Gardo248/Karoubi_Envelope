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
        CapJitDataTypeOfMorphismOfCategory( C ), #is this right? Do I have to put the condition on the morphism here?
    fail );

    #note: I set the source category C as the Underlying category of the output category KarEnvC
    SetUnderlyingCategory( KarEnvC, C );
     
    #Q: Is this a good definition? Does it make sense? Should I use instead AddCategoryObjectWithAttributes? It seems unnecessary, I only have a morphism in the underlying category that I use as object in the new category. I will postpone the check that the morphism is an idempotent inside the IsWellDefinedForObject
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

#Q: shouldn't I implement somehow the underlying category attribute? I saw that Lippa did't
    if CanCompute( C, "IsWellDefinedForObjects" ) then
        AddIsWellDefinedForObjects( KarEnvC,
            function ( KarEnvC, obj )
                local C, e;
                C := UnderlyingCategory( KarEnvC );
                e := IdempotentDatum ( obj );

                return IsCongruentForMorphisms( C, PreCompose(f, f), f );
            end );
    fi;

    AddIsEqualForObjects( KarEnvC,
            function ( KarEnvC, obj1, obj2 )
                local KarEnvC, l1, l2;
                C := UnderlyingCategory( KarEnvC );
                e1 := IdempotentDatum( obj1 );
                e2 := IdempotentDatum( obj2 );

                return IsCongruentForMorphisms( C, e1, e2 );
            end );
     
    AddMorphismConstructor( KarEnvC,
            function ( KarEnvC, s, t, morph )

                return CreateCapCategoryMorphismWithAttributes( KarEnvC, s, t, UnderlyingMorphism, morph);
            end );

    AddMorphismDatum(KarEnvC,
        function (KarEnvC, morph)
        return UnderlyingMorphism ( morph );
    end);

    AddIsEqualForMorphisms( KarEnvC,
            function ( KarEnvC, morphism1, morphism2 )
                local C, mor1, mor2;
                C := UnderlyingCategory( KarEnvC );
                mor1 := UnderlyingMorphism ( morphism1 );
                mor2 := UnderlyingMorphism ( morphism2 );
                return(IsEqualForMorphisms(C, mor1, mor2 ));
            end );

        # Remember: these functions always assume that the morphisms are
        # indeed parallel.
    AddIsCongruentForMorphisms( KarEnvC,
        function ( KarEnvC, morphism1, morphism2 )
            local C, mor1, mor2;
            C := UnderlyingCategory( KarEnvC );
            mor1 := UnderlyingMorphism ( morphism1 );
            mor2 := UnderlyingMorphism ( morphism2 );
            return(IsCongruentForMorphisms(C, mor1, mor2 ));
        end );

    if CanCompute( C, "IsWellDefinedForMorphisms" ) then
            AddIsWellDefinedForMorphisms( IC,
                function ( IC, f )
                    local C, f_l, s_l, t_l;
                    C := UnderlyingCategory( IC );
                    f_l := ListDatum( f );
                    s_l := ListDatum( Source( f ) );
                    t_l := ListDatum( Target( f ) );

                    if Length( f_l ) = 0 then
                        return Length( s_l ) = 0;
                    elif Length( f_l ) = 1 then
                        return Length( s_l ) = 1 and Length( t_l ) = 1
                            and IsWellDefinedForMorphismsWithGivenSourceAndRange( C, s_l[1], f_l[1], t_l[1] );
                            # Q: can I assume that the "WithGivenSourceAndRange" variant is defined?
                            # (does it just check equality of the objects?)
                    else
                        return false;
                    fi;
                end );
        fi;








    # AddMorphismConstructor(KarEnvC,
    #     function(KarEnvC, idempotent)
    #     return AddObject( category, idempotent )
    # end);

end)