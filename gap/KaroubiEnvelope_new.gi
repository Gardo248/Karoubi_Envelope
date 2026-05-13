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
                C := UnderlyingCategory( IC );
                e1 := IdempotentDatum( obj1 );
                e2 := IdempotentDatum( obj2 );

                return IsCongruentForMorphisms( C, e1, e2 );
            end );
    
AddMorphismConstructor( KarEnvC,
            function ( KarEnvC, s, t, morphism )

                return CreateCapCategoryMorphismWithAttributes( IC, s, t, ListDatum, list );
            end );






    # AddMorphismConstructor(KarEnvC,
    #     function(KarEnvC, idempotent)
    #     return AddObject( category, idempotent )
    # end);

end)