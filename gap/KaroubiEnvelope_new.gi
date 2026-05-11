#Q: need this to understand if a morphism is an idempotent or not, is this the correct way? Do I have to put something in the gd file? Like an attribute or an operation? In the old Karoubi envelope is not declared IsIdempotent. is it because it already exists in GAP? Should I find a better name and declare a new Attribute or property with this name?
#note: take a morphism of the category and return a boolean that tells you if the morphism is an idempotent or not
InstallMethod ( IsIdempotent,
	        [ IsCapCategoryMorphism ],
    function (f)
    return IsCongruentForMorphisms( PreCompose(f, f), f );
end);

InstallMethod ( IsMorphismOfIdempotents,
                [ IsIdempotent, IsCapCategoryMorphism, IsIdempotent ],
    function(e, p, f)
    return IsCongruentForMorphisms(p, PreCompose(f, PreCompose(p, e)) );

end)

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
     
    #Q: Is this a good definition? Does it make sense? Should I use instead AddCategoryObjectWithAttributes? It seems unnecessary, I only have a morphism in the underlying category that, after I checked it is an idempotent, I use as object in the new category. Where did I checked that it is indeed an idempotent?
    AddObjectConstructor(KarEnvC,
        function(KarEnvC, idempotent)
        return AddObject( category, idempotent )
    end);
end)