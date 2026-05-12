DeclareCategory("IsKaroubiEnvelope",
                IsCapCategory);

DeclareCategory( "IsCellInIsKaroubiEnvelope",
    IsCapCategoryCell );

DeclareCategory("IsKaroubiObject",
                IsCapCategoryObject);

DeclareCategory("IsKaroubiMorphism",
                IsCapCategoryMorphism);



DeclareAttribute("UnderlyingCategory",
                IsKaroubiEnvelope);

#Q: Why in the following two I have to put "IsKaroubiObject" as second part of DeclareAttribute? Is it because we are somehow trying to say "IdempotentDatum is a type depending on "IsKaroubiObject"?
DeclareAttribute("IdempotentDatum",
                IsKaroubiObject);

DeclareAttribute("UnderlyingSourceOfIdempotent",
                IsKaroubiObject);

DeclareAttribute("UnderlyingObjectForKaroubiObjects",
                IsKaroubiObject);

DeclareOperation("UnderlyingObjectForKaroubiMorphism",
                [IsKaroubiMorphism]);

DeclareAttribute("UnderlyingMorphism",
                IsKaroubiMorphism);