DeclareCategory("IsKaroubiEnvelope",
                IsCapCategory);

DeclareCategory( "IsCellInIsKaroubiEnvelope",
    IsCapCategoryCell );

DeclareCategory("IsKaroubiObject",
                IsCapCategoryObject);

DeclareCategory("IsKaroubiMorphism",
                IsCapCategoryMorphism);

DeclareAttribute("KaroubiEnvelope",
                IsCapCategory);

DeclareOperation("UnderlyingObject",
                [IsKaroubiMorphism]);

DeclareAttribute("Idempotent",
                IsKaroubiObject);

DeclareAttribute("UnderlyingMorphism",
                IsKaroubiMorphism);