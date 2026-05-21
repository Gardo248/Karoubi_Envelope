DeclareCategory("IsKaroubiEnvelope",
                IsCapCategory);

DeclareCategory( "IsCellInIsKaroubiEnvelope",
    IsCapCategoryCell );

DeclareCategory("IsKaroubiObject",
                IsCapCategoryObject);

DeclareCategory("IsKaroubiMorphism",
                IsCapCategoryMorphism);

DeclareAttribute( "KaroubiEnvelope",
                IsCapCategory );

DeclareAttribute("UnderlyingCategory",
                IsKaroubiEnvelope);

#Q: Why in the following two I have to put "IsKaroubiObject" as second part of DeclareAttribute? Is it because we are somehow trying to say "IdempotentDatum is a type depending on "IsKaroubiObject"?
#note: we use it to define the objects, it represent the type of the fundamental information to give to define the object in the Karoubi envelope, i.e. the idempotent
DeclareAttribute("IdempotentDatum",
                IsKaroubiObject);

#note: we use it to add to objects in the Karoubi envelope the datum of the source (and target) of the idempotent that we are splitting in the underlying category
DeclareAttribute("UnderlyingSourceOfIdempotent",
                IsKaroubiObject);

#note: we use this to define the morphism, it represent the type of the fundamental information necessary to define the morphism, i.e. a morphism between the source of the source idempotent and the source of the target idempotent in the underlying category
DeclareAttribute("UnderlyingMorphismDatum",
                IsKaroubiMorphism);