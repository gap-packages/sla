DeclareCategory( "IsSSSDataBase", IsObject );

DeclareOperation( "LieAlgebraAndSubalgebras", [IsString] );

DeclareOperation( "InclusionsGraph", [IsString] );

DeclareOperation( "SubalgebrasInclusion", [IsFLMLOR,IsFLMLOR,IsFLMLOR] );

DeclareOperation( "DynkinIndex", [IsFLMLOR,IsFLMLOR] );

DeclareOperation( "IsomorphismOfSemisimpleLieAlgebras", [IsFLMLOR,IsFLMLOR] );

DeclareOperation( "AreLinearlyEquivalentSubalgebras", 
[IsFLMLOR,IsFLMLOR,IsFLMLOR] );

DeclareOperation( "MakeDatabaseEntry", [IsRecord] );

DeclareOperation( "AddToDatabase", [IsRecord] );
