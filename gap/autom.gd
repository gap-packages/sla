DeclareOperation( "FiniteOrderInnerAutomorphisms", 
[ IsString, IsInt, IsInt ] );

DeclareOperation( "FiniteOrderOuterAutomorphisms", 
[ IsString, IsInt, IsInt, IsInt ] );

DeclareAttribute( "KacDiagram", IsGeneralMapping );


DeclareOperation( "NilpotentOrbitsOfThetaRepresentation", 
                   [ IsGeneralMapping ] );

DeclareAttribute( "CartanSubspace", IsGeneralMapping );

DeclareOperation( "ClosureDiagram", [ IsLieAlgebra, IsObject, IsList ] );

DeclareOperation( "CarrierAlgebra", [ IsLieAlgebra, IsObject, IsObject ] );

