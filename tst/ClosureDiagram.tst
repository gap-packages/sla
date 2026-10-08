gap> START_TEST("ClosureDiagram.tst");
gap> level:= InfoLevel( InfoSLA );;
gap> SetInfoLevel( InfoSLA, 0 );

# The fixed point subalgebra is a torus, see
# https://github.com/gap-packages/sla/issues/8
gap> f:= FiniteOrderInnerAutomorphisms( "A", 1, 2 )[1];;
gap> Length( Grading( f )[1] );
1
gap> s:= NilpotentOrbitsOfThetaRepresentation( f );;
gap> r:= ClosureDiagram( Source( f ), f, s );;
gap> r.sl2;
[ [ v.2, v.3, v.1 ], [ v.1, (-1)*v.3, v.2 ] ]
gap> r.diag;
[  ]

#
gap> f:= FiniteOrderInnerAutomorphisms( "G", 2, 6 )[2];;
gap> Length( Grading( f )[1] );
2
gap> s:= NilpotentOrbitsOfThetaRepresentation( f );;
gap> r:= ClosureDiagram( Source( f ), f, s );;
gap> r.sl2;
[ [ (6)*v.7+(10)*v.8, (6)*v.13+(10)*v.14, v.1+v.2 ], 
  [ v.6+v.7, (-2)*v.14, v.1+v.12 ], 
  [ (2)*v.6+(2)*v.8, (-2)*v.13+(-2)*v.14, v.2+v.12 ], [ v.7, v.13, v.1 ], 
  [ v.8, v.14, v.2 ], [ v.6, (-1)*v.13+(-2)*v.14, v.12 ] ]
gap> r.diag;
[ [ 4, 1 ], [ 4, 2 ], [ 5, 1 ], [ 5, 3 ], [ 6, 2 ], [ 6, 3 ] ]

#
gap> SetInfoLevel( InfoSLA, level );
gap> STOP_TEST("ClosureDiagram.tst");
