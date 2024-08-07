# SLA, chapter 5
#
# DO NOT EDIT THIS FILE - EDIT EXAMPLES IN THE SOURCE INSTEAD!
#
# This file has been generated by AutoDoc. It contains examples extracted from
# the package documentation. Each example is preceded by a comment which gives
# the name of a GAPDoc XML file and a line range from which the example were
# taken. Note that the XML file in turn may have been generated by AutoDoc
# from some other input.
#
gap> START_TEST("sla05.tst");

# doc/manual.xml:1419-1431
gap> f:= FiniteOrderInnerAutomorphisms("E",6,3);
[ [ v.72, v.1, v.2, v.3, v.4, v.5, v.6 ] -> [ (E(3))*v.72, (E(3)^2)*v.1, v.2, 
      v.3, v.4, v.5, v.6 ], [ v.72, v.1, v.2, v.3, v.4, v.5, v.6 ] -> 
    [ v.72, (E(3))*v.1, (E(3))*v.2, v.3, v.4, v.5, v.6 ], 
  [ v.72, v.1, v.2, v.3, v.4, v.5, v.6 ] -> [ (E(3))*v.72, v.1, (E(3))*v.2, 
      v.3, v.4, v.5, v.6 ], [ v.72, v.1, v.2, v.3, v.4, v.5, v.6 ] -> 
    [ v.72, v.1, v.2, v.3, (E(3))*v.4, v.5, v.6 ], 
  [ v.72, v.1, v.2, v.3, v.4, v.5, v.6 ] -> [ (E(3))*v.72, (E(3))*v.1, v.2, 
      v.3, v.4, v.5, (E(3))*v.6 ] ]
gap> Source(f[1]);
<Lie algebra of dimension 78 over CF(3)>

# doc/manual.xml:1471-1479
gap> f:= FiniteOrderOuterAutomorphisms( "A", 5, 4, 2 );;
gap> r:= KacDiagram( f[1] );
rec( 
  CM := [ [ 2, 0, -1, 0 ], [ 0, 2, -1, 0 ], [ -1, -1, 2, -1 ], 
      [ 0, 0, -2, 2 ] ], labels := [ 1, 1, 2, 1 ], weights := [ 1, 1, 0, 0 ] )
gap> r.labels*r.CM;      
[ 0, 0, 0, 0 ]

# doc/manual.xml:1538-1561
gap> # reset random state to ensure the output of this example match
gap> Reset(GlobalMersenneTwister, 1);;
gap> f:= FiniteOrderInnerAutomorphisms( "D", 5, 3 );;   
gap> s:= NilpotentOrbitsOfThetaRepresentation( f[2] : method:= "Carrier" );;
#I  Selected carrier algebra method.
#I  Constructed 123 root bases of possible flat subalgebras, now checking them...
#I  Obtained 30 Cartan elements, weeding out equivalent copies...
gap> Length(s);
10
gap> s[4];
[ v.14+v.15+v.38, (-2)*v.41+(-1)*v.42, v.18+v.34+v.35 ]
gap> L:= SimpleLieAlgebra("E",6,Rationals);;
gap> NilpotentOrbitsOfThetaRepresentation( L, [0,1,0,0,0,0] );
#I  Selected Weyl orbit method.
#I  Constructed a Weyl transversal of 72 elements.
#I  Obtained 5 Cartan elements, weeding out equivalent copies...
[ [ v.65+v.66+v.67, (2)*v.73+(3)*v.74+(4)*v.75+(6)*v.76+(4)*v.77+(2)*v.78, 
      v.29+v.30+v.31 ], 
  [ (2)*v.55+(2)*v.66, (2)*v.73+(4)*v.74+(4)*v.75+(6)*v.76+(4)*v.77+(2)*v.78, 
      v.19+v.30 ],
  [ v.66+v.70, (2)*v.73+(2)*v.74+(3)*v.75+(4)*v.76+(3)*v.77+(2)*v.78, 
      v.30+v.34 ], [ v.71, v.73+v.74+(2)*v.75+(3)*v.76+(2)*v.77+v.78, v.35 ] ]

# doc/manual.xml:1617-1648
gap> f:= FiniteOrderInnerAutomorphisms( "E", 8, 8 );;  
gap> h:= f[8];;
gap> sl2:= NilpotentOrbitsOfThetaRepresentation(h);;  
#I  Selected carrier algebra method.
#I  Constructed 2782 root bases of possible flat subalgebras, now checking them...
#I  Obtained 58 Cartan elements, weeding out equivalent copies...
gap> Length(sl2);
27
gap> L:= Source(h);;                    
gap> r:= ClosureDiagram( L, h, sl2 );;  
#I  All (non-) inclusions proved!
gap> r.diag;
[ [ 2, 1 ], [ 3, 1 ], [ 4, 2 ], [ 4, 3 ], [ 5, 1 ], [ 6, 5 ], [ 7, 2 ], 
  [ 7, 5 ], [ 8, 4 ], [ 9, 4 ], [ 9, 7 ], [ 10, 6 ], [ 10, 7 ], [ 11, 3 ], 
  [ 11, 6 ], [ 12, 7 ], [ 13, 9 ], [ 13, 10 ], [ 13, 11 ], [ 14, 9 ], 
  [ 14, 12 ], [ 15, 8 ], [ 15, 9 ], [ 16, 6 ], [ 17, 10 ], [ 17, 12 ], 
  [ 17, 16 ], [ 18, 13 ], [ 18, 16 ], [ 19, 13 ], [ 19, 15 ], [ 20, 11 ], 
  [ 20, 16 ], [ 21, 14 ], [ 21, 17 ], [ 21, 18 ], [ 22, 14 ], [ 22, 15 ], 
  [ 23, 18 ], [ 23, 20 ], [ 24, 18 ], [ 24, 19 ], [ 25, 21 ], [ 25, 22 ], 
  [ 25, 24 ], [ 26, 23 ], [ 26, 24 ], [ 27, 21 ], [ 27, 23 ] ]
gap> # Now we do the adjoint representation of the Lie algebra of type F4:
gap> L:= SimpleLieAlgebra("F",4,Rationals);;
gap> o:= NilpotentOrbits(L);;
gap> sl2:= List( o, SL2Triple );;
gap> r:= ClosureDiagram( L, [0,0,0,0], sl2 );;      
#I  All (non-) inclusions proved!
gap> r.diag;
[ [ 2, 1 ], [ 3, 2 ], [ 4, 3 ], [ 5, 3 ], [ 6, 4 ], [ 6, 5 ], [ 7, 6 ], 
  [ 8, 7 ], [ 9, 7 ], [ 10, 8 ], [ 10, 9 ], [ 11, 8 ], [ 12, 10 ], 
  [ 13, 11 ], [ 13, 12 ], [ 14, 13 ], [ 15, 14 ] ]

# doc/manual.xml:1680-1697
gap> f:= FiniteOrderInnerAutomorphisms( "F", 4, 5 );;
gap> h:= f[4];;
gap> sl2:= NilpotentOrbitsOfThetaRepresentation( h );;  
#I  Selected Weyl orbit method.
#I  Constructed a Weyl transversal of 144 elements.
#I  Constructed 621 Cartan elements to be checked.
gap> L:= Source(h);   
<Lie algebra of dimension 52 over CF(5)>
gap> r:=CarrierAlgebra( L, h, sl2[1][3] );   
rec( g0 := [ v.49+(2)*v.50+(2)*v.51+(3)*v.52, v.50+(1/2)*v.51+v.52 ], 
  gn := [ [ v.24, v.33 ], [ v.21 ], [ v.15 ] ], 
  gp := [ [ v.9, v.48 ], [ v.45 ], [ v.39 ] ] )
gap> K:= Subalgebra( L, Concatenation( r.g0, Flat(r.gp), Flat(r.gn) ) );
<Lie algebra over CF(5), with 10 generators>
gap> SemiSimpleType( K );
"B2"

# doc/manual.xml:1720-1726
gap> f:= FiniteOrderInnerAutomorphisms( "A", 3, 3 );;
gap> c:= CartanSubspace( f[3] ); 
<vector space of dimension 1 over CF(3)>
gap> BasisVectors( Basis( c ) );
[ v.1+v.5+v.12 ]

#
gap> STOP_TEST("sla05.tst", 1);
