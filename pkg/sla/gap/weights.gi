InstallMethod( ProjectionMatrix,
"for two semisimple Lie algebras", true, [ IsLieAlgebra, IsLieAlgebra ], 0,

function( L, K )

    local H, HK, N, K0, hK, hL, b;

    H:= CartanSubalgebra(L);
    HK:= Intersection( H, K );

    N:= LieNormalizer( K, HK );
    if N <> HK then
       Error("The Cartan subalgebras do not match.");
    fi;

    if HasCartanSubalgebra(K) and CartanSubalgebra(K) <> HK then
       K0:= Subalgebra( L, BasisVectors( Basis(K) ), "basis" );
       SetCartanSubalgebra(K0,HK);
    else
       K0:= K;
    fi;

    hK:= CanonicalGenerators( RootSystem(K0) )[3];
    hL:= CanonicalGenerators( RootSystem(L) )[3];

    b:= Basis( Subspace( L, hL ), hL );
    
    return List( hK, x -> Coefficients( b, x ) );
    

end );


InstallMethod( Branching,
"for two semisimple Lie algebras and a weight", true, 
[ IsLieAlgebra, IsLieAlgebra, IsList ], 0,

function( L, K, wt )


    local P, ch, R, W, w0, m0, i, o, mu, pos, S, sim, b, ord, ww, mm, mult,
          w, isg;
          

    P:= ProjectionMatrix(L,K);
    ch:= DominantCharacter( L, wt );
    R:= RootSystem(L);
    W:= WeylGroup(R);
    w0:= [ ]; m0:= [ ];
    for i in [1..Length(ch[1])] do
        o:= WeylOrbitIterator( W, ch[1][i] );
        while not IsDoneIterator(o) do
             mu:= P*NextIterator( o );
             if ForAll( mu, u -> u >= 0 ) then
                pos:= Position( w0, mu );
                if pos = fail then
                   Add( w0, mu );
                   Add( m0, ch[2][i] );
                else
                   m0[pos]:= m0[pos]+ch[2][i];
                fi;
             fi;
        od;
    od;

    S:= RootSystem(K);
    sim:= SimpleRootsAsWeights(S);
    b:= Basis( VectorSpace( Rationals, sim ), sim );
    
    ord:= function( mu, nu )

        # true if mu < nu

        local cf;

        if mu = nu then return fail; fi;
        cf:= Coefficients( b, nu-mu );
        if ForAll( cf, IsInt ) then
           if ForAll( cf, x -> x >= 0 ) then
              return true;
           elif ForAll( cf, x -> x <= 0 ) then
              return false;
           fi;
        fi;

        return fail;

    end;

    ww:=[ ]; mm:= [ ];

    while Length(w0) > 0 do

        # look for a maximum in w0...

        w:= w0[1];
        mult:= m0[1];
        for i in [1..Length(w0)] do
            isg:= ord( w, w0[i] );
            if isg <> fail and isg then
                 w:= w0[i]; mult:= m0[i];
            fi;
        od;

        Add( ww, w ); Add( mm, mult );
        ch:= DominantCharacter( K, w );
        for i in [1..Length(ch[1])] do
            pos:= Position( w0, ch[1][i] );
            m0[pos]:= m0[pos] - mult*ch[2][i];
        od;
        for i in [1..Length(w0)] do
            if m0[i] = 0 then
               Unbind( m0[i] );
               Unbind( w0[i] );
            fi;
        od;
        m0:= Filtered( m0, x -> IsBound(x) );
        w0:= Filtered( w0, x -> IsBound(x) );
    od;

    return [ww,mm];

end );



InstallMethod( DirectSumDecomposition,
"for a module over a semisimple Lie algebra", 
true, [ IsAlgebraModule ], 0,

# IN FACT: we assume that it is a left algebra module!

function( V )

   local L, R, e, sp, x, m, c, sp0, K;

   L:= LeftActingAlgebra( V );

   # We assume that L is reductive, and that the action is "algebraic".

   if LieDerivedSubalgebra( L ) <> L then
      K:= LieDerivedSubalgebra(L);
   else
      K:= L;
   fi; 

   R:= RootSystem(K);
   if R = fail then return fail; fi;
   e:= CanonicalGenerators( R )[1];

   sp:= V;
   for x in e do
       m:= MatrixOfAction( Basis(V), x );
       m:= TransposedMatDestructive(m);
       c:= NullspaceMat(m);
       sp0:= Subspace( V, List( c, u -> u*Basis(V) ), "basis" );
       sp:= Intersection( sp, sp0 );
   od;

   return List( BasisVectors( Basis(sp) ), u -> SubAlgebraModule( V, [u] ) );
    

end );