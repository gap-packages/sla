InstallMethod( FiniteOrderInnerAutomorphisms,
"for string, integer and integer", true, [ IsString, IsInt, IsInt ], 0,
function( type, rank, m )

    # finite order auts of the simple Lie algebra, 
    # of order m, that correspond to untwisted diagrams,
    # in other words, they correpond to the identity
    # diagram automorphism.

    local L, w, cc, ch, g, a, ss, good, s, i, auts, g0, t, G, f, stack, 
          stack0, j, u, p1, p2, list, n;

    n:= rank;
    if type = "A" then
       list:= [2..n+1]; Add( list, 1 );
       p1:= PermList( list );
       p2:= ();
       i:= 1;
       while 1+i < n+2-i do
           p2:= p2*(1+i,n+2-i);
           i:= i+1;
       od;
       G:= Group( [ p1, p2 ] ); 
    elif type = "B" then
       if rank = 2 then
          G:= Group([(1,3)]);
       else
          G:= Group([(1,2)]);
       fi;
    elif type = "C" then
       p2:= ();
       i:= 1;
       while i < n+2-i do
           p2:= p2*(i,n+2-i);
           i:= i+1;
       od;
       G:= Group( [p2] );
    elif type = "D" and rank > 4 then
       p2:= ();
       i:= 1;
       while i < n+2-i do
           p2:= p2*(i,n+2-i);
           i:= i+1;
       od;
       G:= Group( [(1,2),(n,n+1),p2] );
    elif type = "D" and rank = 4 then
       G:= Group( [ (1,2,4,5), (1,2) ] );
    elif type = "E" and rank = 6 then
       G:= Group( [ (1,2,7)*(3,4,6), (1,2)*(3,4)] );
    elif type = "E" and rank = 7 then
       G:= Group( [ (1,8)*(2,7)*(4,6) ] );
    else
       G:= Group( [ () ] );
    fi;

    G:= Elements( G );
    G:= Filtered( G, x -> x <> x^0 );

    L:= SimpleLieAlgebra( type, rank, CF(m) );
    w:= E(m);

    cc:= ExtendedCartanMatrix( RootSystem(L) );

    ch:= ChevalleyBasis(L);
    g:= [ ch[2][ Length(ch[2]) ] ];
    Append( g, ch[1]{[1..rank]} );

    a:= cc.labels;
    ss:= [ ];

    stack:= [ List( g, x -> 0 ) ]; 

    for i in [1..Length(g)] do

        stack0:= [ ];
        for s in stack do
            u:= a*s;
            if u = m and Gcd(s) = 1 then
               good:= true;
               for p1 in G do
                   t:= Permuted( s, p1 );
                   if t in ss then
                      good:= false; break;
                   fi;
               od;
               if good then
                  Add( ss, s );
               fi;
            elif u < m then
               for j in [0..m-u] do
                   t:= ShallowCopy(s);
                   t[i]:= j; 
                   Add( stack0, t );
               od;
            fi;
        od;
        stack:= stack0;
    od;

    for s in stack do
        u:= a*s;
        if u = m and Gcd(s) = 1 then
           good:= true;
           for p1 in G do
               t:= Permuted( s, p1 );
               if t in ss then
                  good:= false; break;
               fi;
           od;
           if good then
              Add( ss, s );
           fi;
        fi;
    od;


    auts:= [ ];

    for s in ss do
        g0:= List( [1..Length(g)], i -> w^s[i]*g[i] );
        f:= AlgebraHomomorphismByImagesNC( L, L, g, g0 );
        SetOrder(f,m);
        SetKacDiagram( f, rec( CM:= cc.ECM, labels:= cc.labels, weights:= s ) );
        Add( auts, f );
    od;

    return auts;


end );



InstallMethod( FiniteOrderOuterAutomorphisms,
"for string, and three integers", true, [ IsString, IsInt, IsInt, IsInt ], 0,
function( type, rank, m, d )


     # corresponding to the diagram automorphism of 
     # order d.

     local phi, L, w, R, cg, cg0, sim, i, pos, f, mat, mat0, sol, cK, H, K,
           V, y, rt, sp, h, g, rts, B, C, j, v, a, ss, done, s, auts, g0, G, 
           t, n, p2, good, u, p1, stack, stack0, en;

     phi:= function( rt )

        local r0;        
        if type = "A"  then
           return Reversed(rt);
        elif type = "D" and d=2 then
           r0:= ShallowCopy( rt );
           r0[ rank ]:= rt[rank-1];
           r0[rank-1]:= rt[rank];
        elif type = "D" and d = 3 then
           if rank <> 4 then
              Error( "only D_4 has a diagram automorphism of order 3");
           fi;
           r0:= ShallowCopy( rt );
           r0[1]:= rt[4]; r0[3]:= rt[1]; r0[4]:= rt[3];
        else
           r0:= ShallowCopy(rt);
           r0[1]:= rt[6]; r0[6]:= rt[1];
           r0[3]:=rt[5]; r0[5]:= rt[3];
        fi;
        return r0; 

     end;

    if type = "A" and rank = 1 then return [ ]; fi;

    if type ="D" and d = 2 then
       n:= rank-1;
       p2:= ();
       i:= 1;
       while i < n+2-i do
           p2:= p2*(i,n+2-i);
           i:= i+1;
       od;
       G:= Group( [ p2 ] ); 
       G:= Elements( G );
       G:= Filtered( G, x -> x <> x^0 );
    elif type = "A" and IsOddInt(rank) then
       G:= [ (1,2) ];
    else
       G:= [ ];
    fi;

   
    if d=2 then
       L:= SimpleLieAlgebra( type, rank, CF(m) );
    else
       L:= SimpleLieAlgebra( type, rank, CF(3*m) );
    fi;
    
    w:= E(m);

    R:= RootSystem(L);
    cg:= CanonicalGenerators( R );
    cg0:= [ [], [], [] ];

    sim:= SimpleSystemNF( R );
    for i in [1..Length(sim)] do
        pos:= Position( sim, phi(sim[i]) );
        Add( cg0[1], cg[1][pos] );
        Add( cg0[2], cg[2][pos] );
        Add( cg0[3], cg[3][pos] );     
    od;

    f:= AlgebraHomomorphismByImagesNC( L, L, Flat(cg), Flat(cg0) );

    mat:= [ ];
    for i in [1..Dimension(L)] do
        Add( mat, Coefficients( Basis(L), Image( f, Basis(L)[i] ) ) );
    od;

    mat0:= mat- IdentityMat( Dimension(L) );

    sol:= NullspaceMat( mat0 );
       
    K:= Subalgebra( L, List( sol, x -> LinearCombination(Basis(L),x) ) );

    cK:= CanonicalGenerators( RootSystem(K) );

    if d=2 then
       mat0:= mat+IdentityMat( Dimension(L) );
    else
       mat0:= mat-E(3)*IdentityMat( Dimension(L) );
    fi;

    sol:= NullspaceMat( mat0 );
    V:= LeftAlgebraModuleByGenerators( K, function(x,v) return x*v; end,
           List( sol, x -> LinearCombination( Basis(L), x ) ) );

    y:= List( cK[2], x -> MatrixOfAction( Basis(V), x ) );

    # get simultaneous kernel...

    mat:= y[1];
    for i in [2..Length(y)] do Append( mat, y[i] ); od;

    sol:= NullspaceMat( TransposedMatDestructive(mat) );

    g:= [ LinearCombination( Basis(V), sol[1] )![1] ];

    sp:= Basis( VectorSpace( LeftActingDomain(L), g ), g );

    rt:= [ ];
    for h in cK[3] do
        Add( rt, Coefficients( sp, h*g[1] )[1] );
    od;

    sim:= SimpleRootsAsWeights( RootSystem(K) );
    sp:= Basis( VectorSpace( Rationals, sim ), sim );
    rts:= [ Coefficients( sp, rt ) ];
    Append( rts, SimpleSystemNF(RootSystem(K) ) );

    B:= BilinearFormMatNF( RootSystem(K) );
    C:= NullMat( Length(rts), Length(rts) );
    for i in [1..Length(rts)] do
        for j in [1..Length(rts)] do
            C[i][j]:= 2*( rts[i]*(B*rts[j]) )/( rts[j]*(B*rts[j]) );
        od;
    od;

    Append( g, cK[1] );

    if type ="D" and d=2 then
       # find the standard enumeration...
       pos:= PositionProperty( C, x -> Length(Filtered(x,y-> y<>0 ) ) = 2);
       en:= [ pos ];
       while Length(en) < Length(C) do 
           pos:= Filtered( [1..Length(C[pos])], j -> C[pos][j] < 0 and
	                                                     not j in en )[1];
	   Add( en, pos );
       od;
       C:= C{en}{en};
       g:= g{en};
    fi;

    v:= NullspaceMat(C)[1];
    a:= Lcm( List( v, DenominatorRat ) );
    v:= a*v;

    ss:= [ ];

    stack:= [ List( g, x -> 0 ) ]; 
    for i in [1..Length(g)] do
        stack0:= [ ];
        for s in stack do
            u:= d*(v*s);
            if u = m and Gcd(s) = 1 then
               good:= true;
               for p1 in G do
                   t:= Permuted( s, p1 );
                   if t in ss then
                      good:= false; break;
                   fi;
               od;
               if good then
                  Add( ss, s );
               fi;
            elif u < m then
               for j in [0..m-u] do
                   t:= ShallowCopy(s);
                   t[i]:= j; 
                   Add( stack0, t );
               od;
            fi;
        od;
        stack:= stack0;
    od;
    
    for s in stack do
        u:= d*(v*s);
        if u = m and Gcd(s) = 1 then
           good:= true;
           for p1 in G do
               t:= Permuted( s, p1 );
               if t in ss then
                  good:= false; break;
               fi;
           od;
           if good then
              Add( ss, s );
           fi;
        fi;
    od;

    auts:= [ ];
    for s in ss do
        g0:= List( [1..Length(g)], i -> w^s[i]*g[i] );
        f:= AlgebraHomomorphismByImagesNC( L, L, g, g0 );
        SetOrder(f,m);
        SetKacDiagram(f,rec( CM:= C, labels:= v, weights:= s ));
        Add( auts, f );
    od;

    return auts;       

end );


InstallOtherMethod( Grading,
"for a finite order automorphism", true, [ IsGeneralMapping ], 0,
function( f )

    local L, m, w, mat, id, spaces, i, sp;
    
    L:= Source(f);
    m:= Order(f);
    w:= E(m);

    mat:= List( Basis(L), x -> Coefficients( Basis(L), Image(f,x) ) );
    id:= mat^0;

    spaces:= [ ];
    for i in [0..m-1] do
        sp:= NullspaceMat( mat - w^i*id );
        Add( spaces, List( sp, x -> LinearCombination(Basis(L),x) ) );
    od;

    return spaces;

end );



SLAfcts.nil_orbs_inner:= function( L, gr0, gr1, gr2 )

     # Here L is a simple graded Lie algebra; gr0 a basis of the
     # elts of degree 0, gr1 of degree 1, and gr2 of degree -1.
     # We find the nilpotent G_0-orbits in g_1.
     # We assume that the given CSA of L is also a CSA of g_0.

     local F, g0, s, r, HL, Hs, R, Ci, hL, hl, C, rank, posRv_L, posR_L,
           posR, i, j, sums, fundR, inds, tr, h_candidates, BH, W, h, 
           c_h, ph, stb, v, w, is_rep, h0, wr, Omega, good_h, g1, g2, h_mats1,
           h_mats2, mat, sl2s, id1, id2, V, e, f, bb, ef, found, good, co, x, 
           C_h0, sp, sp0, y, b, bas, c, Cs, B, k, sol, info;

     F:= LeftActingDomain(L);

     g0:= Subalgebra( L, gr0, "basis" );

     s:= LieDerivedSubalgebra( g0 );
     r:= LieCentre(g0);

     HL:= CartanSubalgebra(L);
     Hs:= Intersection( s, HL );
     SetCartanSubalgebra( s, Hs );

     R:= RootSystem(L);
     Ci:= CartanMatrix( R )^-1;
     hL:= CanonicalGenerators(R)[3];
     hl:= List( NilpotentOrbits(L), x -> (Ci*WeightedDynkinDiagram(x))*hL );

     for i in [1..Length(hl)] do
         if hl[i] = 0*hl[i] then
            Unbind( hl[i] );
         fi;
     od;
     hl:= Filtered( hl, x -> IsBound(x) );

     C:= CartanMatrix( R );
     rank:= Length(C);

     # we have to compute a root system of s such that its
     # positive roots are also positive in L...
     # Note that since the CSA of s is a subset of the CSA of L,
     # the roots of s are a subset of the roots of L; also:
     # the part of the CSA of L that is not in s, commutes with s,
     # the coordinates of the roots of s with respect to those h-s
     # is zero (if you understand what I mean...). 

     posRv_L:= PositiveRootVectors(R);
     posR_L:= PositiveRootsNF(R);
     posR:= [ ];
     for i in [1..Length(posRv_L)] do
         if posRv_L[i] in s then
            Add( posR, posR_L[i] );
         fi;
     od;

     sums:= [ ];
     for i in [1..Length(posR)] do
         for j in [i+1..Length(posR)] do
             Add( sums, posR[i]+posR[j] );
         od;
     od;
     fundR:= Filtered( posR, x -> not x in sums );
     inds:= List( fundR, x -> Position( posR_L, x ) );
     tr:= WeylTransversal( R, inds ); 

info:= "Constructed a Weyl transversal of ";
Append( info, String(Length(tr)) );
Append( info, " elements.");

Info(InfoSLA,2,info);

     h_candidates:= [ ];
     BH:= Basis( VectorSpace( F, hL ), hL );
     W:= WeylGroup(R);
     for h in hl do
   
         # first we get the indices of the simple reflections that
         # stabilise h...
         c_h:= Coefficients( BH, h );
         ph:= C*c_h;
         stb:= Filtered( [1..rank], k -> ph[k] = 0 );

         for w in tr do
             is_rep:= true;
             for i in stb do
                 # see whether there is an expression for w ending with i
                 v:= ShallowCopy(w); Add( v, i );
                 if LengthOfWeylWord( W, v ) < Length(w) then
                    is_rep:= false;
                    break;
                 fi;
             od;
             if is_rep then
                h0:= ShallowCopy(c_h);
                wr:= Reversed(w);
                for i in wr do
                    h0[i]:= h0[i] - (C[i]*h0);
                od;
                AddSet( h_candidates, h0 );
             fi;
         od;
     od;
     

info:=  "Constructed ";
Append( info, String( Length(h_candidates) ) );
Append( info, " Cartan elements to be checked." );
Info( InfoSLA, 2, info );

     # now we need to compute sl_2 triples wrt the h-s found...

     Omega:= [0..Dimension(L)];
     good_h:= [ ];

     g1:= Basis( Subspace( L, gr1 ), gr1 );
     g2:= Basis( Subspace( L, gr2 ), gr2 );

     # the matrices of hL[i] acting on g1
     h_mats1:= [ ];
     for h0 in hL do
         mat:= [ ];
         for i in [1..Length(g1)] do
             Add( mat, Coefficients( g1, h0*g1[i] ) );
         od;
         Add( h_mats1, mat );
     od;

     # those of wrt g2...
     h_mats2:= [ ];
     for h0 in hL do
         mat:= [ ];
         for i in [1..Length(g1)] do
             Add( mat, Coefficients( g2, h0*g2[i] ) );
         od;
         Add( h_mats2, mat );
     od;

     sl2s:= [ ];
     id1:= IdentityMat( Length(g1) );
     id2:= IdentityMat( Length(g2) );
     for h in h_candidates do

         mat:= h*h_mats1;
         mat:= mat - 2*id1;
         V:= NullspaceMat( mat );
         e:= List( V, v -> v*gr1 );

         mat:= h*h_mats2;
         mat:= mat + 2*id2;
         V:= NullspaceMat( mat );
         f:= List( V, v -> v*gr2 );

         # check whether h0 in [e,f]....
         bb:= [ ];
         for x in e do
             for y in f do
                 Add( bb, x*y );
             od;
         od;
         ef:= Subspace( L, bb );

         h0:= h*hL;

         if h0 in ef then  #otherwise we can just discard h...
            found:= false;
            good:= false;
            while not found do

                co:= List( e, x -> Random(Omega) );
                x:= co*e;
                sp:= Subspace( L, List( f, y -> x*y) );

                if Dimension(sp) = Length(e) and h0 in sp then

                   # look for a nice one...
                   for i in [1..Length(co)] do
                       k:= 0;
                       found:= false;
                       while not found do
                           co[i]:= k;
                           x:= co*e;
                           sp:= Subspace( L, List( f, y -> x*y) );

                           if Dimension(sp) = Length(e) and h0 in sp then
                              found:= true;
                           else
                              k:= k+1;
                           fi;
                       od;
                   od;

                   mat:= List( f, u -> Coefficients( Basis(sp), x*u ) );
                   sol:= SolutionMat( mat, Coefficients( Basis(sp), h0 ) );

                   Add( good_h, h );
                   Add( sl2s, [sol*f,h0,x] );

                   found:= true;

                       
                else
                   C_h0:= LieCentralizer( g0, Subalgebra( g0, [h0] ) );
                   sp0:= Subspace( L, List( Basis(C_h0), y -> y*x ) );
                   if Dimension(sp0) = Length(e) then
                      found:= true;
                      good:= false;
                   fi;
                fi;
      
            od;

         fi;
     od;

     # Now we compute a set of canonical generators of s...
     inds:= List( fundR, x -> Position( posR_L, x ) );

     x:= PositiveRootVectors( R ){inds};
     y:= NegativeRootVectors( R ){inds};
     for i in [1..Length(x)] do
         V:= VectorSpace( F, [ x[i] ] );
         b:= Basis( V, [x[i]] );
         c:= Coefficients( b, (x[i]*y[i])*x[i] )[1];
         y[i]:= y[i]*2/c;
     od;
     bas:= List( [1..Length(x)], i -> x[i]*y[i] );

     Append( bas, BasisVectors( Basis(r) ) );
     b:= Basis( Subspace( L, bas ), bas );     

     # Cartan matrix of s...
     Cs:= NullMat( Length(fundR), Length(fundR) );
     B:= BilinearFormMatNF(R);
     for i in [1..Length(fundR)] do
         for j in [1..Length(fundR)] do
             Cs[i][j]:= 2*( fundR[i]*(B*fundR[j]) )/( fundR[j]*(B*fundR[j]) );
         od;
     od;

     return sl2s;

     return rec( hs:= good_h, sl2:= sl2s, chars:= List( good_h, x ->
                   Cs*( Coefficients( b, x*hL ){[1..Length(x)]} ) ) );

end;

SLAfcts.loop_W:= function( C, h_lst, func )


     # C: Cartan matrix
     # h_lst: list of initial elements of H (given as coefficient vectors,
     # rel to basis of Chevalley type).
     # func: function H --> true, false, 
     # if func(orb elt) = true, then orb elt is included...

     local rank, sim, path, h_orb, h, r, i, j, idone, nu, ispos, wrd, hs0;

     rank:= Length( C );
     sim:= ShallowCopy(C);

     path:= [ rec( wt:= List( [1..rank], x -> 1 ), 
                            word:= [ ],
                            hs:= h_lst,
                            ind:= 0 ) ];
     h_orb:= [ ];
     for h in h_lst do
         if func(h) then Add( h_orb, h ); fi;
     od;

     while Length(path) > 0 do

          r:= path[ Length(path) ];
          i:= r.ind+1;
          idone:= false;
          while i <= rank and not idone do
                if r.wt[i] <= 0 then
                   i:= i+1;
                else

                   nu:= r.wt - r.wt[i]*sim[i];  # i.e. s_i(r.wt)
                   ispos:= true;
                   for j in [i+1..rank] do
                       if nu[j] < 0 then
                          ispos:= false;
                          break;
                       fi;
                   od;
                   if ispos then
                      path[Length(path)]:= rec( wt:= r.wt, 
                                                word:= r.word, 
                                                hs:= r.hs,
                                                ind:= i );
                      wrd:= [ i ]; Append( wrd, r.word );
                      hs0:= ShallowCopy(r.hs);
                      for j in [1..Length(hs0)] do
                          h:= ShallowCopy(hs0[j]);
                          h[i]:= h[i] - C[i]*h;  # i.e., s_i(h)
                          hs0[j]:= h;
                      od;

                      Add( path, rec( wt:= nu,
                                      word:= wrd,
                                      hs:= hs0,
                                      ind:= 0 ) );
                      for h in hs0 do 
                          if func( h ) then
                             if not h in h_orb then
                                Add( h_orb, h );
                             fi;
                          fi;
                      od;
                      idone:= true;
                   else
                      i:= i+1;
                   fi;
                fi;
          od;
          if not idone then  # get rid of last elt as it is searched through
             Unbind( path[Length(path)] );
          fi;

     od;      

     return h_orb;

end;


SLAfcts.nil_orbs_outer:= function( L, gr0, gr1, gr2 )

     # Here L is a simple graded Lie algebra; gr0 a basis of the
     # elts of degree 0, gr1 of degree 1, and gr2 of degree -1.
     # We find the nilpotent G_0-orbits in g_1.
     # We *do not* assume that the given CSA of L is also a CSA of g_0.

     local F, g0, s, r, HL, Hs, R, Ci, hL, hl, C, rank, posRv_L, posR_L,
           posR, i, j, sums, fundR, inds, tr, h_candidates, BH, W, h, 
           c_h, ph, stb, v, w, is_rep, h0, wr, Omega, good_h, g1, g2, h_mats1,
           h_mats2, mat, sl2s, id1, id2, V, e, f, bb, ef, found, good, co, x, 
           C_h0, sp, sp0, y, b, bas, c, Cs, B, Rs, nas, b0, ranks, in_weylch,
           charact, k, sol, info;

     F:= LeftActingDomain(L);

     g0:= Subalgebra( L, gr0, "basis" );

     s:= LieDerivedSubalgebra( g0 );
     r:= LieCentre(g0);

     HL:= CartanSubalgebra(L);
     Hs:= Intersection( s, HL );
     SetCartanSubalgebra( s, Hs );

     R:= RootSystem(L);
     Ci:= CartanMatrix( R )^-1;
     hL:= CanonicalGenerators(R)[3];

     hl:= List( NilpotentOrbits(L), x -> Ci*WeightedDynkinDiagram(x) );
     for i in [1..Length(hl)] do
         if hl[i] = 0*hl[i] then
            Unbind( hl[i] );
         fi;
     od;
     hl:= Filtered( hl, x -> IsBound(x) );

     C:= CartanMatrix( R );
     rank:= Length(C);

     if Dimension(s) > 0 then 
        Rs:= RootSystem(s);
        Cs:= CartanMatrix( Rs );
        ranks:= Length( Cs );

        bas:= ShallowCopy( CanonicalGenerators(Rs)[3] );
        Append( bas, BasisVectors( Basis(r) ) );
        b0:= Basis( VectorSpace( F, bas ), bas );
     else
        ranks:= 0;
        bas:= BasisVectors( Basis(r) );
	b0:= Basis( VectorSpace( F, bas ), bas );
     fi;

     in_weylch:= function( h )

          local cf, u;

          u:= h*hL;
          if not u in g0 then return false; fi;
          cf:= Coefficients( b0, u ){[1..ranks]};
	  if Length(cf)=0 then return true; fi;
          if ForAll( Cs*cf, x -> x >= 0 ) then
             return true;
          else
             return false;
          fi;

     end;

     charact:= function( h )

          local cf;

          cf:= Coefficients( b0, h ){[1..ranks]};
          return Cs*cf;

     end;

     h_candidates:= SLAfcts.loop_W( C, hl, in_weylch );
     
info:= "Constructed ";
Append( info, String(Length(h_candidates)) );
Append( info, " Cartan elements to be checked.");

Info(InfoSLA,2,info);

     # now we need to compute sl_2 triples wrt the h-s found...

     Omega:= [0..Dimension(L)];
     good_h:= [ ];

     g1:= Basis( Subspace( L, gr1 ), gr1 );
     g2:= Basis( Subspace( L, gr2 ), gr2 );

     # the matrices of hL[i] acting on g1
     h_mats1:= [ ];
     for h0 in bas do
         mat:= [ ];
         for i in [1..Length(g1)] do
             Add( mat, Coefficients( g1, h0*g1[i] ) );
         od;
         Add( h_mats1, mat );
     od;

     # those of wrt g2...
     h_mats2:= [ ];
     for h0 in bas do
         mat:= [ ];
         for i in [1..Length(g1)] do
             Add( mat, Coefficients( g2, h0*g2[i] ) );
         od;
         Add( h_mats2, mat );
     od;

     sl2s:= [ ];
     id1:= IdentityMat( Length(g1) );
     id2:= IdentityMat( Length(g2) );
     for h in h_candidates do

         c_h:= Coefficients( b0, h*hL );

         mat:= c_h*h_mats1;
         mat:= mat - 2*id1;
         V:= NullspaceMat( mat );
         e:= List( V, v -> v*gr1 );

         mat:= c_h*h_mats2;
         mat:= mat + 2*id2;
         V:= NullspaceMat( mat );
         f:= List( V, v -> v*gr2 );

         # check whether h0 in [e,f]....
         bb:= [ ];
         for x in e do
             for y in f do
                 Add( bb, x*y );
             od;
         od;
         ef:= Subspace( L, bb );

         h0:= h*hL;

         if h0 in ef then  #otherwise we can just discard h...
            found:= false;
            good:= false;
            while not found do

                co:= List( e, x -> Random(Omega) );
                x:= co*e;
                sp:= Subspace( L, List( f, y -> x*y) );

                if Dimension(sp) = Length(e) and h0 in sp then

                   # look for a nice one...
                   for i in [1..Length(co)] do
                       k:= 0;
                       found:= false;
                       while not found do
                           co[i]:= k;
                           x:= co*e;
                           sp:= Subspace( L, List( f, y -> x*y) );

                           if Dimension(sp) = Length(e) and h0 in sp then
                              found:= true;
                           else
                              k:= k+1;
                           fi;
                       od;
                   od;

                   mat:= List( f, u -> Coefficients( Basis(sp), x*u ) );
                   sol:= SolutionMat( mat, Coefficients( Basis(sp), h0 ) );

                   Add( good_h, h0 );
                   Add( sl2s, [sol*f,h0,x] );

                   found:= true;

                else
                   C_h0:= LieCentralizer( g0, Subalgebra( g0, [h0] ) );
                   sp0:= Subspace( L, List( Basis(C_h0), y -> y*x ) );
                   if Dimension(sp0) = Length(e) then
                      found:= true;
                      good:= false;
                   fi;
                fi;
      
            od;

         fi;
     od;

     return sl2s;

     return rec( hs:= good_h, sl2:= sl2s, chars:= List( good_h, charact ) );

end;

SLAfcts.roots_and_vecs:= function( f )

  # we return the roots and corresponding vectors of g_0, and g_1;
  # the output is a list with two records the first describing 
  # g0, the second describing g1. In the case of g0 the roots are 
  # split in positive/negative.

  local L, R, posR, posRv, negRv, m, vv, g0, g1, pr0, pv0, nr0, nv0, 
        r1, rv1, i, w, m0, gm, rm, rvm, ord2;

  if Order(f) = 2 then ord2:= true; else ord2:= false; fi;

  L:= Source(f);
  w:= E( Order(f) );
  R:= RootSystem(L);
  posR:= PositiveRootsNF(R);
  posRv:= PositiveRootVectors( R );
  negRv:= NegativeRootVectors( R );

  m:= List( Basis(L), x -> ShallowCopy( Coefficients( Basis(L), Image(f,x))));
  m0:= m - IdentityMat( Dimension(L) );

  vv:= NullspaceMat( m0 );
  vv:= List( vv, x -> LinearCombination( Basis(L), x ) );
  g0:= Subspace( L, vv, "basis" );

  m0:= m - w*IdentityMat( Dimension(L) );
  vv:= NullspaceMat( m0 );
  vv:= List( vv, x -> LinearCombination( Basis(L), x ) );
  g1:= Subspace( L, vv, "basis" );

  m0:= m - w^(Order(f)-1)*IdentityMat( Dimension(L) );
  vv:= NullspaceMat( m0 );
  vv:= List( vv, x -> LinearCombination( Basis(L), x ) );
  gm:= Subspace( L, vv, "basis" );


  pr0:= [ ]; pv0:= [ ];
  nr0:= [ ]; nv0:= [ ];

  r1:= [ ]; rv1:= [ ];

  rm:= [ ]; rvm:= [ ];

  for i in [1..Length(posR)] do
      if posRv[i] in g0 then
         Add( pr0, posR[i] );
         Add( pv0, posRv[i] );
         Add( nr0, -posR[i] );
         Add( nv0, negRv[i] );
         if not negRv[i] in g0 then Print("OOOOOOOPS!!!!\n"); fi;
      elif posRv[i] in g1 then
         Add( r1, posR[i] );
         Add( rv1, posRv[i] );
      elif posRv[i] in gm then
         Add( rm, posR[i] );
         Add( rvm, posRv[i] );
      fi;
      if negRv[i] in g1 then
         Add( r1, -posR[i] );
         Add( rv1, negRv[i] );
      elif negRv[i] in gm then
         Add( rm, -posR[i] );
         Add( rvm, negRv[i] );
      fi;
  od;

  if ord2 then # g_{-1} = g_{1}....
      return [ rec( pr0:= pr0, pv0:= pv0, nr0:= nr0, nv0:= nv0 ),
           rec( r1:= r1, rv1:= rv1 ), rec( rm:= r1, rvm:= rv1 ) ];
  else
      return [ rec( pr0:= pr0, pv0:= pv0, nr0:= nr0, nv0:= nv0 ),
           rec( r1:= r1, rv1:= rv1 ), rec( rm:= rm, rvm:= rvm ) ];
  fi;


end;

SLAfcts.root_basis:= function( B, posr )

  local inds, i, j, pos, bas, C, tp, subs, sub, s, rrr, R, pi, posRw,
        rts, concs, news, r;

  inds:=[ ];
  for i in [1..Length(posr)] do
      for j in [i+1..Length(posr)] do
          pos:= Position( posr, posr[i]+posr[j] );
          if pos <> fail then AddSet( inds, pos ); fi;
      od;
  od;

  bas:=[ ];
  for i in [1..Length(posr)] do
      if not i in inds then
         Add( bas, posr[i] );
      fi;
  od;

  C:=List( bas, x -> [ ] );
  for i in [1..Length(bas)] do
      for j in [1..Length(bas)] do
          C[i][j]:= 2*bas[i]*( B*bas[j] )/( bas[j]*(B*bas[j]) );
      od;
  od;
  
  tp:= CartanType( C );

  subs:=[ ];
  for i in [1..Length(tp.types)] do
    
      rrr:= bas{tp.enumeration[i]};
      R:= RootSystem( tp.types[i] );
      pi:= SLAfcts.pi_systems( R );
      sub:= [ ];
      posRw:= PositiveRootsAsWeights( R );
      for j in [1..Length( pi.types )] do
          rts:= pi.roots[j];
          s:= [ ];
          for r in rts do
              pos:= Position( posRw, r );
              if pos <> fail then
                 Add( s, PositiveRootsNF(R)[pos]*rrr );
              else
                 pos:= Position( posRw, -r );
                 Add( s, -PositiveRootsNF(R)[pos]*rrr );
              fi;
          od;
          Add( sub, s );
      od;
      Add( subs, sub );
  od;

  concs:= [ [ ] ];
  for i in [1..Length(subs)] do
      news:= [ ];
      for s in concs do
          for j in [1..Length(subs[i])] do 
              sub:= ShallowCopy( s );
              Append( sub, subs[i][j] );
              Add( news, sub );
          od;
      od;
      concs:= news;
  od;

  return concs;
          

end;



SLAfcts.zero_systems:= function( B, posr )

  local inds, i, j, pos, bas, C, tp, subs, sub, s, rrr, R, pi, posRw,
        rts, concs, news, r;

  if Length(posr) = 0 then
     return rec( bas:= [ ], subs:= [ [] ] );
  fi;

  inds:=[ ];
  for i in [1..Length(posr)] do
      for j in [i+1..Length(posr)] do
          pos:= Position( posr, posr[i]+posr[j] );
          if pos <> fail then AddSet( inds, pos ); fi;
      od;
  od;

  bas:=[ ];
  for i in [1..Length(posr)] do
      if not i in inds then
         Add( bas, posr[i] );
      fi;
  od;

  C:=List( bas, x -> [ ] );
  for i in [1..Length(bas)] do
      for j in [1..Length(bas)] do
          C[i][j]:= 2*bas[i]*( B*bas[j] )/( bas[j]*(B*bas[j]) );
      od;
  od;
  
  tp:= CartanType( C );

  subs:=[ ];
  for i in [1..Length(tp.types)] do
    
      rrr:= bas{tp.enumeration[i]};
      R:= RootSystem( tp.types[i] );
      pi:= SLAfcts.sub_systems( R );
      sub:= [ [ ] ];
      posRw:= PositiveRootsAsWeights( R );
      for j in [1..Length( pi.types )] do
          rts:= pi.roots[j];
          s:= [ ];
          for r in rts do
              pos:= Position( posRw, r );
              if pos <> fail then
                 Add( s, PositiveRootsNF(R)[pos]*rrr );
              else
                 pos:= Position( posRw, -r );
                 Add( s, -PositiveRootsNF(R)[pos]*rrr );
              fi;
          od;
          Add( sub, s );
      od;
      Add( subs, sub );
  od;

  concs:= [ [ ] ];
  for i in [1..Length(subs)] do
      news:= [ ];
      for s in concs do
          for j in [1..Length(subs[i])] do 
              sub:= ShallowCopy( s );
              Append( sub, subs[i][j] );
              Add( news, sub );
          od;
      od;
      concs:= news;
  od;

  return rec( bas:= bas, subs:= concs );
          

end;



SLAfcts.my_are_conjugate_0:= function( W, R, B, mus, lams )


   # R is the big root system, B the bilin form mat wrt weights,
   # mus and lams are lists of weights, we determine whether
   # there exists w in W wich w(mus[i]) = lams[i], all i.

   local sim, i, j, k, a, b, w, mu, rmu;

   sim:= SimpleRootsAsWeights( R );

   for i in [1..Length(mus)] do

       rmu:= List( W.roots, x -> 2*mus[i]*( B*x )/( x*(B*x) ) );
       a:= SLAfcts.conj_dom_wt( mus[i], rmu, W );

       rmu:= List( W.roots, x -> 2*lams[i]*( B*x )/( x*(B*x) ) );
       b:= SLAfcts.conj_dom_wt( lams[i], rmu, W );

       if a[1] <> b[1] then return false; fi;

       w:= Reversed( b[3] );
       Append( w, a[3] );
       w:= Reversed(w);

       for k in [i..Length(mus)] do

           mu:= ShallowCopy(mus[k]);
           rmu:= List( W.roots, x -> 2*mu*( B*x )/( x*(B*x) ) );

           for j in w do

               mu:= mu -rmu[j]*W.roots[j];
               rmu:= rmu - rmu[j]*W.wgts[j];

           od;

           mus[k]:= mu;

       od;

       W:= SLAfcts.stabilizer( lams[i], B, W );

   od;

   return true;


end;


SLAfcts.my_are_conjugate:= function( W, R, B, mus, lams )


   # same as previous function, but now we also permute
   # the mus, lams. We do assume that they arrive in an
   # order that defines the same Cartan matrix...

   local C, perms, i, newperms, p, q, good, j, k, l, nus;

   # however,... first we try the identity permutation...

   if SLAfcts.my_are_conjugate_0( W, R, B, mus, lams ) then
      return true;
   fi;
   
   # The Cartan matrix: 
   C:= List( mus, x -> List( mus, y -> 2*x*(B*y)/( y*(B*y) ) ) );

   # Now we determine all permutations of the mus that leave C invariant:

   perms:= List( [1..Length(mus)], x -> [x] );
   # i.e., the first element can be mapped to one of the other elts.
   # now we see whether this can be extended...

   for i in [2..Length(mus)] do

       newperms:= [ ];
       for p in perms do
           for j in [1..Length(mus)] do
               # see whether p can be extended by adding j...
               if not j in p then
                  q:= ShallowCopy(p);
                  Add( q, j );
                  good:= true;
                  for k in [1..i] do
                      if not good then break; fi;
                      for l in [1..i] do
                          if not good then break; fi;
                          if C[k][l] <> C[ q[k] ][ q[l] ] then
                             good:= false;
                          fi;
                      od;
                  od;
                  if good then Add( newperms, q ); fi;
               fi;
           od;
       od;
       perms:= newperms;
   od;

   perms:= Filtered( perms, x -> x <> [1..Length(mus)] ); # already tried it
   
   # now we see whether there is a permutation mapping 
   # a permuted mus to lams...

   for p in perms do

       nus:= [ ];
       for i in [1..Length(p)] do
           nus[p[i]]:= mus[i];
       od;

       if SLAfcts.my_are_conjugate_0( W, R, B, nus, lams ) then
          return true;
       fi;
   od;

   return false;

end;



SLAfcts.inner_orbits_carrier:= function( f )

   # we give a list of all flat Z-graded subalgebras of the
   # graded Lie algebra corresponding to f.


   local L, R, B, ch, posR, N, rts, rr, pi, r1, zero, stack, res, r, 
         start, rrr, ips, i, vv, u, h, C, CT, pi_0, pi_1, t, s, pos,
         ct, eqns, rhs, eqn, j, sol, h0, psi0, psi1, good, x, y, es, fs, 
         valmat, val, chars, u0, v, done, gr1, gr2, g1, g2, h_mats1, h_mats2, 
         mat, sl2s, id1, id2, Omega, V, e, ff, found, co, k, sp, extended,
         zz, bas, sim, Bw, W0, types, weights, wrts, tp, a, c, comb, hZ, hs,
         info;


   L:= Source(f);

   ch:= ChevalleyBasis(L);

   R:= RootSystem(L);

   posR:= PositiveRootsNF(R);
   N:= Length( posR );
   rts:= ShallowCopy(posR);
   Append( rts, -posR );

   B:= BilinearFormMatNF(R);

   rr:= SLAfcts.roots_and_vecs( f );

   zz:= SLAfcts.zero_systems( B, rr[1].pr0 );
   pi:= zz.subs;

   # now see how we can extend each element in pi with roots of
   # weight 1... and compute the maximal ones first!

   bas:= zz.bas;
   sim:= [ ];
   for a in bas do
       pos:= Position( posR, a );
       Add( sim, PositiveRootsAsWeights( R )[pos] );
   od;

   Bw:= SLAfcts.bilin_weights( R );
   W0:= rec( roots:= sim, wgts:= List( sim, x -> List( sim, y ->
                   2*x*(Bw*y)/( y*(Bw*y) ) ) ) );


   r1:= rr[2].r1;

   zero:= 0*r1[1];

   res:= [ ];
   for k in [1..Length(pi)] do

       types:= [ ];
       weights:= [ ];

       stack:= [ rec( rts0:= pi[k], rts1:= [ ], start:= 0,
                      sp:= VectorSpace( Rationals, pi[k], zero ) ) ];
       while Length(stack) > 0 do
           r:= stack[Length(stack)];
           RemoveElmList( stack, Length(stack) );
           start:= r.start+1;
           rrr:= Concatenation( r.rts0, r.rts1 );
           extended:= false;
           for i in [start..Length(r1)] do
               ips:= List( rrr, x -> x - r1[i] ); 
               if ForAll( ips, x -> not ( x in rts ) ) and
                           not r1[i] in r.sp then
                  vv:= ShallowCopy( BasisVectors( Basis(r.sp) ) );
                  Add( vv, r1[i] );
                  u:= ShallowCopy( r.rts1 );
                  Add( u, r1[i] );
                  Add( stack, rec( rts0:= r.rts0, rts1:= u, start:= i,
                          sp:= VectorSpace( Rationals, vv ) ) );
                  extended:= true;
               fi;
           od;
           if not extended then # see whether we can extend by
                                # adding something "smaller"
              for i in [1..start-1] do
                  if not r1[i] in rrr then
                     ips:= List( rrr, x -> x - r1[i] ); 
                     if ForAll( ips, x -> not ( x in rts ) ) and
                                    not r1[i] in r.sp then
                        extended:= true; break;
                     fi;
                  fi;
              od;
           fi;

           if not extended then 
              C:= List( rrr, x -> List( rrr, y -> 2*x*(B*y)/(y*(B*y)) ) );
              tp:= CartanType( C );
              SortParallel( tp.types, tp.enumeration );
              wrts:= [ ];
              for i in [1..Length(tp.enumeration)] do
                  for j in tp.enumeration[i] do
                      pos:= Position( rts, rrr[j] );
                      if pos <= N then
                         Add( wrts, PositiveRootsAsWeights(R)[pos] );
                      else
                         Add( wrts, -PositiveRootsAsWeights(R)[pos-N] );
                      fi;
                  od;
              od;
              found:= false;
              if tp.types in types then
                 for i in [1..Length(types)] do
                     if tp.types = types[i] then
                        if SLAfcts.my_are_conjugate( W0, R, Bw, wrts, weights[i] ) then
                           found:= true;
                           break;
                        fi;
                     fi;
                 od;
              fi;
              if not found then
                 Add( types, tp.types );
                 Add( weights, wrts );
                 Add( res, r );
              fi; 
           fi;
       od;

   od;

   stack:= [ ];
   for r in res do

       comb:= Combinations( [1..Length(r.rts1)] );
       comb:= Filtered( comb, x -> x <> [ ] );
       for c in comb do
           Add( stack, rec( rts0:= r.rts0, rts1:= r.rts1{c} ) );
       od;

   od;

   res:= stack;

info:= "Constructed ";
Append( info, String(Length(res)) );
Append( info, " root bases of possible flat subalgebras, now checking them...");
Info( InfoSLA, 2, info );

   h:= BasisVectors( Basis( CartanSubalgebra(L) ) );

   C:= CartanMatrix(R);
   CT:= TransposedMat( C );   

   # HERE we assume inner! 

   good:= [ ];
   for r in res do

       pi_0:= r.rts0;
       pi_1:= r.rts1;

       t:= [ ];
       pi:= Concatenation( pi_0, pi_1 );
       for s in pi do
           pos:= Position( rts, s );
           if pos <= N then
              Add( t, ch[1][pos]*ch[2][pos] );
           else
              Add( t, ch[2][pos-N]*ch[1][pos-N] );
           fi;
       od; 

       t:= BasisVectors( Basis( Subspace( L, t ) ) );

       ct:= List( t, x -> Coefficients( Basis(CartanSubalgebra(L)), x ) );

       # i.e. t is a Cartan subalgebra of s

       # find h0 in t such that a(h0)=1 for all a in pi_1, a(h0)=0
       # for all a in pi_0

       eqns:=[ ];
       rhs:= [ ];
       for j in [1..Length(pi_0)] do
           eqn:= [ ];
           for i in [1..Length(t)] do
               eqn[i]:= pi_0[j]*( C*ct[i] );
           od;
           Add( eqns, eqn ); Add( rhs, 0 );
       od;
       for j in [1..Length(pi_1)] do
           eqn:= [ ];
           for i in [1..Length(t)] do
               eqn[i]:= pi_1[j]*( C*ct[i] );
           od;
           Add( eqns, eqn ); Add( rhs, 1 );
       od;

       sol:= SolutionMat( TransposedMat(eqns), rhs );
       h0:= sol*t;

       # Find a basis of the subspace of h consisting of u with 
       # a(u) = 0, for a in pi = pi_0 \cup pi_1.

       eqns:= [ ];
       for i in [1..Length(h)] do
           eqns[i]:= [ ];
           for j in [1..Length(pi_0)] do
               Add( eqns[i], pi_0[j]*CT[i] );
           od;
           for j in [1..Length(pi_1)] do
               Add( eqns[i], pi_1[j]*CT[i] );
           od;
       od;
       sol:= NullspaceMat( eqns );
       hZ:= List( sol, u -> u*h );

       # Now we compute |Psi_0| and |Psi_1|...

       psi0:= [ ];
       for a in rr[1].pv0 do 
           if h0*a = 0*a and ForAll( hZ, u -> u*a = 0*a ) then
              Add( psi0, a );
           fi;
       od;

       psi1:= [ ];
       for a in rr[2].rv1 do
           if h0*a = a and ForAll( hZ, u -> u*a = 0*a ) then
              Add( psi1, a );
           fi;
       od;

       if Length(pi_0)+Length(pi_1) + 2*Length(psi0) = Length(psi1) then

          if not 2*h0 in good then
             Add( good, 2*h0 );
          fi;

       fi;
   od;

info:= "Obtained ";
Append( info, String( Length(good) ) );
Append( info, " Cartan elements, weeding out equivalent copies...");
Info(InfoSLA,2,info);

# NEXT can be obtained from Kac diagram!!

   x:= ChevalleyBasis(L)[1];
   y:= ChevalleyBasis(L)[2];
   es:= [ ];
   fs:= [ ];
   if Image( f, y[Length(y)] ) = y[Length(y)] then
      Add( fs, x[Length(x)] );
      Add( es, y[Length(y)] );
   fi;
   for i in [1..Length(CartanMatrix(R))] do
       if Image( f, x[i] ) = x[i] then
          Add( es, x[i] );
          Add( fs, y[i] );
       fi;
   od;
   hs:= List( [1..Length(es)], i -> es[i]*fs[i] );

   valmat:= [ ];
   for i in [1..Length(hs)] do
       val:= [ ];
       for j in [1..Length(hs)] do
           Add( val, Coefficients( Basis( Subspace(L,[es[j]]), [es[j]] ), 
                       hs[i]*es[j] )[1] );
       od;
       Add( valmat, val );
   od;


   chars:= [ ];
   for i in [1..Length(good)] do

       u0:= good[i];
       v:= List( es, z -> Coefficients( Basis(Subspace(L,[z]),[z]), u0*z )[1] );
       done:= ForAll( v, z -> z >= 0 );
       while not done do
           pos:= PositionProperty( v, z -> z < 0 );
           u0:= u0 - v[pos]*hs[pos];
           v:= v - v[pos]*valmat[pos];
           done:= ForAll( v, z -> z >= 0 );
       od;

       if not u0 in chars then
          Add( chars, u0 );
       fi;
   od;


   gr1:= rr[2].rv1;
   gr2:= rr[3].rvm;

     g1:= Basis( Subspace( L, gr1 ), gr1 );
     g2:= Basis( Subspace( L, gr2 ), gr2 );

     # the matrices of hL[i] acting on g1
     h_mats1:= [ ];
     for h0 in h do
         mat:= [ ];
         for i in [1..Length(g1)] do
             Add( mat, Coefficients( g1, h0*g1[i] ) );
         od;
         Add( h_mats1, mat );
     od;

     # those of wrt g2...
     h_mats2:= [ ];
     for h0 in h do
         mat:= [ ];
         for i in [1..Length(g1)] do
             Add( mat, Coefficients( g2, h0*g2[i] ) );
         od;
         Add( h_mats2, mat );
     od;

     sl2s:= [ ];
     id1:= IdentityMat( Length(g1) );
     id2:= IdentityMat( Length(g2) );
     Omega:= [1..Dimension(L)];
     for h0 in chars do

         ch:= Coefficients( Basis( CartanSubalgebra(L) ), h0 );
         mat:= ch*h_mats1;
         mat:= mat - 2*id1;
         V:= NullspaceMat( mat );
         e:= List( V, v -> v*gr1 );

         mat:= ch*h_mats2;
         mat:= mat + 2*id2;
         V:= NullspaceMat( mat );
         ff:= List( V, v -> v*gr2 );

         found:= false;
         while not found do

             co:= List( e, x -> Random(Omega) );
             x:= co*e;
             sp:= Subspace( L, List( ff, y -> x*y) );

             if Dimension(sp) = Length(e) and h0 in sp then

                # look for a nice one...
                for i in [1..Length(co)] do
                    k:= 0;
                    found:= false;
                    while not found do
                        co[i]:= k;
                        x:= co*e;
                        sp:= Subspace( L, List( ff, y -> x*y) );

                        if Dimension(sp) = Length(e) and h0 in sp then
                           found:= true;
                        else
                           k:= k+1;
                        fi;
                    od;
                od;

                mat:= List( ff, u -> Coefficients( Basis(sp), x*u ) );
                sol:= SolutionMat( mat, Coefficients( Basis(sp), h0 ) );

                Add( sl2s, [sol*ff,h0,x] );

                found:= true;

                       
             fi;
      
         od;
         
     od;
   
   return sl2s;

end;




InstallMethod( NilpotentOrbitsOfThetaRepresentation,
"for a finite order automorphism", true, [ IsGeneralMapping ], 0,
function( f )

   local g, L, rank, r, meth, kd, C, inds, i, w, tr;

   g:= Grading(f);

   if g[2] = [ ] then return [ ]; fi;

   meth:= ValueOption( "method" );

   L:= Source(f);
   rank:= Length( CartanMatrix( RootSystem(L) ) );
   if Length( KacDiagram( f ).weights ) = rank +1 then

      if meth = fail then
         kd:= KacDiagram( f );
         C:= kd.CM;
         inds:= [ ];
         for i in [1..Length(kd.weights)] do
             if kd.weights[i] = 0 then Add( inds, i ); fi;
         od;
	 if Length(inds) > 0 then
            w:= SizeOfWeylGroup( CartanType( C{inds}{inds} ).types );
	 else
	    w:= 1;
	 fi;
         tr:= SizeOfWeylGroup( RootSystem(L) )/w;
         if tr > 8000 then 
            meth:= "Carrier";
         else
            meth:= "WeylOrbit";
         fi;
      fi;

      if meth = "WeylOrbit" then
         Info(InfoSLA,2,"Selected Weyl orbit method."); 
         r:= SLAfcts.nil_orbs_inner( L, g[1], g[2], g[Length(g)] );
      else
         Info(InfoSLA,2,"Selected carrier algebra method."); 
         r:= SLAfcts.inner_orbits_carrier( f );
      fi;
   else
      r:= SLAfcts.nil_orbs_outer( L, g[1], g[2], g[Length(g)] );
   fi;

   return r;



end );

SLAfcts.CartanMatrixToPositiveRoots:= function( C )
        
        local   rank,  posr,  ready,  ind,  le,  i,  a,  j,  ej,  r,  b,  
                q, CT;
        
        rank:= Length( C );
        CT:= TransposedMat(C);

        # posr will be a list of the positive roots. We start with the
        # simple roots, which are simply unit vectors.
        
        posr:= IdentityMat( rank );
        
        ready:= false;
        ind:= 1;
        le:= rank;
        while ind <= le  do
            
            # We loop over those elements of posR that have been found in
            # the previous round, i.e., those at positions ranging from
            # ind to le.
            
            le:= Length( posr );
            for i in [ind..le] do
                a:= posr[i];
                
                # We determine whether a+ej is a root (where ej is the j-th
                # simple root.
                for j in [1..rank] do
                    ej:= posr[j];
                    
                    # We determine the maximum number r such that a-r*ej is
                    # a root.
                    r:= -1;
                    b:= ShallowCopy( a );
                    while b in posr do
                        b:= b-ej;
                        r:=r+1;
                    od; 
                    q:= r-LinearCombination( CT[j], a );
                    if q>0 and (not a+ej in posr ) then 
                        Add( posr, a+ej );
                    fi;
                od;
            od;
            ind:= le+1;
            le:= Length( posr );
        od; 
        
        return posr;
    end;



SLAfcts.sub_systems_Delta:= function( R )

   # simple root system..., we give reps of all orbits of
   # sub root systems that have a basis which is a subset of the basis of R,
   # under the Weyl group

   local pis, B, roots, types, tps, rts, mus, pos, found, i, j, k, comb,
         r0, c, C, r1, tp, e, u, t1, rank; 

   tp:= CartanType( CartanMatrix( R ) );
   pis:= rec( types:= [tp.types], roots:= [SimpleRootsAsWeights(R){tp.enumeration[1]}] );
   B:= SLAfcts.bilin_weights( R );

   roots:= [ ];
   types:= [ ];

   rank:= Length(B);
   comb:= Combinations( [1..rank] );
   comb:= Filtered( comb, x -> (x <> [] and Length(x) <> rank ) );


   for i in [1..Length(pis.types)] do
       tps:= pis.types[i];
       rts:= pis.roots[i];

       Add( roots, rts );
       Add( types, tps );


       for c in comb do

           r0:= rts{c};
           # find its type in normal enumeration...

           C:= List( r0, x -> List( r0, y -> 2*x*(B*y)/(y*(B*y)) ) );
           tp:= CartanType( C );

           e:= tp.enumeration;
           r1:= [ ];
           for j in [1..Length(e)] do
               u:= [ ];
               for k in e[j] do
                   Add( u, r0[k] );
               od;
               Add( r1, u );
           od;

           t1:= tp.types;
           SortParallel( t1, r1 );

           mus:= Concatenation( r1 );

           pos:= Position( types, t1 );
           if pos = fail then
              Add( types, t1 );
              Add( roots, mus );
           else
          
              found:= false;
              for j in [pos..Length(types)] do
                  if types[j] = t1 then      
                 
                     if SLAfcts.are_conjugate( R, B, mus, roots[j] ) then
                        found:= true; break;
                     fi;
  
                  fi;
              od;
              if not found then 
                 Add( types, t1 );
                 Add( roots, mus );
              fi;

           fi; 
       od;
   od;

   return rec( types:= types, roots:= roots );


end;




SLAfcts.roots_and_vecs_Z:= function( L, g0,g1,gm )

  # we return the roots and corresponding vectors of g_0, and g_1;
  # the output is a list with two records the first describing 
  # g0, the second describing g1. In the case of g0 the roots are 
  # split in positive/negative.

  local R, posR, posRv, negRv, m, vv, pr0, pv0, nr0, nv0, 
        r1, rv1, i, rm, rvm;

  R:= RootSystem(L);
  posR:= PositiveRootsNF(R);
  posRv:= PositiveRootVectors( R );
  negRv:= NegativeRootVectors( R );

  pr0:= [ ]; pv0:= [ ];
  nr0:= [ ]; nv0:= [ ];

  r1:= [ ]; rv1:= [ ];

  rm:= [ ]; rvm:= [ ];

  for i in [1..Length(posR)] do
      if posRv[i] in g0 then
         Add( pr0, posR[i] );
         Add( pv0, posRv[i] );
         Add( nr0, -posR[i] );
         Add( nv0, negRv[i] );
         if not negRv[i] in g0 then Print("OOOOOOOPS!!!!\n"); fi;
      elif posRv[i] in g1 then
         Add( r1, posR[i] );
         Add( rv1, posRv[i] );
      elif posRv[i] in gm then
         Add( rm, posR[i] );
         Add( rvm, posRv[i] );
      fi;
      if negRv[i] in g1 then
         Add( r1, -posR[i] );
         Add( rv1, negRv[i] );
      elif negRv[i] in gm then
         Add( rm, -posR[i] );
         Add( rvm, negRv[i] );
      fi;
  od;

  return [ rec( pr0:= pr0, pv0:= pv0, nr0:= nr0, nv0:= nv0 ),
           rec( r1:= r1, rv1:= rv1 ), rec( rm:= rm, rvm:= rvm ) ];


end;


SLAfcts.zero_systems_Z:= function( B, posr )

  local inds, i, j, pos, bas, C, tp, subs, sub, s, rrr, R, pi, posRw,
        rts, concs, news, r;

  if Length( posr ) = 0 then
     return rec( bas:= [ ], subs:= [ [] ] );
  fi;
  
  inds:=[ ];
  for i in [1..Length(posr)] do
      for j in [i+1..Length(posr)] do
          pos:= Position( posr, posr[i]+posr[j] );
          if pos <> fail then AddSet( inds, pos ); fi;
      od;
  od;

  bas:=[ ];
  for i in [1..Length(posr)] do
      if not i in inds then
         Add( bas, posr[i] );
      fi;
  od;

  C:=List( bas, x -> [ ] );
  for i in [1..Length(bas)] do
      for j in [1..Length(bas)] do
          C[i][j]:= 2*bas[i]*( B*bas[j] )/( bas[j]*(B*bas[j]) );
      od;
  od;
  
  tp:= CartanType( C );

  subs:=[ ];
  for i in [1..Length(tp.types)] do
    
      rrr:= bas{tp.enumeration[i]};
      R:= RootSystem( tp.types[i] );
      pi:= SLAfcts.sub_systems_Delta( R );
      sub:= [ [ ] ];
      posRw:= PositiveRootsAsWeights( R );
      for j in [1..Length( pi.types )] do
          rts:= pi.roots[j];
          s:= [ ];
          for r in rts do
              pos:= Position( posRw, r );
              if pos <> fail then
                 Add( s, PositiveRootsNF(R)[pos]*rrr );
              else
                 pos:= Position( posRw, -r );
                 Add( s, -PositiveRootsNF(R)[pos]*rrr );
              fi;
          od;
          Add( sub, s );
      od;
      Add( subs, sub );
  od;

  concs:= [ [ ] ];
  for i in [1..Length(subs)] do
      news:= [ ];
      for s in concs do
          for j in [1..Length(subs[i])] do 
              sub:= ShallowCopy( s );
              Append( sub, subs[i][j] );
              Add( news, sub );
          od;
      od;
      concs:= news;
  od;

  return rec( bas:= bas, subs:= concs );
          

end;


# NOTE: basis of simple roots in g0 directly from grading-diagram!


SLAfcts.zgrad_orbits_carrier:= function( L, grading )

   # L: Lie algebra, gr: grading (0,1,-1 components).
   # 


   local R, B, ch, posR, N, rts, rr, pi, r1, zero, stack, res, r, 
         start, rrr, ips, i, vv, u, h, C, CT, pi_0, pi_1, t, s, pos,
         ct, eqns, rhs, eqn, j, sol, h0, psi0, psi1, good, x, y, es, fs, 
         valmat, val, chars, u0, v, done, gr1, gr2, g2, h_mats1, h_mats2, 
         mat, sl2s, id1, id2, Omega, V, e, ff, found, co, k, sp, extended,
         zz, bas, sim, Bw, W0, types, weights, wrts, tp, a, c, comb, hZ, hs,
         info, posRv, negRv, g0, g1, gm, CM, rr0, l0, l1, gr, deg;


   ch:= ChevalleyBasis(L);

   R:= RootSystem(L);

   posR:= PositiveRootsNF(R);
   posRv:= PositiveRootVectors(R);
   negRv:= NegativeRootVectors(R);
   N:= Length( posR );
   rts:= ShallowCopy(posR);
   Append( rts, -posR );

   B:= BilinearFormMatNF(R);

   rr:= [ rec( pr0:= [ ], pv0:= [ ], nv0:= [] ), rec( r1:= [ ], rv1:= [ ] ), rec( rvm:= [ ] ) ];  
   for i in [1..Length(posR)] do
         v:= posR[i]*grading;
         if v = 0 then
            Add( rr[1].pr0, posR[i] );
            Add( rr[1].pv0, posRv[i] );
            Add( rr[1].nv0, negRv[i] );
         elif v = 1 then
            Add( rr[2].r1, posR[i] );
            Add( rr[2].rv1, posRv[i] );
            Add( rr[3].rvm, negRv[i] );
         fi;
   od;

   zz:= SLAfcts.zero_systems_Z( B, rr[1].pr0 );
   pi:= zz.subs;

   # now see how we can extend each element in pi with roots of
   # weight 1... and compute the maximal ones first!

   bas:= zz.bas;
   sim:= [ ];
   for a in bas do
       pos:= Position( posR, a );
       Add( sim, PositiveRootsAsWeights( R )[pos] );
   od;

   Bw:= SLAfcts.bilin_weights( R );
   W0:= rec( roots:= sim, wgts:= List( sim, x -> List( sim, y ->
                   2*x*(Bw*y)/( y*(Bw*y) ) ) ) );


   r1:= rr[2].r1;

   zero:= 0*r1[1];

   res:= [ ];
   for k in [1..Length(pi)] do

       types:= [ ];
       weights:= [ ];

       stack:= [ rec( rts0:= pi[k], rts1:= [ ], start:= 0,
                      sp:= VectorSpace( Rationals, pi[k], zero ) ) ];
       while Length(stack) > 0 do
           r:= stack[Length(stack)];
           RemoveElmList( stack, Length(stack) );
           start:= r.start+1;
           rrr:= Concatenation( r.rts0, r.rts1 );
           extended:= false;
           for i in [start..Length(r1)] do
               ips:= List( rrr, x -> x - r1[i] ); 
               if ForAll( ips, x -> not ( x in rts ) ) and
                           not r1[i] in r.sp then
                  vv:= ShallowCopy( BasisVectors( Basis(r.sp) ) );
                  Add( vv, r1[i] );
                  u:= ShallowCopy( r.rts1 );
                  Add( u, r1[i] );
                  Add( stack, rec( rts0:= r.rts0, rts1:= u, start:= i,
                          sp:= VectorSpace( Rationals, vv ) ) );
                  extended:= true;
               fi;
           od;
           if not extended then # see whether we can extend by
                                # adding something "smaller"
              for i in [1..start-1] do
                  if not r1[i] in rrr then
                     ips:= List( rrr, x -> x - r1[i] ); 
                     if ForAll( ips, x -> not ( x in rts ) ) and
                                    not r1[i] in r.sp then
                        extended:= true; break;
                     fi;
                  fi;
              od;
           fi;

           if not extended then 
              C:= List( rrr, x -> List( rrr, y -> 2*x*(B*y)/(y*(B*y)) ) );
              tp:= CartanType( C );
              SortParallel( tp.types, tp.enumeration );
              wrts:= [ ];
              for i in [1..Length(tp.enumeration)] do
                  for j in tp.enumeration[i] do
                      pos:= Position( rts, rrr[j] );
                      if pos <= N then
                         Add( wrts, PositiveRootsAsWeights(R)[pos] );
                      else
                         Add( wrts, -PositiveRootsAsWeights(R)[pos-N] );
                      fi;
                  od;
              od;
              found:= false;
              if tp.types in types then
                 for i in [1..Length(types)] do
                     if tp.types = types[i] then
                        if SLAfcts.my_are_conjugate( W0, R, Bw, wrts, weights[i] ) then
                           found:= true;
                           break;
                        fi;
                     fi;
                 od;
              fi;
              if not found then
                 Add( types, tp.types );
                 Add( weights, wrts );
                 Add( res, r );
              fi; 
           fi;
       od;

   od;

   stack:= [ ];
   for r in res do

       comb:= Combinations( [1..Length(r.rts1)] );
       comb:= Filtered( comb, x -> x <> [ ] );
       for c in comb do
           Add( stack, rec( rts0:= r.rts0, rts1:= r.rts1{c} ) );
       od;

   od;

   res:= stack;

info:= "Constructed ";
Append( info, String(Length(res)) );
Append( info, " root bases of possible flat subalgebras, now checking them...");
Info( InfoSLA, 2, info );

   h:= BasisVectors( Basis( CartanSubalgebra(L) ) );

   C:= CartanMatrix(R);
   CT:= TransposedMat( C );   

   good:= [ ];
   for r in res do

       pi_0:= r.rts0;
       pi_1:= r.rts1;
       pi:= Concatenation( pi_0, pi_1 );

       CM:= List( pi, x -> List( pi, y -> 2*x*(B*y)/( y*(B*y) ) ) );
       rr0:= SLAfcts.CartanMatrixToPositiveRoots( CM );
       l0:= 0; l1:= 0;
       gr:= Concatenation( List( pi_0, x -> 0 ), List( pi_1, x -> 1 ) );
       for s in rr0 do 
           deg:= s*gr;
           if deg=0 then
              l0:= l0+1;
           elif deg=1 then
              l1:= l1+1;
           fi;
       od;

       if 2*l0+Length(pi) = l1 then

          t:= [ ];
          for s in pi do
              pos:= Position( rts, s );
              if pos <= N then
                 Add( t, ch[1][pos]*ch[2][pos] );
              else
                 Add( t, ch[2][pos-N]*ch[1][pos-N] );
              fi;
          od; 

          t:= BasisVectors( Basis( Subspace( L, t ) ) );

          ct:= List( t, x -> Coefficients( Basis(CartanSubalgebra(L)), x ) );

          # i.e. t is a Cartan subalgebra of s

          # find h0 in t such that a(h0)=1 for all a in pi_1, a(h0)=0
          # for all a in pi_0

          eqns:=[ ];
          rhs:= [ ];
          for j in [1..Length(pi_0)] do
              eqn:= [ ];
              for i in [1..Length(t)] do
                  eqn[i]:= pi_0[j]*( C*ct[i] );
              od;
              Add( eqns, eqn ); Add( rhs, 0 );
          od;
          for j in [1..Length(pi_1)] do
              eqn:= [ ];
              for i in [1..Length(t)] do
                  eqn[i]:= pi_1[j]*( C*ct[i] );
              od;
              Add( eqns, eqn ); Add( rhs, 1 );
          od;

          sol:= SolutionMat( TransposedMat(eqns), rhs );
          h0:= sol*t;

          # Find a basis of the subspace of h consisting of u with 
          # a(u) = 0, for a in pi = pi_0 \cup pi_1.

          eqns:= [ ];
          for i in [1..Length(h)] do
              eqns[i]:= [ ];
              for j in [1..Length(pi_0)] do
                  Add( eqns[i], pi_0[j]*CT[i] );
              od;
              for j in [1..Length(pi_1)] do
                  Add( eqns[i], pi_1[j]*CT[i] );
              od;
          od;
          sol:= NullspaceMat( eqns );
          hZ:= List( sol, u -> u*h );

          # Now we compute |Psi_0| and |Psi_1|...

          psi0:= [ ];
          for a in rr[1].pv0 do 
              if h0*a = 0*a and ForAll( hZ, u -> u*a = 0*a ) then
                 Add( psi0, a );
              fi;
          od;

          psi1:= [ ];
          for a in rr[2].rv1 do
              if h0*a = a and ForAll( hZ, u -> u*a = 0*a ) then
                 Add( psi1, a );
              fi;
          od;

          if Length(pi_0)+Length(pi_1) + 2*Length(psi0) = Length(psi1) then

             if not 2*h0 in good then
                Add( good, 2*h0 );
             fi;

          fi;
       fi;
   od;

info:= "Obtained ";
Append( info, String( Length(good) ) );
Append( info, " Cartan elements, weeding out equivalent copies...");
Info(InfoSLA,2,info);

# NEXT can be obtained from Kac diagram!!

   x:= ChevalleyBasis(L)[1];
   y:= ChevalleyBasis(L)[2];
   es:= [ ];
   fs:= [ ];
   g0:= Subspace( L, Concatenation( Basis(CartanSubalgebra(L)), rr[1].pv0, rr[1].nv0 ) );

   for i in [1..Length(CartanMatrix(R))] do
       if x[i] in g0 then
          Add( es, x[i] );
          Add( fs, y[i] );
       fi;
   od;
   hs:= List( [1..Length(es)], i -> es[i]*fs[i] );

   valmat:= [ ];
   for i in [1..Length(hs)] do
       val:= [ ];
       for j in [1..Length(hs)] do
           Add( val, Coefficients( Basis( Subspace(L,[es[j]]), [es[j]] ), 
                       hs[i]*es[j] )[1] );
       od;
       Add( valmat, val );
   od;


   chars:= [ ];
   for i in [1..Length(good)] do

       u0:= good[i];
       v:= List( es, z -> Coefficients( Basis(Subspace(L,[z]),[z]), u0*z )[1] );
       done:= ForAll( v, z -> z >= 0 );

       while not done do
           pos:= PositionProperty( v, z -> z < 0 );
           u0:= u0 - v[pos]*hs[pos];
           v:= v - v[pos]*valmat[pos];
           done:= ForAll( v, z -> z >= 0 );
       od;

       if not u0 in chars then
          Add( chars, u0 );
       fi;
   od;

   gr1:= rr[2].rv1;
   gr2:= rr[3].rvm;

     g1:= Basis( Subspace( L, gr1 ), gr1 );
     g2:= Basis( Subspace( L, gr2 ), gr2 );

     # the matrices of hL[i] acting on g1
     h_mats1:= [ ];
     for h0 in h do
         mat:= [ ];
         for i in [1..Length(g1)] do
             Add( mat, Coefficients( g1, h0*g1[i] ) );
         od;
         Add( h_mats1, mat );
     od;

     # those of wrt g2...
     h_mats2:= [ ];
     for h0 in h do
         mat:= [ ];
         for i in [1..Length(g1)] do
             Add( mat, Coefficients( g2, h0*g2[i] ) );
         od;
         Add( h_mats2, mat );
     od;

     sl2s:= [ ];
     id1:= IdentityMat( Length(g1) );
     id2:= IdentityMat( Length(g2) );
     #Omega:= [1..Dimension(L)];
     Omega:= [-1,0,1,1];
     for h0 in chars do

         ch:= Coefficients( Basis( CartanSubalgebra(L) ), h0 );
         mat:= ch*h_mats1;
         mat:= mat - 2*id1;
         V:= NullspaceMat( mat );
         e:= List( V, v -> v*gr1 );

         mat:= ch*h_mats2;
         mat:= mat + 2*id2;
         V:= NullspaceMat( mat );
         ff:= List( V, v -> v*gr2 );

         found:= false;
         while not found do

             co:= List( e, x -> Random(Omega) );
             x:= co*e;
             sp:= Subspace( L, List( ff, y -> x*y) );

             if Dimension(sp) = Length(e) and h0 in sp then

                # look for a nice one...
                for i in [1..Length(co)] do
                    k:= 0;
                    found:= false;
                    while not found do
                        co[i]:= k;
                        x:= co*e;
                        sp:= Subspace( L, List( ff, y -> x*y) );

                        if Dimension(sp) = Length(e) and h0 in sp then
                           found:= true;
                        else
                           k:= k+1;
                        fi;
                    od;
                od;

                mat:= List( ff, u -> Coefficients( Basis(sp), x*u ) );
                sol:= SolutionMat( mat, Coefficients( Basis(sp), h0 ) );

                Add( sl2s, [sol*ff,h0,x] );

                found:= true;

                       
             fi;
      
         od;
         
     od;
   
   return sl2s;

end;

###############################################################################################
# 
#  method based on Weyl group action...
#

SLAfcts.nil_orbits_weyl:= function( L, grading )    

     # grading is a list with the degree of each simple root..., required to be
     # non-negative.

     local R, posR, posRv, negRv, g0, g1, gm, R1, D0, rank, inds0, v, i, perm,
           wrep, rts, w, N, p, D, P0, P1, j, es, fs, hs, valmat, val, chars,
           done, pos, u0, sg1, sgm, h_mats1, h_mats2, mat, sl2s, id1, id2, Omega,
           ch, V, e, ff, found, co, x, sp, k, c0, c1, s0, s1, pi_0, pi_1, t, pi, 
           s, ct, eqns, rhs, C, CT, h, good, sol, h0, hZ, psi0, psi1, a, g00, eqn, info, 
           orth, B, U, pU, CM, rr0, l0, l1, gr, deg;

     R:= RootSystem(L);
     posR:= PositiveRootsNF(R);
     posRv:= PositiveRootVectors(R);
     negRv:= NegativeRootVectors(R);

     g0:= ShallowCopy( BasisVectors( Basis( CartanSubalgebra(L) ) ) );
     g1:= [ ]; gm:= [ ];
     g00:= [ ];

     R1:= [ ];
     D0:= [ ];

     rank:= Length( CartanMatrix(R) );
     inds0:=[ ];
 
     for i in [1..Length(posR)] do
         v:= posR[i]*grading;
         if v = 0 then
            Add( g0, posRv[i] );
            Add( g0, negRv[i] );
            Add( g00, posRv[i] );
            if i <= rank then Add( D0, posR[i] ); Add( inds0, i ); fi;
         elif v = 1 then
            Add( g1, posRv[i] );
            Add( gm, negRv[i] );
            Add( R1, posR[i] );
         fi;
     od;

     perm:= SLAfcts.perms(R);
     wrep:= WeylTransversal( R, inds0 );

info:= "Constructed a Weyl transversal of ";
Append( info, String(Length(wrep)) );
Append( info, " elements.");

Info(InfoSLA,2,info);


     N:= Length( posR );
     rts:= Concatenation( posR, -posR );

     ch:= ChevalleyBasis(L);
     h:= BasisVectors( Basis( CartanSubalgebra(L) ) );
     C:= CartanMatrix(R);
     CT:= TransposedMat( C );
     B:= BilinearFormMatNF( R );
     U:=[];
     
     good:= [ ];
     for w in wrep do

         p:= Product( perm{w} ); p:= p^-1;
         D:= rts{ List( [1..rank], i -> i^p ) };
         P0:= Intersection( D, D0 );
         P1:= Intersection( D, R1 );

         if Length(P1) > 0 then

            c0:= Combinations( [1..Length(P0)] );

            for s0 in c0 do

                    pi_0:= P0{s0};
                    pi_1:= P1;

                    orth:= true;
                    for s in P0 do 
                        if not s in pi_0 then
                           if ForAny( pi_0, x -> not IsZero( x*(B*s) ) ) or
                              ForAny( pi_1, x -> not IsZero( x*(B*s) ) ) then
                              orth:= false; 
                              break;
                           fi;
                        fi;
                    od;

                    if orth then 
                       Sort( pi_0 ); Sort( pi_1 );

                       pi:= Concatenation( pi_0, pi_1 );
                       CM:= List( pi, x -> List( pi, y -> 2*x*(B*y)/( y*(B*y) ) ) );
                       rr0:= SLAfcts.CartanMatrixToPositiveRoots( CM );
                       l0:= 0; l1:= 0;
                       gr:= Concatenation( List( pi_0, x -> 0 ), List( pi_1, x -> 1 ) );
                       for s in rr0 do 
                           deg:= s*gr;
                           if deg=0 then
                              l0:= l0+1;
                           elif deg=1 then
                              l1:= l1+1;
                           fi;
                       od;

                       if 2*l0+Length(pi) = l1 then

                          t:= [ ];
                          for s in pi do
                              pos:= Position( posR, s );
                              Add( t, ch[1][pos]*ch[2][pos] );
                          od;
                          t:= BasisVectors( Basis( Subspace( L, t ) ) );
                          ct:= List( t, x -> Coefficients( Basis(CartanSubalgebra(L)), x ) );

                          # i.e. t is a Cartan subalgebra of s
                          # find h0 in t such that a(h0)=1 for all a in pi_1, a(h0)=0
                          # for all a in pi_0

                          eqns:=[ ];
                          rhs:= [ ];
                          for j in [1..Length(pi_0)] do
                              eqn:= [ ];
                              for i in [1..Length(t)] do
                                  eqn[i]:= pi_0[j]*( C*ct[i] );
                              od;
                              Add( eqns, eqn ); Add( rhs, 0 );
                          od;
                          for j in [1..Length(pi_1)] do
                              eqn:= [ ];
                              for i in [1..Length(t)] do
                                  eqn[i]:= pi_1[j]*( C*ct[i] );
                              od;
                              Add( eqns, eqn ); Add( rhs, 1 );
                          od;

                          sol:= SolutionMat( TransposedMat(eqns), rhs );
                          h0:= sol*t;

                          if not 2*h0 in good then

                             # Find a basis of the subspace of h consisting of u with 
                             # a(u) = 0, for a in pi = pi_0 \cup pi_1.

                             eqns:= [ ];
                             for i in [1..Length(h)] do
                                 eqns[i]:= [ ];
                                 for j in [1..Length(pi_0)] do
                                     Add( eqns[i], pi_0[j]*CT[i] );
                                 od;
                                 for j in [1..Length(pi_1)] do
                                     Add( eqns[i], pi_1[j]*CT[i] );
                                 od;
                             od;
                             sol:= NullspaceMat( eqns );
                             hZ:= List( sol, u -> u*h );

                             # Now we compute |Psi_0| and |Psi_1|...

                             psi0:= [ ];
                             for a in g00 do 
                                 if h0*a = 0*a and ForAll( hZ, u -> u*a = 0*a ) then
                                    Add( psi0, a );
                                 fi;
                             od;

                             psi1:= [ ];
                             for a in g1 do
                                 if h0*a = a and ForAll( hZ, u -> u*a = 0*a ) then
                                    Add( psi1, a );
                                 fi;
                             od;

                             if Length(pi_0)+Length(pi_1) + 2*Length(psi0) = Length(psi1) then
                                Add( good, 2*h0 );
                             fi;
                          fi;
                       fi;
                    fi;
                #od;
            od;

         fi; 
     od;

info:= "Obtained ";
Append( info, String( Length(good) ) );
Append( info, " Cartan elements, weeding out equivalent copies...");
Info(InfoSLA,2,info);

   es:= ChevalleyBasis(L)[1]{inds0};
   fs:= ChevalleyBasis(L)[2]{inds0};
   hs:= List( [1..Length(es)], i -> es[i]*fs[i] );

   valmat:= [ ];
   for i in [1..Length(hs)] do
       val:= [ ];
       for j in [1..Length(hs)] do
           Add( val, Coefficients( Basis( Subspace(L,[es[j]]), [es[j]] ), 
                       hs[i]*es[j] )[1] );
       od;
       Add( valmat, val );
   od;


   chars:= [ ];
   for i in [1..Length(good)] do

       u0:= good[i];
       v:= List( es, z -> Coefficients( Basis(Subspace(L,[z]),[z]), u0*z )[1] );
       done:= ForAll( v, z -> z >= 0 );
       while not done do
           pos:= PositionProperty( v, z -> z < 0 );
           u0:= u0 - v[pos]*hs[pos];
           v:= v - v[pos]*valmat[pos];
           done:= ForAll( v, z -> z >= 0 );
       od;

       if not u0 in chars then
          Add( chars, u0 );
       fi;
   od;

     sg1:= Basis( Subspace( L, g1 ), g1 );
     sgm:= Basis( Subspace( L, gm ), gm );

     # the matrices of hL[i] acting on g1
     h_mats1:= [ ];
     for h0 in h do
         mat:= [ ];
         for i in [1..Length(g1)] do
             Add( mat, Coefficients( sg1, h0*g1[i] ) );
         od;
         Add( h_mats1, mat );
     od;

     # those of wrt gm...
     h_mats2:= [ ];
     for h0 in h do
         mat:= [ ];
         for i in [1..Length(gm)] do
             Add( mat, Coefficients( sgm, h0*gm[i] ) );
         od;
         Add( h_mats2, mat );
     od;

     sl2s:= [ ];
     id1:= IdentityMat( Length(g1) );
     id2:= IdentityMat( Length(gm) );
     #Omega:= [1..Dimension(L)];
     Omega:= [-1,0,1,1];
     for h0 in chars do

         ch:= Coefficients( Basis( CartanSubalgebra(L) ), h0 );
         mat:= ch*h_mats1;
         mat:= mat - 2*id1;
         V:= NullspaceMat( mat );
         e:= List( V, v -> v*g1 );

         mat:= ch*h_mats2;
         mat:= mat + 2*id2;
         V:= NullspaceMat( mat );
         ff:= List( V, v -> v*gm );

         found:= false;

         while not found do

             co:= List( e, x -> Random(Omega) );
             x:= co*e;
             sp:= Subspace( L, List( ff, y -> x*y) );

             if Dimension(sp) = Length(e) and h0 in sp then

                # look for a nice one...
                for i in [1..Length(co)] do
                    k:= 0;
                    found:= false;
                    while not found do
                        co[i]:= k;
                        x:= co*e;
                        sp:= Subspace( L, List( ff, y -> x*y) );

                        if Dimension(sp) = Length(e) and h0 in sp then
                           found:= true;
                        else
                           k:= k+1;
                        fi;
                    od;
                od;

                mat:= List( ff, u -> Coefficients( Basis(sp), x*u ) );
                sol:= SolutionMat( mat, Coefficients( Basis(sp), h0 ) );

                Add( sl2s, [sol*ff,h0,x] );

                found:= true;

                       
             fi;
      
         od;

     od;
   
   return sl2s;

          
end;


InstallOtherMethod( NilpotentOrbitsOfThetaRepresentation,
"for a Lie algebra and a grading diagram", true, [ IsLieAlgebra, IsList ], 0,
function( L, d )

   local meth, rank, C, inds, i, w, tr, r;

   meth:= ValueOption( "method" );

   rank:= Length( d );
   C:= CartanMatrix( RootSystem(L) );
   if meth = fail then
      inds:= [ ];
      for i in [1..Length(d)] do
          if d[i] = 0 then Add( inds, i ); fi;
      od;
      if Length(inds) > 0 then
         w:= SizeOfWeylGroup( CartanType( C{inds}{inds} ).types );
      else
         w:= 1;
      fi;	 
      tr:= SizeOfWeylGroup( RootSystem(L) )/w;
      if tr > 8000 then 
         meth:= "Carrier";
      else
         meth:= "WeylOrbit";
      fi;
   fi;

   if meth = "WeylOrbit" then
      Info(InfoSLA,2,"Selected Weyl orbit method."); 
      r:= SLAfcts.nil_orbits_weyl( L, d );
   else
      Info(InfoSLA,2,"Selected carrier algebra method."); 
      r:= SLAfcts.zgrad_orbits_carrier( L, d );
   fi;

   return r;

end );

#### functions for computing the Hasse diagram of the nil orbs of a theta group ##########

# First: functions for dealing with the type of Weyl orbits that we need.
#
SLAfcts.NextIterator_WeylOrbitH:= function( it )
    local   output,  mu,  rank,  bound,  foundsucc,
            pos,  i,  nu,  a, B, v, lam, sims, stack, simples, stabs;

    if it!.isDone then Error("the iterator is exhausted"); fi;

    output:= it!.currentWeight;

    B:= it!.B;
    v:= it!.v;
    lam:= it!.otherWt;
    stabs:= it!.stabinds;
    sims:= it!.simples;

    #calculate the successor of curweight

    mu:= ShallowCopy(it!.currentWeight);
    rank:= Length( mu );
    stack:= it!.stack;
    bound:= 1;
    foundsucc:= false;
    while not foundsucc do

        pos:= fail;
        for i in [bound..rank] do
            if mu[i]>0 then
               nu:= ShallowCopy(mu);
               nu:= nu -nu[i]*sims[i];
               if ForAll( nu{[i+1..rank]}, x -> x >= 0 ) then
                  if Concatenation( nu, it!.c0 )*(B*Concatenation( lam, it!.c1 )) >= v then
                     pos:= i; break;
                  fi;
               fi;
            fi;
        od;  

        if pos <> fail then
            Add( stack, [ mu, pos ] );
            if not pos in stabs and ForAll( stabs, x -> nu[x] >= 0 ) then
               foundsucc:= true;
            else
               mu:= nu;
               bound:= 1;
            fi;
        else

            if mu = it!.root then

                # we cannot find a sucessor of the root: we are done

                it!.isDone:= true;
                nu:= [];
                foundsucc:= true;
            else
                a:= stack[Length(stack)];
                mu:= a[1]; bound:= a[2]+1;
                RemoveElmList( stack, Length(stack) );
            fi;

        fi;

    od;

    it!.stack:= stack;
    it!.currentWeight:= nu;

    return output*it!.dualBas;

end;

SLAfcts.ClosureWeylOrbit:= function( L, K, H, basH, C, dualBas, B, h0, h1, c1, c0 )

    # K: semsim Lie algebra,
    # H: CSA of K,
    # basH: basis of H, consisting of alpha_i^\vee
    # C: the Cartan matrix wrt the alpha_i
    # h0: element of H, of which we compute the orbit; assumed to be dominant.
    # h1: the other element, used for the Killing value...

    local   mu,  nu, rank, Ci, i, j, c, v, bas, pos, sims, nu1;

    rank:= Length(C);

    bas:= Basis( H, dualBas );

    mu:= Coefficients( bas, h0 );
    nu:= Coefficients(bas,h1);

    nu1:= Concatenation( nu, c1 );
    v:= nu1*B*nu1;

    sims:= List( basH, x -> Coefficients( bas, x ) );

    return IteratorByFunctions( rec(
               IsDoneIterator := IsDoneIterator_WeylOrbit,
               NextIterator   := SLAfcts.NextIterator_WeylOrbitH,

               ShallowCopy:= function( iter ) 
                      return rec( root:= ShallowCopy( iter!.root ),
                        currentWeight:= ShallowCopy( iter!.currentWeight ),
                        stack:= ShallowCopy( iter!.stack ),
                        otherWt:= ShallowCopy( iter!.otherWt ),
                        stabinds:= ShallowCopy( iter!.stabinds ),
                        B:= ShallowCopy( iter!.B ),
                        v:= iter!.v,
                        c0:= iter!.c0,
                        c1:= iter!.c1,
                        dualBas:= iter!.dualBas,
                        simples:= ShallowCopy( iter!.simples ), 
                        isDone:= iter!.isDone );
                     end,
                        root:= mu,
                        currentWeight:= mu,
                        stack:= [ ],
                        otherWt:= nu,
                        stabinds:= Filtered( [1..Length(nu)], i -> nu[i]=0 ),
                        B:= B,
                        v:= v,
                        c0:= c0,
                        c1:= c1,
                        dualBas:= dualBas,
                        simples:= sims,
                        isDone:= false ) );
end;


##########################################################################################
# Next: the main procedure, starting with some subfunctions...
#
SLAfcts.cartanorb_prop:= function( L, K0, H0, basH, C, dualBas, B, h, oh, c1, c0, func )
 

    # h in H; its orbit under the Weyl group...

    local o, hh, count;

    o:= SLAfcts.ClosureWeylOrbit( L, K0, H0, basH, C, dualBas, B, h, oh, c1, c0 );

    while not IsDoneIterator(o) do
        hh:= NextIterator(o);
        if func(hh) then
           return true;
        fi;
    od;    

    return false;

end;


SLAfcts.normaliser:= function( L, K, U )

   # L: Lie algebra
   # K: subalgebra
   # U: basis of a subspace of L
   # return: subalgebra of K, of all x such that [x,U] subset U.

   local n, sp, m, s, eqns, k, d, r, j, i, sol, eqn;

   n:= Dimension(K);
   sp:= Subspace(L,U);
   U:= BasisVectors( Basis(sp) );
   m:= Dimension(sp);
   s:= Dimension(L);   

   eqns:= NullMat( n+m^2, s*m );
   for k in [1..m] do
       d:= Coefficients( Basis(L), U[k] );
       for r in [1..s] do
           if not IsZero(d[r]) then
              for j in [1..m] do
                 eqns[n+k+(j-1)*m][j+(r-1)*m]:= eqns[n+k+(j-1)*m][j+(r-1)*m]+d[r];
              od;
           fi;
       od;
   od;

   for i in [1..n] do
       for j in [1..m] do
           d:= Coefficients( Basis(L), Basis(K)[i]*U[j] );
           for r in [1..s] do
               if not IsZero(d[r]) then
                  eqns[i][j+(r-1)*m]:= eqns[i][j+(r-1)*m]+d[r];
               fi;
           od;
       od;
   od;

   sol:= NullspaceMatDestructive( eqns );
   return List( sol, x -> x{[1..n]}*Basis(K) );

end;


SLAfcts.inc:= function( sl2, domh, L, K, GM, G1, H0, basH, C, dualBas, B, i0, j0, file, matlist )

   # see whether orbit i0 is inclued in j0.

   local hi, hj, gh, W, ww, V2, U, wd, k, v0, f_chk, R, hh, BH, KH, Ci, Um, q,
         K0, h0, b0, sp0, h_start, c0, kk, KL, v, t, mats, oh, sp, kval, adh, Uinds, ord,
         maxU, i, j, mats0, c1, inconvexhull, kappamat, kapinv, invnu, dist0, ip0;


inconvexhull:= function( B, S0, p0, dist, ip, eps0 ) 
                                            # S set of vecs in R^m (rat coords),
                                            # p a point in R^m, is p\in S?
                                            # dist: distance fct

    local m, i, one, eps, dists, pos, v, pp, k, j, u, t, S, p;

    S:= List( S0, x -> Coefficients( B, x ) );
    p:= Coefficients( B, p0 );
    one:= 1.00000000000000000000000000;
    S:= List( S, u -> u*one );
    p:= p*one;

    eps:= one*eps0; 

    dists:= List( S, s -> dist(s,p) );
    pos:= Position( dists, Minimum( dists ) );
    v:= S[pos];
    pp:= S[pos];

    while true do
       if dist(p,pp) < eps*dist(p,v) then
          return [ pp, true ];
       else
          k:= 0;
          for j in [1..Length(S)] do
              if dist(pp,S[j]) >= dist(p,S[j]) then
                 k:= j; break;
              fi;
          od;
          if k > 0 then
             v:= S[k];
          else
             return [ pp, false ];
          fi;
       fi;

       u:= pp-v;
       t:= -ip(u,p-pp)/ip(u,u);
       pp:= pp+t*(-u);

    od;
end;

   kappamat:= List( Basis(H0), h1 -> List( Basis(H0), h2 ->
        TraceMat( AdjointMatrix( Basis(L), h1 )*AdjointMatrix(Basis(L),h2)) ));
   kapinv:= kappamat^-1;

   invnu:= function(x)  # x a root vec in g1, compute invnu of corr root.

        local sp, b, u;

        sp:= Basis( Subspace( L, [x] ), [x] );
        b:= List( Basis(H0), h1 -> Coefficients( sp, h1*x )[1] );
        return (kapinv*b)*Basis(H0);
   end;

    dist0:= function(u,v) return (u-v)*kappamat*(u-v); end;
    ip0:= function(u,v) return u*kappamat*v; end;



   ord:= function( i1, i2 )

      if Length(i1) <> Length(i2) then
         return Length(i1) < Length(i2);
      else
         return i1 < i2;
      fi;
   end;

   hi:= domh[i0];
   hj:= domh[j0];

   kval:=  TraceMat( AdjointMatrix( Basis(L), hi )*AdjointMatrix(Basis(L),hj));
   kval:= kval/TraceMat(AdjointMatrix(Basis(L),hi)*AdjointMatrix(Basis(L),hi));

   if kval < 1 then
      return false; 
   fi;

   ww:= [ ];
   for v in Basis(G1) do
       sp:= Basis( Subspace( L, [v] ), [v] );
       k:= Coefficients( sp, hi*v )[1];
       if k = 2 then Add( ww, v ); fi;
   od;
   V2:= ww;  

   K0:= LieDerivedSubalgebra(K);
   h0:= BasisVectors(Basis( LieCentre(K) ));

   b0:= Concatenation( basH, h0 );
   sp0:= Basis( Subspace(L,b0), b0 );

   R:= RootSystem(K0);

   hh:= CanonicalGenerators(R)[3];

   BH:= Basis( Subspace( L, hh ), hh );
   KH:= List( hh, x -> [] );
   adh:= List( hh, x -> AdjointMatrix( Basis(L), x ) );
   for i in [1..Length(hh)] do
       for j in [i..Length(hh)] do
           kval:= TraceMat( adh[i]*adh[j] );
           KH[i][j]:= kval; 
           if i <> j then KH[j][i]:= kval; fi;
       od;
   od;

   Um:= Filtered( Basis(GM), x -> hi*x = -2*x );
   q:= LieCentralizer( K, Subalgebra(K,[hi]) );

   mats:= [ ];
   mats0:= [ ];

   Uinds:= [ ];
   maxU:= [ ];

   f_chk:= function( h, c0, t )

      local gh, U, k, v0, u1, A, sol, P, M, sp, B, q0, inds, p,
            i, j, m, n, x, u, c, cf, R, a, s, v, d, r, V, t0, Uind, pos, cf0, found, Om,
            matrc, colinds, Bt, kval0, kval1, hhh, kv, h00, eps, bl;


      if Length(c0) > 0 then
         u1:= h+c0*h0;
      else
         u1:= h;
      fi;

      U:= [ ];  
      Uind:= [ ];
      for i in [1..Length(V2)] do
          v:= V2[i];
          sp:= Basis( Subspace( L, [v] ), [v] );
          k:= Coefficients( sp, u1*v )[1];
          if k >= 2 then Add( U, v ); Add( Uind, i ); fi;
      od;

      if Length(U) = 0 then return false; fi;

      pos:= PositionSorted( Uinds, Uind, ord );
      if IsBound(Uinds[pos]) and Uinds[pos] = Uind then
         return false;
      else
         Add( Uinds, Uind, pos );
      fi;

      for i in [1..Length(maxU)] do
          if IsSubset( maxU[i], Uind ) then
             return false;
          fi;
      od;
      #

      M:= SLAfcts.normaliser( L, K, U );
      Om:= [0..Dimension(L)];
      for k in [1..5] do

          cf0:= List( U, x -> Random( Om ) );
          v0:= cf0*U; 
          A:= List( Um, x -> Coefficients( Basis(K), v0*x ) );
          if Length(A) = 0 then
             sol:= fail;
          else
             sol:= SolutionMat( A, Coefficients( Basis(K), hi ) );
          fi;
          if sol <> fail then
             return true;
          else
             if Dimension( Subspace( L, v0*M ) ) = Length(U) then
                Add( maxU, Uind );
                return false;
             fi;
          fi;

      od;

      hhh:= List( U, x -> invnu(x) );
      kv:= TraceMat(AdjointMatrix(Basis(L),hi)*AdjointMatrix(Basis(L),hi));
      h00:= 2*hi/kv;
      eps:= 1/10;
      while eps > 1/10000000 do
         bl:= inconvexhull( Basis(H0), hhh, h00, dist0, ip0, eps )[2];
         if bl then
            eps:= eps/10;
         else  
            return false;
         fi;
      od;

      if Length(file) > 0 then

         V:= Subspace( L, V2 );

         m:= Length(U);
         if m = 0 then return false; fi;
         n:= Dimension(q);
         s:= Dimension(V);
         x:= BasisVectors( Basis(q) );
         v:= BasisVectors( Basis(V) );

         c:= List( [1..n], r -> [ [ ] ] );
         for i in [1..n] do
             for j in [1..s] do
                 c[i][j]:= Coefficients( Basis( V ), x[i]*v[j] );
             od;
         od;

         d:= List( U, r -> Coefficients( Basis(V), r ) );

         P:= PolynomialRing( Rationals, m );
         a:= IndeterminatesOfPolynomialRing( P );
         A:= List( [1..s], r -> [ ] );
         for r in [1..s] do
             for i in [1..n] do
                 cf:= Zero(P);
                 for k in [1..m] do
                     for j in [1..s] do
                         cf:= cf + a[k]*d[k][j]*c[i][j][r];
                     od;
                 od;
                 A[r][i]:= cf;
             od;
         od;

         if Dimension(q)-Length(A) > t then
            return false;
         fi;

         if ForAny(A, IsZero ) then 
            return false;
         fi;

         matrc:= rec( inds:= [i0,j0], numindets:= Length(a), fullmat:= A );

         q0:= BasisVectors( CanonicalBasis( Intersection( 
                                     q, KappaPerp( L, Subalgebra(L,[hi]) ) ) ) );
         B:= [ ];
         # first we find a max set of lin indep rows, for a random v0\in U
         cf0:= List( U, x -> Random( [1..Dimension(L)^2] ) );
         v0:= cf0*U;
         for i in [1..Length(q0)] do
             Add( B, Coefficients( Basis(V), q0[i]*v0 ) );
         od;
         inds:= [ 1 ];
         sp:= MutableBasis( LeftActingDomain(L), [ ], List( Basis(V), x -> 0 ) );
         for i in [1..Length(B)] do
             if not IsContainedInSpan( sp, B[i] ) then
                CloseMutableBasis( sp, B[i] );
                Add( inds, i+1 );
             fi;
         od;

         colinds:= [ ];
         Bt:= TransposedMat(B{[1..Length(B)]});
         sp:= MutableBasis( LeftActingDomain(L), [ ], List( [1..Length(q0)], x -> 0 ) );
         for i in [1..Length(Bt)] do
             if not IsContainedInSpan( sp, Bt[i] ) then
                CloseMutableBasis( sp, Bt[i] );
                Add( colinds, i );
             fi;
         od;

         # now make the "real" matrix...         
         x:= Concatenation( [hi], q0 );
         A:= List( inds, zz -> [ ] );
         c:= List( [1..n], r -> [ [ ] ] );
         for i in [1..n] do
             for j in [1..m] do
                 c[i][j]:= Coefficients( Basis( V ), x[i]*U[j] );
             od;
         od;
         
         for i in [1..Length(inds)] do
             for j in [1..s] do
                 p:= Zero(P);
                 for k in [1..m] do
                     p:= p + a[k]*c[inds[i]][k][j];
                     A[i][j]:= p;
                 od;
             od;
         od;

         matrc.redmat:= A;
         matrc.colinds:= colinds;

         Add( matlist, matrc );

      else
        Add( matlist, rec( inds:= [i0,j0] ) );
      fi;
        
      return false;

   end;

   t:= Dimension( Intersection( LieCentralizer( K, Subalgebra(K,[sl2[i0][2]]) ), 
                LieCentralizer(L,Subalgebra(L,[sl2[i0][3]])) ) );

   Ci:= CartanMatrix(R)^-1;

   h_start:= Coefficients( sp0, hj ){[1..Length(basH)]}*basH;
   c0:= Coefficients( sp0, hj ){[ Length(basH)+1..Length(b0) ]};
   c1:= Coefficients( sp0, hi ){[ Length(basH)+1..Length(b0) ]};

   oh:= Coefficients( sp0, hi ){[1..Length(basH)]}*basH;

   v:= SLAfcts.cartanorb_prop( L, K0, H0, basH, C, dualBas, B, h_start, oh, c1, c0, 
                        h -> f_chk(h,c0,t) );

   return v;

end;


SLAfcts.is_included_in:= function( diag, j )

    local list, done, list0, d, pos;

    list:= [ j ];
    done:= false;
    while not done do

        list0:= [ ];
        for d in diag do
            if d[1] in list then
               AddSet( list0, d[2] );
            fi;
        od;
        list0:= Set( Concatenation( list, list0 ) );
        if Length(list0) = Length(list) then 
           done:= true;
        fi;
        list:= list0;
    od;

    pos:= Position( list, j );
    RemoveElmList( list, pos );

    return list;
     
end;

SLAfcts.minimize_diag:= function( N, diag )

    # if [i,j] and [j,k] and [i,k] then get rid of [i,k]...

    local edges, s, i, j, k, path2, p1, p2;

    Sort(diag);

    edges:= [ ];
    for s in diag do

        i:= s[1]; j:= s[2];
        path2:= false;
        for k in [1..N] do 
            if k <> i and k <> j then
               p1:= PositionSorted( diag, [i,k] );
               p2:= PositionSorted( diag, [k,j] );
               if IsBound(diag[p1]) and IsBound(diag[p2]) and
                  diag[p1] = [i,k] and diag[p2] = [k,j] then
               #if [i,k] in diag and [k,j] in diag then        
                  path2:= true;
               fi;
            fi;
            if path2 then break; fi;
        od;

        if not path2 then 
           Add( edges, s );
        fi;
    od;

    return edges;

end;



SLAfcts.hasse_diag:= function( L, grad, sl2 )
   
   local K, GM, G1, dim, dim1, d1, d2, diag, i, j, k, incs, b, file, K0, R, posRv,
         posR, negRv, fundR, sums, inds, basH, H0, rank, C, B, posR_L, dualBas,
         Ci, c, g0, g1, gm, gsp, Cu, domh, sims, pos, bas, mu, h0, b0, c0, sp0,
         m, m0, r, numvar, matlist, info, set, magmaprog, dualBas0;

   g0:= grad[1]; gm:= grad[ Length(grad) ]; 
   if Length( grad ) > 1 then
      g1:= grad[2];
   else
      g1:= grad[1];
   fi;

   file:= ValueOption( "filenm" );
   if file = fail then file:= ""; fi;

   K:= Subalgebra( L, g0 );
   GM:= Subspace( L, gm );
   G1:= Subspace( L, g1 );

   K0:= LieDerivedSubalgebra(K);

   R:= RootSystem(K0);
   posR:= PositiveRootsNF(R);
   fundR:= SimpleSystemNF(R);
   inds:= List( fundR, x -> Position( posR, x ) );
   posRv:= PositiveRootVectors(R);
   negRv:= NegativeRootVectors(R);
   basH:= List( inds, i -> posRv[i]*negRv[i] );

   H0:= Subalgebra( K0, basH );  

   rank:= Length( basH );
   C:= CartanMatrix(R);

    dualBas:= [ ];
    Ci:= C^-1;
    for i in [1..rank] do
        c:= 0*[1..rank];
        c[i]:= 1;
        c:= Ci*c;
        Add( dualBas, c*basH );
    od;

    dualBas0:= Concatenation( dualBas, BasisVectors(Basis( LieCentre(K) ) ) );
    B:= List( [1..Length(dualBas0)], x -> [] );
    for i in [1..Length(dualBas0)] do
        for j in [i..Length(dualBas0)] do
            B[i][j]:= TraceMat( AdjointMatrix( Basis(L), dualBas0[i] )*
                                AdjointMatrix( Basis(L), dualBas0[j] ) );
            B[j][i]:= B[i][j];
        od;
    od;

   dim:= function( u ) return Dimension( Subspace( L, Basis(K)*u[3] ) ); end;

   d1:= List( sl2, dim );

   SortParallel( d1, sl2 );
   d1:= Reversed(d1);
   sl2:= Reversed(sl2);

   # now map all h-s to dominant Weyl chamber.
   h0:= BasisVectors(Basis( LieCentre(K) ));
   b0:= Concatenation( basH, h0 );
   sp0:= Basis( Subspace(L,b0), b0 );

   domh:= [ ];
   bas:= Basis( H0, dualBas );
   sims:= List( basH, x -> Coefficients( bas, x ) );
   for i in [1..Length(sl2)] do

       h0:= Coefficients( sp0, sl2[i][2] ){[1..Length(basH)]}*basH;
       c0:= Coefficients( sp0, sl2[i][2] ){[ Length(basH)+1..Length(b0) ]};

       mu:= Coefficients( bas, h0 );
       pos:= PositionProperty( mu, x -> x < 0 );
       while pos <> fail do
          mu:= mu -mu[pos]*sims[pos];
          pos:= PositionProperty( mu, x -> x < 0 );
       od;
       if Length(c0) = 0 then
          Add( domh, mu*bas );
       else
          Add( domh, mu*bas + c0*b0{[Length(basH)+1..Length(b0) ]} );
       fi;
   od;

   gsp:= List( grad, x -> Subspace( L, x ) );
   d2:= [ ];
   for i in [1..Length(sl2)] do
       Cu:= LieCentralizer( L, Subalgebra( L, [sl2[i][3]] ) );
       Add( d2, List( gsp, x -> Dimension( Intersection( x, Cu ) ) ) );
   od;

   diag:= [ ];

   # [ i, j ] in diag means orbit i is included in the closure of
   # orbit j.

   matlist:= [ ];

   for i in [2..Length(sl2)] do
       for j in [i-1,i-2..1] do

           if (not [i,j] in diag) and d1[i] < d1[j] and ForAll( [1..Length(grad)], k ->
              d2[i][k] >= d2[j][k] ) then 

              b:= SLAfcts.inc( sl2, domh, L, K, GM, G1, H0, basH, C, dualBas, B, i, j, file, matlist );
              if b then
                 Add( diag, [i,j] );
                 incs:= SLAfcts.is_included_in( diag, j );
                 for k in incs do Add( diag, [i,k] ); od;
              fi;
           fi;
       od;                 
   od;

   matlist:= Filtered( matlist, x -> not x.inds in diag );

   if Length(matlist) = 0 then
      Info( InfoSLA,2,"All (non-) inclusions proved!");
   else
      info:= "For the following pairs of orbits the first could be included in the\nclosure of the second\
 (but this is unlikely):\n";
      set:= Set( List( matlist, r -> r.inds ) );
      for i in  [1..Length(set)] do
          Append( info, String(set[i]) );
          if i < Length( set ) then
             Append( info, ", " );
          fi;
      od;
      Info( InfoSLA,2, info );
   fi;      

   if Length(file) > 0 and Length(matlist) > 0 then

magmaprog:= 
"minors:= function( m )\n\n\
   \/\/ m and rxs matrix with s >= r, compute all rxr minors,\n\
   \/\/ return false if a nonzero found; otherwise return true.\n\n\
   r:= NumberOfRows(m);\n\
   s:= NumberOfColumns(m);\n\
   if r eq s then return Determinant(m) eq 0; end if;\n\
   rows:= [1..r];\n\
   done:= false;\n\
   len:= s-r;\n\
   exc:= [1..len];\n\
   while not done do\n\
        cols:= [ ];\n\
        for i in [1..s] do\n\
            if not i in exc then Append( ~cols, i ); end if;\n\
        end for;\n\
        d:= Minor( m, rows, cols ); \n\
        if not IsZero(d) then return false; end if;\n\
        pos:= len;\n\
        found:= (exc[pos] lt s); \n\
        while not found do \n\
            pos:= pos-1; \n\
            if pos eq 0 then // done... \n\
               done:= true;\n\
               found:= true;\n\
            else\n\
               found:= (exc[pos] lt s-(len-pos));\n\
            end if;\n\
        end while;\n\
        if not done then \n\
           l:= exc[pos]+1;\n\
           for i in [pos..len] do \n\
               exc[i]:= l+i-pos; \n\
           end for; \n\
        end if; \n\
   end while; \n\
   return true;\n\
end function;\n\n\n\n\
minors0:= function( m, cols )\n\n\
   \/\/ m and rxs matrix with s > r \n\
   \/\/ and cols are indices of lin indep columns.\n\
   \/\/ check whether first row is in span of last r-1 rows...\n\n\
   r:= NumberOfRows(m);\n\
   s:= NumberOfColumns(m);\n\
   rows:= [1..r]; \n\
   for i in [1..s] do \n\
       if not i in cols then \n\
          columns:= cols; \n\
          Append( ~columns, i ); \n\
          Sort( ~columns ); \n\
          d:= Minor( m, rows, columns ); \n\
          if not IsZero(d) then return false; end if; \n\
       end if; \n\
   end for; \n\
   return true; \n\
end function; \n\n";

      AppendTo( file, magmaprog );

      numvar:= 0;
      for r in matlist do 
          if r.numindets > numvar then numvar:= r.numindets; fi;
      od;
      AppendTo( file, "F<" );
      for i in [1..numvar] do
          AppendTo( file, "x_" );
          AppendTo( file, i );
          if i < numvar then
             AppendTo(file,",");
          fi;
      od;
      AppendTo( file, ">:= RationalFunctionField( Rationals(), ");
      AppendTo( file, numvar );
      AppendTo( file, ");\n\n");

      for r in matlist do
          AppendTo( file, "print \"inclusion: orbit \", ",r.inds[1], ", \" in orbit \",",r.inds[2],";\n");
          m:= r.fullmat; m0:= r.redmat;
          AppendTo( file, "m:= \n ",m,";\n\n", "m:= Matrix(m);\n\n",
                          "m0:= \n ",m0,";\n\n", "m0:= Matrix(m0);\n\n" );
          AppendTo( file, "cols:= ",r.colinds,";\n\n" );
          if Length(m[1])-Length(m) < Length(m0[1])-Length(m0) then
             AppendTo( file, "minors(m);\n\n" );
          else
             AppendTo( file, 
                    "if not minors0(m0,cols) then minors(m); else true; end if;\n\n");
          fi;
      od;     
   fi;

   return rec( diag:= diag, sl2:= sl2 );

end;

InstallMethod( ClosureDiagram,
"for Lie algebra, list or automorphism, list of sl2 triples", true, [ IsLieAlgebra, IsObject, IsList ], 0,
function( L, obj, sl2 )

   local d, g0, g1, gm, R, posR, posRv, negRv, i, v, r, diag, f, g;

   if IsList( obj ) then
      d:= obj;
      g0:= ShallowCopy( ChevalleyBasis(L)[3] );
      g1:= [ ]; gm:= [ ];
      R:= RootSystem(L);
      posR:= PositiveRootsNF(R);
      posRv:= PositiveRootVectors(R);
      negRv:= NegativeRootVectors(R);

      for i in [1..Length(posR)] do
          v:= posR[i]*d;
          if v = 0 then
              Add( g0, posRv[i] );
              Add( g0, negRv[i] );
          elif v = 1 then
            Add( g1, posRv[i] );
            Add( gm, negRv[i] );
         fi;
      od;
      if Length(g1) > 0 then
         r:= SLAfcts.hasse_diag( L, [g0,g1,gm], sl2 );
      else
         r:= SLAfcts.hasse_diag( L, [g0], sl2 );
      fi;
   elif IsMapping( obj ) then
      f:= obj;
      g:= Grading(f);
      r:= SLAfcts.hasse_diag( L, g, sl2 );
   else
      Error( "the second argument has to be an automorphism or a list giving a Z-grading");
   fi;
   
   diag:= SLAfcts.minimize_diag( Length(sl2), r.diag );
   return rec( diag:= diag, sl2:= r.sl2 );

end );

SLAfcts.carrZ:= function( L, diag, e )

   # L Z-graded by diag, e in L(1); get its carrier algebra.

   local R, posR, pRv, nRv, g0, i, v, K, h, sp, gp, gn, lams, b, C, c, eigensp, gpos, gneg,
         gzero, h1, good;

   R:= RootSystem(L);
   posR:= PositiveRootsNF(R);
   pRv:= PositiveRootVectors(R);
   nRv:= NegativeRootVectors(R);

   gpos:= [ ];
   gneg:= [ ];

   gzero:= ShallowCopy( CanonicalGenerators(R)[3] );
   for i in [1..Length(posR)] do
       v:= posR[i]*diag;
       if v = 0 then 
          Add( gzero, pRv[i] );
          Add( gzero, nRv[i] );
       elif v > 0 then
          if not IsBound( gpos[v] ) then
             gpos[v]:= [ pRv[i] ];    
             gneg[v]:= [ nRv[i] ];
          else
             Add( gpos[v], pRv[i] );
             Add( gneg[v], nRv[i] );
          fi;
       fi;
   od;
   K:= Subalgebra( L, gzero ); 

   h1:= BasisVectors( CanonicalBasis( Intersection( LieNormalizer( L, Subalgebra(L,[e]) ), 
             CartanSubalgebra(L) ) ) );
   h:= BasisVectors(CanonicalBasis( ( CartanSubalgebra(LieNormalizer(L,Subalgebra(L,[e]))))));


   if Length(h) = Length(h1) then
      good:= true;
   else
      good:= false;
   fi;

   lams:= [ ];
   sp:= Basis( Subspace( L, [e] ), [e] );
   for i in [1..Length(h)] do
       Add( lams, Coefficients( sp, h[i]*e )[1] );
   od;

   gp:= [ ]; gn:= [ ];
   if good then

      g0:= ShallowCopy( CanonicalGenerators(R)[3] );
      b:= List( h, x -> Coefficients( CanonicalBasis(CartanSubalgebra(L)), x ) );
      C:= CartanMatrix( R );

      for i in [1..Length(posR)] do
          v:= posR[i]*diag;
          c:= List( b, x ->  posR[i]*C*x );

          if v = 0 then
             if c = 0*c then          
                Add( g0, pRv[i] );
                Add( g0, nRv[i] );
             fi;
          else
             if c = v*lams then
                if not IsBound( gp[v] ) then
                   gp[v]:= [];
                   gn[v]:= [];
                fi;
                Add( gp[v], pRv[i] );
                Add( gn[v], nRv[i] );
             fi;
          fi;
      od;

   else

      eigensp:= function( uu, t )

         local m, s, sp, eqns, i, j, k, c, sol;

         m:= Length(h);
         s:= Length(uu);
         sp:= Basis( Subspace( L, uu ), uu );
         eqns:= NullMat( s, s*m );
         for j in [1..m] do
             for i in [1..s] do
                 c:= Coefficients( sp, h[j]*uu[i] );
                 for k in [1..s] do
                     eqns[i][(k-1)*m+j]:= c[k];
                 od;
             od;
         od;
         for k in [1..s] do
             for j in [1..m] do
                 eqns[k][(k-1)*m+j]:= eqns[k][(k-1)*m+j]-t*lams[j];
             od;
         od;

         sol:= NullspaceMat( eqns );
         return List( sol, x -> x*uu );
      end;
         
      g0:= eigensp( gzero, 0 );
      for i in [1..Length(gpos)] do
          if IsBound( gpos[i] ) then
             gp[i]:= eigensp( gpos[i], i );
             gn[i]:= eigensp( gneg[i], -i );
          fi;
      od;
      
   fi;

   K:= Subalgebra(L,Concatenation(g0,Flat(gp),Flat(gn)));
   K:= LieDerivedSubalgebra(K); 

   sp:= Intersection( Subspace(L,g0), K );
   g0:= BasisVectors( Basis( sp ) );
   for i in [1..Length(gp)] do
       if IsBound( gp[i] ) then
          sp:= Intersection( Subspace(L,gp[i]), K );
          gp[i]:= BasisVectors( Basis( sp ) );
       else
          gp[i]:= [ ];
       fi;
   od;
   for i in [1..Length(gn)] do
       if IsBound( gn[i] ) then
          sp:= Intersection( Subspace(L,gn[i]), K );
          gn[i]:= BasisVectors( Basis( sp ) );
       else
          gn[i]:= [ ];
       fi;
   od;

   return rec( g0:= g0, posdeg:= gp, negdeg:= gn );

end;


SLAfcts.carrZm:= function( L, f, e )

   local h, lams, sp, i, gp, gn, eigensp, g0, g1, gm, m, gr, K, k, dim,t0;

   gr:= Grading(f);
   sp:= Subspace( L, gr[1] );
   h:= BasisVectors(CanonicalBasis( Intersection( sp, CartanSubalgebra(LieNormalizer(L,
                            Subalgebra(L,[e]))))));
   lams:= [ ];
   sp:= Basis( Subspace( L, [e] ), [e] );
   for i in [1..Length(h)] do
       Add( lams, Coefficients( sp, h[i]*e )[1] );
   od;

   gp:= [ ]; gn:= [ ];

    eigensp:= function( uu, t )

         local m, s, sp, eqns, i, j, k, c, sol;

         m:= Length(h);
         s:= Length(uu);
         sp:= Basis( Subspace( L, uu ), uu );
         eqns:= NullMat( s, s*m );
         for j in [1..m] do
             for i in [1..s] do
                 c:= Coefficients( sp, h[j]*uu[i] );
                 for k in [1..s] do
                     eqns[i][(k-1)*m+j]:= c[k];
                 od;
             od;
         od;
         for k in [1..s] do
             for j in [1..m] do
                 eqns[k][(k-1)*m+j]:= eqns[k][(k-1)*m+j]-t*lams[j];
             od;
         od;

         sol:= NullspaceMat( eqns );
         return List( sol, x -> x*uu );
      end;

   m:= Length(gr);
   g0:= eigensp( gr[1], 0 );
   g1:= eigensp( gr[2], 1 );
   gm:= eigensp( gr[ m ], -1 );

   K:= LieDerivedSubalgebra( Subalgebra( L, Concatenation( gm, g0, g1 ) ) );

   g0:= BasisVectors( Basis( Intersection( Subspace( L, g0 ), K ) ) );

   dim:= Length(g0);
   k:= 1;
   while dim < Dimension(K) do
      g1:= BasisVectors( Basis( Intersection( Subspace( L, 
              eigensp( gr[ (k mod m) +1 ], k ) ), K ) ) );
      Add( gp, g1 );
      dim:= dim+Length(g1);
      gm:= BasisVectors( Basis( Intersection( Subspace( L, 
              eigensp( gr[ (-k mod m) +1 ], -k ) ), K ) ) );
      Add( gn, gm );
      dim:= dim+Length(gm);
      k:= k+1;
   od;
 
   return rec( g0:= g0, gp:= gp, gn:= gn );
   
end;

InstallMethod( CarrierAlgebra,
"for Lie algebra, list or automorphism, a nilpotent element", true, 
[ IsLieAlgebra, IsObject, IsObject ], 0,
function( L, obj, e )

   local d, g0, g1, gm, R, posR, posRv, negRv, i, v, r, diag, f, g;

   if IsList( obj ) then
      d:= obj;
      r:= SLAfcts.carrZ( L, d, e );
   elif IsMapping( obj ) then
      f:= obj;
      r:= SLAfcts.carrZm( L, f, e );
   else
      Error( "the second argument has to be an automorphism or a list giving a Z-grading");
   fi;
   
   return r;

end );


SLAfcts.jord_dec:= function ( mat )

    local  F, p, B, f, g, fac, ff, h, w;

    F := DefaultFieldOfMatrix( mat );
    if F = fail  then
        return TRY_NEXT_METHOD;
    fi;
    p := Characteristic( F );
    f := CharacteristicPolynomial( F, F, mat );
    fac := Set( Factors( f ) );
    g:= Product( fac ); 
    if f = g  then
        return [ mat, 0 * mat ];
    fi;
    w := GcdRepresentation( g, Derivative( g ) )[2];
    w := w * g;
    B := ShallowCopy( mat );
    while Value( g, B ) <> 0 * B  do
        B := B - Value( w, B );
    od;
    return [ B, mat - B ];
end;

SLAfcts.semsim_part:= function( L, x, b, B )

  # x elm of semsim Lie alg, L, b: basis of Lie alg 
  # B: basis of space spanned by ad L, such that i-th
  # basis elements is ad b_i.

  local adx, cf;

  adx:= AdjointMatrix( Basis(L), x );
  cf:= Coefficients( B, SLAfcts.jord_dec( adx )[1] );
  return cf*b;

end;

InstallMethod( CartanSubspace,
"for a finite order automorphism", true, [ IsGeneralMapping ], 0,
function( f )

  local F, sp0, sp1, g, s, r, Omega, s1, b, ad, B, found, x, xs, s0, V,
        i, cf, cf1, x1, xs1, adx, found0, L, g0, g1;

  L:= Source(f);
  g0:= Grading(f)[1];
  g1:= Grading(f)[2];

  F:= LeftActingDomain(L);

  sp0:= Subspace( L, g0 );
  sp1:= Subspace( L, g1 );

  g:= L;
  s:= L;
  r:= Subalgebra( L, [] );

  Omega:= [ 0, 1, 1, 1 ];

  while true do

     s1:= Intersection( s, sp1 );
     if Dimension( s1 ) = 0 then
        return Intersection( g, sp1 );
     fi;

     b:= BasisVectors( Basis(s) );
     ad:= List( b, x -> AdjointMatrix( Basis(s), x ) );
     B:= Basis( VectorSpace( F, ad ), ad );

     found:= false;

     while not found do

          cf:= List( Basis(s1), u -> Random( Omega) );
          x:= cf*BasisVectors( Basis(s1) );
          adx:= AdjointMatrix( Basis(s), x );

          if not IsZero(adx^Dimension(s)) then

             found0:= false;  # we find one with maybe better coefficients
             while not found0 do
               cf:= List( Basis(s1), u -> Random( [0,1] ) );
               x:= cf*BasisVectors( Basis(s1) );
               adx:= AdjointMatrix( Basis(s), x );
               found0:= not IsZero( adx^Dimension(s) );
             od;

             for i in [1..Length(cf)] do
                 if not IsZero(cf[i]) then
                    cf1:= ShallowCopy(cf);
                    cf1[i]:= 0;
                    x1:= cf1*BasisVectors( Basis(s1) );
                    adx:= AdjointMatrix( Basis(s), x1 );
                    if not IsZero( adx^Dimension(s) ) then
                       x:= x1; cf:= cf1;
                    fi;
                 fi;
             od;

             for i in [1..Length(cf)] do
                 if not IsZero(cf[i]) then
                    cf1:= ShallowCopy(cf);
                    cf1[i]:= 0;
                    x1:= cf1*BasisVectors( Basis(s1) );
                    adx:= AdjointMatrix( Basis(s), x1 );
                    if not IsZero( adx^Dimension(s) ) then
                       x:= x1; cf:= cf1;
                    fi;
                 fi;
             od;

             xs:= SLAfcts.semsim_part( s, x, b, B );

             g:= LieCentralizer( g, Subalgebra( g, [xs] ) );          
             s:= LieDerivedSubalgebra(g);
             r:= LieCentre(g);

             found:= true;
          else

             s0:= Intersection( s, sp0 );
             V:= VectorSpace( F, List( Basis(s0), u -> u*x ) );
             if Dimension(V) = Dimension(s1) then
                return Intersection( r, sp1 );
             fi;
          fi;

     od;

  od;
  
end );
