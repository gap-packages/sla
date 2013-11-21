SLAfcts.highest_root:= function( type )

     # here type is a list, e.g., [ "B", 5 ] -- we return the
     # coefficients of the highest root of the root system

     local t, rank, c;

     t:= type[1]; rank:= type[2];

     if t = "A" then
        c:= List( [1..rank], x -> 1 );
     elif t = "B" then
        c:= [1];
        Append( c, List( [2..rank], x -> 2 ) );
     elif t = "C" then
        c:= List( [1..rank-1], x -> 2 );
        Add( c, 1 );
     elif t = "D" then
        c:= [1];
        Append( c, List( [2..rank-2], x -> 2 ) );
        Append( c, [1,1] );
     elif t = "E" and rank = 6 then
        c:= [ 1, 2, 2, 3, 2, 1 ];
     elif t ="E" and rank = 7 then
        c:= [ 2, 2, 3, 4, 3, 2, 1 ];
     elif t = "E" and rank = 8 then
        c:= [ 2, 3, 4, 6, 5, 4, 3, 2 ];
     elif t ="F" then
        c:= [ 2, 3, 4, 2 ];
     elif t = "G" then
        c:= [ 3, 2 ];
     fi;

     return c;

end;


SLAfcts.derived_systems:= function( B, p )

     # here p is a pi-system, B matrix of the bilinear form.

     local rts, tps, der, i, j, k, l, rts0, tps0, c, rr, rank, C, t, rt, 
           tp, e, r;
     
     rts:= p.roots;
     tps:= p.types;

     der:= [ ];

     for i in [1..Length(tps)] do

         rts0:= List( rts, x -> ShallowCopy(x) );
         tps0:= List( tps, x -> ShallowCopy(x) );
         RemoveElmList( rts0, i );
         RemoveElmList( tps0, i );

         c:= -SLAfcts.highest_root( tps[i] );
         c:= c*rts[i];
         for j in [1..Length(rts[i])] do
             rr:= ShallowCopy( rts[i] );
             rr[j]:= c;
             rank:= Length(rr);
             C:= NullMat( rank, rank );
             for k in [1..rank] do
                 for l in [1..rank] do
                     C[k][l]:= 2*rr[k]*(B*rr[l])/( rr[l]*(B*rr[l]) );
                 od;
             od;

             t:= CartanType( C );

             if not ( Length(t.types) = 1 and t.types[1] = tps[i] ) then

                rt:= List( rts0, ShallowCopy );
                tp:= List( tps0, ShallowCopy );
                for k in [1..Length(t.types)] do
                    e:= t.enumeration[k];
                    r:= [ ];
                    for l in [1..Length(e)] do
                        Add( r, rr[ e[l] ] );
                    od;
                    Add( rt, r );
                    Add( tp, t.types[k] );
                od;
                Add( der, rec( roots:= rt, types:= tp ) );
             fi;
         od;
     od;

     return der;

end;


SLAfcts.pi_systems_0:= function( R )
     
     # We assume R is a simple root system.

     local C, t, e, rts, i, p, res, newpis, news, x, B;

     C:= CartanMatrix(R);
     t:= CartanType( C );

     B:= BilinearFormMatNF(R);

     e:= t.enumeration[1];
     rts:= [ ];
     for i in [1..Length(e)] do
         Add( rts, SimpleSystemNF(R)[ e[i] ] );
     od;
     p:= rec( roots:= [rts], types:= t.types );

     res:= [ p ];
     newpis:= [ p ];
     while newpis <> [ ] do

         news:= [ ];
         for x in newpis do
             Append( news, SLAfcts.derived_systems( B, x ) );
         od;

         newpis:= news;
         Append( res, newpis );
     od;

     return res;

end;


# now some functions for dealing with sub-Weyl groups
# They are given as records: W.roots gives the roots
# as weights rel to the big root system, W.wgts, gives
# the simple roots as weights rel to the small root system.

SLAfcts.conj_dom_wt:= function( wt, relwt, W )

    # Here wt is a weight (rel to the big root system).
    # relwt is the weight rel to the small root system (i.e., 
    # the vector of values < mu, \beta_i^\vee >, i = 1,..,m.
    # W a sub-Weyl group datum..
    # We compute the dominant weight (rel to small root sys) 
    # conj to wt, we output the dom wt, its rel wt, and the word,
    # in terms of the generators of W that maps the weight
    # to the dominant one.

    local lam, rlam, pos, w;
     
    lam:= ShallowCopy( wt );
    rlam:= ShallowCopy( relwt );
    pos:= PositionProperty( rlam, x -> x < 0 );
    w:= [ ];
    while pos <> fail do

       Add( w, pos );
       lam:= lam - rlam[pos]*W.roots[pos];
       rlam:= rlam - rlam[pos]*W.wgts[pos];
       pos:= PositionProperty( rlam, x -> x < 0 );
    od;

    return [ lam, rlam, Reversed(w) ];


end;

SLAfcts.stabilizer:= function( wt, B, W )

    # Here W is a sub-Weyl group, and wt a weight rel to
    # the big root system R. B is the matrix of the bilin form
    # wrt weight basis (in the big root system).
    # we find generators of the stabiliser of wt in W,
    # output as a sub-Weyl group

    local relwt, d, inds, i, j, g, w, rt, relt, CM;

    relwt:= List( W.roots, x -> 2*wt*(B*x)/( x*(B*x) ) );

    d:= SLAfcts.conj_dom_wt( wt, relwt, W );

    inds:= [ ];
    for i in [1..Length(d[2])] do
        if d[2][i] = 0 then Add( inds, i ); fi;
    od;

    g:= [ ];

    w:= d[3];

    for i in inds do
        rt:= ShallowCopy(W.roots[i]);
        relt:= ShallowCopy(W.wgts[i]);

        # apply w...

        for j in w do
            rt:= rt - relt[j]*W.roots[j];
            relt:= relt - relt[j]*W.wgts[j];
        od;
        Add( g, rt );

    od;

    CM:= List( g, x -> List( g, y -> 2*x*(B*y)/( y*(B*y) ) ) );

    return rec( roots:= g, wgts:= CM );


end;


SLAfcts.bilin_weights:= function( R )

   # The bilin form mat wrt basis of fund weights...

   local sp, rank, B, b, bas, i, j, c;

   sp:= Basis( VectorSpace( Rationals, SimpleRootsAsWeights(R) ),
            SimpleRootsAsWeights(R) );

   rank:= Length( CartanMatrix(R) );
   B:= NullMat( rank, rank );
   b:= BilinearFormMatNF( R );
   bas:= IdentityMat( rank );
   for i in [1..rank] do
       for j in [i..rank] do
           c:= Coefficients( sp, bas[i] )*( b*Coefficients(sp,bas[j]) );
           B[i][j]:= c; B[j][i]:= c;
       od;
   od;

   return B;

end;



SLAfcts.are_conjugate_0:= function( R, B, mus, lams )


   # R is the big root system, B the bilin form mat wrt weights,
   # mus and lams are lists of weights, we determine whether
   # there exists w in W wich w(mus[i]) = lams[i], all i.

   local sim, W, i, j, k, a, b, w, mu, rmu;

   sim:= SimpleRootsAsWeights( R );
   W:= rec( roots:= sim, wgts:= sim );

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


SLAfcts.are_conjugate:= function( R, B, mus, lams )


   # same as previous function, but now we also permute
   # the mus, lams. We do assume that they arrive in an
   # order that defines the same Cartan matrix...

   local C, perms, i, newperms, p, q, good, j, k, l, nus;

   # however,... first we try the identity permutation...

   if SLAfcts.are_conjugate_0( R, B, mus, lams ) then
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

       if SLAfcts.are_conjugate_0( R, B, nus, lams ) then
          return true;
       fi;
   od;

   return false;

end;


SLAfcts.pi_systems:= function( R )

   # simple root system...

   local pis, B, sim, roots, types, p, tps, rts, mus, pos, found, i; 

   pis:= SLAfcts.pi_systems_0(R);
   B:= SLAfcts.bilin_weights( R );
   sim:= SimpleRootsAsWeights(R);

   roots:= [ ];
   types:= [ ];

   for p in pis do
       tps:= p.types;
       rts:= p.roots;

       SortParallel( tps, rts );

       mus:= Concatenation( List( rts, x -> List( x, y -> y*sim ) ) );

       pos:= Position( types, tps );
       if pos = fail then
          Add( types, tps );
          Add( roots, mus );
       else
          
          found:= false;
          for i in [pos..Length(types)] do
              if types[i] = tps then      
                 
                 if SLAfcts.are_conjugate( R, B, mus, roots[i] ) then
                    found:= true; break;
                 fi;
 
              fi;
          od;
          if not found then 
             Add( types, tps );
             Add( roots, mus );
          fi;

       fi; 

   od;

   return rec( types:= types, roots:= roots );


end;


sub_systems:= function( R )

   # simple root system..., we give reps of all orbits of
   # sub root systems under the Weyl group

   local pis, B, roots, types, tps, rts, mus, pos, found, i, j, k, comb,
         r0, c, C, r1, tp, e, u, t1, rank; 

   pis:= SLAfcts.pi_systems(R);
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

InstallMethod( RegularSemisimpleSubalgebras,
"for a Lie algebra", true, [ IsLieAlgebra ], 0,

function( L )

   local R, s, posRw, ch, xL, yL, algs, i, j, r, x, y, pos, K, tL, tK, 
         h, fund, rt, sp, CartInt, posR, posRv, oldR, oldRv, negR, negRv,
         oldneg, newneg, newR, newRv, allrts, C, RK, k, u;

    CartInt := function( R, a, b )
       local s,t,rt;
       s:=0; t:=0;
       rt:=a-b;
       while (rt in R) or (rt=0*R[1]) do
         rt:=rt-b;
         s:=s+1;
       od;
       rt:=a+b;
       while (rt in R) or (rt=0*R[1]) do
         rt:=rt+b;
         t:=t+1;
       od;
       return s-t;
    end;

   
   R:= RootSystem(L);
   s:= sub_systems( R );

   posRw:= PositiveRootsAsWeights( R );
   ch:= ChevalleyBasis(L);
   xL:= ch[1]; yL:= ch[2];

   tL:= SemiSimpleType(L);

   algs:= [ ];
   for i in [1..Length(s.roots)] do

       tK:= Concatenation( s.types[i][1][1], String( s.types[i][1][2] ) );
       if tK <> tL then

          r:= s.roots[i];
          x:= [ ]; y:= [ ];
          for j in [1..Length(r)] do
              pos:= Position( posRw, r[j] );
              if pos <> fail then
                 Add( x, xL[pos] );
                 Add( y, yL[pos] );
              else
                 pos:= Position( posRw, -r[j] );
                 Add( x, yL[pos] );
                 Add( y, xL[pos] );
              fi;
          od;

          K:= Subalgebra( L, Concatenation( x, y ) );

          # make the root system of K...
          h:= List( [1..Length(x)], k -> x[k]*y[k] );
          SetCartanSubalgebra( K, Subalgebra(K,h) );

          fund:= [ ];
          for j in [1..Length(x)] do
              rt:= [ ];
              sp:= Basis( Subspace(L,[x[j]]), [x[j]] );
              for k in [1..Length(h)] do
                  Add( rt, Coefficients( sp, h[k]*x[j] )[1] );
              od;
              Add( fund, rt );
          od;

          posR:= ShallowCopy( fund );
          posRv:= ShallowCopy( x );
          oldR:= ShallowCopy(fund);
          oldRv:= ShallowCopy( x );

          negR:= List( fund, q -> -q );
          negRv:= ShallowCopy(y);
          oldneg:= ShallowCopy( negRv );

          while oldR <> [ ] do
              newR:= [ ];
              newRv:= [ ];
              newneg:= [ ];
              for j in [1..Length(fund)] do
                  for k in [1..Length(oldR)] do
                      u:= x[j]*oldRv[k];
                      if not IsZero( u ) then
                         rt:= fund[j]+oldR[k];
                         if not rt in newR then
                            Add( newR, rt );
                            Add( newRv, u );
                            Add( newneg, y[j]*oldneg[k] );
                         fi;
                      fi;
                  od;
              od;
              Append( posR, newR );
              Append( posRv, newRv );
              Append( negR, -newR );
              Append( negRv, newneg );
              oldR:= newR; oldRv:= newRv;
              oldneg:= newneg;
          od;
             
          allrts:= Concatenation( posR, negR );            

          C:= List( fund, a -> List( fund, b -> CartInt( allrts, a, b ) ) );

          RK:= Objectify( NewType( NewFamily( "RootSystemFam", IsObject ),
                     IsAttributeStoringRep and IsRootSystemFromLieAlgebra ), 
                     rec() );
          SetCanonicalGenerators( RK, [ x, y, h ] );
          SetUnderlyingLieAlgebra( RK, K );
          SetPositiveRootVectors( RK, posRv );
          SetNegativeRootVectors( RK, negRv );
          SetCartanMatrix( RK, C );
    
          SetPositiveRoots( RK, posR );
          SetNegativeRoots( RK, negR ); 
          SetSimpleSystem( RK, fund );
          SetRootSystem( K, RK );

          Add( algs, K );
       fi;
   od;

   return algs;

end );
