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


InstallOtherMethod( ProjectionMatrix,
"for two semisimple Lie algebras", true, [ IsLieAlgebra, IsLieAlgebra, IsList ], 0,

function( L, K, cc )

    local H, HK, N, K0, hK, hL, b;

    H:= CartanSubalgebra(L);
    HK:= Intersection( H, K );

    N:= LieNormalizer( K, HK );
    if N <> HK then
       Error("The Cartan subalgebras do not match.");
    fi;

    if not ForAll( cc, x -> x in H ) then
       Error("The toral elements do noy lie in the Cartan.");
    fi;

    if not HasCartanSubalgebra(K) then
       K0:= K;
       SetCartanSubalgebra(K0,HK);
    elif  CartanSubalgebra(K) <> HK then
       K0:= Subalgebra( L, BasisVectors( Basis(K) ), "basis" );
       SetCartanSubalgebra(K0,HK);
    else
       K0:= K;
    fi;

    hK:= Concatenation( CanonicalGenerators( RootSystem(K0) )[3], cc );
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


InstallOtherMethod( Branching,
"for two semisimple Lie algebras and a weight", true, 
[ IsLieAlgebra, IsLieAlgebra, IsList, IsList ], 0,

function( L, K, cc, wt )


    local P, ch, R, W, w0, m0, i, o, mu, pos, S, sim, b, ord, ww, mm, mult,
          w, isg, semsimrk;

   

    P:= ProjectionMatrix( L, K, cc );
    semsimrk:= Dimension( CartanSubalgebra(K) );

    ch:= DominantCharacter( L, wt );
    R:= RootSystem(L);
    W:= WeylGroup(R);
    w0:= [ ]; m0:= [ ];
    for i in [1..Length(ch[1])] do
        o:= WeylOrbitIterator( W, ch[1][i] );
        while not IsDoneIterator(o) do
             mu:= P*NextIterator( o );
             if ForAll( [1..semsimrk], k -> mu[k] >= 0 ) then
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

        local cf, mu0, nu0;

        mu0:= mu{[1..semsimrk]};
        nu0:= nu{[1..semsimrk]};	
        if mu0 = nu0 then return fail; fi;
        cf:= Coefficients( b, nu0-mu0 );
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
        ch:= DominantCharacter( K, w{[1..semsimrk]} );
        for i in [1..Length(ch[1])] do
	    mu:= Concatenation( ch[1][i], w{[semsimrk+1..Length(w)]} );
            pos:= Position( w0, mu );
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

   local L, R, e, sp, x, m, c, sp0, K, h, U, es;

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
   m:= List( e, u -> TransposedMatDestructive( MatrixOfAction( Basis(V), u )));
   m:= List( [1..Dimension(V)], i -> Concatenation( List( m, u -> u[i] ) ) );
   c:= NullspaceMatDestructive(m);
   sp:= Subspace( V, List( c, u -> u*Basis(V) ), "basis" );

   # in sp find a basis of weight vectors
   h:= CanonicalGenerators( R )[3];
   sp:= [ sp ];
   for x in h do
       sp0:= [ ];
       for U in sp do
           m:= List( Basis(U), a -> Coefficients( Basis(U), x^a ) );
           es:= Eigenspaces(LeftActingDomain(L),m);
           Append( sp0, List( es, M -> Subspace( V, List( Basis(M), v ->
                                          v*Basis(U) ) ) ) );
       od;
       sp:= sp0;
   od;

   sp0:= [ ];
   for U in sp do
       Append( sp0, List( Basis(U), u -> SubAlgebraModule( V, [u] ) ) );
   od;
   return sp0;
    

end );

SLAfcts.strata:= function( K, L, cen, Bil, hw )
        # K : reductive Lie algebra
        # L: semisimple part of L
        # cen: list of basis vectors of the centre,
        # hw: list of highest weights, the last coords are the
        # eigenvectors of the centre. It is assumed that
        # with R = RootSystem(L), h = CanonicalGenerators(R)[3],
        # the first coordinates of each elt of hw are the eigenvalues
        # of the elements of h.
        # Bil: matrix of nondegenerate bilinear form on the maximal torus,
        # wrt basis given by h \cup cen (h as before).

    local ch, W, wts, w, o, hh, KM, hwts, perms, rk, i, R, B, rho, exprs, 
          p, a, sa, mults, H, BH, ip, posR, csa, inconvexhull, hdimstrata,
          weylorbs, j, A, sim, id, q, wt, pos, hw0, M, g, D, v, sp, convdata,
          srk, rrk, u, lst, wts0, torustrata;

# first we have three functions...

weylorbs:= function( W, srk, rrk, wts, A )

     # wts is a set of weights, in usual notation, permuted 
     # by the Weyl group, we find subsets of length up to the rank
     # containing reps of each orbit of the Weyl group, but 
     # probably rather redundant.

     local sets, zeros, s1, z1, i, j, k, s, z, s0, z0, inds, len, cont, 
           r, l, OO, dt, dets, mat, rows, row, cols, col, pms, t1;

     sets:= [ ];
     zeros:= [ ];

     s1:= [ ];
     z1:= [ ];
     for i in [1..Length(wts)] do
         if ForAll( wts[i]{[1..srk]}, m -> m >= 0 ) then 
            Add( s1, [i] ); 
            Add( z1, Filtered( [1..srk], m -> wts[i][m] = 0 ) );
         fi;
     od;
     Add( sets, s1 );
     Add( zeros, z1 );

     for len in [2..rrk] do
         s1:= [ ]; z1:= [ ]; dets:= [ ]; rows:= [ ]; cols:= [ ];
         for i in [1..Length(sets[len-1])] do
             s:= sets[len-1][i];
             z:= zeros[len-1][i];
             for j in [1..Length(wts)] do
                 pos:= PositionSorted( s, j );
                 if pos > Length(s) or s[pos] <> j then
                    if ForAll( z, m -> wts[j][m] >= 0 ) then
                       s0:= ShallowCopy(s); 
                       InsertElmList( s0, pos, j );
                       z0:= [ ];
                       for k in [1..srk] do
                           if k in z and wts[j][k]=0 then
                              Add( z0, k );
                           fi;
                       od;

                       pms:= [ ];
                       for k in [1..Length(s0)] do
                           t1:= ShallowCopy(s0);
                           l:= RemoveElmList( t1, k );
                           mat:= A{t1}{t1};
                           row:= List( mat, Sum );
                           Sort( row );
                           Add( pms, row );
                       od;
                       if Minimum(pms) = pms[pos] then

                          pos:= PositionSorted( s1, s0 );
                          if pos > Length(s1) or s1[pos] <> s0 then 
                             cont:= false;
                             mat:= List( [1..Length(s0)], s -> [ ] );
                             for k in [1..Length(s0)] do
                                 for l in [k..Length(s0)] do
                                     mat[k][l]:= A[s0[k]][s0[l]];
                                     mat[l][k]:= mat[k][l];
                                 od;
                             od;
                             dt:= Permanent(mat);
                             row:= List( mat, Sum );
                             Sort( row );
   
                             col:= List( mat, ShallowCopy );
                             for l in [1..Length(col)] do Sort(col[l]); od;
                             Sort(col);
                             for l in [1..Length(s1)] do
                                if dt = dets[l] and row = rows[l] and
                                  col = cols[l] then
                                    r:= RepresentativeAction( W, s0, s1[l],
                                                                       OnSets );
                                    if r <> fail then
                                       cont:= true;
                                       break;
                                    fi;
                                fi;
                             od;

                             if not cont then
                                InsertElmList( s1, pos, s0 );
                                InsertElmList( z1, pos, z0 );
                                InsertElmList( dets, pos, dt );
                                InsertElmList( rows, pos, row );
                                InsertElmList( cols, pos, col );
                             fi;
                          fi;
                       fi;
                    fi;
                 fi; 
             od;
         od;
         Add( sets, s1 ); Add( zeros, z1 );
     od; 

     return sets;        

end;


inconvexhull:= function( data, S0, p0 ) 
                                            # S set of vecs in R^m (rat coords),
                                            # p a point in R^m, is p\in S?
                                            # dist: distance fct

    local m, i, one, eps, dists, pos, v, pp, k, j, u, t, S, p, dist, ip;

    dist:= data.dist;
    ip:= data.ip;

    S:= List( S0, x -> Coefficients( data.BH, x ) );
    p:= Coefficients( data.BH, p0 );
    one:= 1.000000000000000000000;
    S:= List( S, u -> u*one );
    p:= p*one;

    eps:= one*1/10; # small eps, but not very small, the algorithm for 
                    # the strata is rather sensitive to the choice of eps,
                    # smaller eps, longer runtime...

    dists:= List( S, s -> dist(s,p) );
    pos:= Position( dists, Minimum( dists ) );
    v:= S[pos];
    pp:= S[pos];

    if p = pp then return [ pp, true ]; fi;

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

torustrata:= function( H, hh, ip, rrk, h_wts, mults, wts, convdata, bool )


    # this is the same function as hdimstrata (i.e., the next function),
    # but specially for tori. 

    local w, hs, k, OO, orbs, st, hst, diffs, i, j, V, hset, h, mat, sol,
          bas, B, cfs, h0, dims, dim, out, hh0, bcsa, BC, hw0, mu0,
          res, inds, wt0;


    # detect the trivial rep, ie all weights are 0
    w:= List( h_wts, v -> List( hh, u -> ip(u,v) ) );
    if ForAll( w, IsZero ) then
       # no nilpotent elements
       return [ [], [] ];
    fi;       

       hs:= [ ];

       for k in [1..rrk] do
           OO:= Combinations( [1..Length(h_wts)], k );
           orbs:= Filtered( OO, v -> not 0*h_wts[1] in h_wts{v} );

           for st in orbs do
               # find the affine space generated by st...

               hst:= h_wts{st};
               diffs:= [ ];
               for i in [1..Length(hst)] do
                   for j in [i+1..Length(hst)] do
                       Add( diffs, hst[j]-hst[i] );
                   od;
               od;
               V:= Subspace( H, diffs );
               
               # so the affine space is A=hst[1]+V...
               # see if there are more elms in this space

               hset:= ShallowCopy( hst );
               for h in h_wts do
                   if h-hst[1] in V and not h in hset then
                      Add( hset, h );
                   fi;
               od;
               hst:= hset;

               # find point closest to 0 on A:
               if Length(st)>1 then
                  mat:= List( [1..Dimension(H)], i -> 
                            List( [1..Dimension(V)], j -> 
                                     ip( Basis(H)[i], Basis(V)[j] ) ) );
                  sol:= List( NullspaceMat( mat ), u -> u*Basis(H) );

                 # so this is a basis of the space orthogonal to V...
                 # so sol and V span the whole space, therefore, finding the
                 # intersection point amounts to expressing hst[1] on this basis

                  bas:= -ShallowCopy( Basis(V) );
                  Append( bas, sol );
                  B:= Basis( H, bas );
                  cfs:= Coefficients( B, hst[1] );
                  h0:= hst[1]+cfs{[1..Dimension(V)]}*Basis(V);
               else
                  h0:= h_wts[ st[1] ];
               fi;

               # see whether it is contained
               # in the convex hull of hst.
                 
               if not IsZero(h0) then
                  if Length(hst)=1 or 
                           inconvexhull( convdata, hst, h0 )[2] then
                     h0:= (2/ip(h0,h0))*h0;
                     if not h0 in hs then
                        Add( hs, h0 );
                     fi; 
                  fi;
               fi;
           od;

       od;            

       # now for each elt of hs we compute the dimension of the corr stratum
       # (in case it is a characteristic).
     
       dims:= [ ];
       for h0 in hs do
          dim:= 0;
          for i in [1..Length(h_wts)] do
              if ip(h0,h_wts[i]) >= 2 then dim:= dim+mults[i]; fi;
          od;
          Add( dims, dim );
       od;    

       if not bool then
          dim:= 0; # compute maximum dim, less than total dim of V...
          for i in [1..Length(dims)] do
              if dims[i] > dim and dims[i] <= Sum( mults ) then
                 dim:= dims[i];
              fi;
          od;             
          inds:= Filtered( [1..Length(hs)], i -> dims[i] = dim );
          hs:= hs{inds};      
       else
          dim:= Sum( mults );
          inds:= Filtered( [1..Length(hs)], i -> dims[i] <= dim );
          hs:= hs{inds}; dims:= dims{inds};
       fi;

       # now for each elt of hs, do a recursive call...

       out:= [ [], [] ]; # first the chars, then the dims of the corr stratum.

       for k in [1..Length(hs)] do

           h0:= hs[k];
           # have to compute tilde z(h)...

           mat:= List( hh, h1 -> [ip(h1,h0)] );
           hh0:= List( NullspaceMat(mat), u -> u*hh );

           bcsa:= ShallowCopy(hh0); Add( bcsa, h0 );
           BC:= Basis( Subspace(H,bcsa), bcsa );
           # now the h_wts of V_2(h0):
           # those are the elts h of h_wts such that ip(h0,h)=2...
           hw0:= [ ];
           mu0:= [ ];
           wt0:= [ ];
           for i in [1..Length(h_wts)] do
               if ip(h0,h_wts[i]) = 2 then
                  # project h_wts[i] on cs:
                  if Length(hh0) > 0 then
                     cfs:= Coefficients( BC, h_wts[i] );
                     Add( hw0, cfs{[1..Length(hh0)]}*hh0 );
                  else
                     Add( hw0, Zero(H) );
                  fi;
                  Add( mu0, mults[i] );
                  Add( wt0, wts[i] );
               fi;
           od;

            res:= torustrata( H, hh0, ip, rrk-1, hw0, mu0, wt0, 
                             convdata, false );

           # is there a stratum in the recursive output of dimension equal
           # to the dimension of V_2(h)? If yes, then h is not a char.

           if not Sum( mu0 ) in res[2] then
              # so h0 is a char
              if bool then
                 Add( out[1], h0 ); Add( out[2], dims[k] ); 
              else
                 Add( out[1], h0 ); Add( out[2], dim );
              fi;
           fi;

       od;
       return out;

end;        



hdimstrata:= function( R, H, BH, hh, ip, srk, rrk, posR, delt, h_wts, mults, wts, www, W, exps, A, convdata, bool )

    # This function has a lot of inputs, divided into two groups: the first
    # group remains the same for every round of the recursion, the second
    # group changes every round of the recursion.

    # first group:    

    # R: the root system of the big Lie alg
    # H: Cartan subalgebra of the "big" Lie alg
    # BH: basis of H, wrt Chevalley basis vecs
    # ip: inner product function on H (fct of two arguments)
    # convdata: a record with some data used to decide whether a point in H
    #           lies in the convex hull of a list of other points

    # second group:    

    # hh: "canonical basis" of the a CSA of the reductive input Lie algebra
    #     this consists of first the Chevalley generators, then a basis of
    #     the centre    
    # srk: semisimple rank of the input Lie algebra (rk of root system)
    # rrk: reductive rank of input Lie algebra (i.e., dim of its CSA)    
    # posR: pos roots of input Lie alg, as weights (this is always a subset
    #       of the positive roots of R)        
    # h_wts: List of wts of the rep, as elts in the CSA,
    # mults: their multiplicities
    # wts: the weights in in weight notation relative to the big root system R
    # www: the weights, but now the i-th coordinate of each weight gives its
    #      value on hh[i]    
    # W : list of perms on [1..Length(wts)], giving the action of the
    #     Weyl group
    # exps: reduced expressions of the reflections corr to the rts in posR
    # A: matrix of the bilinear form on the weights A[i][j] is the inner
    #    product of wts[i], wts[j]    
    # bool: a boolean, if true then we do not consider only the stata of 
    #       highest dim (it is true in the first iteration, false afterwards).

    local dist, out, i, G, k, XX, OO, orbs, st, hst, diffs, V, j, hset, h,
          mat, sol, bas, B, dims, dim, cfs, p, inds, pR, wt0, ex0,
          h0, cs, hw0, mu0, perms, res, hs, dist0, w, ip0, bcsa, BC, bigger,
          sums, xx, yy, conjdomh, Onew, d, r, u, v, rep, len, N, 
          totlen, dets, dt, orbs0, q, sim, sp, BH0, hh0, wtsnf, A0, hmat;


    # detect the trivial rep, ie all weights are 0
    w:= List( h_wts, v -> List( hh, u -> ip(u,v) ) );
    if ForAll( w, IsZero ) then
       # no nilpotent elements
       return [ [], [] ];
    fi;       

    if srk = 0 then  #torus
        return torustrata( H, hh, ip, rrk, h_wts, mults, wts, convdata, bool);
    fi;

    # compute simple roots, Weyl group etc.
    # to later erase W-conjugate h-s...

    conjdomh:= function( h )
           # the conjugate dominant elt in H to h.

       local h0, a, c, pos;
  
       h0:= h;
       while true do 
          c:= Coefficients( BH, h0 );
          a:= List( delt, u -> u*c );
          pos:= PositionProperty( a, x -> x<0 );
          if pos = fail then
             return h0;
          else
             h0:= h0-a[pos]*hh[pos];
          fi;
       od;

    end;        


       G:= Group(W);
       hs:= [ ];

       orbs0:= weylorbs( G, srk, rrk, www, A );

       for k in [1..rrk] do
           OO:= orbs0[k];
           orbs:= Filtered( OO, v -> not 0*h_wts[1] in h_wts{v} );

           for st in orbs do
               # find the affine space generated by st...

               hst:= h_wts{st};
               diffs:= [ ];
               for i in [1..Length(hst)] do
                   for j in [i+1..Length(hst)] do
                       Add( diffs, hst[j]-hst[i] );
                   od;
               od;
               V:= Subspace( H, diffs );
               
               # so the affine space is A=hst[1]+V...
               # see if there are more elms in this space

               hset:= ShallowCopy( hst );
               for h in h_wts do
                   if h-hst[1] in V and not h in hset then
                      Add( hset, h );
                   fi;
               od;
               hst:= hset;

               # find point closest to 0 on A:
               if Length(st)>1 then
                  mat:= List( [1..Dimension(H)], i -> 
                            List( [1..Dimension(V)], j -> 
                                     ip( Basis(H)[i], Basis(V)[j] ) ) );
                  sol:= List( NullspaceMat( mat ), u -> u*Basis(H) );

                 # so this is a basis of the space orthogonal to V...
                 # so sol and V span the whole space, therefore, finding the
                 # intersection point amounts to expressing hst[1] on this basis

                  bas:= -ShallowCopy( Basis(V) );
                  Append( bas, sol );
                  B:= Basis( H, bas );
                  cfs:= Coefficients( B, hst[1] );
                  h0:= hst[1]+cfs{[1..Dimension(V)]}*Basis(V);
               else
                  h0:= h_wts[ st[1] ];
               fi;

               # see whether it is contained
               # in the convex hull of hst.
                 
               if not IsZero(h0) then
                  if Length(hst)=1 or 
                           inconvexhull( convdata, hst, h0 )[2] then
                     h0:= (2/ip(h0,h0))*h0;
                     h0:= conjdomh(h0);
                     if not h0 in hs then
                        Add( hs, h0 );
                     fi; 
                  fi;
               fi;
           od;

       od;            

       # now for each elt of hs we compute the dimension of the corr stratum
       # (in case it is a characteristic).
     
       dims:= [ ];
       for h0 in hs do
          dim:= 2*Length(posR)+Length(hh);
          for i in [1..Length(h_wts)] do
              if ip(h0,h_wts[i]) >= 2 then dim:= dim+mults[i]; fi;
          od;
          cfs:= Coefficients( BH, h0 );
          for p in posR do
              if cfs*p <> 0 then # so either the pos or the neg root contrbs
                 dim:= dim-1;
              else
                 # now both the pos and the neg root contribs
                 dim:= dim-2;
              fi;
          od;
          dim:= dim-Length(hh);
          Add( dims, dim );
       od;    

       if not bool then
          dim:= 0; # compute maximum dim, less than total dim of V...
          for i in [1..Length(dims)] do
              if dims[i] > dim and dims[i] <= Sum( mults ) then
                 dim:= dims[i];
              fi;
          od;             
          inds:= Filtered( [1..Length(hs)], i -> dims[i] = dim );
          hs:= hs{inds};      
       else
          dim:= Sum( mults );
          inds:= Filtered( [1..Length(hs)], i -> dims[i] <= dim );
          hs:= hs{inds}; dims:= dims{inds};
       fi;

       # now for each elt of hs, do a recursive call...

       out:= [ [], [] ]; # first the chars, then the dims of the corr stratum.

       BH0:= Basis( Subspace(H,hh), hh );

       for k in [1..Length(hs)] do

           h0:= hs[k];
           # have to compute tilde z(h)...
           # first its posR...

           pR:= [ ];
           ex0:= [ ];
           wt0:= [ ];
           cfs:= Coefficients( BH, h0 );
           for i in [1..Length(posR)] do
               if cfs*posR[i] = 0 then
                  Add( pR, posR[i] );
                  Add( ex0, exps[i] );
               fi;
           od;

           sums:= [ ];
           for i in [1..Length(pR)] do
               for j in [i+1..Length(pR)] do
                   Add( sums, pR[i]+pR[j] );
               od;
           od;
           sim:= Filtered( pR, x -> not x in sums );

           inds:= List( sim, x -> Position( PositiveRootsAsWeights(R), x ) );
           xx:= PositiveRootVectors(R){inds};
           yy:= NegativeRootVectors(R){inds};
           hh0:= List( [1..Length(inds)], i -> xx[i]*yy[i] );
           
           # next the csa:
           mat:= List( hh, h1 -> [ip(h1,h0)] );
           cs:= List( NullspaceMat(mat), u -> u*hh );

           sp:= MutableBasis( LeftActingDomain(H), hh0, Zero(H) );
           i:= 1;
           while Length(hh0) < Length(cs) do
                if not IsContainedInSpan( sp, cs[i] ) then
                   CloseMutableBasis( sp, cs[i] );
                   Add( hh0, cs[i] );
                fi;
                i:= i+1;
           od;

           hmat:= List( hh0, x -> Coefficients( BH0, x ) );

           bcsa:= ShallowCopy(cs); Add( bcsa, h0 );
           BC:= Basis( Subspace(H,bcsa), bcsa );
           # now the h_wts of V_2(h0):
           # those are the elts h of h_wts such that ip(h0,h)=2...
           hw0:= [ ];
           mu0:= [ ];
           wtsnf:= [ ];
           for i in [1..Length(h_wts)] do
               if ip(h0,h_wts[i]) = 2 then
                  # project h_wts[i] on cs:
                  if Length(cs) > 0 then
                     cfs:= Coefficients( BC, h_wts[i] );
                     Add( hw0, cfs{[1..Length(cs)]}*cs );
                  else
                     Add( hw0, Zero(H) );
                  fi;
                  Add( mu0, mults[i] );
                  Add( wt0, wts[i] );
                  if Length(cs) > 0 then
                     Add( wtsnf, hmat*www[i] );
                  else
                     Add( wtsnf, [] );
                  fi;
               fi;
           od;

           inds:= List( wt0, x -> Position( wts, x ) );
           A0:= A{inds}{inds};

           # and finally the Weyl group: 
           perms:= [ ];
           for i in [1..Length(pR)] do
               Add( perms, PermList( 
                 List( wt0, w -> Position( wt0, 
                               ApplyWeylElement(WeylGroup(R),w,ex0[i]) ))) );
           od;

            res:= hdimstrata( R, H, BH, hh0, ip, Length(sim), rrk-1, pR, sim,
            hw0, mu0, wt0, wtsnf,
                             perms, ex0, A0, convdata, false );

           # is there a stratum in the recursive output of dimension equal
           # to the dimension of V_2(h)? If yes, then h is not a char.

           if not Sum( mu0 ) in res[2] then
              # so h0 is a char
              if bool then
                 Add( out[1], h0 ); Add( out[2], dims[k] ); 
              else
                 Add( out[1], h0 ); Add( out[2], dim );
              fi;
           fi;

       od;
       return out;

end;

    # Now we start with the main function.

    # first we compute the character of the module,
    # then map the weights to the CSA, where we use the Killing form.

    if Dimension(L) = 0 then # torus case

        hh:= cen;
        H:= K;
        BH:= Basis( H, hh );

        ip:= function(h1,h2) return Coefficients(BH,h1)*Bil*Coefficients(BH,h2);
                   end;
        rrk:= Dimension( H );

        convdata:= rec( # stuff needed for the convex hull function
                 dist:= function(u,v) return (u-v)*Bil*(u-v); end,
                 ip:= function(u,v) return u*Bil*v; end,
                 BH:= BH ); 

        hw0:= Collected( hw );
        wts:= List( hw0, x -> x[1] );
        mults:= List( hw0, x -> x[2] );
        hwts:= [ ];
        for w in wts do
            Add( hwts, SolutionMat( Bil, w )*hh );
        od;

        return torustrata( H, hh, ip, rrk, hwts, mults, wts, convdata, true );
    fi;


    R:= RootSystem(L);
    srk:= Length( CartanMatrix( R ) );
    rrk:= srk+Length(cen);
    W:= WeylGroup( R );
    wts:= [ ];
    mults:= [ ];
    hw0:= Collected( hw );
    for q in hw0 do 
        ch:= DominantCharacter( L, q[1]{[1..srk]} );
        for w in [1..Length(ch[1])] do
            o:= WeylOrbitIterator( W, ch[1][w] );
            while not IsDoneIterator( o ) do
                  wt:= NextIterator( o );
                  wt:= Concatenation( wt, q[1]{[srk+1..rrk]} );
                  pos:= Position( wts, wt );
                  if pos = fail then
                     Add( wts, wt ); 
                     Add( mults, q[2]*ch[2][w] );
                  else
                     mults[pos]:= mults[pos]+q[2]*ch[2][w];
                  fi;
            od;
        od;
    od;

    #hh:= ChevalleyBasis(L)[3];
    #rk:= Length(hh);
    #KM:= List( hh, h1 -> List( hh, h2-> TraceMat( AdjointMatrix(Basis(L),h1)*
    #       AdjointMatrix(Basis(L),h2) ) ) );

    hh:= ShallowCopy( CanonicalGenerators(R)[3] );
    Append( hh, cen );
     

    hwts:= [ ];
    for w in wts do
        Add( hwts, SolutionMat( Bil, w )*hh );
    od;

    # next we get permutations generating the permutation action of W on the
    # weights:

    perms:= [ ];
    wts0:= List( wts, u -> u{[1..srk]} );
    for i in [1..srk] do
        lst:= [ ];
        for w in [1..Length(wts)] do
            u:= ApplyWeylElement(W,wts0[w],[i]);
            Append( u, wts[w]{[srk+1..rrk]} );
            Add( lst, Position( wts, u ) );
        od;
        Add( perms, PermList( lst ) );
    od;

    # find reduced expressions for the reflections corr the pos rts:
    B:= BilinearFormMatNF(R);
    rho:= List( [1..srk], i -> 1);
    exprs:= [ ];
    for i in [1..Length(PositiveRoots(R))] do
        p:= PositiveRootsNF(R)[i];
        a:= Sum( [1..srk], j -> p[j]*B[j][j] );
        sa:= rho -a/(p*B*p)*PositiveRootsAsWeights(R)[i];
        w:= ConjugateDominantWeightWithWord( W, sa );
        Add( exprs, w[2] );
    od;

    H:= Subalgebra( K, hh );
    BH:= Basis( H, hh );

    ip:= function(h1,h2) return Coefficients(BH,h1)*Bil*Coefficients(BH,h2);
         end;
    posR:= PositiveRootsAsWeights(R);
 
    A:= List( hwts, x -> [] );
    for i in [1..Length(hwts)] do
        for j in [i..Length(hwts)] do
            A[i][j]:= ip(hwts[i],hwts[j]);
            A[j][i]:= A[i][j];
        od;
    od;

    # now A is the matrix of an invariant inner product on the space of weights

    convdata:= rec( # stuff needed for the convex hull function
                 dist:= function(u,v) return (u-v)*Bil*(u-v); end,
                 ip:= function(u,v) return u*Bil*v; end,
                 BH:= BH ); 

    return  hdimstrata( R, H, BH, hh, ip, srk, rrk, posR,
                SimpleRootsAsWeights(R), hwts, mults, 
                wts, wts, perms, exprs, A, convdata, true );


end;


InstallMethod( CharacteristicsOfStrata,
"for a semisimple Lie algebra and a highest weight", 
true, [ IsLieAlgebra, IsList ], 0,

function( L, hw ) # L: semisimple Lie algebra, hw: highest weight
                  # or list of highest weights

     local hw0, h, ad, Bil, i, j;

     h:= CanonicalGenerators( RootSystem(L) )[3];
     ad:= List( h, x -> AdjointMatrix( Basis(L), x ) );
     Bil:= List( ad, x -> [] );
     for i in [1..Length(ad)] do
         for j in [i..Length(ad)] do
	     Bil[i][j]:= TraceMat( ad[i]*ad[j] );
	     Bil[j][i]:= Bil[i][j];
	 od;
     od;

     if not IsList( hw[1] ) then
        hw0:= [ hw ];
     else
        hw0:= hw;
     fi;

     return SLAfcts.strata( L, L, [], Bil, hw0 );

end );


InstallOtherMethod( CharacteristicsOfStrata,
"for a semisimple Lie algebra and a highest weight", 
true, [ IsLieAlgebra, IsMatrix, IsList ], 0,

function( L, Bil, hw ) # L: semisimple Lie algebra, hw: highest weight
                       # or list of highest weights

     local hw0;

     if not IsList( hw[1] ) then
        hw0:= [ hw ];
     else
        hw0:= hw;
     fi;

     return SLAfcts.strata( L, LieDerivedSubalgebra(L),
               BasisVectors(Basis(LieCentre(L))), Bil, hw0 );

end );





