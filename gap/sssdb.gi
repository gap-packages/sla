#### first some aux functions, maybe to be renamed later....
SLAfcts.canbas:= function( L, c )


    # L: semisimple Lie algebra, c: lists of three lists, x, y, h,
    # which are canonical generators.
    # return: three lists , x1, y1, h; which form a basis of L,
    # x1, y1 consist of commutators of elts of x, y resp; we
    # take the lex smallest sequence.

    # NB: we can also construct a basis of a subalgebra of L this way!

    local x, y, x1, y1, done, levelx, levely, newlevx, newlevy,
          sp, i, j, u;

    x:= c[1];
    y:= c[2];

    x1:= ShallowCopy(x); y1:= ShallowCopy(y);

    done:= false;
    levelx:= ShallowCopy(x);
    levely:= ShallowCopy(y);
    while not done do
        newlevx:= [ ];
        newlevy:= [ ];
        sp:= MutableBasis( LeftActingDomain(L), [], Zero(L) );
        for i in [1..Length(x)] do
            for j in [1..Length(levelx)] do
                u:= x[i]*levelx[j];
                if not IsZero(u) and not IsContainedInSpan(sp,u) then
                   Add( newlevx, u );
                   CloseMutableBasis( sp, u );
                   u:= y[i]*levely[j];
                   Add( newlevy, u );
                fi;
            od;
        od;
        if newlevx <> [ ] then
           Append( x1, newlevx ); 
           Append( y1, newlevy );
           levelx:= newlevx;
           levely:= newlevy;
        else
           done:= true;
        fi;
    od;

    return [x1,y1,c[3]];

end;


SLAfcts.rtsys:= function( L, c )


    # L semsim Lie alg, c a set of can gens of a subalgebra;
    # we return the root system of the subalg gen by c.

    local CartInt, posR, B, basH, i, j, a, sp, fundR, C, R, S;

    # Let a and b be two roots of the rootsystem R.
    # Let s and t be the largest integers such that a-s*b and a+t*b
    # are roots.
    # Then the Cartan integer of a and b is s-t.

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

    posR:= [ ];
    B:= SLAfcts.canbas( L, c );

    basH:= c[3];

    for i in [ 1 .. Length(B[1]) ] do
      a:= [ ];
      sp:= Basis( Subspace(L,[B[1][i]]), [B[1][i]] );

      for j in [1..Length(basH)] do
          Add( a, Coefficients( sp, basH[j]*B[1][i] )[1] );
      od;
      Add( posR, a );
    od;

    fundR:= posR{[1..Length(c[1])]};
    # Now we calculate the Cartan matrix C of the root system.
    S:= Concatenation( posR, -posR );
    C:= List( fundR, i -> List( fundR, j -> CartInt( S, i, j ) ) );

    R:= Objectify( NewType( NewFamily( "RootSystemFam", IsObject ),
                IsAttributeStoringRep and IsRootSystemFromLieAlgebra ), 
                rec() );
    SetCanonicalGenerators( R, List( c, ShallowCopy) );
    SetUnderlyingLieAlgebra( R, Subalgebra(L,Flat(B),"basis") );
    SetPositiveRootVectors( R, ShallowCopy(B[1]) );
    SetNegativeRootVectors( R, ShallowCopy(B[2]) );
    SetCartanMatrix( R, C );
    
    SetPositiveRoots( R, posR );
    SetNegativeRoots( R, -posR ); 
    SetSimpleSystem( R, posR{[1..Length(C)]} );

    SetRootSystem( UnderlyingLieAlgebra(R), R );

    return R;
    

end;

SLAfcts.seq_to_elm:= function( M, e )

    local u, i;

    u:= Zero(M);
    for i in [1,3..Length(e)-1] do
        u:= u+e[i]*CanonicalBasis(M)[ e[i+1] ];
    od;
    return u;

end;

SLAfcts.elm_to_seq:= function( M, u )

    local cf, e, i;

    cf:= Coefficients( CanonicalBasis(M), u );
    e:= [ ];
    for i in [1..Length(cf)] do
        if not IsZero(cf[i]) then
           Add( e, cf[i] ); Add( e, i ); 
        fi;
    od;

    return e;

end;

SLAfcts.type:= function( K )

    # K is a semsim Lie alg; we return a record:
    # type : the sorted Cartan type,
    # K0: same as K, but with root sys that has Cartan mat
    # in normal form, with corr can gens etc.

    local C, tp, c, en, R;
    
    C:= CartanMatrix( RootSystem(K) );
    tp:= CartanType( C );
    SortParallel( tp.types, tp.enumeration );

    c:= List( CanonicalGenerators(RootSystem(K)), ShallowCopy );
    en:= Flat( tp.enumeration );
    c[1]:= c[1]{en};
    c[2]:= c[2]{en};
    c[3]:= c[3]{en};

    R:= SLAfcts.rtsys( K, c );
    return rec( type:= tp.types, K0:= UnderlyingLieAlgebra(R) );


end;


SLAfcts.make_db:= function( L, list )

    # list is a list of can gen sets of subalgs of L;
    # we produce the corr database entry;
    # we assume that the Lie algebra has been produced
    # by the function SimpleLieAlgebra, and DirectSum, etc;
    # so that the neumeration is standard.
    
    local tL, L0, K, subalgs, i, t, K0, c;

    K:= List( list, c -> UnderlyingLieAlgebra( SLAfcts.rtsys(L,c) ) );
    subalgs:= [ ];
    for i in [1..Length(K)] do
        t:= SLAfcts.type(K[i]);
        K0:= t.K0;
        c:= CanonicalGenerators( RootSystem(K0) );
        c:= List( c, u -> List( u, v -> SLAfcts.elm_to_seq(L,v) ) );

        Add( subalgs, rec( num:=i, dim:= Dimension(K0), type:= t.type,
                           inclusions:= [ ], cangens:= c ) );
    od;

    return rec( dim:= Dimension(L), 
                type:= CartanType(CartanMatrix(RootSystem(L))).types, 
                subalgs:= subalgs );
    

end;

SLAfcts.kappa:= function( L, K, u, v )


   return Coefficients( Basis(L), u )*(K*Coefficients(Basis(L),v));

end;

SLAfcts.h_to_weight:= function( R, BH, HK, h )

  # R is the root system.
  # here BH is a basis of the CSA wrt h_\alpha, for simple roots,
  # HK is the matrix of the Killing form with respect to those 
  # same basis elements, h is an element of the CSA; we produce
  # a correponsinh weight.

  local a, norm, i;

  a:= ShallowCopy(Coefficients( BH, h ));
  norm:= a*(HK*a);
  for i in [1..Length(a)] do a[i]:= a[i]*HK[i][i]/norm; od;
  return a*SimpleRootsAsWeights( R ); 

end;



SLAfcts.diag_auts:= function( type )

    local i, j, k, auts, rank, pieces, start, p0, p, q, d;


    rank:= Sum( List(type), x -> x[2] );
    pieces:= [ ];
    start:= 0;
    for i in [1..Length(type)] do
        Add( pieces, [start+1..start+type[i][2]] );
        start:= start + type[i][2];
    od;
    auts:= [ ];
    p0:= [1..rank];
    for i in [1..Length(type)] do
 
        if type[i][1] = "A" and type[i][2] > 1 then
           p:= ShallowCopy( p0 );
           q:= pieces[i];
           for j in [1..Length(q)] do p[q[j]]:= q[ Length(q)-j+1 ]; od;
           Add( auts, p );
        elif type[i][1] = "D" and type[i][2] = 4 then
             p:= ShallowCopy(p0);
             q:= pieces[i];
             p[q[1]]:= q[4];
             p[q[3]]:= q[1];
             p[q[4]]:= q[3];
             Add( auts, p );

             p:= ShallowCopy(p0);
             q:= pieces[i];
             p[q[1]]:= q[4];
             p[q[4]]:= q[1];
             Add( auts, p );

        elif type[i][1] = "D" and type[i][2] > 4 then
             p:= ShallowCopy(p0);
             q:= pieces[i];
             d:= Length(q);
             p[q[d]]:= q[d-1];
             p[q[d-1]]:= q[d];
             Add( auts, p );
        elif type[i][1] = "E" and type[i][2] = 6 then
             p:= ShallowCopy(p0);
             q:= pieces[i];
             p[q[1]]:= q[6];
             p[q[3]]:= q[5];
             p[q[5]]:= q[3];
             p[q[6]]:= q[1];
             Add( auts, p );
        fi;
    od;

    for i in [1..Length(type)] do
        for j in [i+1..Length(type)] do

            if type[i] = type[j] then

               p:= ShallowCopy(p0);
               d:= type[i][2];
               for k in [1..d] do
                   p[pieces[i][k]]:= pieces[j][k];
                   p[pieces[j][k]]:= pieces[i][k];
               od;
               Add( auts, p );

            fi;
        od;
    od;    

    if auts = [ ] then
       return [ () ];
    else
       return Elements( Group( List( auts, PermList ) ) );
    fi;

end;

SLAfcts.erase_linconjsubalgs:= function( L, list )

    local R, K, ch, BH, KH, BW, list0, weightsets, contained, k, ww, u;

    R:= RootSystem(L);
    K:= KillingMatrix( Basis(L) );
    ch:= CanonicalGenerators(R)[3];
    BH:= Basis( Subspace( L, ch ), ch );
    KH:= List( ch, x -> List(ch, y -> SLAfcts.kappa(L,K,x,y)));
    BW:= SLAfcts.bilin_weights(R);

    list0:= [ ];
    weightsets:= [ ];
    for u in list do 
        ww:= List( u[3], x -> SLAfcts.h_to_weight( R, BH, KH, x ) );

        contained:= false;
        for k in [1..Length(weightsets)] do
            if SLAfcts.are_conjugate( R, BW, ww, weightsets[k] ) then
               contained:= true; break;
            fi;
        od;
        if not contained then 
           Add( weightsets, ww );
           Add( list0, u );
        fi;
    od;

    return list0;


end;


SLAfcts.ssisomorphism:= function( L1, L2 )


    local b1, b2, c1, c2, R1, R2, t, tp, en, i;

    
    R1:= RootSystem(L1);
    t:= CartanType( CartanMatrix(R1) );
    tp:= ShallowCopy( t.types );
    en:= ShallowCopy( t.enumeration );
    SortParallel( tp, en );
    c1:= [ [], [], [] ];
    for i in [1..Length(en)] do
        Append( c1[1], CanonicalGenerators(R1)[1]{en[i]} );
        Append( c1[2], CanonicalGenerators(R1)[2]{en[i]} );
        Append( c1[3], CanonicalGenerators(R1)[3]{en[i]} );
    od;

    R2:= RootSystem(L2);
    t:= CartanType( CartanMatrix(R2) );
    tp:= ShallowCopy( t.types );
    en:= ShallowCopy( t.enumeration );
    SortParallel( tp, en );
    c2:= [ [], [], [] ];
    for i in [1..Length(en)] do
        Append( c2[1], CanonicalGenerators(R2)[1]{en[i]} );
        Append( c2[2], CanonicalGenerators(R2)[2]{en[i]} );
        Append( c2[3], CanonicalGenerators(R2)[3]{en[i]} );
    od;

    b1:= SLAfcts.canbas( L1, c1 );
    b2:= SLAfcts.canbas( L2, c2 );

    return AlgebraHomomorphismByImagesNC( L1, L2, Concatenation(b1),
                     Concatenation(b2) );

end;



SLAfcts.subalgs_semsim0:= function( F, db, type )

    #here type is a normalised Cartan type; we find all semsim subalgebras
    #of the Lie algebra of that type;
    #assuming the types of smaller dims are in the database.
    # NB: we assume Length(type) > 1

    local K, L, c, c1, c2, K1, K2, t1, t2, M1, M2, f1, f2, pos, r, list1,
          list2, tps1, tps2, i, j, k, d, c0, t0, subs, subs0, tps0, cc,
          tc, matches, m, l, mm, sets, auts, start, pieces1, pieces2, pieces, 
          tp, pi, a1, tp0, s0, c00, dd, en; 

    
    K:= List( type, x -> SimpleLieAlgebra( x[1], x[2], F ) );
    L:= DirectSumOfAlgebras(K);        

    en:= CartanType( CartanMatrix(RootSystem(L))).enumeration;

    # get the direct summands as subalgebras
    c:= CanonicalGenerators( RootSystem(L) );
    c1:= List( c, x -> x{en[1]} );
    c2:= List( c, x -> Concatenation( List( [2..Length(type)], i -> 
                               x{en[i]} ) ) );

    K1:= UnderlyingLieAlgebra( SLAfcts.rtsys(L,c1) );
    K2:= UnderlyingLieAlgebra( SLAfcts.rtsys(L,c2) );
    
    t1:= [ type[1] ];
    t2:= type{[2..Length(type)]};

    M1:= SimpleLieAlgebra( t1[1][1], t1[1][2], F );
    M2:= List( t2, x -> SimpleLieAlgebra( x[1], x[2], F ) );
    M2:= DirectSumOfAlgebras(M2);

    f1:= SLAfcts.ssisomorphism( M1, K1 );
    f2:= SLAfcts.ssisomorphism( M2, K2 );

    pos:= PositionProperty( db, x -> x.type = t1 );
    r:= db[pos];
    list1:= List( r.subalgs, s -> List( s.cangens, z -> 
                   List( z, x -> Image( f1, SLAfcts.seq_to_elm(M1,x) ) ) ) );
    tps1:= List( r.subalgs, x -> x.type );
    Add( list1, c1 ); 
    Add( tps1, t1 );

    pos:= PositionProperty( db, x -> x.type = t2 );
    r:= db[pos];
    list2:= List( r.subalgs, s -> List( s.cangens, z -> 
                   List( z, x -> Image( f2, SLAfcts.seq_to_elm(M2,x) ) ) ) );
    tps2:= List( r.subalgs, x -> x.type );

    Add( list2, c2 );
    Add( tps2, t2 );


    subs:= [ ];
    for i in [1..Length(list1)] do
        Add(subs,rec( type:= tps1[i], inclusions:= [ ], cangens:= list1[i] ));
    od;
    for i in [1..Length(list2)] do
        Add(subs,rec( type:= tps2[i], inclusions:= [ ], cangens:= list2[i] ));
    od;

    for i in [1..Length(list1)] do
        for j in [1..Length(list2)] do
            if [i,j] <> [Length(list1),Length(list2)] then
               c0:= List( list1[i], ShallowCopy );
               Append( c0[1], list2[j][1] );
               Append( c0[2], list2[j][2] );
               Append( c0[3], list2[j][3] );
               t0:= ShallowCopy(tps1[i]); Append( t0, tps2[j] );         

               pieces:= [ [], [], [] ];
               start:= 0;
               for k in [1..Length(t0)] do
                   for l in [1,2,3] do
                       Add( pieces[l], 
                               c0[l]{[start+1..t0[k][2]+start]} );
                   od;
                   start:= start+t0[k][2];
               od;

               for l in [1,2,3] do
                   tp0:= ShallowCopy( t0 );
                   SortParallel( tp0, pieces[l] );
               od;

               Add(subs,rec( type:= tp0, inclusions:= [ ], 
                                  cangens:= List( pieces, Flat ) ));
            fi;
        od;
    od;

    subs0:= [ ];
    tps0:= [ ];
    for i in [1..Length(list1)] do
        for j in [1..Length(list2)] do

            # we have to see how parts of list1 and parts of list2 can be
            # matched...

            cc:= Combinations( [1..Length(tps1[i])] );
            pos:= Position( cc, [] );
            RemoveElmList( cc, pos );
            for c in cc do

                # see if c also occurs in the second type

                tc:= tps1[i]{c};

                dd:= Combinations( [1..Length(tps2[j])], Length(c) );
                matches:= [ ];
                for d in dd do
                    if tps2[j]{d} = tc then
                       Add( matches, d );
                    fi;
                od;

                mm:= [ ];
                for m in matches do
                    if ForAll( [1..Length(c)], x -> IsBound( m[x] ) ) then
                       Add( mm, m );
                    fi;
                od;
 
                sets:= [  ];
                matches:= mm;
                mm:= [ ];
                for m in matches do
                    if not Set(m) in sets then
                       Add( mm, m );
                       Add( sets, Set(m) );
                    fi;
                od;

                matches:= mm;
                auts:= SLAfcts.diag_auts( tc );

                pieces1:= [ [], [], [] ];
                start:= 0;
              
                for k in [1..Length(tps1[i])] do
                    if k in c then
                       for l in [1,2,3] do
                           Append( pieces1[l], 
                                 list1[i][l]{[start+1..start+tps1[i][k][2]]} );
                       od;
                    fi;
                    start:= start + tps1[i][k][2];
                od;

                for m in matches do

                    tp:= [ ];

                    c0:= [ [],[],[] ];
                    start:= 0;
                    for k in [1..Length(tps1[i])] do
                        if not k in c then
                           for l in [1,2,3] do
                               Append( c0[l], 
                                 list1[i][l]{[start+1..start+tps1[i][k][2]]} );
                           od;
                           Add( tp, tps1[i][k] );
                        fi;
                        start:= start + tps1[i][k][2];
                    od;

                    start:= 0;
                    for k in [1..Length(tps2[j])] do
                        if not k in m then
                           for l in [1,2,3] do
                               Append( c0[l], 
                                 list2[j][l]{[start+1..start+tps2[j][k][2]]} );
                           od;
                           Add( tp, tps2[j][k] );
                        fi;
                        start:= start + tps2[j][k][2];
                    od;

                    pieces2:= [ [], [], [] ];
                    start:= 0;
                
                    for k in [1..Length(tps2[j])] do
                        if k in m then
                           for l in [1,2,3] do
                               Append( pieces2[l], 
                                 list2[j][l]{[start+1..start+tps2[j][k][2]]} );
                           od;
                        fi;
                        start:= start + tps2[j][k][2];
                    od;

                    Append( tp, tc );

                    for pi in auts do

                        # apply pi to the elms of pieces, and glue to list2[j]

                        c00:= List( c0, ShallowCopy );
                        for l in [1,2,3] do
                            a1:= Permuted( pieces1[l], pi );
                            for k in [1..Length(a1)] do
                                a1[k]:= a1[k] + pieces2[l][k];
                            od;
                            Append( c00[l], a1 );
                        od;

                        pieces:= [ [], [], [] ];
                        start:= 0;
                        for k in [1..Length(tp)] do
                            for l in [1,2,3] do
                               Add( pieces[l], 
                                    c00[l]{[start+1..tp[k][2]+start]} );
                            od;
                            start:= start+tp[k][2];
                        od;

                        for l in [1,2,3] do
                            tp0:= ShallowCopy( tp );
                            SortParallel( tp0, pieces[l] );
                        od;

                        Add( subs0, List( pieces, Flat ) );
                        Add( tps0, tp0 );

                    od;
                od;
            od;
            
        od;

    od;

    while subs0 <> [ ] do
        s0:= [ ];
        tp0:= tps0[1];
        for i in [1..Length(subs0)] do
            if tps0[i] = tp0 then
               Add( s0, subs0[i] );
               Unbind( subs0[i] ); 
               Unbind( tps0[i] );
            fi;
        od;

        subs0:= Filtered( subs0, x -> IsBound(x) );
        tps0:= Filtered( tps0, x -> IsBound(x) );

        s0:= SLAfcts.erase_linconjsubalgs( L, s0 );

        for j in [1..Length(s0)] do 
            Add( subs, rec( type:= tp0, inclusions:= [], 
                                             cangens:= s0[j]));
        od;

    od;

    for i in [1..Length(subs)] do
        subs[i].cangens:= List( subs[i].cangens,  
                   x -> List( x, y -> SLAfcts.elm_to_seq(L,y) ) );
    od;

    Sort( subs, function(r,s) return Length(r.cangens[1]) 
                                           < Length(s.cangens[1]); end );

    for i in [1..Length(subs)] do
        subs[i].num:= i;
    od;

    return rec( dim:= Dimension(L), type:= type, subalgs:= subs );
 

end;


SLAfcts.add_increls:= function( F, db, r )

    # here db is a database, and r a record; maybe in the database
    # maybe not. We add all inclusion rels, assuming that in the
    # db this has been done for smaller ranks, and for smaller dim.

    local K, L, R, ch, BH, KH, BW, list, i, j, k, pos, s, M, f, t, h1, w1,
          h2, w2; 

    K:= List( r.type, x -> SimpleLieAlgebra( x[1], x[2], F ) );
    L:= DirectSumOfAlgebras(K);        

    R:= RootSystem(L);
    K:= KillingMatrix( Basis(L) );
    ch:= CanonicalGenerators(R)[3];
    BH:= Basis( Subspace( L, ch ), ch );
    KH:= List( ch, x -> List(ch, y -> SLAfcts.kappa(L,K,x,y)));
    BW:= SLAfcts.bilin_weights(R);

    list:= List( r.subalgs, s -> UnderlyingLieAlgebra( SLAfcts.rtsys( L, 
       List( s.cangens, z -> List( z, x -> SLAfcts.seq_to_elm(L,x) ) ) ) ) );

    for i in [1..Length(list)] do

        # compute the subalgebras of list[i]:

        pos:= PositionProperty( db, x -> x.type = r.subalgs[i].type );
        if pos <> fail then

           s:= db[pos];
           # make an isom of the lie alg of the record in position pos
           # to the subalg list[i]:

           M:= List( s.type, 
                    x -> SimpleLieAlgebra( x[1], x[2], F ) );
           M:= DirectSumOfAlgebras(M);
           
           f:= SLAfcts.ssisomorphism( M, list[i] );

           # the record in position pos contains the subalgebras of M;
           # we map their canonical generators to list[i] \subset L;
           # and see whether any of them are conjugate to a subalgebra
           # in list[i]:

           for j in [1..Length(s.subalgs)] do

               t:= s.subalgs[j];
               h1:= List( t.cangens[3], x -> Image( f, SLAfcts.seq_to_elm(M,x) ) );
               w1:= List( h1, x -> SLAfcts.h_to_weight( R, BH, KH, x ) );

               for k in [1..Length(r.subalgs)] do
                   if r.subalgs[k].type = t.type then
                      h2:= List( r.subalgs[k].cangens[3], 
                                            x -> SLAfcts.seq_to_elm(L,x) );
                      w2:= List( h2, x -> SLAfcts.h_to_weight( R, BH, KH, x ) );
                      if SLAfcts.are_conjugate( R, BW, w1, w2 ) then
                         # the k-th subalgebra of L is isomorphic to
                         # a subalgebra of the i-th subalgebra of L...
                         AddSet( r.subalgs[k].inclusions, i );
                         break;
                      fi;
                   fi;
               od;

           od;
        fi;
    od;


end;

SLAfcts.dimension:= function(type)

    # the dimension of the Lie algebra with type type.

    local dim, i, s, r;

    dim:= 0;
    for i in [1..Length(type)] do

        s:= type[i][1]; r:= type[i][2];
        if s = "A" then
           dim:= dim +(r+1)^2-1;
        elif s = "B" then
           dim:= dim + 2*r^2+r;
        elif s = "C" then
           dim:= dim + 2*r^2+r;
        elif s ="D" then
           dim:= dim + 2*r^2-r;
        elif s = "E" then
           if r = 6 then
              dim:= dim+78;
           elif r=7 then
              dim:= dim + 133;
           else
              dim:= dim + 248;
           fi;
        elif s="F" then
           dim:= dim + 52;
        else 
           dim:= dim + 14;
        fi;

    od;

    return dim;

end;


#########################################################################
# main functions for working with the database:


SLADBASE:= Objectify( NewType( NewFamily( "dbasefam", IsSSSDataBase ),
    IsSSSDataBase and IsAttributeStoringRep ), rec( data:= SLAfcts.db ) );

InstallMethod( PrintObj,
        "for database",
        true,
       [ IsSSSDataBase ], 0,
       function( d )


     Print("<database of semisimple subalgebras of semisimple Lie algebras>");

end );


SSSTypes:= function()

     local t, d, i, j, s;

     if not IsBound( SLADBASE!.types ) then
        t:= [ ];
        d:= SLADBASE!.data;
        for i in [1..Length(d)] do
            s:= "";
            for j in d[i].type do
                Append( s, j[1] );
                Append( s, String(j[2]) );
                Append( s, " " );
            od;
            s:= s{[1..Length(s)-1]};
            Add( t, s );
        od;
        SLADBASE!.types:= t;
     fi;

     return SLADBASE!.types;

end;


InstallMethod( LieAlgebraAndSubalgebras,
        "for type", true,
       [ IsString ], 0,
function( type )


     local pos, s, d, u, i, j, k, F, K, L, list, tp, lett, d1, d2, r;

    
     pos:= Position( SSSTypes(), type );

     if pos = fail then
        if Length(type) = 2 then # i.e., simple type
           s:= "The database does not contain a Lie algebra of type "; 
           Append( s, type ); 
           Error(s);
        else
           # sem sim type, trigger computation...
           # note that if there are more than two components, we
           # also need those...

           # first parse and sort the type..
           k:= 1;
           tp:= [ ];
           lett:= "ABCDEFG";
           while k <= Length(type) do
               pos:= Position( lett, type[k] );
               k:= k+1;
               s:= "";
               while k <= Length(type) and type[k] <> ' ' do
                   Add( s, type[k] ); k:= k+1;
               od;
               while k <= Length(type) and type[k] = ' ' do k:= k+1; od;
               Add( tp, [ [lett[pos]], Rat(s) ] );
           od;  

           Sort( tp );

           pos:= PositionProperty( SLADBASE!.data, x -> x.type = [ tp[1] ] );
           if pos = fail then
              s:= "The database does not contain a Lie algebra of type "; 
              Append( s, tp[1][1] ); Append( s, String(tp[1][2]) ); 
              Error(s);
           fi;

           d1:= SLADBASE!.data[pos];

           s:= "";
           for j in tp{[2..Length(tp)]} do
               Append( s, j[1] );
               Append( s, String(j[2]) );
               Append( s, " " );
           od;
           s:= s{[1..Length(s)-1]};    

           r:= LieAlgebraAndSubalgebras( s );
           d2:= SLAfcts.make_db( r.liealg, List( r.subalgs, x -> 
                             CanonicalGenerators(RootSystem(x) ) ) );
           r:= SLAfcts.subalgs_semsim0( CF(840), [d1,d2], tp );
           r.added_increls:= false;   
           Add( SLADBASE!.data, r );
           pos:= Length( SLADBASE!.data );
           Unbind( SLADBASE!.types );
        fi;
     fi;

     d:= SLADBASE!.data[pos];
     u:= [ ];
     for s in d.subalgs do
         for i in [1..Length(s.cangens)] do
             for j in [1..Length(s.cangens[i])] do
                 for k in [1,3..Length(s.cangens[i][j])-1] do
                     Add( u, s.cangens[i][j][k] );
                 od;
             od;
         od;
     od;
     if u = [] then u:=[1]; fi;
     F:= DefaultField( u );

     K:= List( d.type, x -> SimpleLieAlgebra( x[1], x[2], F ) );
     L:= DirectSumOfAlgebras(K);

     list:= List( d.subalgs, s -> UnderlyingLieAlgebra( SLAfcts.rtsys( L, 
        List( s.cangens, z -> List( z, x -> SLAfcts.seq_to_elm(L,x) ) ) ) ) );

     for i in [1..Length(list)] do
         s:= "";
         for j in d.subalgs[i].type do
             Append( s, j[1] );
             Append( s, String(j[2]) );
             Append( s, " " );
         od;
         s:= s{[1..Length(s)-1]};
         SetSemiSimpleType( list[i], s );
     od;

     return rec( liealg:= L, subalgs:= list );
          
end );

InstallMethod( InclusionsGraph,
        "for type", true,
       [ IsString ], 0,
function( type )

   # here type is a type from the database; we compute the
   # inclusions among its subalgebras.

   local pos, tps, i, s, r, j, edges, c, a, c0; 

   pos:= Position( SSSTypes(), type );
   if pos = fail then
      s:= "The database does not contain a Lie algebra of type "; 
      Append( s, type ); 
      Error(s);
   fi;

   if IsBound( SLADBASE!.data[pos].graph ) then
      return SLADBASE!.data[pos].graph;
   fi;

   tps:= Set( List( SLADBASE!.data[pos].subalgs, x -> x.type ) );
   Sort( tps, function(a,b) return SLAfcts.dimension(a) < SLAfcts.dimension(b); end );  

   for i in [1..Length(tps)] do

       s:= "";
       for j in tps[i] do
           Append( s, j[1] );
           Append( s, String(j[2]) );
           Append( s, " " );
       od;
       s:= s{[1..Length(s)-1]};    
       if not s in SSSTypes() then # force it to be added
          r:= LieAlgebraAndSubalgebras( s );       
       fi;

   od;
    
   SLAfcts.add_increls( CF(840), SLADBASE!.data, SLADBASE!.data[pos] );

   edges:= [];
   s:= SLADBASE!.data[pos].subalgs;
   for i in [1..Length(s)] do

       # see in which algs s[i] is contained as maximal subalg...

       c:= ShallowCopy( s[i].inclusions );
       if c = [] then
          Add( edges, [0,i] );
       else
          a:= Concatenation( List( c, x -> s[x].inclusions ) );
          c0:= [ ];
          for j in c do if not j in a then Add( c0, j ); fi; od;
          for j in c0 do Add( edges, [j,i] ); od;
       fi;
   od;

   for i in [1..Length(s)] do Unbind( s[i].inclusions ); od;

   SLADBASE!.data[pos].graph:= edges;
   return edges;

  
end );

InstallMethod( SubalgebrasInclusion,
        "for three Lie algebras", true,
       [ IsFLMLOR, IsFLMLOR, IsFLMLOR ], 0,
function( L, K1, K2 )


    # here K1, K2, are two subalgebras of L, such that a linear
    # conjugate of K1 is contained in K2; we return that linear conjugate.

    local R, Kil, ch, BH, KH, BW, type, r, M, f, ss, w, w1, k, c;

    # in order to decide lin conjugacy we need the following:
    R:= RootSystem(L);
    Kil:= KillingMatrix( Basis(L) );
    ch:= CanonicalGenerators(R)[3];
    BH:= Basis( Subspace( L, ch ), ch );
    KH:= List( ch, x -> List(ch, y -> SLAfcts.kappa(L,Kil,x,y)));
    BW:= SLAfcts.bilin_weights(R);

    type:= SemiSimpleType( K2 );
    r:= LieAlgebraAndSubalgebras( type );
    M:= r.liealg;
    f:= SLAfcts.ssisomorphism( M, K2 );

    ss:= Filtered( r.subalgs, x -> SemiSimpleType(x) = SemiSimpleType(K1) );

    w:= List( CanonicalGenerators(RootSystem(K1))[3], x -> 
                    SLAfcts.h_to_weight( R, BH, KH, x ) );

    for k in [1..Length(ss)] do

        w1:= List( CanonicalGenerators( RootSystem(ss[k]) )[3], x -> 
                SLAfcts.h_to_weight( R, BH, KH, Image(f,x) ) );
        if SLAfcts.are_conjugate( R, BW, w, w1 ) then 
           c:= List( CanonicalGenerators( RootSystem(ss[k]) ), x ->
                  List( x, y -> Image( f, y ) ) );
           M:= UnderlyingLieAlgebra( SLAfcts.rtsys( L, c ) );
           SetSemiSimpleType( M, SemiSimpleType(K1) );
           return M;
        fi;
    od;

    return fail;

end );


InstallMethod( DynkinIndex,
        "for two Lie algebras", true,
       [ IsFLMLOR, IsFLMLOR ], 0,
function( K, L )


    # here K is a semisimple subalgebra of the simple Lie algebra L; we
    # compute the Dynkin index of K in L. 

    local R, kL, cL, u, fL, S, cK, ct, di, i, c, A, kA, pos;
    
    R:= RootSystem(L);
    kL:= KillingMatrix( Basis(L) );
    cL:= CanonicalGenerators( R );
    u:= List( cL[3], h -> SLAfcts.kappa( L, kL, h, h ) );
    fL:= 2/Minimum(u);

    S:= RootSystem(K);
    cK:= CanonicalGenerators( S );
    ct:= CartanType( CartanMatrix(S) );
    di:= [ ];
    for i in [1..Length(ct.types)] do
        c:= List( cK, x -> x{ct.enumeration[i]} );
        A:= UnderlyingLieAlgebra( SLAfcts.rtsys( L, c ) );
        kA:= KillingMatrix( Basis(A) );
        u:= List( c[3], h -> SLAfcts.kappa( A, kA, h, h ) );
        pos:= Position( u, Minimum(u) );
        Add( di, fL*SLAfcts.kappa(L,kL,c[3][pos],c[3][pos])/2 );
    od;

    return di;

end );


InstallMethod( IsomorphismOfSemisimpleLieAlgebras,
        "for two Lie algebras", true,
       [ IsFLMLOR, IsFLMLOR ], 0,

function( L1, L2 ) return SLAfcts.ssisomorphism(L1,L2); end );


InstallMethod( AreLinearlyEquivalentSubalgebras,
"for three Lie algebras", true,
[ IsFLMLOR, IsFLMLOR, IsFLMLOR ], 0,

function( L, K1, K2 )

   local R1, R2, t1, t2, H, c1, c2, R, BW, BH, KH, w1, w2, hh;


   R1:= RootSystem(K1);
   R2:= RootSystem(K2);
   t1:= CartanType( CartanMatrix( R1 ) );
   t2:= CartanType( CartanMatrix( R2 ) );

   SortParallel( t1.types, t1.enumeration );
   SortParallel( t2.types, t2.enumeration );

   if t1.types <> t2.types then return false; fi;

   H:= CartanSubalgebra( L );
   c1:= CanonicalGenerators( R1 )[3];
   if not ForAll( c1, x -> x in H ) then return fail; fi;
   c1:= Concatenation( List( t1.enumeration, x -> c1{x} ) );
   c2:= CanonicalGenerators( R2 )[3];
   if not ForAll( c2, x -> x in H ) then return fail; fi;
   c2:= Concatenation( List( t2.enumeration, x -> c2{x} ) );   

   R:= RootSystem(L);
   BW:= SLAfcts.bilin_weights(R);

   hh:= CanonicalGenerators(R)[3];
   BH:= Basis( Subspace( L, hh ), hh );
   KH:= List( hh, x -> List(hh, y -> SLAfcts.kappa(L,KillingMatrix(Basis(L)),x,y)));

   w1:= List( c1, x -> SLAfcts.h_to_weight( R, BH, KH, x) );
   w2:= List( c2, x -> SLAfcts.h_to_weight( R, BH, KH, x) );

   return SLAfcts.are_conjugate( R, BW, w1, w2 );

end );


InstallMethod( MakeDatabaseEntry,
"for a record", true,
[ IsRecord ], 0,
function( r )

   local L, c;

   if not IsBound( r.liealg ) or not IsBound( r.subalgs ) then
      Error( "Not a valid record." );
   fi;

   L:= r.liealg;
   c:= List( r.subalgs, x -> CanonicalGenerators( RootSystem(x) ) );
   return SLAfcts.make_db( L, c );

end );


InstallMethod( AddToDatabase,
"for a record", true, [ IsRecord ], 0,
function( d )

    local s, j;

    if not IsBound( d.dim ) or not IsBound( d.type ) or 
       not IsBound( d.subalgs ) then
       Error( "Not a valid record.");
    fi;

    Add( SLADBASE!.data, d );
    if IsBound( SLADBASE!.types ) then
       s:= "";
       for j in d.type do
           Append( s, j[1] );
           Append( s, String(j[2]) );
           Append( s, " " );
       od;
       s:= s{[1..Length(s)-1]};
       Add( SLADBASE!.types, s );
    fi;

end );