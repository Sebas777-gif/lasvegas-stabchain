randomized_stab_chain := function( gens, id, options)
    local S,            # stabilizer chain
          degree,       # degree of S
          givenbase,    # list of points from which first base points should come
          correct,      # boolean; true if a correct base is given
          size,         # size of <G> as constructed
          order,        # size of G if given in input
          limit,        # upper bound on Size(G) given in input
          orbits,       # list of orbits of G
          orbits2,      # list of orbits of G
          k,            # number of pairs of generators checked
          param,        # list of parameters guiding number of repetitions
                        # in random constructions
          orbit_list,   # list indicating which orbit contains points in domain
          basesize,     # list; i^th entry = number of base points in orbits[i]
          i,j,
          warning,      # used at warning if given and computed size differ
          new,          # list of permutations to be added to stab. chain
          result,       # output of checking phase; nontrivial if stabilizer
                        # chain is incorrect
          base,         # ordering of domain from which base points are taken
          missing;      # if a correct base was provided by input, missing
                        # contains those points of it which are not in
                        # constructed base

    S:= rec( generators := ShallowCopy( gens ), identity := id );
    if options.random = 1000 then
       #case of deterministic computation with known size
       k := 1;
    else
       k:=First([1..14],x->(3/5)^x<1-options.random/1000);
    fi;

    degree := LargestMovedPoint( S.generators );

    if IsBound( options.knownBase) and
      Length(options.knownBase)<4+LogInt(degree,10)  then
        param:=[k,4,0,0,0,0];
    else
        param:=[QuoInt(k,2),4,QuoInt(k+1,2),4,50,5];
        options:=ShallowCopy(options);
        Unbind(options.knownBase);
    fi;
    if options.random <= 200 then
       param[2] := 2;
       param[4] := 2;
    fi;

    #param[1] = number of pairs of random subproducts from generators in
    #           first checking phase
    #param[2] = (number of random elements from created set)/S.diam
    #           in first checking phase
    #param[3] = number of pairs of random subproducts from generators in
    #           second checking phase
    #param[4] = (number of random elements from created set)/S.diam
    #           in second checking phase
    #param[5] = maximum size of orbits in  which we evaluate words on all
    #           points of orbit
    #param[6] = minimum number of random points from orbit to plug in to check
    #           whether given word is identity on orbit


    # prepare input of construction
    if IsBound(options.base)  then
        givenbase := options.base;
    else
        givenbase := [];
    fi;

    if IsBound(options.size) then
        order := options.size;
        warning := 0;
        limit := 0;
    else
        order := 0;
        if IsBound(options.limit) then
            limit := options.limit;
        else
            limit := 0;
        fi;
    fi;

    if IsBound( options.knownBase )  then
        correct := true;
    else
        correct := false;
    fi;

    if correct then
        # if correct  base was given as input, no need for orbit information
        base:=Concatenation(givenbase,Difference(options.knownBase,givenbase));
        missing := Set(options.knownBase);
        basesize := [];
        orbit_list := [];
        orbits := [];
    else
        # create ordering of domain used in choosing base points and
        # compute orbit information
        base:=Concatenation(givenbase,Difference([1..degree],givenbase));
        missing:=[];
        orbits2:=OrbitsPerms(S.generators,[1..degree]);
        #throw away one-element orbits
        orbits:=[];
        j:=0;
        for i in [1..Length(orbits2)] do
            if Length(orbits2[i]) >1 then
               j:=j+1; orbits[j]:= orbits2[i];
            fi;
        od;
        basesize:=[];
        orbit_list:=[];
        for i in [1..Length(orbits)] do
            basesize[i]:=0;
            for j in [1..Length(orbits[i])] do
                orbit_list[orbits[i][j]]:=i;
            od;
        od;
        # temporary solution to speed up of handling of lots of small orbits
        # until compiler
        if Length(orbits) > degree/40 then
           param[1] := 0;
           param[3] := k;
        fi;
    fi;

    new:=S.generators;
    SCRMakeStabStrong(S,new,param,orbits,orbit_list,basesize,base,correct,missing,true);
    #restore usual record elements
    if not IsBound(S.labels) then
       S := SCRRestoredRecord(S);
    fi;
    return S;
end;
