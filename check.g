Read("presentation_constr.g");

comp_series_stab_chain := function( C )
    local   normals,    # first component of output; normals[i] contains
                        # generators for i^th subgroup in comp. series
            factors,    # second component of output; factors[i] contains
                        # the action of generators in normals[i]
            factorsize, # third component of output; factorsize[i] is the
                        # size of the i^th factor group
            homlist,    # list of homomorphisms applied to input group
            auxiliary,  # if auxiliary[j] is bounded, it contains
                        # a subg. which must be added to kernel of homlist[j]
            index,      # variable recording how many elements of normals are
                        # computed
            workgroup,  # the subnormal factor group we currently work with
            workgrouporbit,
            lastpt,     # degree of workgroup
            tchom,      # transitive constituent homomorphism applied to
                        # intransitive workgroup
            bhom,       # block homomorphism applied to imprimitive workgroup
            fahom,      # factor homomorphism to store
            bl,         # block system in workgroup
            D,          # derived subgroup of workgroup
            top,        # index of D in workgroup
            lenhomlist, # length of homlist
            i, s,  t,   #
            fac,        # factor group as permutation group
            list;       # output of CompositionSeries

    # initialize output and work arrays
    normals := [];
    factors := [];
    factorsize := [];
    auxiliary := [];
    homlist := [];
    index := 1;
    workgroup := GroupStabChain(C);

    # workgroup is always a factor group of the input Gr such that a
    # composition series for Gr/workgroup is already computed.
    # Try to get a factor group of workgroup
    while (Size(workgroup) > 1) or (Length(homlist) > 0) do
        if Size(workgroup) > 1  then
            lastpt := LargestMovedPoint(workgroup);

            # if workgroup is not transitive
            workgrouporbit:= StabChainMutable( workgroup ).orbit;
            if Length(workgrouporbit) < lastpt   then
                tchom :=
                  ActionHomomorphism(workgroup,workgrouporbit,"surjective");
                Add(homlist,tchom);
                workgroup := Image(tchom,workgroup);
            else
                bl := MaximalBlocks(workgroup,[1..lastpt]);

                # if workgroup is not primitive
                if Length(bl) > 1  then
                    bhom:=ActionHomomorphism(workgroup,bl,OnSets,"surjective");
                    workgroup := Image(bhom,workgroup);
                    Add(homlist,bhom);
                else
                    D := DerivedSubgroup(workgroup);
                    top := Size(workgroup)/Size(D);

                    # if workgroup is not perfect
                    if top > 1  then

                        # fill up workgroup/D by cyclic factors
                        index := NonPerfectCSPG(homlist,normals,factors,
                                 auxiliary,factorsize,top,index,D,workgroup);
                        workgroup := D;

                    # otherwise chop off simple factor group from top of
                    # workgroup
                    else
                        workgroup := PerfectCSPG(homlist,normals,factors,
                                       auxiliary,factorsize,index,workgroup);
                        index := index+1;
                    fi;  # nonperfect-perfect

                fi;  # primitive-imprimitive

            fi;  # transitive-intransitive

        # if the workgroup was trivial
        else
            lenhomlist := Length(homlist);

            # pull back natural homs
            PullBackNaturalHomomorphismsPool(homlist[lenhomlist]);

            workgroup := KernelOfMultiplicativeGeneralMapping(
                             homlist[lenhomlist] );

            # if auxiliary[lenhmlist] is bounded, it is faster to augment it
            # by generators of the kernel of `homlist[lenhomlist]'
            if IsBound(auxiliary[lenhomlist])  then
                workgroup := auxiliary[lenhomlist];
                workgroup := ClosureGroup( workgroup, GeneratorsOfGroup(
                                KernelOfMultiplicativeGeneralMapping(
                                    homlist[lenhomlist] ) ) );
            fi;
            Unbind(auxiliary[lenhomlist]);
            Unbind(homlist[lenhomlist]);

        fi; # workgroup is nontrivial-trivial
    od;

    # loop over the subgroups
    #s := SubgroupNC( Gr, normals[1] );
    #SetSize( s, Size( Gr ) );
    s:= GroupStabChain(C);
    list := [ s ];
    for i  in [2..Length(normals)]  do
        t := SubgroupNC( s, normals[i] );
        SetSize( t, Size( s ) / factorsize[i-1] );
        fac := GroupByGenerators( factors[i-1] );
        SetSize( fac, factorsize[i-1] );
        SetIsSimpleGroup( fac, true );
        fahom:=GroupHomomorphismByImagesNC( s, fac,
                        normals[i-1], factors[i-1] );
        #if IsIdenticalObj(Parent(t),s) then
        #  Setter( NaturalHomomorphismByNormalSubgroupInParent )( t,fahom);
        #fi;
        AddNaturalHomomorphismsPool(s, t,fahom);
        Add( list, t );
        s := t;
    od;
    t := TrivialSubgroup( s );
    Assert(1,Size( s )=factorsize[Length(normals)]);
    fac := GroupByGenerators( factors[Length(normals)] );
    SetSize( fac, factorsize[Length(normals)] );
    SetIsSimpleGroup( fac, true );
    fahom:=GroupHomomorphismByImagesNC( s, fac,
                    normals[Length(normals)], factors[Length(normals)] );
    if IsIdenticalObj(Parent(t),s) then
      Setter( NaturalHomomorphismByNormalSubgroupInParent )( t,fahom);
    fi;
    AddNaturalHomomorphismsPool(s, t,fahom);
    Add( list, t );

    # return output
    return list;
end;

check := function(C, S)
    local res, cs, k, p, i, epi, new_pr, f_gens, gens, gen, x, rels, r;
    
    BreakOnError := false;
    res := CALL_WITH_CATCH(comp_series_stab_chain, [C]);
    BreakOnError := true;
    if res[1] then
        cs := res[2];
    else
        return false;
    fi;

    k := Length(cs);
    p := IsomorphismFpGroup(cs[k]);
    for i in [k-1,k-2..1] do
        if Size(Group(GeneratorsOfGroup(cs[i]))) <> Size(cs[i]) then
            return false;
        fi;
        if not IsNormal(cs[i], cs[i+1]) then
            return false;
        fi;
        epi := NaturalHomomorphismByNormalSubgroup(cs[i], cs[i+1]);
        new_pr := construct_presentation(cs[i], IsomorphismFpGroup(Image(epi)), p, epi);
        p := new_pr;
    od;

    f_gens := FreeGeneratorsOfFpGroup(Range(p));
    gens := [];
    for gen in GeneratorsOfGroup(Range(p)) do
        Add(gens, PreImage(p, gen));
    od;

    rels := RelatorsOfFpGroup(Range(p));
    for r in rels do
        if MappedWord(UnderlyingElement(r), f_gens, gens) <> () then
            return false;
        fi;
    od;
    return true;
   
end;
