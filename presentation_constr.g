# G                 group
# pr_normal_iso     isomorphism from normal factor N of G to a finite presentation
# pr_quot_iso       isomorphism from quotient G/N to a finite presentation
# epi               epimorphism G -> G/N
# computes finite presentation for G using these things
construct_presentation := function(G, pr_quot_iso, pr_normal_iso, epi)
    local pr_quot, pr_normal, m, h, f, gen, new_gens, m_new, h_new, g, n, rho,
        r1, r3, r4, i, j, r, a, b, c, d, new_pr, gens, pr_gens, x;
    pr_quot := Range(pr_quot_iso);
    pr_normal := Range(pr_normal_iso);
    m := FreeGeneratorsOfFpGroup(pr_normal);
    h := FreeGeneratorsOfFpGroup(pr_quot);
    f := FreeGroup(Length(m) + Length(h));
    new_gens := FreeGeneratorsOfFpGroup(f);
    m_new := new_gens{[1..Length(m)]};
    h_new := new_gens{Length(m)+[1..Length(h)]};
    
    g := [];
    for gen in GeneratorsOfGroup(pr_quot) do
        x := PreImagesRepresentative(epi, PreImagesRepresentative(pr_quot_iso, gen));
        if x <> () then
            Add(g, x);
        fi;
    od;

    n := [];
    for gen in GeneratorsOfGroup(pr_normal) do
        Add(n, PreImagesRepresentative(pr_normal_iso, gen));
    od;

    rho := function(x)
        return MappedWord(UnderlyingElement(pr_normal_iso(MappedWord(x, h, g))), m, m_new);
    end;

    r1 := [];
    for r in RelatorsOfFpGroup(pr_normal) do
        Add(r1, MappedWord(r, m, m_new));
    od;

    r3 := [];
    for r in RelatorsOfFpGroup(pr_quot) do
        a := ExtRepOfObj(MappedWord(r, h, h_new));
        b := ExtRepOfObj(rho(r));
        if m <> [] then
            c := ExtRepOfObj(m[1]^0);
        else
            c := [];
        fi;
        if h <> [] then
            d := ExtRepOfObj(h[1]^0);
        else
            d := [];
        fi;
        Append(c, a);
        Append(b, d);
        Add(r3, ObjByExtRep(FamilyObj(new_gens[1]), c) / ObjByExtRep(FamilyObj(new_gens[1]), b));
    od;

    r4 := [];
    for i in [1..Length(m)] do
        for j in [1..Length(h)] do
            b := MappedWord(UnderlyingElement(pr_normal_iso(n[i]^g[j])), m, m_new);
            Add(r4, m_new[i]^h_new[j] / b);
        od;
    od;

    r := Concatenation(r1, r3, r4);
    new_pr := f / r;

    pr_gens := GeneratorsOfGroup(new_pr);
    gens := Concatenation(n, g);
    for x in n do
        i := Position(m, UnderlyingElement(pr_normal_iso(x)));
        # it might happen that the isomorphism maps to the inverse if the generator is equal to its inverse
        if i = fail then
            i := Position(m, UnderlyingElement(pr_normal_iso(x)^-1));
        fi;
        gens[i] := x;
    od;
    for x in g do
        i := Position(h, UnderlyingElement(pr_quot_iso(epi(x))));
        if i = fail then
            i := Position(h, UnderlyingElement(pr_quot_iso(epi(x))^-1));
        fi;
        gens[Length(m)+i] := x;
    od;

    return GroupHomomorphismByImagesNC(G, new_pr, gens, pr_gens);
end;
