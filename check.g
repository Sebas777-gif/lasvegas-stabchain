Read("presentation_constr.g");

check := function(C)
    local g, cs, k, p, i, epi, new_pr;
    g := GroupStabChain(C);
    cs := CompositionSeries(g); # edit later to compute the cs using the custom stab chain
    k := Length(cs);
    p := IsomorphismFpGroup(cs[k]);
    for i in [k-1,k-2..1] do
        epi := NaturalHomomorphismByNormalSubgroup(cs[i], cs[i+1]);
        new_pr := construct_presentation(cs[i], IsomorphismFpGroup(Image(epi)), p, epi);
        p := new_pr;
    od;
    return Image(p);
end;