Read("presentation_constr.g");

check := function(C, G)
    local g, hom, cs, nf, pres, gen_sets, f, p, i, k, n_pres, h, h_pres, new_pres, gens, gen, pr_gens, rels, r, n;
    g := GroupStabChain(C);
    cs := CompositionSeries(g);
    nf := [];
    for i in [1..Length(cs)-1] do
        Add(nf, cs[i] / cs[i+1]);
    od;
    nf := Reversed(nf);
    pres := [];
    gen_sets := [];
    for f in nf do
        p := Image(IsomorphismFpGroup(f));
        Add(pres, p);
        Add(gen_sets, PreImage(IsomorphismFpGroup(f), GeneratorsOfGroup(p)));
    od;
    k := Length(pres);
    h_pres := pres[k];
    h := gen_sets[k];
    for i in [1..k-1] do
        n_pres := pres[k-i];
        n := gen_sets[k-i];
        new_pres := construct_presentation(n, h, n_pres, h_pres, i);
        h_pres := new_pres;
        h := GeneratorsOfGroup(Image(IsomorphismPermGroup(h_pres)));
    od;
    return new_pres;
end;