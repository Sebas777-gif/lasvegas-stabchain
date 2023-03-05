# for a presentation <m|r1> of N = <n> and <h|r2> of G/N, compute a presentation of G = <N, g>
construct_presentation := function(n, g, m, h, r1, r2)
    local r, r3, r4;
    r3 := [];
    r4 := [];
    for r in r2 do
        Append(r3, r(h) / UnderlyingElement(r(g)))
    od;
    for i in [1..Length(m)] do
        for j in [1..Length(h)] do
            Append(r4, m[i]^h[j] / UnderlyingElement(n[i]^g[j]))
        od;
    od;
    return Concatenation(h, m) / Concatenation(r1, r3, r4);
end;
