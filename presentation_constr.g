# for a presentation <m|r1> of N = <n> and <h|r2> of G/N, compute a presentation of G = <N, g>,
# where h_i = N g_i
construct_presentation := function(n, g, pr_normal, pr_quotient)
    local m, h, r, r1, r2, r3, r4, new_r, convert_relation, rho, elm, i, j;
    m := FreeGeneratorsOfFpGroup(pr_normal);
    r1 := RelatorsOfFpGroup(pr_normal);
    h := FreeGeneratorsOfFpGroup(pr_quotient);
    r2 := RelatorsOfFpGroup(pr_quotient);
    r3 := [];
    r4 := [];
    convert_relation := function(r) # replace occurences of the hi in r with gi
        local w, z, c;
        w := StringFactorizationWord(r);
        z := ();
        for c in w do
            for i in [1..Length(h)] do
                if c = StringFactorizationWord(h[i]) then
                    z := z * g[i];
                    break;
                fi;
                if c = UppercaseString(StringFactorizationWord(h[i])) then # inverse
                    z := z / g[i];
                    break;
                fi;
            od;
        od;
        return z;
    end;
    rho := function(x)
        return Factorization(pr_normal, x);
    end;
    for r in r2 do
        elm := convert_relation(r);
        Add(r3, r / rho(elm));
    od;
    for i in [1..Length(m)] do
        for j in [1..Length(h)] do
            Add(r4, m[i]^h[j] / rho(n[i]^g[j]));
        od;
    od;
    return Concatenation(h, m) / Concatenation(r1, r3, r4);
end;
