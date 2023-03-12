# for a presentation <m|r1> of N = <n> and <h|r2> of G/N, compute a presentation of G = <N, g>,
# where h_i = N g_i
construct_presentation := function(n, g, pr_normal, pr_quotient)
    local m, h, r, r1, r2, r3, r4, new_pr, new_gens, new_rels, f, x, m_names, h_names,
        convert_rel, rho, a, b, i, j;
    m := FreeGeneratorsOfFpGroup(pr_normal);
    r1 := RelatorsOfFpGroup(pr_normal);
    h := FreeGeneratorsOfFpGroup(pr_quotient);
    r2 := RelatorsOfFpGroup(pr_quotient);
    m_names := [];
    h_names := [];
    for x in m do
        Add(m_names, StringFactorizationWord(x));
    od;
    for x in h do
        Add(h_names, StringFactorizationWord(x));
    od;
    f := FreeGroup(Concatenation(m_names, h_names));
    new_gens := FreeGeneratorsOfFpGroup(f);
    new_rels := [];
    # replace occurences of the hi in r with gi if b = 1,
    # replace occurences of elmts of m with the corresponding gens in the new presentation if b = 2,
    # replace occurences of elmts of h with the corresponding gens in the new presentation if b = 3
    convert_rel := function(r, b)
        local w, neutr, z, last_elm, c, k;
        w := StringFactorizationWord(r);
        if b = 1 then
            neutr := ();
        else
            neutr := new_gens[1]^0;
        fi;
        z := neutr;
        last_elm := neutr;
        j := 0;
        while j < Length(w) do
            j := j + 1;
            c := w[j];
            if c = '(' then
                j := j + 1;
                c := w[j];
                while not c = ')' do
                    if b = 1 then
                        for i in [1..Length(h)] do
                            if ReplacedString(String(c), "'", "") = h_names[i] then
                                last_elm := last_elm * g[i];
                                break;
                            fi;
                            if ReplacedString(String(c), "'", "") = UppercaseString(h_names[i]) then
                                last_elm := last_elm / g[i];
                                break;
                            fi;
                        od;
                    fi;
                    if b = 2 then
                    for i in [1..Length(m)] do
                        if ReplacedString(String(c), "'", "") = m_names[i] then
                            last_elm := last_elm * new_gens[i];
                            break;
                        fi;
                        if ReplacedString(String(c), "'", "") = UppercaseString(m_names[i]) then # inverses
                            last_elm := last_elm / new_gens[i];
                            break;
                        fi;
                    od;
                    fi;
                    if b = 3 then
                        for i in [1..Length(h)] do
                            if ReplacedString(String(c), "'", "") = h_names[i] then
                                last_elm := last_elm * new_gens[Length(m) + i];
                                break;
                            fi;
                            if ReplacedString(String(c), "'", "") = UppercaseString(h_names[i]) then # inverses
                                last_elm := last_elm / new_gens[Length(m) + i];
                                break;
                            fi;
                        od;
                    fi;
                    j := j + 1;
                    c := w[j];
                od;
                j := j + 1;
                c := w[j];
                k := Int(ReplacedString(String(c), "'", "")); 
                for i in [1..k] do
                    z := z * last_elm;
                od;
                last_elm := neutr;
                continue;
            fi;
            if IsDigitChar(c) then # handle exponents
                k := Int(ReplacedString(String(c), "'", "")); # why is this so cumbersome
                for i in [1..k-1] do
                    z := z * last_elm;
                od;
                last_elm := neutr;
                continue;
            fi;
            if b = 1 then
                for i in [1..Length(h)] do
                    if ReplacedString(String(c), "'", "") = h_names[i] then
                        z := z * g[i];
                        last_elm := g[i];
                        break;
                    fi;
                    if ReplacedString(String(c), "'", "") = UppercaseString(h_names[i]) then # inverses
                        z := z / g[i];
                        last_elm := g[i]^-1;
                        break;
                    fi;
                od;
            fi;
            if b = 2 then
                for i in [1..Length(m)] do
                    if ReplacedString(String(c), "'", "") = m_names[i] then
                        z := z * new_gens[i];
                        last_elm := new_gens[i];
                        break;
                    fi;
                    if ReplacedString(String(c), "'", "") = UppercaseString(m_names[i]) then # inverses
                        z := z / new_gens[i];
                        last_elm := new_gens[i]^-1;
                        break;
                    fi;
                od;
            fi;
            if b = 3 then
                for i in [1..Length(h)] do
                    if ReplacedString(String(c), "'", "") = h_names[i] then
                        z := z * new_gens[Length(m) + i];
                        last_elm := new_gens[Length(m) + i];
                        break;
                    fi;
                    if ReplacedString(String(c), "'", "") = UppercaseString(h_names[i]) then # inverses
                        z := z / new_gens[Length(m) + i];
                        last_elm := new_gens[Length(m) + i]^-1;
                        break;
                    fi;
                od;
            fi;
        od;
        return z;
    end;
    for r in r1 do
        Add(new_rels, convert_rel(r, 2));
    od;
    rho := function(x)
        local hom, w;
        hom := EpimorphismFromFreeGroup(Group(n):names:=m_names);
        w := PreImagesRepresentative(hom, x);
        return convert_rel(w, 2);
    end;
    r3 := [];
    r4 := [];
    for r in r2 do
        a := convert_rel(r, 3);
        b := convert_rel(r, 1);
        Add(r3, a / rho(b));
    od;
    for i in [1..Length(m)] do
        for j in [1..Length(h)] do
            a := new_gens[i]^new_gens[Length(m) + j];
            b := n[i]^g[j];
            Add(r4, a / rho(b));
        od;
    od;
    return f / Concatenation(new_rels, r3, r4);
end;
