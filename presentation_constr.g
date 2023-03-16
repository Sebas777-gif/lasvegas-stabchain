gen_to_char := function(i)
    # avoid '(', ')', '^', numerical characters and the character reversed for inversion
    # we are assuming (or rather hoping) that there are no more than 242 generators
    if i < 40 then
        return CharInt(i);
    fi;
    if i < 46 then
        return CharInt(i + 2);
    fi;
    if i < 82 then
        return CharInt(i + 12);
    fi;
    return CharInt(i + 13);
end;

char_to_gen := function(c)
    local i;
    i := IntChar(c);
    if i < 40 then
        return i;
    fi;
    if i < 48 then
        return i - 2;
    fi;
    if i < 94 then
        return i - 12;
    fi;
    return i - 13;
end;

# for a presentation <m|r1> of N = <n> and <h|r2> of G/N, compute a presentation of G = <N, g>,
# where h_i = N g_i
# iter specifies the character used for the generator names, i.e. 1 -> A, 2 -> B, etc.
construct_presentation := function(n, g, pr_normal, pr_quotient, iter)
    local m, h, r, r1, r2, r3, r4, new_pr, new_gens, new_rels, f, x, m_names, h_names, g_names, new_gen_names,
        rho, a, b, i, j, convert_rel, ind, ind2;
    m := FreeGeneratorsOfFpGroup(pr_normal);
    r1 := RelatorsOfFpGroup(pr_normal);
    h := FreeGeneratorsOfFpGroup(pr_quotient);
    r2 := RelatorsOfFpGroup(pr_quotient);
    m_names := [];
    h_names := [];
    new_gen_names := [];
    g_names := [];
    for x in m do
        Add(m_names, StringFactorizationWord(x));
    od;
    for x in h do
        Add(h_names, StringFactorizationWord(x));
    od;
    for i in [1..Length(m)+Length(h)] do
        Add(new_gen_names, [gen_to_char(i)]);
    od;
    for x in g do
        Add(g_names, String(x));
    od;
    f := FreeGroup(Length(m) + Length(h) : generatorNames := [CharInt(64+iter)]);
    new_gens := FreeGeneratorsOfFpGroup(f);
    # replace occurences of the elmts of to_be_repl with elmts of repl_with
    convert_rel := function(r, to_be_repl, repl_with, b)
        local w, v, s, z, last_elm, c, k, exp, j;
        if b then
            w := StringFactorizationWord(r);
        else
            w := String(r);
        fi;
        if w = "<identity>" then
            if b then
                return new_gens[1]^0;
            fi;
            return ();
        fi;
        for i in [1..Length(to_be_repl)] do
            s := to_be_repl[i];
            v := ReplacedString(w, s, repl_with[i]);
            w := v;
            if b then # generator word
                v := ReplacedString(w, LowercaseString(s), Concatenation(repl_with[i], [CharInt(255)]));
            else # permutation
                v := ReplacedString(w, LowercaseString(s), Concatenation("(", String(g[i]^-1), ")"));
            fi;
            w := v;
        od;
        if b then
            z := new_gens[1]^0;
            last_elm := new_gens[1]^0;
            i := 0;
            while i < Length(w) do
                i := i + 1;
                c := w[i];
                if c = '(' then
                    i := i + 1;
                    c := w[i];
                    while not c = ')' do
                        if i < Length(w) and w[i+1] = CharInt(255) then # inverse
                            last_elm := last_elm / new_gens[char_to_gen(c)];
                            i := i + 1;
                        else
                            last_elm := last_elm * new_gens[char_to_gen(c)];
                        fi;
                        i := i + 1;
                        c := w[i];
                    od;
                    i := i + 1;
                    k := [w[i]];
                    while i < Length(w) and IsDigitChar(w[i+1]) do
                        Add(k, w[i]);
                        i := i + 1;
                    od;
                    exp := Int(k);
                    for j in [1..exp] do
                        z := z * last_elm;
                    od;
                    last_elm := new_gens[1]^0;
                fi;
                if IsDigitChar(c) then
                    k := [c];
                    while i < Length(w) and IsDigitChar(w[i+1]) do
                        Add(k, w[i+1]);
                        i := i + 1;
                    od;
                    exp := Int(k);
                    for j in [1..exp-1] do
                        z := z * last_elm;
                    od;
                    last_elm := new_gens[1]^0;
                    if i = Length(w) then
                        return z;
                    fi;
                else 
                    if i < Length(w) and w[i+1] = CharInt(255) then # inverse
                        z := z / new_gens[char_to_gen(c)];
                        last_elm := new_gens[char_to_gen(c)]^-1;
                        i := i + 1;
                    else
                        z := z * new_gens[char_to_gen(c)];
                        last_elm := new_gens[char_to_gen(c)];
                    fi;
                fi;
            od;
            return z;
        fi;
        return EvalString(w);
    end;
    new_rels := [];
    for r in r1 do
        Add(new_rels, convert_rel(r, m_names, new_gen_names{[1..Length(m)]}, true));
    od;
    rho := function(x)
        local hom, w;
        hom := EpimorphismFromFreeGroup(Group(n):names:=m_names);
        w := PreImagesRepresentative(hom, x);
        return convert_rel(w, m_names, new_gen_names{[1..Length(m)]}, true);
    end;
    r3 := [];
    r4 := [];
    for r in r2 do
        a := convert_rel(r, h_names, new_gen_names{[Length(m)+1..Length(m)+Length(h)]}, true);
        b := convert_rel(r, h_names, g_names, false);
        Add(r3, a / rho(b));
    od;
    for ind in [1..Length(m)] do
        for ind2 in [1..Length(h)] do
            a := new_gens[ind]^new_gens[Length(m) + ind2];
            b := n[ind]^g[ind2];
            Add(r4, a / rho(b));
        od;
    od;
    return f / Concatenation(new_rels, r3, r4);
end;
