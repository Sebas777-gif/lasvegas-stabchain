membership_test := function(C, x) # returns fail or transversal elements giving x
    local L, p;
    L := [];
    while C.generators <> [] do
        p := Position(C.orbit, C.orbit[1]^x);
        if p = fail then return fail; fi;
        Add(L, C.transversal[p]);
        x := x / C.transversal[p];
        C := C.next;
    od;
    if x = () then return Reversed(L);
    else return fail; fi;
end;

extend_sc := function(C, x, B, pos)
    local beta, g, i, extend_orb, orbit_length;

    extend_orb := function(i, x)
        local p;
        p := Position(C.orbit, C.orbit[i]^x);
        if p = fail then
            Add(C.orbit, C.orbit[i]^x);
            Add(C.transversal, C.transversal[i]*x);
        else
            extend_sc(C.next, C.transversal[i]*x / C.transversal[p], B, pos + 1);
        fi;
    end;

    if membership_test(C, x) <> fail then return false; fi;
    if C.generators = [] then # extend chain
        if pos <= Length(B) then beta := B[pos]; else beta := SmallestMovedPointPerm(x); fi;
        C.generators := [x];
        C.orbit := []; C.transversal := []; C.next := rec(generators := []);
        g := ();
        repeat
            Add(C.orbit, beta);
            Add(C.transversal, g);
            beta := beta^x;
            g := g*x;
        until beta = C.orbit[1];
        extend_sc(C.next, g, B, pos+1);
    else # extend orbit
        Add(C.generators, x);
        orbit_length := Length(C.orbit);
        for  i in[1..orbit_length] do
            extend_orb(i, x);
        od;
        i := orbit_length + 1;
        while i <= Length(C.orbit) do
            for g in C.generators do
                extend_orb(i, g);
            od;
            i := i + 1;
        od;
    fi;
    return true;
end;

schreier_sims := function(S, B...)
    local C, x;
    if B <> [] then B := B[1]; fi;
    C := rec(generators := []);
    for x in S do extend_sc(C, x, B, 1); od;
    return C;
end;

pseudo_random := function(w, Y) # generation of pseudo-random element from <w>
    local a, r, s, t, e;
    a := ();
    r := Maximum(11, Length(w));
    # pick two random list elements
    s := Random([1..r]);
    t := Random(Concatenation([1..s-1], [s+1..r]));
    e := Random([-1, 1]); # random choice of product/quotient
    if Random([1, 2]) = 1 then # random product order
        Y[s] := Y[s] * Y[t]^e; # replace one list entry by product
        a := a * Y[s]; # accumulate product
    else
        Y[s] := Y[t]^e * Y[s];
        a := Y[s] * a;
    fi;
    return a;
end;

pseudo_random_init := function(w) # initialize with repititions of the generator set w
    local k, r, i, Y;
    k := Length(w);
    r := Maximum(11, k);
    Y := [];
    for i in [1..k] do
        Y[i] := w[i];
    od;
    for i in [k+1..r] do
        Y[i] := Y[i-k];
    od;
    for i in [1..50] do # 50 is heuristic
        pseudo_random(w, Y); # initial randomization
    od;
    return Y;
end;

random_schreier := function(w, S, B...)
    local C, x, loops_without_extension, Y;
    if B <> [] then B := B[1]; fi;
    C := rec(generators := []);
    loops_without_extension := 0;
    Y := pseudo_random_init(S);
    while loops_without_extension < w do
        x := pseudo_random(S, Y);
        if not extend_sc(C, x, B, 1) then
            loops_without_extension := loops_without_extension + 1;
        else
            loops_without_extension := 0;
        fi;
    od;
    return C;
end;

sanity_check := function(C, G)
    while C.generators <> [] do
        if not ForAll(C.generators,x -> x in G) then return "Generators not in G"; fi;
        if Group(C.generators) <> G then return "Generators don't generate G"; fi;
        if C.transversal[1] <> () then return "Bad first transversal"; fi;
        if Length(C.orbit) <> Length(C.transversal) then return "Not same length"; fi;
        if not ForAll([1..Length(C.orbit)],i -> C.orbit[1]^C.transversal[i] = C.orbit[i]) then 
            return "Transversal wrong";
        fi;
        G := Stabilizer(G, C.orbit[1]);
        C := C.next;
    od;
    if not IsTrivial(G) then return "Doesn't end with trivial group"; fi;
    return true;
end;