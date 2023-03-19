Read("schreier_sims.g");

InstallMethod(StabChainOp, [IsPermGroup, IsRecord], function(G, options)
    if not IsBound(options.lasvegas) then TryNextMethod(); fi;
    return stab_chain_las_vegas(GeneratorsOfGroup(G), options.lasvegas);
    end);