LoadPackage( "4ti2Interface" );
LoadPackage( "ToricIdeals" );
LoadPackage( "ToricVarieties" );

if IsPackageMarkedForLoading( "4ti2Interface", ">=2013.03.19" ) then
    
    Print( "4ti2 is used for groebner basis.\n" );
    
    HOMALG_GRADED_RING.groebner_basis_function_for_binomial_ideals := 4ti2Interface_groebner_basis;

elif IsPackageMarkedForLoading( "ToricIdeals", ">=2011.01.01" ) then
    
    Print( "ToricIdeals is used for groebner basis.\n" );
    
    HOMALG_GRADED_RING.groebner_basis_function_for_binomial_ideals := GensetForToricIdeal;
    
elif IsPackageMarkedForLoading( "ToricVarieties", ">=2012.11.07" ) then
    
    Print( "ToricVarieties fallback method is used for groebner basis.\n" );
    
    HOMALG_GRADED_RING.groebner_basis_function_for_binomial_ideals := GeneratingSetOfToricIdealGivenByHilbertBasis;
    
else
    
    LogPackageLoadingMessage( PACKAGE_WARNING,
        [
           "No method to compute groebner basis of lattice ideal.\n",
           "Computation of homogeneous part will not work.\n"
        ] );
    
fi;

HomogeneousPartOfDegreeZeroOfRing := function( ring )
    local deg_group, weight_matrix,
          deg_group_projection, kernel_embedding, entries_of_kernel_matrix,
          monomial_cone, hilbert_basis_of_monomial_cone, hilbert_basis_of_monomial_cone_matrix,
          relations_of_hilbert_basis, number_of_variables, new_ring, variables,
          a, b, k, i, j, image_of_hilbert_basis, ring_map;  
    
    deg_group := DegreeGroup( ring );
    
    weight_matrix := WeightsOfIndeterminates( ring );
    
    weight_matrix := List( weight_matrix, UnderlyingListOfRingElementsInCurrentPresentation );
    
    weight_matrix := HomalgMatrix( weight_matrix, HomalgRing( deg_group ) );
    
    deg_group_projection := HomalgMap( weight_matrix, "free", deg_group );
    
    kernel_embedding := KernelEmb( deg_group_projection );
    
    entries_of_kernel_matrix := EntriesOfHomalgMatrixAsListList( Involution( MatrixOfMap( kernel_embedding ) ) );
    
    monomial_cone := ConeByInequalities( entries_of_kernel_matrix );
    
    hilbert_basis_of_monomial_cone := HilbertBasis( monomial_cone );
    
    hilbert_basis_of_monomial_cone_matrix := HomalgMatrix( hilbert_basis_of_monomial_cone, HomalgRing( deg_group ) );
    
    relations_of_hilbert_basis := EntriesOfHomalgMatrixAsListList( SyzygiesGeneratorsOfRows( hilbert_basis_of_monomial_cone_matrix ) );
    
    number_of_variables := Length( hilbert_basis_of_monomial_cone );
    
    new_ring := GradedRing( CoefficientsRing( ring ) * Concatenation( "x1..", String( number_of_variables ) ) );
    
    SetDegreeGroup( new_ring, deg_group );
    
    SetWeightsOfIndeterminates( new_ring, List( [ 1 .. number_of_variables ], i -> TheZeroElement( deg_group ) ) );
    
    variables := Indeterminates( new_ring );
    
    if relations_of_hilbert_basis <> [ ] then
        
        relations_of_hilbert_basis := HOMALG_GRADED_RING.groebner_basis_function_for_binomial_ideals( relations_of_hilbert_basis );
        
        if Length( relations_of_hilbert_basis ) > 0 then
            
            k := Length( relations_of_hilbert_basis );
            
            for i in [ 1 .. k ] do
                
                a := "1";
                
                b := "1";
                
                for j in [ 1 .. Length( variables ) ] do
                    
                    if relations_of_hilbert_basis[ i ][ j ] < 0 then
                        
                        b := JoinStringsWithSeparator( [ b , JoinStringsWithSeparator( [ variables[ j ], String( - relations_of_hilbert_basis[ i ][ j ] ) ], "^" ) ], "*" );
                        
                    elif relations_of_hilbert_basis[ i ][ j ] > 0 then
                        
                        a := JoinStringsWithSeparator( [ a, JoinStringsWithSeparator( [ variables[ j ], String( relations_of_hilbert_basis[ i ][ j ] ) ], "^" ) ], "*" );
                        
                    fi;
                    
                od;
                
                relations_of_hilbert_basis[ i ] := JoinStringsWithSeparator( [ a, b ], "-" );
                
                relations_of_hilbert_basis[ i ] := HomalgRingElement( relations_of_hilbert_basis[ i ], new_ring );
                
            od;
            
            new_ring := new_ring / relations_of_hilbert_basis;
            
        fi;
        
    fi;
    
    image_of_hilbert_basis := EntriesOfHomalgMatrixAsListList( hilbert_basis_of_monomial_cone_matrix * MatrixOfMap( kernel_embedding ) );
    
    variables := Indeterminates( ring );
    
    k := Length( variables );
    
    ring_map := [ ];
    
    for i in image_of_hilbert_basis do
        
        a := "1";
        
        for j in [ 1 .. k ] do
            
            a := JoinStringsWithSeparator( [ a, JoinStringsWithSeparator( [ variables[ j ], String( i[ j ] ) ], "^" ) ], "*" );
            
        od;
        
        Add( ring_map, HomalgRingElement( a, ring ) );
        
    od;
    
    return RingMap( ring_map, new_ring, ring );
    
end;


HomogeneousPartOfRingAsDegreeZeroModule := function( ring, degree )
  local S_0, deg_group, weight_matrix, deg_group_projection, kernel_embedding,
        entries_of_kernel_matrix;
    
    S_0 := HomogeneousPartOfDegreeZeroOfRing( ring );
    
    deg_group := DegreeGroup( ring );
    
    weight_matrix := WeightsOfIndeterminates( ring );
    
    weight_matrix := List( weight_matrix, UnderlyingListOfRingElementsInCurrentPresentation );
    
    weight_matrix := HomalgMatrix( weight_matrix, HomalgRing( deg_group ) );
    
    deg_group_projection := HomalgMap( weight_matrix, "free", deg_group );
    
    if not IsHomalgElement( degree ) then
        
        degree := HomalgModuleElement( degree, DegreeGroup );
        
    fi;
    
    
    
    kernel_embedding := KernelEmb( deg_group_projection );
    
    entries_of_kernel_matrix := EntriesOfHomalgMatrixAsListList( Involution( MatrixOfMap( kernel_embedding ) ) );
    
end;