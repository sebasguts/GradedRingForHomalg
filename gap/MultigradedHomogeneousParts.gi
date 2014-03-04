LoadPackage( "4ti2Interface" );
LoadPackage( "ToricIdeals" );
#LoadPackage( "ToricVarieties" );

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

HomogeneousPartOfDegreeZeroOfRing := function( ring, index_localized_variables )
    local degree_group, weight_matrix, degree_group_map, kernel_embedding_of_degree_group,
          matrix_of_kernel, transposed_matrix_of_kernel, list_of_inequalities, i, polytope_of_module,
          list_of_indeterminates_of_ring, generators, generating_set_of_new_ring, relations_of_new_generating_set,
          generating_set_for_ideal, new_ring, a, b, relations_list, indeterminates_of_new_ring, j,
          localized_ring, ideal_for_localized_ring, weights_for_localized_ring, ring_map, indeterminates_old_ring, indeterminates_of_localized_ring,
          new_image;
    
    degree_group := DegreeGroup( ring );
    
    weight_matrix := List( WeightsOfIndeterminates( ring ), UnderlyingListOfRingElements );
    
    degree_group_map := HomalgMap( HomalgMatrix( weight_matrix, HomalgRing( degree_group ) ), "free", degree_group );
    
    kernel_embedding_of_degree_group := KernelEmb( degree_group_map );
    
    matrix_of_kernel := EntriesOfHomalgMatrixAsListList( MatrixOfMap( kernel_embedding_of_degree_group ) );
    
    transposed_matrix_of_kernel := TransposedMat( matrix_of_kernel );
    
    list_of_inequalities := [ ];
    
    list_of_indeterminates_of_ring := Indeterminates( ring );
    
    for i in [ 1 .. Length( list_of_indeterminates_of_ring ) ] do
        
        if not i in index_localized_variables then
            
            Add( list_of_inequalities, transposed_matrix_of_kernel[ i ] );
            
        fi;
        
    od;
    
    list_of_inequalities := List( list_of_inequalities, i -> Concatenation( [ 0 ], i ) );
    
    polytope_of_module := PolytopeByInequalities( list_of_inequalities );
    
    generators := LatticePointsGenerators( polytope_of_module );
    
    generators := Concatenation( generators[ 2 ], generators[ 3 ], -generators[ 3 ] );
    
#     if Length( generators ) = 0 then
#         
#         generators := LatticePointsGenerators( polytope_of_module )[ 1 ];
#         
#     fi;
    
    generating_set_of_new_ring := generators * matrix_of_kernel;
    
    relations_of_new_generating_set := KernelEmb( HomalgMap( HomalgMatrix( generating_set_of_new_ring, HomalgRing( degree_group ) ), "free"  ) );
    
    relations_of_new_generating_set := EntriesOfHomalgMatrixAsListList( MatrixOfMap( relations_of_new_generating_set ) );
    
    if Length( relations_of_new_generating_set ) > 0 then
        
        generating_set_for_ideal := HOMALG_GRADED_RING!.groebner_basis_function_for_binomial_ideals( relations_of_new_generating_set );
        
    else
        
        generating_set_for_ideal := [ ];
        
    fi;
    
    if Length( generating_set_of_new_ring ) > 0 then
        
        new_ring := UnderlyingNonGradedRing( CoefficientsRing( ring ) ) * Concatenation( "x1..", String( Length( generating_set_of_new_ring ) ) );
        
    else
        
        new_ring := CoefficientsRing( ring );
        
    fi;
    
    new_ring!.generators_as_module_elements := generating_set_of_new_ring;
    
    indeterminates_of_new_ring := Indeterminates( new_ring );
    
    relations_list := [ ];
    
    for i in generating_set_for_ideal do
        
        a := "1";
        
        b := "1";
        
        for j in [ 1 .. Length( i ) ] do
            
            if i[ j ] < 0 then
                
                b := JoinStringsWithSeparator( [ b, JoinStringsWithSeparator( [ indeterminates_of_new_ring[ j ], - i[ j ] ], "^" ) ], "*" );
                
            elif i[ j ] > 0 then
                
                a := JoinStringsWithSeparator( [ a, JoinStringsWithSeparator( [ indeterminates_of_new_ring[ j ], i[ j ] ], "^" ) ], "*" );
                
            fi;
            
        od;
        
        Add( relations_list, Concatenation( a, "-", b ) );
        
    od;
    
    if Length( relations_list ) > 0 then
        
        new_ring := new_ring / relations_list;
        
    fi;
    
    # SetWeightsOfIndeterminates( new_ring, List( indeterminates_of_new_ring, i -> 0 ) );
    
    new_ring!.generators_as_module_elements := generating_set_of_new_ring;
    
    new_ring!.abstract_generators := generators;
    
    ## construct the localized ring
    
    localized_ring := List( Indeterminates( ring ), String );
    
    ideal_for_localized_ring := [ ];
    
    indeterminates_old_ring := Indeterminates( ring );
    
    for i in index_localized_variables do
        
        Add( localized_ring, Concatenation( String( indeterminates_old_ring[ i ] ), "_" ) );
        
        Add( ideal_for_localized_ring, Concatenation( String( indeterminates_old_ring[ i ] ), "*", String( indeterminates_old_ring[ i ] ), "_-1" ) );
        
    od;
    
    localized_ring := JoinStringsWithSeparator( localized_ring, "," );
    
    localized_ring := CoefficientsRing( ring )*localized_ring;
    
    if Length( index_localized_variables ) > 0 then
        
        localized_ring := localized_ring / ideal_for_localized_ring;
        
    fi;
    
    indeterminates_of_localized_ring := Indeterminates( localized_ring );
    
    ring_map := [ ];
    
    for i in generating_set_of_new_ring do
        
        new_image := "";
        
        for j in [ 1 .. Length( i ) ] do
            
            if i[ j ] >= 0 then
                
                new_image := Concatenation( new_image, "*", String( indeterminates_of_localized_ring[ j ] ), "^", String( i[ j ] ) );
                
            else
                
                new_image := Concatenation( new_image, "*",
                                            String( indeterminates_of_localized_ring[ Position( index_localized_variables, j ) + Length( i ) ] ),
                                            "^", String( i[ j ] ) );
                
            fi;
        od;
        
        Add( ring_map, new_image );
        
    od;
    
    ring_map := RingMap( ring_map, new_ring, localized_ring );
    
    new_ring!.embedding_in_localized_ring := ring_map;
    
    return new_ring;
    
end;


HomogeneousPartOfRing := function( ring, index_localized_variables, degree )
  local degree_as_intlist, hom_part_of_degree_zero, degree_group, weight_matrix, transposed_weight_matrix, degree_group_map, kernel_embedding_of_degree_group,
        matrix_of_kernel, transposed_matrix_of_kernel, list_of_inequalities, list_of_indeterminates_of_ring,
        inequalities_list_for_preimage, i, current_inequality, preimage_polytope, preimage_polytope_lattice_points, preimage_of_degree,
        module_polytope, module_polytope_lattice_points, generators_of_module, presentation_matrix, k,l, relation_matrix, relation_polytope_a,
        relation_polytope_b, relation_polytope, relation_polytope_lattice_points, inequalities_for_ring_cone, relation_matrix_entry, current_relation,
        indeterminates_of_new_ring, current_relation_a, current_relation_b, a, b, relation_inequality, nr_generators_hom_zero, solution_polytope_relation,
        abstract_generators_of_degree_zero, transposed_abstract_generators_of_degree_zero, solution_polytope, solution_of_equation_of_relation,
        nr_of_relations, map_of_module, cokernel;
        
    
    ## First part, look search one element with the desired degree
    
    hom_part_of_degree_zero := HomogeneousPartOfDegreeZeroOfRing( ring, index_localized_variables );
    
    degree_group := DegreeGroup( ring );
    
    weight_matrix := List( WeightsOfIndeterminates( ring ), UnderlyingListOfRingElements );
    
    transposed_weight_matrix := TransposedMat( weight_matrix );
    
    degree_group_map := HomalgMap( HomalgMatrix( weight_matrix, HomalgRing( degree_group ) ), "free", degree_group );
    
    list_of_indeterminates_of_ring := Indeterminates( ring );
    
    inequalities_list_for_preimage := [ ];
    
    if IsHomalgElement( degree ) then
        
        degree_as_intlist := UnderlyingListOfRingElements( degree );
        
    elif IsInt( degree ) then
        
        degree_as_intlist := [ degree ];
        
    else
        
        degree_as_intlist := degree;
        
    fi;
    
    for i in [ 1 .. Length( transposed_weight_matrix ) ] do
        
        Add( inequalities_list_for_preimage, Concatenation( [ - degree_as_intlist[ i ] ], transposed_weight_matrix[ i ] ) );
        
        Add( inequalities_list_for_preimage, Concatenation( [ degree_as_intlist[ i ] ], - transposed_weight_matrix[ i ] ) );
        
    od;
    
    for i in [ 1 ..  Length( list_of_indeterminates_of_ring ) ] do
        
        if not i in index_localized_variables then
            
            current_inequality := List( [ 1 .. Length( list_of_indeterminates_of_ring ) + 1 ], k -> 0 );
            
            current_inequality[ i + 1 ] := 1;
            
            Add( inequalities_list_for_preimage, current_inequality );
            
        fi;
        
    od;
    
    preimage_polytope := PolytopeByInequalities( inequalities_list_for_preimage );
    
    preimage_polytope_lattice_points := LatticePointsGenerators( preimage_polytope );
    
    if Length( preimage_polytope_lattice_points[ 1 ] ) = 0 then
        
        return ZeroLeftModule( hom_part_of_degree_zero );
        
    fi;
    
    preimage_of_degree := preimage_polytope_lattice_points[ 1 ][ 1 ];
    
    degree_group_map := HomalgMap( HomalgMatrix( weight_matrix, HomalgRing( degree_group ) ), "free", degree_group );
    
    kernel_embedding_of_degree_group := KernelEmb( degree_group_map );
    
    matrix_of_kernel := EntriesOfHomalgMatrixAsListList( MatrixOfMap( kernel_embedding_of_degree_group ) );
    
    transposed_matrix_of_kernel := TransposedMat( matrix_of_kernel );
    
    list_of_inequalities := [ ];
    
    for i in [ 1 .. Length( list_of_indeterminates_of_ring ) ] do
        
        if not i in index_localized_variables then
            
            Add( list_of_inequalities, Concatenation( [ preimage_of_degree[ i ] ], transposed_matrix_of_kernel[ i ] ) );
            
        fi;
        
    od;
    
    module_polytope := PolytopeByInequalities( list_of_inequalities );
    
    module_polytope_lattice_points := LatticePointsGenerators( module_polytope );
    
    module_polytope_lattice_points := module_polytope_lattice_points[ 1 ];
    
    generators_of_module := module_polytope_lattice_points;
    
    inequalities_for_ring_cone := hom_part_of_degree_zero!.abstract_generators;
    
    relation_matrix := [];
    
    if Length( inequalities_for_ring_cone ) > 0 then
        
        inequalities_for_ring_cone := Cone( inequalities_for_ring_cone );
        
        inequalities_for_ring_cone := DefiningInequalities( inequalities_for_ring_cone );
        
        indeterminates_of_new_ring := Indeterminates( hom_part_of_degree_zero );
        
        nr_generators_hom_zero := Length( hom_part_of_degree_zero!.abstract_generators );
        
        relation_inequality := List( [ 1 .. nr_generators_hom_zero ], i -> List( [ 1 .. nr_generators_hom_zero + 1 ], j -> 0 ) );
        
        for i in [ 2 .. nr_generators_hom_zero + 1 ] do
            
            relation_inequality[ i - 1 ][ i ] := 1;
            
        od;
        
        abstract_generators_of_degree_zero := hom_part_of_degree_zero!.abstract_generators;
        
        transposed_abstract_generators_of_degree_zero := TransposedMat( abstract_generators_of_degree_zero );
        
        for k in [ 1 .. Length( generators_of_module ) ] do
            
            for l in [ k + 1 .. Length( generators_of_module ) ] do
                
                relation_polytope := [ ];
                
                for i in inequalities_for_ring_cone do
                    
                    Add( relation_polytope, Concatenation( [ - Maximum( i * generators_of_module[ k ], i * generators_of_module[ l ] ) ], i ) );
                    
                od;
                
                relation_polytope := PolytopeByInequalities( relation_polytope );
                
                relation_polytope_lattice_points := LatticePointsGenerators( relation_polytope )[ 1 ];
                
                if Length( relation_polytope_lattice_points ) = 0 then
                    
                    continue;
                    
                fi;
                
                for current_relation in relation_polytope_lattice_points do
                    
                    relation_matrix_entry := [ ];
                    
                    for i in [ 1 .. k - 1 ] do
                        
                        Add( relation_matrix_entry, "0" );
                        
                    od;
                    
                    current_relation_a := current_relation - generators_of_module[ k ];
                    
                    solution_polytope_relation := [ ];
                    
                    for a in [ 1 .. Length( current_relation_a ) ] do
                        
                        Add( solution_polytope_relation, Concatenation( [ - current_relation_a[ a ] ], transposed_abstract_generators_of_degree_zero[ a ] ) );
                        
                        Add( solution_polytope_relation, Concatenation( [ current_relation_a[ a ] ], - transposed_abstract_generators_of_degree_zero[ a ] ) );
                        
                    od;
                    
                    solution_polytope := PolytopeByInequalities( Concatenation( solution_polytope_relation, relation_inequality ) );
                    
                    solution_of_equation_of_relation := LatticePointsGenerators( solution_polytope )[ 1 ];
                    
                    if Length( solution_of_equation_of_relation ) = 0 then
                        
                        Error( "This should not happen" );
                        
                    fi;
                    
                    solution_of_equation_of_relation := solution_of_equation_of_relation[ 1 ];
                    
                    Add( relation_matrix_entry, JoinStringsWithSeparator( 
                                                List( [ 1 .. Length( solution_of_equation_of_relation ) ],
                                                      i -> JoinStringsWithSeparator( [ indeterminates_of_new_ring[ i ], solution_of_equation_of_relation[ i ] ], 
                                                                                      "^" ) ), "*" ) );
                    
                    for i in [ k + 1 .. l - 1 ] do
                        
                        Add( relation_matrix_entry, "0" );
                        
                    od;
                    
                    current_relation_a := current_relation - generators_of_module[ l ];
                    
                    solution_polytope_relation := [ ];
                    
                    for a in [ 1 .. Length( current_relation_a ) ] do
                        
                        Add( solution_polytope_relation, Concatenation( [ - current_relation_a[ a ] ], transposed_abstract_generators_of_degree_zero[ a ] ) );
                        
                        Add( solution_polytope_relation, Concatenation( [ current_relation_a[ a ] ], - transposed_abstract_generators_of_degree_zero[ a ] ) );
                        
                    od;
                    
                    solution_polytope := PolytopeByInequalities( Concatenation( solution_polytope_relation, relation_inequality ) );
                    
                    solution_of_equation_of_relation := LatticePointsGenerators( solution_polytope )[ 1 ];
                    
                    if Length( solution_of_equation_of_relation ) = 0 then
                        
                        Error( "This should not happen" );
                        
                    fi;
                    
                    solution_of_equation_of_relation := solution_of_equation_of_relation[ 1 ];
                    
                    Add( relation_matrix_entry, JoinStringsWithSeparator(
                                                List( [ 1 .. Length( solution_of_equation_of_relation ) ],
                                                      i -> JoinStringsWithSeparator( [ indeterminates_of_new_ring[ i ], solution_of_equation_of_relation[ i ] ], 
                                                                                      "^" ) ), "*" ) );
                    
                    for i in [ l + 1 .. Length( generators_of_module ) ] do
                        
                        Add( relation_matrix_entry, "0" );
                        
                    od;
                    
                od;
                
                Add( relation_matrix, JoinStringsWithSeparator( relation_matrix_entry, "," ) );
                
            od;
            
        od;
        
    fi;
    
    nr_of_relations := Length( relation_matrix );
    
    relation_matrix := JoinStringsWithSeparator( relation_matrix, "," );
    
    relation_matrix := Concatenation( "[", relation_matrix, "]" );
    
    if nr_of_relations = 0 then
        
        relation_matrix := HomalgZeroMatrix( 0, Length( generators_of_module ), hom_part_of_degree_zero );
        
    else
        
        relation_matrix := HomalgMatrix( relation_matrix, nr_of_relations, Length( generators_of_module ), hom_part_of_degree_zero );
        
    fi;
    
    map_of_module := HomalgMap( relation_matrix, "free", hom_part_of_degree_zero );
    
    return map_of_module;
    
end;