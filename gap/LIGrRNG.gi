#############################################################################
##
##  LIGrRNG.gi                  LIGrRNG subpackage           Mohamed Barakat
##                                                    Markus Lange-Hegermann
##
##         LIGrRNG = Logical Implications for homalg GRaded RiNGs
##
##  Copyright 2010, Mohamed Barakat, University of Kaiserslautern
##           Markus Lange-Hegermann, RWTH-Aachen University
##
##  Implementations for the LIGrRNG subpackage.
##
#############################################################################

####################################
#
# global variables:
#
####################################

# a central place for configuration variables:

InstallValue( LIGrRNG,
        rec(
            color := "\033[4;30;46m",
            intrinsic_properties := LIRNG.intrinsic_properties,
            intrinsic_attributes := [
                                     "KrullDimension",
                                     "Characteristic"
                                     ],
            ringelement_attributes := [
                                       RationalParameters,
                                       IndeterminateCoordinatesOfRingOfDerivations,
                                       IndeterminateDerivationsOfRingOfDerivations,
                                       IndeterminateAntiCommutingVariablesOfExteriorRing,
                                       IndeterminateAntiCommutingVariablesOfExteriorRing,
                                       IndeterminatesOfExteriorRing,
                                       IndeterminatesOfPolynomialRing
                                       ]
            )
        );

##
Append( LIGrRNG.intrinsic_properties,
        [ 
          ] );

##
Append( LIGrRNG.intrinsic_attributes,
        [ 
          ] );

####################################
#
# immediate methods for properties:
#
####################################

##
InstallImmediateMethodToPullPropertiesOrAttributes(
        IsHomalgGradedRingRep,
        IsHomalgGradedRingRep,
        LIGrRNG.intrinsic_properties,
        Concatenation( LIGrRNG.intrinsic_properties, LIGrRNG.intrinsic_attributes ),
        UnderlyingNonGradedRing );

####################################
#
# immediate methods for attributes:
#
####################################

##
InstallImmediateMethodToPullPropertiesOrAttributes(
        IsHomalgGradedRingRep,
        IsHomalgGradedRingRep,
        LIGrRNG.intrinsic_attributes,
        Concatenation( LIGrRNG.intrinsic_properties, LIGrRNG.intrinsic_attributes ),
        UnderlyingNonGradedRing );

##
InstallImmediateMethod( IsZero,
        IsHomalgGradedRingElementRep and HasDegreeOfRingElement, 0,
        
  function( r )
    local zero;
    
    zero := Zero( r );
    
    if HasDegreeOfRingElement( zero ) and
       DegreeOfRingElement( r ) <> DegreeOfRingElement( zero ) then
        return false;
    fi;
    
    TryNextMethod( );
    
end );

##
InstallImmediateMethod( IsOne,
        IsHomalgGradedRingElementRep and HasDegreeOfRingElement, 0,
        
  function( r )
    local one;
    
    one := One( r );
    
    if HasDegreeOfRingElement( one ) and
       DegreeOfRingElement( r ) <> DegreeOfRingElement( one ) then
        return false;
    fi;
    
    TryNextMethod( );
    
end );

##
InstallImmediateMethod( IsMinusOne,
        IsHomalgGradedRingElementRep and HasDegreeOfRingElement, 0,
        
  function( r )
    local one;
    
    one := One( r );	## One( r ) is not a mistake
    
    if HasDegreeOfRingElement( one ) and
       DegreeOfRingElement( r ) <> DegreeOfRingElement( one ) then
        return false;
    fi;
    
    TryNextMethod( );
    
end );

####################################
#
# methods for attributes:
#
####################################

##
InstallGlobalFunction( HelperToInstallMethodsForGradedRingElementsAttributes,
  function( L )
    local GRADEDRING_prop;
    
    for GRADEDRING_prop in L do
        
        InstallMethod( GRADEDRING_prop,
                "for homalg graded rings",
                [ IsHomalgGradedRingRep ],
                
          function( S )
            local indets;
            
            indets := GRADEDRING_prop( UnderlyingNonGradedRing( S ) );
            
            return List( indets, x -> GradedRingElement( x, S ) );
            
        end );
        
    od;
    
end );

## invoke it
HelperToInstallMethodsForGradedRingElementsAttributes( LIGrRNG.ringelement_attributes );

##
InstallMethod( Zero,
        "for homalg graded rings",
        [ IsHomalgGradedRingRep ],
        
  function( S )
    
    return GradedRingElement( Zero( UnderlyingNonGradedRing( S ) ), S );
    
end );

##
InstallMethod( DegreeOfRingElementFunction,
        "for homalg rings",
        [ IsHomalgGradedRing ],
        
  function( S )
    local degreehelpfunction, degreehelper, weights, degrees, gens;
    
    weights := WeightsOfIndeterminates( S );
    
    if NrGenerators( DegreeGroup( S ) ) > 1 then
        
        degreehelpfunction := DegreeOfRingElementFunction(
                       UnderlyingNonGradedRing( S ),
                       MatrixOfWeightsOfIndeterminates( S )
                       );
        
        return function( elm )
            local degreeofelem;
            degreeofelem := GeneratingElements( DegreeGroup( S ) ) * degreehelpfunction( elm );
            return degreeofelem[1];
        end;
        
    fi;
    
    degrees := List( weights, UnderlyingListOfRingElements );
    
    if degrees = [ ] then
        Error( "empty list of weights\n" );
    fi;
    
    if Length( degrees[1] ) = 1 then
        
        degrees := Flat( degrees );
        
    fi;
    
    degreehelpfunction := DegreeOfRingElementFunction(
                   UnderlyingNonGradedRing( S ),
                   degrees
                   );
    
    return function( elm )
        local degreeofelem;
        degreeofelem := GeneratingElements( DegreeGroup( S ) ) * degreehelpfunction( elm );
        return degreeofelem[1];
    end;
    
end );

##
InstallMethod( DegreeOfRingElement,
        "for homalg rings elements",
        [ IsHomalgGradedRingElement ],
        
  function( r )
    
    return DegreeOfRingElementFunction( HomalgRing( r ) )( UnderlyingNonGradedRingElement( r ) );
    
end );

##
InstallMethod( DegreesOfEntriesFunction,
        "for homalg graded rings",
        [ IsHomalgGradedRing ],
        
  function( S )
    local A, degree_help_function, degrees, i, j;
    
    A := DegreeGroup( S );
    
    if NrGenerators( A ) > 1 then
        
        degree_help_function :=
          DegreesOfEntriesFunction(
                  UnderlyingNonGradedRing( S ),
                    MatrixOfWeightsOfIndeterminates( S )
                    );
        
        return function( mat )
            return
              List(
                   degree_help_function( mat ),
                     j -> List( List( j, i -> GeneratingElements( A ) * i ), k -> k[1] ) );
            end;
        
    fi;
    
    degrees := List( WeightsOfIndeterminates( S ), UnderlyingListOfRingElements );
    
    if degrees = [ ] then
        Error( "empty list of weights\n" );
    fi;
    
    if Length( degrees[1] ) = 1 then
        
        degrees := Flat( degrees );
        
    fi;
    
    degree_help_function :=
      DegreesOfEntriesFunction(
              UnderlyingNonGradedRing( S ),
                degrees
                );
    
    return function( mat )
        return
          List(
               degree_help_function( mat ),
                 j -> List( List( j, i -> GeneratingElements( A ) * i ) , k -> k[1] ) );
        end;
    
end );

##
InstallMethod( NonTrivialDegreePerRowWithColPositionFunction,
        "for homalg graded rings",
        [ IsHomalgGradedRing ],
        
  function( S )
    local degrees, degree_of_zero, degree_of_one, generators_of_degree_group,
          degree_help_function;
    
    degrees := List( WeightsOfIndeterminates( S ), UnderlyingListOfRingElements );
    
    if Length( degrees[ 1 ] ) = 1 then
        
        degrees := Flat( degrees );
        
    fi;
    
    degree_of_zero := DegreeOfRingElement( Zero( S ) );
    
    degree_of_zero := UnderlyingListOfRingElements( degree_of_zero );
    
    degree_of_one := DegreeOfRingElement( One( S ) );
    
    generators_of_degree_group := GeneratingElements( DegreeGroup( S ) );
    
    degree_help_function :=
      NonTrivialDegreePerRowWithColPositionFunction(
              UnderlyingNonGradedRing( S ),
                degrees,
                degree_of_zero,
                degree_of_one
                );
    
    return function( mat )
        return
          List( List(
                  degree_help_function( mat ),
                    j ->  j * generators_of_degree_group ), i -> i[1] );
        end;
    
end );

##
InstallMethod( NonTrivialDegreePerColumnWithRowPositionFunction,
        "for homalg graded rings",
        [ IsHomalgGradedRing ],
        
  function( S )
    local degrees, degree_of_zero, degree_of_one, generators_of_degree_group,
          degree_help_function;
    
    degrees := List( WeightsOfIndeterminates( S ), UnderlyingListOfRingElements );
    
    if Length( degrees[ 1 ] ) = 1 then
        
        degrees := Flat( degrees );
        
    fi;
    
    degree_of_zero := DegreeOfRingElement( Zero( S ) );
    
    degree_of_zero := UnderlyingListOfRingElements( degree_of_zero );
    
    degree_of_one := DegreeOfRingElement( One( S ) );
    
    generators_of_degree_group := GeneratingElements( DegreeGroup( S ) );
    
    degree_help_function :=
      NonTrivialDegreePerColumnWithRowPositionFunction(
              UnderlyingNonGradedRing( S ),
                degrees,
                degree_of_zero,
                degree_of_one
                );
    
    return function( mat )
        return
          List( List(
                  degree_help_function( mat ),
                    j ->  j * generators_of_degree_group ), i -> i[1] );
        end;
    
end );

##
InstallMethod( MaximalIdealAsColumnMatrix,
        "for homalg graded rings",
        [ IsHomalgGradedRingRep ],
        
  function( S )
    local var;
    
    var := Indeterminates( S );
    
    return HomalgMatrix( var, Length( var ), 1, S );
    
end );

##
InstallMethod( MaximalIdealAsRowMatrix,
        "for homalg graded rings",
        [ IsHomalgGradedRingRep ],
        
  function( S )
    local var;
    
    var := Indeterminates( S );
    
    return HomalgMatrix( var, 1, Length( var ), S );
    
end );
