/*
 *
 *  Copyright 2013 Mario Alviano, Carmine Dodaro, and Francesco Ricca.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 */

#include <stdint.h>

#include "WaspFacade.h"

#include "Restart.h"

#include "outputBuilders/WaspOutputBuilder.h"
#include "outputBuilders/SilentOutputBuilder.h"
#include "outputBuilders/ThirdCompetitionOutputBuilder.h"
#include "outputBuilders/CompetitionOutputBuilder.h"
#include "outputBuilders/DimacsOutputBuilder.h"

#include "MinisatHeuristic.h"
#include "input/InputFacade.h"

void
WaspFacade::readInput()
{
    InputFacade inputFacade( solver );
    inputFacade.parse();
    
    if( inputFacade.isInstanceOfSAT() )
        solver.setOutputBuilder( new DimacsOutputBuilder() );
    else if( !inputFacade.isInstanceOfASP() )
        ErrorMessage::errorDuringParsing( "Error while reading input file." );    
//    else    
//        solver.setOutputBuilder( new WaspOutputBuilder() );
}

void
WaspFacade::solve()
{
    if( printProgram )
    {
        solver.printProgram();
        return;
    }

    if( claspQuery() )
    {
        solveQueryClaspApproach();
        return;
    }
    else if( waspQuery() )
    {
        solveQueryWaspApproach();
        return;
    }
    
    assert( !hasQuery() );
    
    solver.init();     
    
    if( solver.preprocessing() )
    {        
        while( solver.solve() )
        {
            solver.printAnswerSet();
            trace_msg( enumeration, 1, "Model number: " << numberOfModels + 1 );
            if( ++numberOfModels >= maxModels )
            {
                trace_msg( enumeration, 1, "Enumerated " << maxModels << "." );
                break;
            }
            else
            {
                if( !solver.addClauseFromModelAndRestart() )
                {
                    trace_msg( enumeration, 1, "All models have been found." );
                    break;
                }                
            }
        }
    }

    if( numberOfModels == 0 )
    {
        trace_msg( enumeration, 1, "No model found." );
        solver.foundIncoherence();
    }
}

void
WaspFacade::solveQueryClaspApproach()
{
    assert( claspQuery() );
    solver.init();

    if( solver.preprocessing() )
    {
        computeLowerEstimate();
        cerr << "Answers from well founded: " << solver.getLowerEstimate().size() << endl;
        
        printLowerEstimate();

        while( solver.solve() )
        {
            ++numberOfModels;

            if( !claspApproachForQuery() )
                break;            
        }
    }

    if( numberOfModels == 0 )
    {
        trace_msg( enumeration, 1, "No model found." );
        solver.foundIncoherence();
    }
    else
    {
        assert( clauseFromModel != NULL );        
        cerr << "Enumerated Models: " << numberOfModels << endl;

        cout << "Cautious consequences:" << endl;
        for( unsigned int i = 0; i < solver.getLowerEstimate().size(); i++ )
            cout << *solver.getLowerEstimate()[ i ] << " ";
        
        for( unsigned int i = 0; i < clauseFromModel->size(); i++ )
            cout << *clauseFromModel->getAt( i ).getVariable() << " ";
        cout << endl;
    }
}

void
WaspFacade::solveQueryWaspApproach()
{
    assert( waspQuery() );
    solver.init();

    if( solver.preprocessing() )
    {
        for( unsigned int i = 1; i <= solver.numberOfVariables(); i++ )
        {
            Variable* var = solver.getVariable( i );
            if( !VariableNames::isHidden( var ) )
            {
                assert( !var->hasBeenEliminated() );
                if( var->isTrue() )
                {
                    assert( var->getDecisionLevel() == 0 );
                    solver.addVariableInLowerEstimate( var );
                }
                else if( var->isUndefined() )
                    solver.addPreferredChoice( var );
            }
        }

        uint64_t lowerEstimateSize = solver.getLowerEstimate().size();
        uint64_t upperEstimateSize = solver.getPreferredChoices().size();
        uint64_t diff = 0;
        cerr << "Answers from well founded: " << lowerEstimateSize << endl;
        cerr << "Number of atoms to try: " << upperEstimateSize << endl;        
        
        printLowerEstimate();
        solver.printUpperEstimate();

        while( !solver.getPreferredChoices().empty() )
        {
            if( solver.solve() )
            {
                ++numberOfModels;
                vector< Variable* >& upperEstimate = solver.getPreferredChoices();
                for( unsigned int i = 0; i < upperEstimate.size(); )
                {
                    Variable* var = upperEstimate[ i ];
                    assert( !var->isUndefined() );
                    if( !var->isTrue() )
                    {
                        upperEstimate[ i ] = upperEstimate.back();
                        upperEstimate.pop_back();
                    }
                    else
                        ++i;
                }
                
                diff = diff + ( upperEstimateSize - upperEstimate.size() );
                upperEstimateSize = upperEstimate.size();
                solver.printUpperEstimate();

                if( upperEstimate.empty() )
                    break;

                solver.doRestart();
                solver.simplifyOnRestart();
                solver.clearConflictStatus();
            }
            else
            {
                break;                
            }
//            if( !solver.addClauseFromModelAndRestart() )
//            {
//                trace_msg( enumeration, 1, "All models have been found." );
//                break;
//            }
        }
        
        if( numberOfModels > 0 )
        {            
            cerr << "Avg of cut Models: " << diff / numberOfModels << endl;
        }
        cerr << "Answers not in well founded: " << solver.getLowerEstimate().size() - lowerEstimateSize << endl;
        cerr << "Enumerated Models: " << numberOfModels << endl;
    }

    if( numberOfModels == 0 )
    {
        trace_msg( enumeration, 1, "No model found." );
        solver.foundIncoherence();
    }
    else
    {
        cout << "Cautious consequences:" << endl;
        for( unsigned int i = 0; i < solver.getLowerEstimate().size(); i++ )
            cout << *solver.getLowerEstimate()[ i ] << " ";
        cout << endl;
    }
}

void
WaspFacade::setDeletionPolicy(
    DELETION_POLICY deletionPolicy,
    unsigned int deletionThreshold )
{
    switch( deletionPolicy )
    {
//        case RESTARTS_BASED_DELETION_POLICY:
//            heuristic->setDeletionStrategy( new RestartsBasedDeletionStrategy( solver ) );
//            break;
//            
//        case MINISAT_DELETION_POLICY:
//            heuristic->setDeletionStrategy( new MinisatDeletionStrategy( solver ) );
//            break;
//            
//        case GLUCOSE_DELETION_POLICY:
//            heuristic->setDeletionStrategy( new GlueBasedDeletionStrategy( solver, deletionThreshold ) );
//            break;
//
//        case AGGRESSIVE_DELETION_POLICY:
//        default:
//            heuristic->setDeletionStrategy( new AggressiveDeletionStrategy( solver ) );
//            break;
    }
}

void
WaspFacade::setDecisionPolicy(
    DECISION_POLICY decisionPolicy,
    unsigned int threshold )
{
    switch( decisionPolicy )
    {
//        case HEURISTIC_BERKMIN:
//            assert( threshold > 0 );
//            heuristic->setDecisionStrategy( new BerkminHeuristic( solver, threshold ) );
//            break;
//            
//        case HEURISTIC_BERKMIN_CACHE:
//            assert( threshold > 0 );
//            heuristic->setDecisionStrategy( new BerkminHeuristicWithCache( solver, threshold ) );            
//            break;
//        
//        case HEURISTIC_FIRST_UNDEFINED:
//            heuristic->setDecisionStrategy( new FirstUndefinedHeuristic( solver ) );
//            break;
//            
//        case HEURISTIC_MINISAT:
//            heuristic->setDecisionStrategy( new MinisatHeuristic( solver ) );
//            break;
//    
//        default:
//            heuristic->setDecisionStrategy( new BerkminHeuristic( solver, 512 ) );
//            break;
    }
}

void
WaspFacade::setOutputPolicy(
    OUTPUT_POLICY outputPolicy )
{
    switch( outputPolicy )
    {
        case COMPETITION_OUTPUT:
            solver.setOutputBuilder( new CompetitionOutputBuilder() );
            break;
            
        case DIMACS_OUTPUT:
            solver.setOutputBuilder( new DimacsOutputBuilder() );
            break;
            
        case SILENT_OUTPUT:
            solver.setOutputBuilder( new SilentOutputBuilder() );
            break;
            
        case THIRD_COMPETITION_OUTPUT:
            solver.setOutputBuilder( new ThirdCompetitionOutputBuilder() );
            break;
            
        case WASP_OUTPUT:
        default:
            solver.setOutputBuilder( new WaspOutputBuilder() );
            break;
    }
}

void
WaspFacade::setRestartsPolicy(
    RESTARTS_POLICY restartsPolicy,
    unsigned int threshold )
{
    assert( threshold > 0 );
    Restart* restart;
    switch( restartsPolicy )
    {
        case GEOMETRIC_RESTARTS_POLICY:
            restart = new Restart( threshold, false );
            solver.setRestart( restart );
            break;            

        case SEQUENCE_BASED_RESTARTS_POLICY:
        default:
            restart = new Restart( threshold, true );
            solver.setRestart( restart );
            break;
    }
}

bool
WaspFacade::claspApproachForQuery()
{
    if( clauseFromModel == NULL )
    {
        clauseFromModel = solver.computeClauseFromModel();
        clauseFromModel->canBeSimplified = false;
    }
    else
    {
        unsigned int maxLevel = 0;
        unsigned int maxPosition = 0;
        unsigned int secondMaxLevel = 0;
        unsigned int secondMaxPosition = 0;

        if( clauseFromModel->size() > 1 )
            clauseFromModel->detachClause();

        unsigned int size = solver.getLowerEstimate().size();
        for( unsigned int i = 0; i < clauseFromModel->size(); )
        {
            Variable* var = clauseFromModel->getAt( i ).getVariable();
            unsigned int dl = var->getDecisionLevel();

            if( !var->isTrue() )
            {
                clauseFromModel->swapLiteralsNoWatches( i, clauseFromModel->size() - 1 );
                clauseFromModel->removeLastLiteralNoWatches();
            }
            else if( dl == 0 )
            {
                clauseFromModel->swapLiteralsNoWatches( i, clauseFromModel->size() - 1 );
                clauseFromModel->removeLastLiteralNoWatches();
                solver.addVariableInLowerEstimate( var );
            }
            else
            {
                if( dl > maxLevel )
                {
                    secondMaxLevel = maxLevel;
                    secondMaxPosition = maxPosition;
                    maxLevel = dl;
                    maxPosition = i;
                }
                else if( dl > secondMaxLevel )
                {
                    secondMaxLevel = dl;
                    secondMaxPosition = i;
                }
                i++;
            }
        }
        
        if( size < solver.getLowerEstimate().size() )
            solver.printLowerEstimate();

        if( clauseFromModel->size() > 1 )
        {    
            assert( maxLevel > 0 );
            assert( secondMaxLevel > 0 );

            clauseFromModel->swapLiteralsNoWatches( 0, maxPosition );
            clauseFromModel->swapLiteralsNoWatches( 1, secondMaxPosition != 0 ? secondMaxPosition : maxPosition );
            statistics( onAddingClause( size ) );
            clauseFromModel->attachClause();            
        }
    }

    assert( clauseFromModel != NULL );
    
    cout << "Possible answers:" << endl;
    for( unsigned int i = 0; i < clauseFromModel->size(); i++ )
    {
        cout << " " << *clauseFromModel->getAt( i ).getVariable();
    }
    cout << endl;

    if( clauseFromModel->size() == 0 )
        return false;

    unsigned int size = clauseFromModel->size();
    if( size > 1 )
    {
        unsigned int unrollLevel = clauseFromModel->getAt( 1 ).getDecisionLevel();
        if( clauseFromModel->getAt( 0 ).getDecisionLevel() == unrollLevel )
            --unrollLevel;

        solver.unroll( unrollLevel );
        if( !clauseFromModel->getAt( 1 ).isUndefined() )
        {
            assert( clauseFromModel->getAt( 0 ).isUndefined() );
            solver.assignLiteral( clauseFromModel );
        }
    }
    else
    {
        assert( size == 1 );
        solver.doRestart();
        solver.simplifyOnRestart();
        solver.assignLiteral( clauseFromModel->getAt( 0 ) );                        
        solver.clearConflictStatus();        
    }
    return true;
}