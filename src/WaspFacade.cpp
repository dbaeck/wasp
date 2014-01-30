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

    unsigned int queryType = solver.getQueryType();
    
    switch( queryType )
    {
        case CLASPQUERY:
            //no break here
        case CLASPQUERYRESTART:
            solveQueryClaspApproach();
            return;
            
        case WASPQUERY:
            solveQueryWaspApproach();
            return;
            
        case WASPQUERYFIRSTMODEL:
            solveQueryWaspApproach();
            return;
            
        case HYBRIDQUERY:
            solveQueryHybridApproach();
            return;
            
        case ITERATIVEQUERY:
            solveQueryWaspApproach();
            return;
            
        default:
            assert( queryType == NOQUERY );
    }
    
    assert( !solver.hasQuery() );
    
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
                if( !solver.addClauseFromModelAndBackjump() )
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
    assert( solver.claspApproachForQuery() );
    solver.init();

    unsigned int diff = 0;
    if( solver.preprocessing() )
    {
        computeLowerUpperEstimate();        
        printInitialState();
        
        if( solver.clauseFromModel->size() > 0 )
            solver.clauseFromModel->attachClause();
        
        while( solver.solve() )
        {
            ++numberOfModels;            
            
            if( !claspApproachForQuery( diff ) )
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
        assert( solver.clauseFromModel != NULL );
//        cerr << "Avg of cut Models: " << diff / numberOfModels << endl;
//        cerr << "Answers not in well founded: " << ( solver.getLowerEstimate().size() + solver.clauseFromModel->size() ) - lowerEstimateInitialSize << endl;
//        cerr << "Enumerated Models: " << numberOfModels << endl;
        
        if( solver.clauseFromModel->size() > 1 )
            solver.clauseFromModel->detachClause();
        for( unsigned int i = 0; i < solver.clauseFromModel->size(); )
        {
            Variable* var = solver.clauseFromModel->getAt( i ).getVariable();
            if( var->isCautiousConsequence() )
                var->setCautiousConsequenceCandidate( false );
            else
                solver.addVariableInLowerEstimate( var );
            
            solver.clauseFromModel->swapLiteralsNoWatches( i, solver.clauseFromModel->size() - 1 );
            solver.clauseFromModel->removeLastLiteralNoWatches();            
        }
        solver.printUpperEstimate();
        solver.printLowerEstimate();
    }
}

void
WaspFacade::solveQueryWaspApproach()
{
    assert( solver.waspApproachForQuery() );
    solver.init();
    
    if( solver.preprocessing() )
    {
        computeLowerUpperEstimate();
        uint64_t upperEstimateSize = solver.upperEstimateSize();
        uint64_t diff = 0;
        
        printInitialState();
        
        if( solver.waspFirstModelApproachForQuery() || solver.iterativeApproachForQuery() )
        {            
            if( solver.solve() )
            {
                solver.setFirstChoiceFromQuery( true );
                ++numberOfModels;
                solver.shrinkUpperEstimate();
                diff = diff + ( upperEstimateSize - solver.upperEstimateSize() );
                upperEstimateSize = solver.upperEstimateSize();
                solver.printUpperEstimate();
                solver.doRestart();
                solver.simplifyOnRestart();
                solver.clearConflictStatus();
            }
            else
                goto foundIncoherence;
        }        

        solver.setFirstChoiceFromQuery( true );
        if( solver.iterativeApproachForQuery() )
            solver.setShuffleAtEachRestart( false );
        
        while( solver.upperEstimateSize() != 0 )
        {
            if( solver.solve() )
            {
                ++numberOfModels;
                solver.shrinkUpperEstimate();
                diff = diff + ( upperEstimateSize - solver.upperEstimateSize() );
                upperEstimateSize = solver.upperEstimateSize();
                solver.printUpperEstimate();

                if( solver.upperEstimateSize() == 0 )
                    break;

                solver.doRestart();
                solver.simplifyOnRestart();
                solver.clearConflictStatus();
            }
            else
                break;
        }
        
//        if( numberOfModels > 0 )
//            cerr << "Avg of cut Models: " << diff / numberOfModels << endl;
//        cerr << "Answers not in well founded: " << solver.getLowerEstimate().size() - lowerEstimateSize << endl;
//        cerr << "Enumerated Models: " << numberOfModels << endl;
    }

    if( numberOfModels == 0 )
    {
        foundIncoherence:;
        trace_msg( enumeration, 1, "No model found." );
        solver.foundIncoherence();
    }
    else
        solver.printLowerEstimate();
}

//void
//WaspFacade::solveQueryWaspApproachFirstModel()
//{
//    assert( solver.waspFirstModelApproachForQuery() );
//    solver.init();
//
//    if( solver.preprocessing() )
//    {
//        computeLowerUpperEstimate();
//        uint64_t lowerEstimateSize = solver.getLowerEstimate().size();
//        uint64_t upperEstimateSize = solver.getPreferredChoices().size();
//        uint64_t diff = 0;
//        cout << "Answers from well founded: " << lowerEstimateSize << endl;
//        //cout << "Number of atoms to try: " << upperEstimateSize << endl;        
//        
//        printInitialState();
//
//        if( solver.solve() )
//        {                
//            solver.setFirstChoiceFromQuery( true );
//            ++numberOfModels;
//            shrinkUpperEstimate();
//            diff = diff + ( upperEstimateSize - solver.getPreferredChoices().size() );
//            upperEstimateSize = solver.getPreferredChoices().size();
//            solver.printUpperEstimate();                
//            solver.doRestart();
//            solver.simplifyOnRestart();
//            solver.clearConflictStatus();
//        }
//        else
//            solver.getPreferredChoices().clear();
//
//        while( !solver.getPreferredChoices().empty() )
//        {
//            if( solver.solve() )
//            {                
//                shrinkUpperEstimate();
//                diff = diff + ( upperEstimateSize - solver.getPreferredChoices().size() );
//                upperEstimateSize = solver.getPreferredChoices().size();
//                solver.printUpperEstimate();
//
//                if( solver.getPreferredChoices().empty() )
//                    break;
//
//                solver.doRestart();
//                solver.simplifyOnRestart();
//                solver.clearConflictStatus();
//            }
//            else
//                break;
//        }
//        
//        if( numberOfModels > 0 )
//            cerr << "Avg of cut Models: " << diff / numberOfModels << endl;
//        cerr << "Answers not in well founded: " << solver.getLowerEstimate().size() - lowerEstimateSize << endl;
//        cerr << "Enumerated Models: " << numberOfModels << endl;
//    }
//
//    if( numberOfModels == 0 )
//    {
//        trace_msg( enumeration, 1, "No model found." );
//        solver.foundIncoherence();
//    }
//    else
//    {
//        cerr << "Cautious consequences:" << endl;
//        for( unsigned int i = 0; i < solver.getLowerEstimate().size(); i++ )
//            cerr << *solver.getLowerEstimate()[ i ] << " ";
//        cerr << endl;
//    }
//}

void
WaspFacade::solveQueryHybridApproach()
{
    assert( solver.hybridApproachForQuery() );
    solver.init();

    uint64_t lowerEstimateInitialSize = 0;
    unsigned int diff = 0;
    if( solver.preprocessing() )
    {
        computeLowerUpperEstimate();
        cout << "Answers from well founded: " << lowerEstimateInitialSize << endl;
        
        printInitialState();

        while( solver.solve() )
        {
            ++numberOfModels;    
            solver.shrinkUpperEstimate();            
            if( numberOfModels == 1 )
                solver.setFirstChoiceFromQuery( true );
            
            if( !claspApproachForQuery( diff ) )
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
        assert( solver.clauseFromModel != NULL );
        cerr << "Avg of cut Models: " << diff / numberOfModels << endl;
        cerr << "Answers not in well founded: " << ( solver.getLowerEstimate().size() + solver.clauseFromModel->size() ) - lowerEstimateInitialSize << endl;
        cerr << "Enumerated Models: " << numberOfModels << endl;

        cerr << "Cautious consequences:" << endl;
        for( unsigned int i = 0; i < solver.getLowerEstimate().size(); i++ )
            cerr << *solver.getLowerEstimate()[ i ] << " ";
        
        for( unsigned int i = 0; i < solver.clauseFromModel->size(); i++ )
            cerr << *solver.clauseFromModel->getAt( i ).getVariable() << " ";
        cerr << endl;
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
WaspFacade::claspApproachForQuery(
    unsigned int& diff )
{       
    unsigned int maxLevel = 0;
    unsigned int maxPosition = 0;
    unsigned int secondMaxLevel = 0;
    unsigned int secondMaxPosition = 0;

    unsigned int initialClauseFromModelSize = solver.upperEstimateSize();
    if( initialClauseFromModelSize > 1 )
        solver.clauseFromModel->detachClause();

    unsigned int size = solver.getLowerEstimate().size();
    for( unsigned int i = 0; i < solver.clauseFromModel->size(); )
    {
        Variable* var = solver.clauseFromModel->getAt( i ).getVariable();
        unsigned int dl = var->getDecisionLevel();            

        if( !var->isTrue() )
        {
            solver.clauseFromModel->swapLiteralsNoWatches( i, solver.clauseFromModel->size() - 1 );
            solver.clauseFromModel->removeLastLiteralNoWatches();
            var->setCautiousConsequenceCandidate( false );
        }
        else if( dl == 0 )
        {
            solver.clauseFromModel->swapLiteralsNoWatches( i, solver.clauseFromModel->size() - 1 );
            solver.clauseFromModel->removeLastLiteralNoWatches();
            var->setCautiousConsequenceCandidate( false );
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

    diff = diff + ( initialClauseFromModelSize - solver.upperEstimateSize() );
    if( size < solver.getLowerEstimate().size() )
        solver.printLowerEstimate();

    if( solver.upperEstimateSize() > 1 )
    {
        assert( maxLevel > 0 );
        assert( secondMaxLevel > 0 );

        solver.clauseFromModel->swapLiteralsNoWatches( 0, maxPosition );
        solver.clauseFromModel->swapLiteralsNoWatches( 1, secondMaxPosition != 0 ? secondMaxPosition : maxPosition );
        statistics( onAddingClause( size ) );
        solver.clauseFromModel->attachClause();            
    }
    assert( solver.clauseFromModel != NULL );

    solver.printUpperEstimate();

    if( solver.upperEstimateSize() == 0 )
        return false;

    if( solver.upperEstimateSize() > 1 )
    {
        unsigned int unrollLevel = solver.clauseFromModel->getAt( 1 ).getDecisionLevel();
        if( solver.clauseFromModel->getAt( 0 ).getDecisionLevel() == unrollLevel )
            --unrollLevel;
        
        if( solver.getQueryType() == CLASPQUERYRESTART )
            unrollLevel = 0;

        solver.unroll( unrollLevel );
        if( !solver.clauseFromModel->getAt( 1 ).isUndefined() )
        {
            Literal lit = solver.clauseFromModel->getAt( 0 );
            assert( lit.isUndefined() );
            if( unrollLevel == 0  )
            {
                if( !solver.propagateLiteralOnRestart( lit ) )
                    return false;
            }
            else
                solver.assignLiteral( solver.clauseFromModel );
        }
    }
    else
    {
        assert( solver.upperEstimateSize() == 1 );
        solver.doRestart();
        solver.simplifyOnRestart();
        if( !solver.propagateLiteralOnRestart( solver.clauseFromModel->getAt( 0 ) ) )
            return false;
    }
    return true;
}