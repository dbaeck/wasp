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

#include "OllBB.h"

unsigned int
OllBB::run()
{   
    trace_msg( weakconstraints, 1, "Starting algorithm OLLBB" );        

    solver.turnOffSimplifications();
    initInUnsatCore();
    originalNumberOfVariables = solver.numberOfVariables();
    strategyModelGuided->createOptimizationAggregate();    
    initHeuristicValues();
    
    unsigned int i = 0;
    while( true )
    {
        setAndUpdateHeuristicValues();
        unsigned int res;
        trace_msg( weakconstraints, 1, i << " iteration" );
        if( i++ % 2 == 0 )
            res = oll();
        else
            res = bb();
        
        if( lb == ub || res == OPTIMUM_FOUND )
            return OPTIMUM_FOUND;        
        
        if( res == INCOHERENT )
            return numberOfModels == 0 ? INCOHERENT : OPTIMUM_FOUND;
    }    
}

unsigned int
OllBB::bb()
{
    trace_msg( weakconstraints, 1, "Starting BB" );
    solver.unrollToZero();
    assumptionsAND.clear();
    solver.setComputeUnsatCores( false );    
    unsigned int res = solver.solve();
    while( res == COHERENT )
    {
        numberOfModels++;
        solver.printAnswerSet();
        ub = solver.computeCostOfModel(); 

        solver.printOptimizationValue( ub );
        trace_msg( weakconstraints, 2, "Decision level of solver: " << solver.getCurrentDecisionLevel() );
        if( ub == lb || ub == 0 || solver.getCurrentDecisionLevel() == 0 )
            break;
        
        trace_msg( weakconstraints, 2, "Updating bound of optimization aggregate. Model cost: " << ub );        
        if( !strategyModelGuided->updateOptimizationAggregate( ub ) )
        {
            trace_msg( weakconstraints, 3, "Failed updating of optimization aggregate: return" );
            break;        
        }                
        
        trace_msg( weakconstraints, 2, "Calling solver..." );
        res = solver.solve();
    }

    if( res == INTERRUPTED )
        return res;
    return OPTIMUM_FOUND;
}

unsigned int
OllBB::oll()
{
    solver.unrollToZero();        
    solver.setComputeUnsatCores( true );
    assumptionsAND.clear();
    computeAssumptionsAND();    
    unsigned int res = solver.solve( assumptionsAND, assumptionsOR );    
    while( res == INCOHERENT )
    {        
        if( !foundUnsat() )
            return INCOHERENT;
        
        assumptionsAND.clear();
        computeAssumptionsAND();
        
        res = solver.solve( assumptionsAND, assumptionsOR );        
    }

    if( res == INTERRUPTED )
        return res;

    ub = solver.computeCostOfModel();
    assert_msg( lb == ub, lb << " != " << ub );
    solver.printAnswerSet();
    solver.printOptimizationValue( ub );
    numberOfModels++;
    
    return OPTIMUM_FOUND;    
}            