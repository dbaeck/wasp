/*
 *
 *  Copyright 2013 Mario Alviano, Carmine Dodaro, Wolfgang Faber, Nicola Leone, Francesco Ricca, and Marco Sirianni.
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

#include "HigherGlobalCounterVisitor.h"
#include <cassert>

#include "../../Solver.h"

void
HigherGlobalCounterVisitor::choosePolarity(
    Literal* literal,
    Literal* oppositeLiteral )
{    
    assert( "Solver has not been set." && solver != NULL );
    
    unsigned int value1 = estimatePropagation( literal );
    if( value1 == UINT_MAX )
    {
        chosenLiteral = literal;
        return;
    }

    unsigned int value2 = estimatePropagation( oppositeLiteral );

    if( value1 > value2 )
        chosenLiteral = literal;
    else
        chosenLiteral = oppositeLiteral;
}

unsigned int
HigherGlobalCounterVisitor::estimatePropagation(
    Literal* literal )
{
    assert( literal->isUndefined() );
    solver->incrementCurrentDecisionLevel();
    solver->setAChoice( literal );
    
    while( solver->hasNextLiteralToPropagate() )
    {
        Literal* literalToPropagate = solver->getNextLiteralToPropagate();
        literalToPropagate->setOrderInThePropagation( solver->numberOfAssignedLiterals() );
        solver->propagate( literalToPropagate );
        
        if( solver->conflictDetected() )
        {
            solver->unrollOne();
            solver->clearConflictStatus();
            return UINT_MAX;
        }
    }
    
    unsigned int lookaheadValue = literal->numberOfWatchedClauses() + solver->numberOfAssignedLiterals();
    
    solver->unrollOne();    
    return lookaheadValue;
}