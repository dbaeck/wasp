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

#include "OutputBuilder.h"
#include "../Solver.h"

extern int EXIT_CODE;

void
OutputBuilder::foundModelOptimization(
    Solver& solver,
    unsigned int cost,
    unsigned int numberOfLevels )
{
    cout << COST;
    for( int i = numberOfLevels - 1; i >= 0; --i )
    {
        cout << " " << solver.getCostOfLevel( i, cost ) << WEIGHT_LEVEL_WEAKCONSTRAINT_SEPARATOR << ( i + 1 );
    }
    #ifdef TRACE_ON
        cout << " = " << cost;
    #endif
    cout << endl;    
}

void
OutputBuilder::optimumFound()
{
    cout << OPTIMUM_STRING << endl;
    EXIT_CODE = 30;
}

void
OutputBuilder::foundLowerBound(
    unsigned int )
{
}

void
OutputBuilder::onKill()
{
}

void
OutputBuilder::onFinish()
{
}