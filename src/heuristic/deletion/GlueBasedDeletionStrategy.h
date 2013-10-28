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
 
#ifndef GLUEBASEDDELETIONSTRATEGY_H
#define GLUEBASEDDELETIONSTRATEGY_H

#include "DeletionStrategy.h"
#include "../UseClauseData.h"
#include "../GlueBasedHeuristic.h"
#include "../../Solver.h"

class GlueBasedDeletionStrategy : public DeletionStrategy, public UseClauseData< GlueBasedHeuristic >
{
public:
    inline GlueBasedDeletionStrategy( Solver& solver, unsigned int thresholdGlueClauses );
    virtual void onLearning( Clause* clause );
    virtual void onRestart() {}
    
private:
    inline void deleteClauses();
    
    Solver& solver;
    unsigned int countOfDeletion;
    unsigned int thresholdGlueClauses;
};

GlueBasedDeletionStrategy::GlueBasedDeletionStrategy( 
    Solver& s,
    unsigned int t )
: solver( s ), countOfDeletion( 0 ), thresholdGlueClauses( t )
{
}

#endif