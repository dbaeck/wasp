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

#ifndef OLL_H
#define OLL_H

#include "WeakInterface.h"

struct OllData
{
    unsigned int bound_;
    unsigned int guardId_;
    vector< Literal > literals_;
    vector< unsigned int > weights_;

    void addElement( unsigned int bound, unsigned int guard, vector< Literal >& literals, vector< unsigned int >& weights )
    {
        bound_ = bound;
        guardId_ = guard;
        literals_.swap( literals );
        weights_.swap( weights );
    }
};

class Oll : public WeakInterface
{
    public:
        inline Oll( Solver& s ) : WeakInterface( s ) {}
        unsigned int run();

    private:
        void processCoreOll( vector< Literal >& literals, vector< unsigned int >& weights, unsigned int minWeight );
        bool addAggregateOll( unordered_map< Var, OllData* >& guardMap, vector< Literal >& literals, vector< unsigned int >& weights, unsigned int bound );
        inline Var addBinaryClauseForAggregateOll( Var aggrId );        
};

Var
Oll::addBinaryClauseForAggregateOll(
    Var aggrId )
{    
    Literal lit( addAuxVariable(), POSITIVE );
    solver.addOptimizationLiteral( lit, 1, UINT_MAX, true );    
    solver.addClause( lit, Literal( aggrId, NEGATIVE ) );
    
    assert( !solver.isFalse( aggrId ) );
    if( solver.isTrue( aggrId ) )
        solver.addClause( lit );
    
    return lit.getVariable();
}


#endif