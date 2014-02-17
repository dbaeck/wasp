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

#ifndef WASPFACADE_H
#define	WASPFACADE_H

#include <cassert>
using namespace std;

#include "util/Constants.h"
#include "Solver.h"
#include "input/Dimacs.h"
#include "inputBuilders/SATFormulaBuilder.h"

class WaspFacade
{
    public:
        inline WaspFacade();
        inline ~WaspFacade();
        
        void readInput();
        void solve();        
        
        inline void greetings(){ solver.greetings(); }
        
        void setDeletionPolicy( DELETION_POLICY, unsigned int deletionThreshold );
        void setDecisionPolicy( DECISION_POLICY, unsigned int heuristicLimit );
        void setOutputPolicy( OUTPUT_POLICY );
        void setRestartsPolicy( RESTARTS_POLICY, unsigned int threshold );

        inline void setMaxModels( unsigned int max );
        inline void setPrintProgram( bool printProgram );        

        inline void setQuery( unsigned int value );
        inline void setMultiSolver( bool multi );
        
        inline void setAnytime( bool anytime );
        inline void setQueryVerbosity( unsigned int verb );
        
    private:
        Solver solver;        
        
        unsigned int numberOfModels;
        unsigned int maxModels;
        bool printProgram;
        //vector< Variable* > lowerEstimate;
        //vector< Variable* > upperEstimate;
        
        inline void computeLowerUpperEstimate();
        bool modelBasedAlgorithmQuery( unsigned int& diff );
        
        void solveQueryModelBased();
        void solveQueryUnderestimateIncrease();
        void solveQueryEnumeration();
        
        inline void printInitialState();
};

WaspFacade::WaspFacade() : numberOfModels( 0 ), maxModels( 1 ), printProgram( false )
{    
}

WaspFacade::~WaspFacade()
{
}

void
WaspFacade::setMaxModels(
    unsigned int max )
{
    maxModels = max;
}

void
WaspFacade::setPrintProgram(
    bool print )
{
    printProgram = print;
}

void
WaspFacade::setQueryVerbosity(
    unsigned int verb )
{
    solver.setQueryVerbosity( verb );
}

void
WaspFacade::computeLowerUpperEstimate()
{
    solver.createClauseFromModel();        
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
                solver.addInClauseFromModel( var );
        }
    }
}

void
WaspFacade::setQuery(
    unsigned int value )
{
    solver.setQuery( value );
}

void
WaspFacade::setMultiSolver(
    bool multi )
{
    solver.setMultiSolver( multi );
}

void
WaspFacade::setAnytime(
    bool anytime )
{
    solver.setAnytime( anytime );
}

void
WaspFacade::printInitialState()
{
    if( solver.isMultiSolver() )
        solver.printNames();
    else
        cout << "Answers from well founded: " << solver.getLowerEstimate().size() << endl;

    solver.printLowerEstimate();
    solver.printUpperEstimate();
}

#endif	/* WASPFACADE_H */
