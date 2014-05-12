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

#ifndef CRULE_H
#define CRULE_H

#include "util/Assert.h"
#include "Clause.h"
#include "Learning.h"
#include "Literal.h"
#include "Propagator.h"
using namespace std;

class Learning;

/**
 * This class is a rule modelling the Clark Completion for a specific atom.
 * The literal associated to the atom is referred as literalOfCompletion.
 * 
 */
class CRule : public Clause, public Propagator
{
    public:

//        inline CRule();
//        inline CRule( Clause& clause );
        
        /**
         * Constructor of CRule which takes in input the number of literals in the CRule.
         * 
         * @param size the numbers of literals.
         */
        inline CRule( unsigned int size );        
        inline void setCLiteral( Literal literal );

//        bool onLiteralFalse( Literal literal ); //Clause
        void onLiteralFalse( Solver& solver, Literal literal, int pos ); //Propagator
        
        virtual void onLearning( Learning* strategy, Literal lit );
        virtual bool onNavigatingLiteralForAllMarked( Learning* strategy, Literal lit );
        virtual bool detach() { detachClause(); return false; }
        inline void attachCRule();
        inline void reset(){}
        
        inline bool removeDuplicateOfCliteral();
        
    private:
        inline CRule( const CRule& );

        Literal cLiteral;
        Literal firstTrueLiteral;
        
        virtual ostream& print( ostream& out ) const
        {
            if( literals.empty() )
                return out;

            out << literals[ 0 ];
            if( literals[ 0 ] == cLiteral )
                out << "(*)";
            
            for( unsigned int i = 1; i < literals.size(); i++ )
            {
                out << " | " << literals[ i ];
                if( literals[ i ] == cLiteral )
                    out << "(*)";                
            }

            return out;
        }        
};
//
//CRule::CRule() : cLiteral( Literal::null ), firstTrueLiteral( Literal::null )
//{
//}

CRule::CRule(
    unsigned int size ) :
        Clause( size ),
        cLiteral( Literal::null ),
        firstTrueLiteral( Literal::null )
{
}
//
//CRule::CRule(
//    Clause& clause ) : cLiteral( Literal::null ), firstTrueLiteral( Literal::null )
//{
//    for( unsigned int i = 0; i < clause.size(); i++ )
//        this->addLiteral( clause.getAt( i ) );
//    this->state = UNIT_PROPAGATION;
//}

void
CRule::setCLiteral(
    Literal literal )
{
    cLiteral = literal;
}

void
CRule::attachCRule()
{
    for( unsigned int i = 0; i < literals.size(); i++ )
        literals[ i ].getOppositeLiteral().addPriorityPropagator( this, -1 );    
}

bool
CRule::removeDuplicateOfCliteral()
{
    assert( cLiteral != Literal::null );
    Literal lit = cLiteral.getOppositeLiteral();
    assert( literals[ 0 ] == cLiteral );
    for( unsigned int i = 1; i < literals.size(); i++ )
    {
        if( lit == literals[ i ] )
        {
            swapLiterals( i, literals.size() - 1 );
            removeLastLiteralNoWatches();
            return true;
        }
    }
    
    return false;
}

#endif

