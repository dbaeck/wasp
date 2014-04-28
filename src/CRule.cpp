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

#include "CRule.h"
#include "Solver.h"

void
CRule::onLiteralFalse(
    Solver& solver,
    Literal lit,
    int )
{
    assert( !solver.conflictDetected() );
    Literal literal = lit.getOppositeLiteral();
    if( literal == cLiteral )
    {
        //The literal has been inferred using this CRule: return.        
        if( literal.getVariable()->getImplicant() == this )
            return;

        state = LIT_OF_COMPLETION;
        for( unsigned int i = 0; i < literals.size(); i++ )
        {            
            if( !literals[ i ].isFalse() && literals[ i ] != cLiteral )
            {                
                solver.assignLiteral( literals[ i ].getOppositeLiteral(), this );
                if( solver.conflictDetected() )
                    return;
            }
        }        
    }
    else
    {
        if( !cLiteral.isFalse() )
        {
            state = FIRST_TRUE_LIT;
            firstTrueLiteral = literal;

            solver.assignLiteral( cLiteral.getOppositeLiteral(), this );            
        }
    }
}

//bool
//CRule::onLiteralFalse(
//    Literal literal )
//{
//    //The literal has been inferred using this CRule: return.
//    if( literal.getVariable()->getImplicant() == this )
//        return false;
//
//    if( Clause::onLiteralFalse( literal ) )
//    {
//        state = UNIT_PROPAGATION;
////        typeOfPropagation = &CRule::useUnit;
//        return true;
//    }
//
//    return false;
//}

void
CRule::onLearning(
    Learning* strategy,
    Literal )
{   
    switch( state )
    {
        case UNIT_PROPAGATION:
            Clause::onLearning( strategy, Literal::null );
            break;
            
        case FIRST_TRUE_LIT:
            strategy->onNavigatingLiteral( firstTrueLiteral.getOppositeLiteral() );
            break;
            
        case LIT_OF_COMPLETION:
            strategy->onNavigatingLiteral( cLiteral.getOppositeLiteral() );
            break;
    }
}

bool
CRule::onNavigatingLiteralForAllMarked(
    Learning* strategy,
    Literal )
{
    switch( state )
    {
        case UNIT_PROPAGATION:
            return Clause::onNavigatingLiteralForAllMarked( strategy, Literal::null );            
            
        case FIRST_TRUE_LIT:
            return strategy->onNavigatingLiteralForAllMarked( firstTrueLiteral.getOppositeLiteral() );
            
        case LIT_OF_COMPLETION:
            return strategy->onNavigatingLiteralForAllMarked( cLiteral.getOppositeLiteral() );
            
        default:
            assert( 0 );
            return false;
    }
    
    assert( 0 );
    return false;
}