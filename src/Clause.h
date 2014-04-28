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

#ifndef CLAUSE_H
#define CLAUSE_H

#include <cassert>
#include <iostream>
#include <vector>

#include "Clause.h"
#include "Literal.h"
#include "Learning.h"

using namespace std;

class Solver;
enum SubsumptionData { NO_SUBSUMPTION = 0, SUBSUMPTION = 1, SELFSUBSUMPTION = 2 };

/**
 *  This class represents a clause.
 *  A clause is a disjunction of literals.
 *  For example (a1 v a2 v not a3) is a clause and a1, a2 are positive literals and not a3 is a negative literal.
 * 
 */
class Clause
{
    friend ostream &operator<<( ostream & out, const Clause & clause );
    friend Clause* Learning::onConflict( Literal conflictLiteral, Clause* conflictClause );
    friend Clause* Learning::learnClausesFromUnfoundedSet( Vector< Variable* >& unfoundedSet );

    public:        
        virtual ~Clause();
        inline Clause( unsigned reserve = 8 );

        inline Literal getAt( unsigned idx ) const { assert( idx < literals.size() ); return literals[ idx ]; }
        inline void flipLiteralAt( unsigned idx ) { assert( idx < literals.size() ); literals[ idx ] = literals[ idx ].getOppositeLiteral(); }
        inline void markAsDeleted() { literals[ 0 ] = Literal::null; }
        inline bool hasBeenDeleted() const { assert( !literals.empty() ); return literals[ 0 ] == Literal::null; }
        inline void addLiteral( Literal literal );
        inline void addLiteralInLearnedClause( Literal literal );
        inline bool addUndefinedLiteral( Literal literal );

        inline bool contains( Literal literal );
        inline bool containsAnyComplementOf( Clause* clause );

        inline void attachClause();
        inline void attachClause( unsigned int firstWatch, unsigned int secondWatch );
        inline void attachClauseToAllLiterals();
        virtual bool detach() { detachClause(); return true; }
        inline void detachClause();
        inline void detachClauseFromAllLiterals();        
        inline void detachClauseFromAllLiterals( Literal literal );        
        inline void removeLiteral( Literal literal );
        inline void removeLastLiteralNoWatches(){ literals.pop_back(); }
        
        virtual void onLearning( Learning* strategy, Literal lit );
        virtual bool onNavigatingLiteralForAllMarked( Learning* strategy, Literal lit );
        inline bool onLiteralFalse( Literal literal );
        inline void onRemovingNoDelete( Literal literal );

        inline unsigned int size() const;
//        inline bool checkUnsatisfiedAndOptimize( Heuristic* collector );
        bool isSatisfied() const;
        
        unsigned getMaxDecisionLevel( unsigned from, unsigned to ) const;       

        inline bool isLocked() const;        

        inline void swapLiteralsNoWatches( unsigned int pos1, unsigned int pos2 ){ swapLiterals( pos1, pos2 ); }
        inline void swapUnwatchedLiterals( unsigned int pos1, unsigned int pos2 );
        inline void swapWatchedLiterals();        
          
        inline uint64_t getSignature() const { return signature(); }
        inline Literal getLiteralWithMinOccurrences() const;
        inline Variable* getVariableWithMinOccurrences();
        
        inline void setPositionInSolver( unsigned int pos ) { clauseData.positionInSolver = pos; }
        inline unsigned int getPositionInSolver(){ return clauseData.positionInSolver; }

        /**
         * This method returns true if the clause is a subset of another clause.
         * Note that the check is expensive.
         */
        inline bool isSubsetOf( const Clause* clause ) const;
        
        inline Activity& activity(){ return act(); }
        inline const Activity& activity() const { return act(); }
        inline void setLearned(){ clauseData.learned = 1; }
        inline bool isLearned() const { return clauseData.learned == 1; }
        
        inline bool removeSatisfiedLiterals();
        inline void removeDuplicates();
        inline bool removeDuplicatesAndCheckIfTautological();
        inline bool removeDuplicatesAndFalseAndCheckIfTautological();
        
        inline void free();
        inline SubsumptionData subsumes( Clause& other );        
        
        inline void resetInQueue(){ clauseData.inQueue = 0; }
        inline void setInQueue(){ clauseData.inQueue = 1; }
        inline bool isInQueue(){ return clauseData.inQueue == 1; }
        
        inline void copyLiterals( const Clause& c );
        
        inline void swapLiterals( unsigned int pos1, unsigned int pos2 );
        
        inline void recomputeSignature();
        
        void printDimacs() const;
        
        bool allUndefined() const;
        bool isTautology() const;
        
    protected:
        vector< Literal > literals;
        unsigned int state;
//        unsigned lastSwapIndex;

        virtual ostream& print( ostream& out ) const;  
    private:
        
        Clause( const Clause& )
        {
            assert( "The copy constructor has been disabled." && 0 );
        }
        
//        inline void resetLastSwapIndex() { lastSwapIndex = 1; }
        inline void setWatchesInRandomPositions();
        
        inline void attachFirstWatch();
        inline void attachSecondWatch();        
        
        inline bool updateWatch();
        void notifyImplication( Solver& solver );        
        
//        uint64_t signature;
//        unsigned int positionInSolver;
        
//        Activity act;
//        bool learned;
        
        union SignatureAct
        {
            uint64_t signature;
            Activity act;
            
            SignatureAct() { memset( this, 0, sizeof( SignatureAct ) ); }
        } signature_act;
        inline uint64_t& signature() { assert( !isLearned() ); return signature_act.signature; }
        inline const uint64_t& signature() const { assert( !isLearned() ); return signature_act.signature; }
        inline Activity& act() { assert( isLearned() ); return signature_act.act; }
        inline const Activity& act() const { assert( isLearned() ); return signature_act.act; }
        
        struct
        {        
            unsigned inQueue                : 1;
            unsigned learned                : 1;            
            unsigned positionInSolver       : 30;
        } clauseData;
};

Clause::Clause(
    unsigned reserve ) /*: lastSwapIndex( 1 ),*/ /*signature( 0 ), act( 0.0 )*/
{
    literals.reserve( reserve );
    clauseData.inQueue = 0;
    clauseData.learned = 0;
    state = UNIT_PROPAGATION;
    //free();
}

//Clause::Clause(
//    unsigned int size ) : lastSwapIndex( 1 ), activity( 0 )
//{
//    literals.reserve( size );
//}

void
Clause::addLiteral(
    Literal literal )
{
    assert( !isLearned() );
    literals.push_back( literal );
    signature() |= literal.getVariable()->getSignature();
}

void
Clause::addLiteralInLearnedClause(
    Literal literal )
{
    assert( isLearned() );
    literals.push_back( literal );
}

bool
Clause::addUndefinedLiteral(
    Literal literal )
{
    if( literal.isTrue() )
        return false;
    if( literal.isUndefined() )
    {
        addLiteral( literal );
    }
    return true;
}

void
Clause::attachFirstWatch()
{
    assert( "Unary clause must be removed." && literals.size() > 1 );
    literals[ 0 ].addWatchedClause( this );
}

void
Clause::attachSecondWatch()
{
    assert( "Unary clause must be removed." && literals.size() > 1 );
    literals[ 1 ].addWatchedClause( this );
}

void
Clause::attachClause()
{
    assert( "Unary clauses must be removed." && literals.size() > 1 );
    attachFirstWatch();
    attachSecondWatch();
}

void
Clause::attachClauseToAllLiterals()
{
    unsigned int size = literals.size();
    for( unsigned int i = 0; i < size; i++ )
    {
        literals[ i ].addClause( this );
    }
}

void
Clause::attachClause( 
    unsigned int first,
    unsigned int second )
{
    assert( "First watch is out of range." && first < literals.size() );
    assert( "Second watch is out of range." && second < literals.size() );
    assert( "First watch and second watch point to the same literal." && first != second );   
    
    #ifndef NDEBUG
    Literal tmp1 = literals[ first ];
    Literal tmp2 = literals[ second ];
    #endif

    swapLiterals( 0, first );
    second == 0 ? swapLiterals( 1, first ) : swapLiterals( 1, second );    

    assert( literals[ 0 ] == tmp1 );
    assert( literals[ 1 ] == tmp2 );
    
    attachFirstWatch();
    attachSecondWatch();
}

void
Clause::detachClause()
{
    literals[ 0 ].findAndEraseWatchedClause( this );
    literals[ 1 ].findAndEraseWatchedClause( this );
}

void
Clause::detachClauseFromAllLiterals(
    Literal literal )
{
    for( unsigned int i = 0; i < literals.size(); ++i )
    {
        if( literals[ i ] != literal )
            literals[ i ].findAndEraseClause( this );
    }    
}

void
Clause::detachClauseFromAllLiterals()
{
    for( unsigned int i = 0; i < literals.size(); ++i )
    {
        literals[ i ].findAndEraseClause( this );
    }    
}

void
Clause::onRemovingNoDelete(
    Literal literal )
{
    for( unsigned int i = 0; i < literals.size(); ++i )
    {
        if( literals[ i ] != literal )
            literals[ i ].findAndEraseClause( this );
    }
    
    assert( !literals.empty() );
    literals.push_back( getAt( 0 ) );
    markAsDeleted();
}

void
Clause::removeLiteral(
    Literal literal )
{
    unsigned int size = literals.size() - 1;
    unsigned int i = 0;
    for( ; i < size; ++i )
    {
        if( literals[ i ] == literal )
        {
            literals[ i ] = literals.back();
            break;
        }
    }

    assert( literals.back() == literal || literals.back() == literals[ i ] );
    literals.pop_back();
    
    recomputeSignature();
}

bool
Clause::isLocked() const
{
    assert( "Unary clauses must be removed." && literals.size() > 1 );

    //We assume that the literal inferred is always in the first position.
    return ( literals[ 0 ].isImplicant( this ) );
}

void
Clause::setWatchesInRandomPositions()
{
    assert( "Unary clauses must be removed." && literals.size() > 1 );
    unsigned int first = rand() % literals.size();
    unsigned int second = rand() % ( literals.size() - 1 );

    if( second >= first )
        second++;    

    assert( "First watch is not in range." && first < literals.size() );
    assert( "Second watch is not in range." && second < literals.size() );
    swapLiterals( 0, first );
    swapLiterals( 1, second );    
}

unsigned int
Clause::size() const
{
    return literals.size();
}

//void
//Clause::onLearning(
//    Learning* strategy )
//{
//    assert( "LearningStrategy is not initialized." && strategy != NULL );
//
//    //Navigating all literals in the clause.    
//    for( unsigned int i = 0; i < literals.size(); i++ )
//    {
//        Literal literal = literals[ i ];
//        strategy->onNavigatingLiteral( literal );
//    }
//}

//bool
//Clause::checkUnsatisfiedAndOptimize( 
//    Heuristic* collector )
//{
//    assert( "Unary clauses must be removed." && literals.size() > 1 );
//    
//    if( literals.back().isTrue() )
//        return false;
//    Variable* variable = literals.back().getVariable();
//    if( variable->isUndefined() )
//        collector->collectUndefined( variable );
//    
//    if( literals[ 0 ].isTrue() )
//        return false;
//    variable = literals[ 0 ].getVariable();
//    if( variable->isUndefined() )
//        collector->collectUndefined( variable );
//    
//    unsigned size = literals.size() - 1;
//    for( unsigned int i = 1; i < size; ++i )
//    {
//        if( literals[ i ].isTrue() )
//        {
//            if( i == 1 )
//                swapLiterals( 0, 1 );
//            else
//                swapLiterals( i, size );
//            
//            return false;
//        }
//        variable = literals[ i ].getVariable();
//        if( variable->isUndefined() )
//            collector->collectUndefined( variable );
//    }
//    
//    return true;
//}

void
Clause::swapLiterals( 
    unsigned int pos1, 
    unsigned int pos2 )
{
    assert_msg( pos1 < literals.size(), "First position is out of range: " << pos1 << " of " << literals.size() );
    assert_msg( pos2 < literals.size(), "Second position is out of range: " << pos2 << " of " << literals.size() );
    std::swap( literals[ pos1 ], literals[ pos2 ] );
}

void
Clause::swapWatchedLiterals()
{
    swapLiterals( 0, 1 );
}

void
Clause::swapUnwatchedLiterals( 
    unsigned int pos1, 
    unsigned int pos2 )
{
    assert( "First position is out of range." && pos1 < literals.size() );
    assert( "Second position is out of range." && pos2 < literals.size() );
    assert( pos1 >= 2 );
    assert( pos2 >= 2 );
    swapLiterals( pos1, pos2 );
}

bool
Clause::updateWatch()
{
    assert( "Unary clauses must be removed." && literals.size() > 1 );
    
    for( unsigned i = 2; i < literals.size(); ++i )
    {
        if( !literals[ i ].isFalse() )
        {
//            lastSwapIndex = i;
            //Swap the two literals
            swapLiterals( 1, i );

            //Attach the watch in the new position
            attachSecondWatch();            
            return true;
        }
    }
    
//    for( unsigned i = 2; i <= lastSwapIndex; ++i )
//    {
//        assert( i < literals.size() );
//        if( !literals[ i ].isFalse() )
//        {
//            lastSwapIndex = i;
//            //Swap the two literals
//            swapLiterals( 1, lastSwapIndex );
//
//            //Attach the watch in the new position
//            attachSecondWatch();            
//            return true;
//        }
//    }

    assert( "The other watched literal cannot be true." && !literals[ 0 ].isTrue() );
    
    //Propagate literals[ 0 ];
    state = UNIT_PROPAGATION;
    return false;
//    notifyImplication( solver );
}

bool
Clause::onLiteralFalse(
    Literal literal )
{
    assert( "The literal must be false." && literal.isFalse() );    
    assert( "Unary clauses must be removed." && literals.size() > 1 );

    if( literal == literals[ 0 ] )
    {
        //The watch to update should be always in position 1.
        literals[ 0 ] = literals[ 1 ];
        literals[ 1 ] = literal;
    }

    assert( "Literal is not watched." && literal == literals[ 1 ] );
    //if the clause is already satisfied do nothing.
    if( literals[ 0 ].isTrue() )
        return false;
        
    //update watch
    return !updateWatch();
}

Literal
Clause::getLiteralWithMinOccurrences() const
{
    assert( literals.size() > 1 );
    Literal minLiteral = literals[ 0 ];
    assert( minLiteral.numberOfOccurrences() > 0 );

    unsigned int i = 1;
    do
    {
        assert( literals[ i ].numberOfOccurrences() > 0 );
        if( literals[ i ].numberOfOccurrences() < minLiteral.numberOfOccurrences() )
        {
            minLiteral = literals[ i ];
        }
    } while( ++i < literals.size() );    
        
    return minLiteral;
}

Variable*
Clause::getVariableWithMinOccurrences()
{
    assert( literals.size() > 1 );
    assert( !hasBeenDeleted() );
    Variable* minVariable = literals[ 0 ].getVariable();
    assert_msg( minVariable->numberOfOccurrences() > 0, "Variable " << *minVariable << " does not know to occur in " << *this );

    unsigned int i = 1;
    do
    {
        assert_msg( literals[ i ].getVariable()->numberOfOccurrences() > 0, "Variable " << *literals[ i ].getVariable() << " does not know to occur in " << *this );
        if( literals[ i ].getVariable()->numberOfOccurrences() < minVariable->numberOfOccurrences() )
        {
            minVariable = literals[ i ].getVariable();
        }
    } while( ++i < literals.size() );    
        
    return minVariable;
}

bool
Clause::isSubsetOf(
    const Clause* clause ) const
{
    assert_msg( clause != NULL, "Clause cannot be null" );
    for( unsigned int i = 0; i < literals.size(); i++ )
    {
        if( find( clause->literals.begin(), clause->literals.end(), literals[ i ] ) == clause->literals.end() )
            return false;        
    }
    
    return true;
}

bool
Clause::removeSatisfiedLiterals()
{
    if( literals[ 0 ].isTrue() )
    {        
        if( isLocked() )
            literals[ 0 ].getVariable()->setImplicant( NULL );    
        return true;        
    }
    
    assert_msg( !literals[ 0 ].isFalse(), "Literal " << literals[ 0 ] <<  " in clause " << *this << " is false" );
    assert_msg( !literals[ 1 ].isFalse(), "Literal " << literals[ 1 ] <<  " in clause " << *this << " is false" );

    if( literals[ 1 ].isTrue() )
        return true;        
    
    for( unsigned int i = 2; i < literals.size(); )
    {
        if( literals[ i ].isTrue() )
            return true;

        if( literals[ i ].isFalse() )
        {
            literals[ i ] = literals.back();
            literals.pop_back();
        }
        else
        {
            i++;
        }        
    }

//    if( lastSwapIndex >= literals.size() )
//        resetLastSwapIndex();
        
    return false;
}

bool
Clause::contains(
    Literal literal )
{
    for( unsigned k = 0; k < literals.size(); ++k )
        if( literals[ k ] ==  literal )
            return true;
    return false;
}

bool
Clause::containsAnyComplementOf(
    Clause* clause )
{
    for( unsigned i = 0; i < clause->size(); ++i )
        if( contains( clause->getAt( i ).getOppositeLiteral() ) )
            return true;
    return false;
}

inline bool literalComparator( Literal l1, Literal l2 ){ return l1.getVariable()->getId() < l2.getVariable()->getId(); }

void
Clause::removeDuplicates()
{
    sort( literals.begin(), literals.end(), literalComparator );
    
    Literal previousLiteral = literals[ 0 ];
    
    unsigned int i = 1;
    unsigned int j = 1;
    while( i < literals.size() )
    {
        if( previousLiteral != literals[ i ] )
            previousLiteral = literals[ j++ ] = literals[ i++ ];
        else
            ++i;
    }

    if( i != j )
    {
        literals.resize( j );
        recomputeSignature();
    }
}

bool
Clause::removeDuplicatesAndCheckIfTautological()
{
    sort( literals.begin(), literals.end(), literalComparator ); 
    
    Literal previousLiteral = literals[ 0 ];
    
    unsigned int i = 1;
    unsigned int j = 1;
    while( i < literals.size() )
    {
        if( previousLiteral != literals[ i ] )
        {
            //The same variable with two different polarities: clause is tautological
            if( previousLiteral.getVariable() == literals[ i ].getVariable() )
            {
                //TAUTOLOGICAL
                return true;
            }
            else
            {
               previousLiteral = literals[ j++ ] = literals[ i ];
            }
        }
        
        ++i;
    }

    if( i != j )
    {
        literals.resize( j );
        recomputeSignature();
    }

    return false;
}

bool
Clause::removeDuplicatesAndFalseAndCheckIfTautological()
{
    sort( literals.begin(), literals.end(), literalComparator ); 
    
    Literal previousLiteral = Literal::null;
    
    unsigned int i = 0;
    unsigned int j = 0;
    while( i < literals.size() )
    {
        if( literals[ i ].isTrue() )
            return true;
        if( !literals[ i ].isFalse() && previousLiteral != literals[ i ] )
        {
            //The same variable with two different polarities: clause is tautological
            if( previousLiteral.getVariable() == literals[ i ].getVariable() )
            {
                //TAUTOLOGICAL
                return true;
            }
            else
            {
              previousLiteral = literals[ j++ ] = literals[ i ];
            }
        }
        
        ++i;
    }
    
    if( i != j )
    {
        literals.resize( j );
        recomputeSignature();
    }
    
    return false;
}

void
Clause::recomputeSignature()
{
    signature() = 0;
    for( unsigned int i = 0; i < literals.size(); i++ )    
         signature() |= literals[ i ].getVariable()->getSignature();
}

void
Clause::free()
{
//    lastSwapIndex = 1;
    clauseData.inQueue = 0;
    clauseData.learned = 0;
    signature() = 0;
//    act = 0.0;
    literals.clear();
}

SubsumptionData
Clause::subsumes(
    Clause& other )
{
    unsigned int size = this->size();
    unsigned int otherSize = other.size();
    if( size < otherSize && ( signature() & ~other.signature() ) != 0 )
        return NO_SUBSUMPTION;
    
    SubsumptionData ret = SUBSUMPTION;
    unsigned int position = MAXUNSIGNEDINT;    
    
    for( unsigned int i = 0; i < size; i++ )
    {
        for( unsigned int j = 0; j < otherSize; j++ )
        {
            if( getAt( i ) == other.getAt( j ) )
                goto ok;
            else if( ret == SUBSUMPTION && getAt( i ) == other.getAt( j ).getOppositeLiteral() )
            {
                ret = SELFSUBSUMPTION;
                position = j;
                goto ok;
            }
        }
        
        return NO_SUBSUMPTION;
        ok:;
    }
    
    if( ret == SELFSUBSUMPTION )
    {
        assert_msg( position < otherSize, "Position is " << position << " while the size of the clause is " << otherSize );
        other.swapLiterals( position, otherSize - 1 );
    }

    return ret;
}

void
Clause::copyLiterals(
    const Clause& c )
{
    for( unsigned int i = 0; i < c.literals.size(); i++ )    
        this->addLiteral( c.literals[ i ] );    
}

#endif
