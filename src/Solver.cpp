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

#include "Solver.h"
#include "input/Dimacs.h"
#include <algorithm>
#include <stdint.h>
using namespace std;

Solver::~Solver()
{
    while( !clauses.empty() )
    {
        assert( clauses.back() );
        delete clauses.back();
        clauses.pop_back();
    }
    
    while( !learnedClauses.empty() )
    {
        assert( learnedClauses.back() );
        delete learnedClauses.back();
        learnedClauses.pop_back();
    }
    
    while( !poolOfClauses.empty() )
    {
        assert( poolOfClauses.back() );
        delete poolOfClauses.back();
        poolOfClauses.pop_back();
    }
        
    if( outputBuilder != NULL )
        delete outputBuilder;
    
    if( satelite != NULL )
        delete satelite;
    
    if( restart != NULL )
        delete restart;
}

void
Solver::unroll(
    unsigned int level )
{
    assert_msg( !unrollVector.empty(), "There is nothing to unroll" );
    assert_msg( level < unrollVector.size(), "Level " << level << " is greater than unrollVector size " << unrollVector.size() );
    assert_msg( currentDecisionLevel >= level, "Level " << level << " is greater than current decision level " << currentDecisionLevel );
    assert( "Vector for unroll is inconsistent" && variables.numberOfAssignedLiterals() >= unrollVector[ level ] );    
    unsigned int toUnroll = variables.numberOfAssignedLiterals() - unrollVector[ level ];
    unsigned int toPop = currentDecisionLevel - level;
    
    currentDecisionLevel = level;
    
    while( toUnroll > 0 )
    {
        unrollLastVariable();
        toUnroll--;
    }
    
    while( toPop > 0 )
    {
        unrollVector.pop_back();
        toPop--;
    }
    
    variables.onUnroll();
}

//bool
//Solver::addClauseFromModelAndRestart()
//{
//    assert( variables.numberOfAssignedLiterals() > 0 );
//    
//    trace_msg( enumeration, 2, "Creating the clause representing the model." );
//    Clause* clause = newClause(); //new Clause();
//    clause->setLearned();
//    
//    for( unsigned int i = 1; i <= variables.numberOfVariables(); i++ )
//    {
//        Variable* v = variables[ i ];
//        assert( !v->isUndefined() );
//
//        unsigned int dl = v->getDecisionLevel();        
//        trace_msg( enumeration, 3, "Checking literal " << *v << " with decision level " << dl << " and its implicant is " << ( v->hasImplicant() ? "not null" : "null" ) );        
//        if( !v->hasImplicant() && dl != 0 )
//        {            
//            if( v->isTrue() )
//            {
//                Literal lit( v, NEGATIVE );
//                trace_msg( enumeration, 2, "Adding literal " << lit << " in clause." );
//                clause->addLiteral( lit );
//            }
//            else
//            {
//                Literal lit( v );
//                trace_msg( enumeration, 2, "Adding literal " << lit << " in clause." );
//                clause->addLiteral( lit );
//            }
//        }
//    }        
//    
//    unsigned int size = clause->size();    
//    if( size == 0 )
//    {        
//        releaseClause( clause );
//        return false;
//    }
//    
//    if( size > 1 )
//    {
//        statistics( onAddingClause( size ) );
//        clause->attachClause();
//        learnedClauses.push_back( clause );
//        
//        doRestart();
//        simplifyOnRestart();
//        clearConflictStatus();
//        //unroll( secondMaxLevel );
////        if( !clause->getAt( 1 ).isUndefined() )
////        {
////            assert( clause->getAt( 0 ).isUndefined() );
////            assignLiteral( clause );
////        }
//    }
//    else
//    {
//        assert( size == 1 );
//        this->doRestart();
//        simplifyOnRestart();
//        assignLiteral( clause->getAt( 0 ) );
//        releaseClause( clause );
//        clearConflictStatus();        
//    }        
//
//    return true;
//    
////    return addClauseFromModel( clause );
//}

bool
Solver::addClauseFromModelAndBackjump()
{
    assert( variables.numberOfAssignedLiterals() > 0 );
    
    trace_msg( enumeration, 2, "Creating the clause representing the model." );
    Clause* clause = newClause(); //new Clause();
    
    unsigned int maxLevel = 0;
    unsigned int maxPosition = 0;
    unsigned int secondMaxLevel = 0;
    unsigned int secondMaxPosition = 0;
    for( unsigned int i = 1; i <= variables.numberOfVariables(); i++ )
    {
        Variable* v = variables[ i ];
        assert( !v->isUndefined() );

        unsigned int dl = v->getDecisionLevel();        
        trace_msg( enumeration, 3, "Checking literal " << *v << " with decision level " << dl << " and its implicant is " << ( v->hasImplicant() ? "not null" : "null" ) );        
        if( !v->hasImplicant() && dl != 0 )
        {
            if( dl > maxLevel )
            {
                secondMaxLevel = maxLevel;
                secondMaxPosition = maxPosition;
                maxLevel = dl;
                maxPosition = clause->size();
            }
            else if( dl > secondMaxLevel )
            {
                secondMaxLevel = dl;
                secondMaxPosition = clause->size();
            }
            
            if( v->isTrue() )
            {
                Literal lit( v, NEGATIVE );
                trace_msg( enumeration, 2, "Adding literal " << lit << " in clause." );
                clause->addLiteral( lit );
            }
            else
            {
                Literal lit( v );
                trace_msg( enumeration, 2, "Adding literal " << lit << " in clause." );
                clause->addLiteral( lit );
            }
        }
    }        
    
    unsigned int size = clause->size();    
    if( size == 0 )
    {
        releaseClause( clause );
        return false;
    }
    
    if( size > 1 )
    {
        assert( maxLevel > 0 );
        assert( secondMaxLevel > 0 );

        clause->swapLiteralsNoWatches( 0, maxPosition );
        clause->swapLiteralsNoWatches( 1, secondMaxPosition != 0 ? secondMaxPosition : maxPosition );
        statistics( onAddingClause( size ) );
        clause->attachClause();
        clause->setPositionInSolver( clauses.size() );
        clauses.push_back( clause );
        
        unroll( secondMaxLevel );
        if( !clause->getAt( 1 ).isUndefined() )
        {
            assert( clause->getAt( 0 ).isUndefined() );
            assignLiteral( clause );
        }
    }
    else
    {
        assert( size == 1 );
        this->doRestart();
        simplifyOnRestart();
        assignLiteral( clause->getAt( 0 ) );
        releaseClause( clause );
        clearConflictStatus();        
    }        

    return true;
    
//    return addClauseFromModel( clause );
}

Clause*
Solver::computeClauseFromModel()
{
    assert( variables.numberOfAssignedLiterals() > 0 );   
    
    unsigned int maxLevel = 0;
    unsigned int maxPosition = 0;
    unsigned int secondMaxLevel = 0;
    unsigned int secondMaxPosition = 0;
    
    Clause* clause = newClause();
    uint64_t initialSize = lowerEstimate.size();
    for( unsigned int i = 0; i < preferredChoices.size(); )
    {
        Variable* v = preferredChoices[ i ];
        assert( !v->isUndefined() );
        
        unsigned int dl = v->getDecisionLevel();        
        if( v->isTrue() && !VariableNames::isHidden( v ) )
        {
            if( dl != 0 )
            {
                if( dl > maxLevel )
                {
                    secondMaxLevel = maxLevel;
                    secondMaxPosition = maxPosition;
                    maxLevel = dl;
                    maxPosition = clause->size();
                }
                else if( dl > secondMaxLevel )
                {
                    secondMaxLevel = dl;
                    secondMaxPosition = clause->size();
                }

                clause->addLiteral( Literal( v, NEGATIVE ) );
            }
            else
            {
                assert( dl == 0 );
                addVariableInLowerEstimate( v );
                
                preferredChoices[ i ] = preferredChoices.back();
                preferredChoices.pop_back();
                continue;
            }
        }
        
        i++;
    }
    
    if( initialSize < lowerEstimate.size() )
        printLowerEstimate();
    
    if( clause->size() > 1 )
    {    
        assert( maxLevel > 0 );
        assert( secondMaxLevel > 0 );

        clause->swapLiteralsNoWatches( 0, maxPosition );
        clause->swapLiteralsNoWatches( 1, secondMaxPosition != 0 ? secondMaxPosition : maxPosition );
        statistics( onAddingClause( clause->size() ) );
        clause->attachClause();
        clause->setPositionInSolver( clauses.size() );
        clauses.push_back( clause );
    }
    
    return clause;
}

bool 
Solver::solve()
{
    trace( solving, 1, "Starting solving.\n" );
    if( hasNextVariableToPropagate() )
        goto propagation;        
    
    while( hasUndefinedLiterals() )
    {
        /*
        static unsigned int PROVA = 0;
        static time_t PROVA_TIME = time( 0 );


        unsigned int end = 10001;
        unsigned int printValue = 10000;

        if( ++PROVA > end ) {
            cerr << "PROVA END!" << endl;
            return false;
        }
        else if( ++PROVA % printValue == 0 )
        {
            cout << PROVA << " " << learnedClauses.size() <<  " " << ( time( 0 ) - PROVA_TIME ) << endl;
        }
        //*/
        
        if( hasToDelete() )
        {
            deleteClauses();
        }

        assert( !conflictDetected() );
        if( !chooseLiteral() )
            return false;
        
        while( hasNextVariableToPropagate() )
        {
            propagation:;

            nextValueOfPropagation--;
            Variable* variableToPropagate = getNextVariableToPropagate();
            propagate( variableToPropagate );            

            if( conflictDetected() )
            {
                trace( solving, 1, "Conflict detected.\n" );
                if( getCurrentDecisionLevel() == 0 )
                {
                    trace( solving, 1, "Conflict at level 0: return. \n");
                    statistics( endSolving() );
                    return false;
                }
                
                if( !analyzeConflict() )
                {
                    statistics( endSolving() );
                    return false;
                }
                minisatHeuristic.variableDecayActivity();                
                assert( hasNextVariableToPropagate() || getCurrentDecisionLevel() == 0 );
            }
        }
    }

    completeModel();
    assert_msg( getNumberOfUndefined() == 0, "Found a model with " << getNumberOfUndefined() << " undefined variables." );
    assert_msg( allClausesSatisfied(), "The model found is not correct." );
    
    statistics( endSolving() );
    return true;
}

void
Solver::propagate(
    Variable* variable )
{
    assert( "Variable to propagate has not been set." && variable != NULL );
    trace_msg( solving, 2, "Propagating: " << *variable << " as " << ( variable->isTrue() ? "true" : "false" ) );
    
    Literal complement = Literal::createOppositeFromAssignedVariable( variable );
    
    variable->unitPropagationStart();
    assert( !conflictDetected() );
    while( variable->unitPropagationHasNext() && !conflictDetected() )
    {
        Clause* clause = variable->unitPropagationNext();
        assert( "Next clause to propagate is null." && clause != NULL );
        trace( solving, 5, "Considering clause %s.\n", toString( *clause ).c_str() );
        if( clause->onLiteralFalse( complement ) )
        {
            assignLiteral( clause );
        }
        else
            assert( !conflictDetected() );
    }
}

void
Solver::propagateAtLevelZero(
    Variable* variable )
{
    assert( "Variable to propagate has not been set." && variable != NULL );    
    Literal literal = Literal::createFromAssignedVariable( variable );
    trace_msg( solving, 2, "Propagating " << literal << " as true at level 0" );
    literal.startIterationOverOccurrences();

    while( literal.hasNextOccurrence() )
    {
        Clause* clause = literal.nextOccurence();
        trace_msg( solving, 5, "Considering clause " << *clause );
        clause->detachClauseToAllLiterals( literal );
        deleteClause( clause );
    }

    assert( !conflictDetected() );
    Literal complement = Literal::createOppositeFromAssignedVariable( variable );
    trace_msg( solving, 2, "Propagating " << complement << " as false at level 0" );
    complement.startIterationOverOccurrences();

    while( complement.hasNextOccurrence() && !conflictDetected() )
    {
        Clause* clause = complement.nextOccurence();
        assert( "Next clause to propagate is null." && clause != NULL );
        trace( solving, 5, "Considering clause %s.\n", toString( *clause ).c_str() );
        
        clause->removeLiteral( complement );
        if( clause->size() == 1 )
        {
            if( !clause->getAt( 0 ).isTrue() )
            {
                trace_msg( solving, 5, "Assigning literal " << clause->getAt( 0 ) << " as true" );
                assignLiteral( clause->getAt( 0 ) );
            }
            clause->detachClauseToAllLiterals( Literal::null );
            deleteClause( clause );
        }
        else
            assert( !conflictDetected() );
    }
}

void
Solver::propagateAtLevelZeroSatelite(
    Variable* variable )
{
    if( variable->hasBeenEliminated() )    
        return;
    
    assert( "Variable to propagate has not been set." && variable != NULL );    
    Literal literal = Literal::createFromAssignedVariable( variable );
    trace_msg( solving, 2, "Propagating " << literal << " as true at level 0" );
    literal.startIterationOverOccurrences();

    while( literal.hasNextOccurrence() )
    {
        Clause* clause = literal.nextOccurence();
        trace_msg( solving, 5, "Considering clause " << *clause );
        clause->detachClauseToAllLiterals( literal );
        markClauseForDeletion( clause );
    }

    assert( !conflictDetected() );
    Literal complement = Literal::createOppositeFromAssignedVariable( variable );
    trace_msg( solving, 2, "Propagating " << complement << " as false at level 0" );
    complement.startIterationOverOccurrences();

    while( complement.hasNextOccurrence() && !conflictDetected() )
    {
        Clause* clause = complement.nextOccurence();
        assert( "Next clause to propagate is null." && clause != NULL );
        trace( solving, 5, "Considering clause %s.\n", toString( *clause ).c_str() );
        
        clause->removeLiteral( complement );
        if( clause->size() == 1 )
        {
            if( !clause->getAt( 0 ).isTrue() )
            {
                trace_msg( solving, 5, "Assigning literal " << clause->getAt( 0 ) << " as true" );
                assignLiteral( clause->getAt( 0 ) );
            }
            clause->detachClauseToAllLiterals( Literal::null );
            markClauseForDeletion( clause );
        }
        else
        {
            satelite->onStrengtheningClause( clause );
            assert( !conflictDetected() );
        }
    }
}

void
Solver::printProgram() const
{
    for( ConstClauseIterator it = clauses.begin(); it != clauses.end(); ++it )
    {
        cout << *( *it ) << endl;
    }
}

unsigned int
Solver::getNumberOfUndefined() const
{
    unsigned countUndef = 0;
    for( unsigned int i = 1; i <= variables.numberOfVariables(); i++ )
    {
        Variable const* var = variables[ i ];
        if( var->isUndefined() )
        {
            countUndef++;
        }
    }

    return countUndef;
}

bool
Solver::allClausesSatisfied() const
{
    for( ConstClauseIterator it = clauses.begin(); it != clauses.end(); ++it )
    {
        Clause& clause = *( *it );
        if( !clause.isSatisfied() )
            return false;
    }

    return true;
}

bool compareClauses( Clause* c1, Clause* c2 ){ return c1->activity() < c2->activity(); }

void
Solver::deleteClauses()
{
    ClauseIterator i = learnedClauses_begin();
    ClauseIterator j = learnedClauses_begin();
    Activity threshold = deletionCounters.increment / numberOfLearnedClauses();
    
    sort( learnedClauses.begin(), learnedClauses.end(), compareClauses );
    
    unsigned int numberOfDeletions = 0;
    unsigned int size = numberOfLearnedClauses();
    unsigned int toDelete = size / 2;
    while( i != learnedClauses.end() )
    {
        Clause& clause = **i;
        if( clause.size() > 2 && !clause.isLocked() && ( numberOfDeletions < toDelete || clause.activity() < threshold ) )
        {
            deleteLearnedClause( i );
            numberOfDeletions++;
        }
        else
        {
            *j = *i;
            j++;
        }
        
        i++;
    }

    finalizeDeletion( size - numberOfDeletions );
    statistics( onDeletion( size, numberOfDeletions ) );
}

//void
//Solver::deleteClauses()
//{
//    Activity activitySum = 0;
//    unsigned int activityCount = 0;
//    Activity threshold = deletionCounters.increment / numberOfLearnedClauses();      
//    
//    ClauseIterator i = learnedClauses_begin();
//    ClauseIterator j = learnedClauses_begin();
//    
//    unsigned int size = numberOfLearnedClauses();
//    unsigned int halfSize = size / 2;    
//    unsigned int numberOfDeletions = 0;
//
//    assert( i != learnedClauses_end() );
//    
//    do
//    {
//        Clause& clause = **i;
//        
//        if( !clause.isLocked() )
//        {            
//            activitySum += clause.activity();
//            ++activityCount;
//            if ( clause.activity() < threshold )
//            {
//                deleteLearnedClause( i );
//                numberOfDeletions++;
//            }
//            else
//            {
//                *j = *i;
//                j++;
//            }
//        }
//        else
//        {
//            *j = *i;
//            j++;
//        }
//
//        ++i;
//    } while( i != learnedClauses_end() );
//    
//    finalizeDeletion( size - numberOfDeletions );
//    
//    numberOfDeletions = 0;
//    size = numberOfLearnedClauses();
//
//    if( activityCount > 0 && numberOfDeletions < halfSize )
//    {
//        activitySum = activitySum / activityCount;
//        i = learnedClauses_begin();
//        j = learnedClauses_begin();
//        assert( i != learnedClauses_end() );
//        do
//        {
//            if( numberOfDeletions < halfSize )
//            {
//                Clause& clause = **i;
//
//                if( !clause.isLocked() && clause.activity() < activitySum )
//                {
//                    deleteLearnedClause( i );
//                    numberOfDeletions++;
//                }
//                else
//                {
//                    *j = *i;
//                    j++;
//                }
//            }
//            else
//            {
//                *j = *i;
//                j++;
//            }
//            ++i;
//        } while( i != learnedClauses_end() );
//    }
//    
//    finalizeDeletion( size - numberOfDeletions );
//    statistics( onDeletion( size, numberOfDeletions ) );
//}

void
Solver::updateActivity( 
    Clause* learnedClause )
{
    assert_msg( learnedClause != NULL, "It is not possible to update activity of NULL clauses.");
    if( ( learnedClause->activity() += deletionCounters.increment ) > 1e20 )
    {
        for( ClauseIterator it = learnedClauses_begin(); it != learnedClauses_end(); ++it )
        {
            ( *it )->activity() *= 1e-20;
        }

        deletionCounters.increment *= 1e-20;
    }
}

void
Solver::simplifyOnRestart()
{
    if( variables.numberOfAssignedLiterals() == assignedVariablesAtLevelZero || nextValueOfPropagation > 0 )
        return;

    removeSatisfied( learnedClauses );    
    //Maybe in future we want to disable this function.
    removeSatisfied( clauses );

    assignedVariablesAtLevelZero = variables.numberOfAssignedLiterals();
    nextValueOfPropagation = literalsInClauses + literalsInLearnedClauses;
}

void
Solver::removeSatisfied(
    vector< Clause* >& clauses )
{
    assert( currentDecisionLevel == 0 );
    for( unsigned int i = 0; i < clauses.size(); )
    {
        assert_msg( clauses[ i ] != NULL, "Current clause is NULL" );
        Clause* current = clauses[ i ];
        uint64_t size = current->size();
        if( current->removeSatisfiedLiterals() )
        {
            current->detachClause();            
            if( current->isLearned() )
                literalsInLearnedClauses -= size;
            else
                literalsInClauses -= size;
            assert( !current->isLocked() );
            delete current;
            clauses[ i ] = clauses.back();            
            clauses.pop_back();            
        }
        else
        {
            ++i;
            uint64_t newsize = current->size();
            size -= newsize;
            if( current->isLearned() )
                literalsInLearnedClauses -= size;
            else
                literalsInClauses -= size;
        }
    }
}

bool hasNewInput()
{
    if( !cin.good() || cin.eof() )
        return false;
        
    struct timeval tv;
    fd_set fds;
    tv.tv_sec = 0;
    tv.tv_usec = 0;
    FD_ZERO(&fds);
    FD_SET(STDIN_FILENO, &fds); //STDIN_FILENO is 0
    select(STDIN_FILENO+1, &fds, NULL, NULL, &tv);
    return FD_ISSET(STDIN_FILENO, &fds);
}

bool
Solver::checkForNewMessages()
{
    while( hasNewInput() )
    {
//            cerr << "HAS INPUT" << endl;
        char buff [ 1024 ];
        cin.getline( buff, 1023 );
        switch( buff[ 0 ] )
        {
            //unary clauses
            case 'u':
                break;
            case 'a': 
            {
                unsigned int id = atoi( buff + 2 );                
                Variable* var = getVariable( id );
                //cerr << "A " << var->getId() << endl;
                if( !var->isTrue() )
                {
                    if( var->isFalse() )
                        return false;

                    assignLiteral( Literal( var, POSITIVE ) );
                    while( hasNextVariableToPropagate() )
                    {
                        nextValueOfPropagation--;            
                        Variable* variableToPropagate = getNextVariableToPropagate();
                        propagate( variableToPropagate );

                        if( conflictDetected() )
                            return false;
                    }

                    simplifyOnRestart();
                }
                break;
            }

            case 'r':
            {
                Variable* var = getVariable( atoi( buff + 2 ) );
                //cerr << "R " << var->getId() << endl;
                Literal lit( var, NEGATIVE );
                if( clauseFromModel != NULL )
                {
                    clauseFromModel->detachClause();
                    for( unsigned i = 0; i < clauseFromModel->size(); i++ )
                    {
                        if( clauseFromModel->getAt( i ) == lit )
                        {
                            clauseFromModel->swapLiteralsNoWatches( i, clauseFromModel->size() - 1 );
                            clauseFromModel->removeLastLiteralNoWatches();
                            break;
                        }
                    }
                    clauseFromModel->attachClause();
                }
                else
                {
                    for( unsigned int k = 0; k < preferredChoices.size(); k++ )
                    {
                        if( preferredChoices[ k ] == var )
                        {
                            preferredChoices[ k ] = preferredChoices.back();
                            preferredChoices.pop_back();
                            break;
                        }                        
                    }                                        
                }
                break;
            }
            
            case 'b':
            {
                assert( 0 && "IMPLEMENT GET VARIABLE!!!");
                exit( 12 );
                Literal lit;//getVariable( atoi( buff + 2 ) );
                Literal lit2;
                
                if( lit.isTrue() || lit2.isTrue() )
                    continue;
                
                if( lit.isFalse() && lit2.isFalse() )
                    return false;
                
                if( lit.isFalse() )
                {
                    if( !propagateLiteralOnRestart( lit ) )
                        return false;
                }
                else if( lit2.isFalse() )
                {
                    if( !propagateLiteralOnRestart( lit2 ) )
                        return false;
                }
                
                Clause* clause = newClause();
                clause->addLiteral( lit );
                clause->addLiteral( lit2 );
                clause->attachClause();
                addLearnedClause( clause );                
            }

            default:
                continue;
        }
    }
    return true;
}