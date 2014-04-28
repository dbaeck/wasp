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

#ifndef CONSTANTS_H
#define CONSTANTS_H

#include <climits>
//enum TruthValue { UNDEFINED = 0, FALSE = 1, TRUE = 2 };
#define UNDEFINED 0
#define FALSE 1
#define TRUE 2
#define CACHE_FALSE 8
#define CACHE_TRUE 16
#define UNROLL_MASK 3

#define POSITIVE 0
#define NEGATIVE 1
#define ELIMINATED_BY_DISTRIBUTION 2

#define AGGRESSIVE_DELETION_POLICY 0
#define RESTARTS_BASED_DELETION_POLICY 1
#define MINISAT_DELETION_POLICY 2
#define GLUCOSE_DELETION_POLICY 3

#define HEURISTIC_BERKMIN 0
#define HEURISTIC_FIRST_UNDEFINED 1
#define HEURISTIC_MINISAT 2
#define HEURISTIC_BERKMIN_CACHE 3

#define WASP_OUTPUT 0
#define COMPETITION_OUTPUT 1
#define DIMACS_OUTPUT 2
#define SILENT_OUTPUT 3
#define THIRD_COMPETITION_OUTPUT 4

#define SEQUENCE_BASED_RESTARTS_POLICY 0
#define GEOMETRIC_RESTARTS_POLICY 1
#define MINISAT_RESTARTS_POLICY 2
#define NO_RESTARTS_POLICY 3

/*
 * Wasp constants
 */
#define WASP_STRING "WASP 2.0\n"
#define NOMODEL "INCOHERENT"
#define NOMODEL_COMPETITION_OUTPUT "INCONSISTENT"
#define ANSWER "ANSWER"
#define ANSWER_THIRD_COMPETITION "ANSWER SET FOUND"
#define WEIGHT_LEVEL_WEAKCONSTRAINT_SEPARATOR "@"
#define COST "COST"
#define OPTIMUM "OPTIMUM"
#define QUERY_FALSE_OUTPUT "no."
#define QUERY_TRUE_OUTPUT "yes."
#define MAXUNSIGNEDINT UINT_MAX

/* 
 * Error messages
 */
#define ERRORPARSING WASP_STRING "\nError during parsing"
#define ERRORGENERIC WASP_STRING "\nGeneric error"
#define ERRORPARSINGCODE 100
#define ERRORGENERICCODE 110

/*
 * DIMACS Format
 */
#define COMMENT_DIMACS 'c'
#define FORMULA_INFO_DIMACS 'p'
#define SOLUTION_DIMACS 's'
#define VALUE_DIMACS 'v'
#define UNSAT "UNSATISFIABLE"
#define SAT "SATISFIABLE"

/*
 * Gringo Numeric Format
 */
#define GRINGO_NORMAL_RULE_ID 1
#define GRINGO_COUNT_CONSTRAINT_RULE_ID 2
#define GRINGO_CHOICE_RULE_ID 3
#define GRINGO_SUM_CONSTRAINT_RULE_ID 5
#define GRINGO_OPTIMIZATION_RULE_ID 6
#define GRINGO_DISJUNCTIVE_RULE_ID 8
#define GRINGO_LINE_SEPARATOR 0
#define GRINGO_BPLUS "B+"
#define GRINGO_BMINUS "B-"

/*
 * New types
 */
typedef double Activity;
typedef unsigned int TruthValue;
typedef unsigned int DELETION_POLICY;
typedef unsigned int DECISION_POLICY;
typedef unsigned int OUTPUT_POLICY;
typedef unsigned int RESTARTS_POLICY;

/*
 * Crules 
 */
#define UNIT_PROPAGATION 0
#define LIT_OF_COMPLETION 1
#define FIRST_TRUE_LIT 2

#ifdef TRACE_ON
#include <string>
#include <sstream>

template < class T >
std::string toString( const T& t )
{
    std::stringstream ss;
    ss << t;
    return ss.str();
}
#endif


#endif

