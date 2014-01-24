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

#include "Time.h"

void printTime( ostream& o )
{
    struct rusage usage;
    getrusage( RUSAGE_SELF, &usage );
    
    o << "[" << setw( 8 ) << ( ( usage.ru_stime.tv_sec + usage.ru_utime.tv_sec ) * 1000 + ( usage.ru_stime.tv_usec + usage.ru_utime.tv_usec ) / 1000 ) << "ms] ";
}