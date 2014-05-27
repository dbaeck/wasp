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

#ifndef CLAUSEPROPAGATOR_H
#define CLAUSEPROPAGATOR_H

class Literal;
class Learning;
#include <iostream>
using namespace std;

class ClausePropagator
{
    friend ostream &operator<<( ostream & out, const ClausePropagator & clause )
    {
        return clause.print( out );
    }

    public:
        virtual ~ClausePropagator(){}
        virtual bool onLiteralFalse( Literal literal ) = 0;
        virtual void onLearning( Learning* strategy, Literal lit ) = 0;
        virtual bool onNavigatingLiteralForAllMarked( Learning* strategy, Literal lit ) = 0;
        virtual Literal getAt( unsigned int ) const = 0;
        virtual bool isLearned() const { return false; }
        virtual ClausePropagator* getReason() = 0;
        virtual ostream& print( ostream& out ) const = 0;
};

#endif