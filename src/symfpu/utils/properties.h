/*
** Copyright (C) 2015 Martin Brain
** 
** This program is free software: you can redistribute it and/or modify
** it under the terms of the GNU General Public License as published by
** the Free Software Foundation, either version 3 of the License, or
** (at your option) any later version.
** 
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
** GNU General Public License for more details.
** 
** You should have received a copy of the GNU General Public License
** along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

/*
** properties.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 07/08/14
**
** Macros for specifying invariants in an application specific way.
** Note that there are two kinds of assertions -- those within a
** single back-end and those that are used in instruction encodings.
** The internal assertions take bools and are intended to catch
** (statically or dynamically) cases where the back-end is not being
** used correctly.  The main assertions take traits::prop s and are
** used to document and record assumptions and assertions about the
** state of the floating-point numbers during execution.  Depending on
** whether traits::prop are concrete or symbolic, the handling of
** these may be really quite different.
**
*/

#include <assert.h>

#ifndef SYMFPU_PROPERTIES
#define SYMFPU_PROPERTIES

// For use within the implementation of one base type
#define IPRECONDITION(X) iprecondition(X)
#define IPOSTCONDITION(X) ipostcondition(X)
#define IINVARIANT(X) iinvariant(X)

// For use in anything that is templated by base type traits
#define PRECONDITION(X) t::precondition(X)
#define POSTCONDITION(X) t::postcondition(X)
#define INVARIANT(X) t::invariant(X)


#endif



