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
** nondet.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 05/01/15
**
** Symbolic back-ends can create non-deterministic variables.  To do
** this within the type system and preserving the invariants of
** objects always being correctly constructed, the easiest way is to
** create a 'non-deterministic constructor'.  C++'s syntax requires
** that this constructor is distinguished by an argument so...
**
*/

#ifndef SYMFPU_NONDET
#define SYMFPU_NONDET

namespace symfpu {

  typedef struct _nonDetMarkerType {} nonDetMarkerType;
  extern const nonDetMarkerType NONDET;

}

#endif
