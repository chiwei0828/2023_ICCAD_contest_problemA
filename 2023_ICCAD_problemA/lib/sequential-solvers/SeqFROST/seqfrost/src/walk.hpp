/***********************************************************************[walk.hpp]
Copyright(c) 2022, Muhammad Osama - Anton Wijs,
Technische Universiteit Eindhoven (TU/e).

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
**********************************************************************************/

#ifndef __WALK_
#define __WALK_

#include "solvetypes.hpp"

namespace SeqFROST {

	struct CINFO {
		uint32 size;
		uint32 unsatidx;
	};

	struct WALK {
		BCNF orgs;
		uVec1D trail, unsat;
		Vec<CINFO> cinfo;
		Vec<double> scores;
		LIT_ST* value;
		uint64 limit;
		uint32 initial, current;
		uint32 minimum, flipped;
		uint32 nclauses, best;

		            WALK			();
					~WALK			();
		inline void destroy			();

	};

}

#endif