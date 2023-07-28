/***********************************************************************[version.hpp]
Copyright(c) 2020, Muhammad Osama - Anton Wijs,
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

namespace SeqFROST {

	const char* version();
	const char* compiler();
	const char* compilemode();
	const char* osystem();
	const char* date();

}
#define VERSION "1.0.0"
#define OSYSTEM "linux n168.star.cs.uiowa.edu 3.10.0-1160.62.1.el7.x86_64 x86_64"
#define DATE "Fri May 13 05:49:52 CDT 2022"
#define COMPILER "g++ (GCC) 7.3.1 20180303 (Red Hat 7.3.1-5)"
