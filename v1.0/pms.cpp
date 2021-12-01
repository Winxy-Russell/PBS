#include "basis_pms.h"
#include "pms.h"
#include <sstream>

int main(int argc, char *argv[])
{
	srand((unsigned)time(NULL));
	start_timing();
	Satlike s;
	stringstream ss;
	ss.str(argv[2]);
	int cutoff;
	ss>>cutoff;
	s.cutoff_time = cutoff;
	//cout<<s.cutoff_time<<endl;
	
	vector<int> init_solution;
	s.build_instance(argv[1]);

	s.local_search_with_decimation(init_solution, argv[1]);

	//s.simple_print();
	s.print_best_solution();
	s.free_memory();
	cout<<1<<" "<<endl;
	return 0;
}
