#include "basis_pms.h"
#include "pms.h"
#include <sstream>
#include <iostream>

//int main(int argc, char *argv[])
//{
//    srand((unsigned)time(NULL));
//    start_timing();
//    Satlike s;
//    stringstream ss;
//    ss.str(argv[2]);
//    int cutoff;
//    ss>>cutoff;
//    s.cutoff_time = cutoff;
//    //cout<<s.cutoff_time<<endl;
//
//    vector<int> init_solution;
//    s.build_instance(argv[1]);
//
//    s.local_search_with_decimation(init_solution, argv[1]);
//
//    //s.simple_print();
//    s.print_best_solution();
//    s.free_memory();
//    cout<<1<<" "<<endl;
//    return 0;
//}
int main()
{

    srand((unsigned)time(NULL));
    start_timing();
    Satlike s;
    int cutoff = 300;
    s.cutoff_time = cutoff;
    //cout<<s.cutoff_time<<endl;
    vector<int> init_solution;

    char filename[1024] = "100-1.opb.wecnf";

    s.build_instance(filename);

    s.local_search_with_decimation(init_solution, filename);

//    //s.simple_print();
    cout<<(s.isSatisfiable?"Satisfiable":"Not satisfiable")<<endl;
    s.print_best_solution();
    s.free_memory();
    cout<<1<<" "<<endl;
    return 0;
}
