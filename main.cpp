#include "basis_pms.h"
#include "pms.h"
//#include "compEx.h"
#include <sstream>
#include <iostream>
#include <dirent.h>
#include <stdlib.h>

Satlike s;
void my_exit(){
    printf("Unchangable literals rate %.1f%\n", (1.0 * s.nrOfUnchangable / s.sum_literals) * 100);
}

int main(int argc, char* argv[])
{
//    vector<string> files;
//    atexit(my_exit);
    string path = "/media/winxy/Data1/Clion projects/PBS/v1.13/normalized-mps-v2-20-10-bell4.opb";
//    string path = "/home/hudh/PBS/data";
//    getFiles(path, files);
//    srand((unsigned)time(NULL));
    srand(2);
//    start_timing();


//    int satisfiable = 0, sumOfInstances = 0;
//    for(auto& it:files){
        char filename[1024];
//        strcpy(filename, argv[1]);
        strcpy(filename, path.c_str());
        s.build_instance(filename);

        s.local_search_with_decimation(filename);

//    //s.simple_print();
        cout<<(s.isSatisfiable?"Satisfiable":"Not satisfiable")<<endl;

        for(int i = 1;i <= s.num_vars;i++){
            cout<<s.cur_soln[i]<<" ";
            if(i % 60 == 0){
                cout<<endl;
            }
        }
//        if(s.isSatisfiable)satisfiable++;
//        sumOfInstances++;
//        s.print_best_solution();
        if(!s.verify_sol() && s.isSatisfiable){
            cout<<"Error 1"<<endl;
        }
        s.free_memory();
//        cout<<1<<" "<<endl;
//    }

    return 0;
}
