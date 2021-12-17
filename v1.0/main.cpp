#include "basis_pms.h"
#include "pms.h"
#include <sstream>
#include <iostream>
#include <dirent.h>

void getFiles(string path, vector<string>& filenames)
{
    DIR *pDir;
    struct dirent* ptr;
    if(!(pDir = opendir(path.c_str()))){
        cout<<"Folder doesn't Exist!"<<endl;
        return;
    }
    while((ptr = readdir(pDir))!=0) {
        if (strcmp(ptr->d_name, ".") != 0 && strcmp(ptr->d_name, "..") != 0){
            filenames.push_back(path + "/" + ptr->d_name);
        }
    }
    closedir(pDir);
}

int main()
{
    vector<string> files;
    string path = "";
    getFiles(path, files);
    srand((unsigned)time(NULL));
    start_timing();
    Satlike s;
    int cutoff = 300;
    s.cutoff_time = cutoff;
    //cout<<s.cutoff_time<<endl;
    vector<int> init_solution;


    for(auto& it:files){
        char filename[1024];
        strcpy(filename, it.c_str());
        s.build_instance(filename);

        s.local_search_with_decimation(init_solution, filename);

//    //s.simple_print();
        cout<<(s.isSatisfiable?"Satisfiable":"Not satisfiable")<<endl;
        s.print_best_solution();
        s.verify_sol();
        s.free_memory();
        cout<<1<<" "<<endl;
    }

    return 0;
}
