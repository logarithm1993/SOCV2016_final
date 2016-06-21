#include <iostream>
#include <cstdlib>
#include <string>
#include <vector>
#include <fstream>


using namespace std;

int main(int argc, char** argv){
   // parse caselist.txt
   ifstream fCase("../caselist.txt");
   vector<string> vFileName;
   string tmp;
   while(fCase >> tmp){
      tmp += ".aig";
      vFileName.push_back(tmp);
   }
   fCase.close();
   
   // usage: run 1~5 |& tee log/dox.out
   int option;
   if (argc == 1)
      option = 0;
   else{
      option = atoi(argv[1]);
   }
   if (option > 5 || option < 0) option = 0;

   ofstream doFile;
   if(!option){
      cout << "do all comming sooooon\n";
   }
   else{
      for(int i = 0; i < 9; ++i){
         string thisFile = vFileName[ (option-1)*9 + i];
         cout <<"[" << i+1 << "] current File = " << thisFile << endl;       
         doFile.open("./TMP.dofile");
         doFile << "read aig ../hwmcc/" << thisFile << endl;
         doFile << "satv pdr -o 0\n";
         doFile << "q -f\n";
         doFile.close();
         string sysStr = "timeout 300 ../pdrv -f TMP.dofile \n";
         system( sysStr.c_str() );
         cout << "--------------------------\n";
      }
   }
   cout <<"all testCase done!\n";
}
