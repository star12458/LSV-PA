#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <iostream>
#include <vector>
#include <algorithm>
#include <string>

using namespace std;

static int Lsv_CommandPrintGates(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv);


void init(Abc_Frame_t* pAbc) 
{
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_gates", Lsv_CommandPrintGates, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintSopunate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager 
{
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintGates(Abc_Ntk_t* pNtk) 
{
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachObj(pNtk, pObj, i) 
  {
    //printf("Object Id = %d, name = %s, Data = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj), Abc_ObjData(pObj));

    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) 
    {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
  }
}

int Lsv_CommandPrintGates(Abc_Frame_t* pAbc, int argc, char** argv) 
{
  
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);



  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) 
  {
    switch (c) 
    {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) 
  {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintGates(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_gates [-h]\n");
  Abc_Print(-2, "\t        prints the gates in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}




bool compare (Abc_Obj_t*& a, Abc_Obj_t*& b)
{
  return (Abc_ObjId(a) < Abc_ObjId(b));
}

void print_unate(string str, vector<Abc_Obj_t*>& vec)
{
    if (!vec.empty()) 
    {
      cout<<str<<"nate inputs: ";
      cout<<Abc_ObjName(vec[0]);

      for(int i=1; i<vec.size(); ++i)
        cout<<","<<Abc_ObjName(vec[i]);
      cout<<'\n';
    }

}


int Lsv_CommandPrintSopunate(Abc_Frame_t* pAbc, int argc, char** argv) 
{
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  
  if (!pNtk) 
  {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }

  if(!Abc_NtkIsSopLogic(pNtk))
  {
    Abc_Print(-1, "The network does not have SOP.\n");
    return 1 ;
  }

  Abc_Obj_t* pObj;
  int n;

  Abc_NtkForEachNode( pNtk, pObj, n ) 
  {


    vector<char> table;
    table.resize(Abc_ObjFaninNum(pObj), '-');

    if(table.empty())
      continue;

    bool flip = false;

    char* sop = (char*)Abc_ObjData(pObj);

    if(sop[table.size()+1] == '0')
      flip = true;

    int v = 0;
    
    for(int i=0; sop[i]!='\0'; ++i)
    {
      if(sop[i] == ' ')
      {  
        i += 2;
        v = 0;
        continue;
      }

      if(table[v] == '-')
        table[v] = sop[i];
      else if( (table[v] == '1' && sop[i] == '0') || (table[v] == '0' && sop[i] == '1') )
        table[v] = '2';

      ++v;
    }

    
    if(flip)
      for(int i=0; i<table.size(); ++i)
      {
        if(table[i] == '0')
          table[i] = '1';
        else if(table[i] == '1')
          table[i] = '0';
      }
    

    vector<Abc_Obj_t*> neg;
    vector<Abc_Obj_t*> pos;
    vector<Abc_Obj_t*> bi;

    int i;
    Abc_Obj_t* pFanin;
    Abc_ObjForEachFanin(pObj, pFanin, i) 
    {
      if(table[i] == '0')
        neg.push_back(pFanin);
      else if(table[i] == '1')
        pos.push_back(pFanin);
      else if(table[i] == '2')
        bi.push_back(pFanin);
    }

    sort(neg.begin(), neg.end(), compare);
    sort(pos.begin(), pos.end(), compare);
    sort(bi.begin(), bi.end(), compare);



    cout<<"node "<< Abc_ObjName(pObj)<<":\n";

    print_unate("+u", pos);
    print_unate("-u", neg);
    print_unate("bi", bi);

  }

  return 0;
}