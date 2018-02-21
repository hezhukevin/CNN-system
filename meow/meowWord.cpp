#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "proof/fraig/fraig.h"
#include "opt/fxu/fxu.h"
#include "opt/cut/cut.h"
#include "map/fpga/fpga.h"
#include "map/if/if.h"
#include "opt/sim/sim.h"
#include "opt/res/res.h"
#include "opt/lpk/lpk.h"
#include "aig/gia/giaAig.h"
#include "opt/dar/dar.h"
#include "opt/mfs/mfs.h"
#include "proof/fra/fra.h"
#include "aig/saig/saig.h"
#include "proof/int/int.h"
#include "proof/dch/dch.h"
#include "proof/ssw/ssw.h"
#include "opt/cgt/cgt.h"
#include "bool/kit/kit.h"
#include "map/amap/amap.h"
#include "opt/ret/retInt.h"
#include "sat/cnf/cnf.h"
#include "proof/cec/cec.h"
#include "proof/pdr/pdr.h"
#include "misc/tim/tim.h"
#include "bdd/llb/llb.h"
#include "bdd/bbr/bbr.h"
#include "map/cov/cov.h"
#include "base/cmd/cmd.h"
#include "proof/abs/abs.h"
#include "sat/bmc/bmc.h"
#include "proof/ssc/ssc.h"
#include "opt/sfm/sfm.h"
#include "bool/rpo/rpo.h"
#include "map/mpm/mpm.h"
#include "ext/meow/wordNode.h"
#include "ext/meow/wordGraph.h"
#include "aig/gia/gia.h"

#include<iostream>
using namespace std;
ABC_NAMESPACE_IMPL_START

void meowUsageWord(){

  Abc_Print( -2, "usage: transWord <cir> <output> [-s]\n" );
  Abc_Print( -2, "\t Recognize transparent in circuit and save to output\n" );
  Abc_Print( -2, "\t-s : only use structure method\n ");
 
}
void printGraph(wordGraph* wGraph){
  
  wGraph->printNodes();
}
wordGraph* getWord(Gia_Man_t* cir){
  Gia_ManStaticFanoutStart( cir ); 
  wordGraph* newWordGraph = new wordGraph(cir);
  do{
  //  cerr<<"walk!"<<endl;
   //Note: dc2, mfs2 
   //1. extend one step
    newWordGraph->walkOneStep();
    //if(newWordGraph->checkOverlap())
    //  break;
    //newWordGraph->printSupport();
    //newWordGraph->printTarget(); 
   newWordGraph->findCandidate(); 
//   newWordGraph->walkOneStep();

  //  newWordGraph->findCandidate(); 
//    newWordGraph->walkOneStep();
    //newWordGraph->walkOneStep();
//    newWordGraph->printTarget(); 

//    newWordGraph->walkOneStep();
//    newWordGraph->printSupport();
//    newWordGraph->printTarget(); 
   //2. find Candidate and prove
//    newWordGraph->findCandidate(); // find and prove
//    newWordGraph->printTarget();
  }while(!(newWordGraph->checkTerminate()));
  Gia_ManStaticFanoutStop( cir );
  return newWordGraph;
}
ABC_NAMESPACE_IMPL_END
