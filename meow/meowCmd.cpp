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
#include "ext/meow/meowMux.h" 
#include "ext/meow/meowBound.h" // old for Baruch
#include "ext/meow/meowBound2.h" // new for Verilog
#include "ext/meow/meowCNN.h"
#include "ext/meow/meowDGSyn.h"
#include "aig/gia/gia.h"


#ifndef _WIN32
#include <unistd.h>
#endif

#include<iostream>
using namespace std;
ABC_NAMESPACE_IMPL_START
static int Meow_CommandMux(Abc_Frame_t* pAbc, int argc, char** argv);
static int Meow_CommandBound(Abc_Frame_t* pAbc, int argc, char** argv);
static int Meow_CommandCNN(Abc_Frame_t* pAbc, int argc, char** argv);
static int Meow_CommandBound2(Abc_Frame_t* pAbc, int argc, char** argv);
static int Meow_CommandDGSynthesis(Abc_Frame_t* pAbc, int argc, char** argv);
void Meow_Init(Abc_Frame_t * pAbc)
{
    Cmd_CommandAdd(pAbc, "ZZMeow", "meowMux", Meow_CommandMux, 0);
    Cmd_CommandAdd(pAbc, "ZZMeow", "meowBound", Meow_CommandBound, 0);
    Cmd_CommandAdd(pAbc, "ZZMeow", "meowCNN", Meow_CommandCNN, 0);
    Cmd_CommandAdd(pAbc, "ZZMeow", "meowReverse", Meow_CommandBound2, 0);
    Cmd_CommandAdd(pAbc, "ZZMeow", "meowDGSyn", Meow_CommandDGSynthesis, 0);
}
extern void meowUsageCNN();
extern void meowUsageDGSyn();
extern void meowUsageMux();
extern void meowUsageBound();
extern void meowUsageBound2();

int Meow_CommandDGSynthesis(Abc_Frame_t* pAbc, int argc, char** argv){
  FILE* pFile;
  char * pFileSpec = NULL;
  char* pGoldenSpec = NULL;
  char* pDGName = NULL;
  Gia_Man_t* pCircuit;
  Gia_Man_t* pNewCircuit;
  Gia_Man_t* pGolden;
  meowDGSyn* dgAPI = NULL;
  Extra_UtilGetoptReset();
  int c = 0;
  int depth = 2;
  int greedy = 0;
  //int r = 0;
  while(( c = Extra_UtilGetopt( argc, argv, "gdhDFG" ) ) != EOF ) {
    switch(c){
      case 'F':
        if ( globalUtilOptind >= argc ){
           Abc_Print( -1, "Command line switch \"-F\" should be followed by a file name.\n" );
           goto usage;
        }
        pFileSpec = argv[globalUtilOptind];
        globalUtilOptind++;
        break;
      case 'D':
        if ( globalUtilOptind >= argc ){
           Abc_Print( -1, "Command line switch \"-D\" should be followed by a dot name.\n" );
           goto usage;
        }
        pDGName = argv[globalUtilOptind];
        globalUtilOptind++;
        break;
      case 'G':
        if ( globalUtilOptind >= argc ){
           Abc_Print( -1, "Command line switch \"-G\" should be followed by a file name.\n" );
           goto usage;
        }
        pGoldenSpec = argv[globalUtilOptind];
        globalUtilOptind++;
        break;

      case 'h':
        goto usage; 
        break;
      case 'd':
        if ( globalUtilOptind >= argc ){
           Abc_Print( -1, "Command line switch \"-d\" should be followed by a nature number.\n" );
           goto usage;
        }
        depth = atoi(argv[globalUtilOptind]);
        globalUtilOptind++;
        break;  
      case 'g':
        greedy = 1;
        break; 
      default:
        goto usage;
    }
  }
  if ( pAbc->pGia == NULL ){
     Abc_Print( -1, "Meow_CommandDGSynthesis(): There is no target GIA.\n" );
     return 1;
  }
  pCircuit = Gia_ManDupOrderAiger( pAbc->pGia ); // <= revised Cir  
  if(Gia_ManRegNum(pCircuit) == 0){
    Abc_Print(-1, "meowDGSyn only accepts sequential circuits.\n");
    return 1; 
  }
  dgAPI = new meowDGSyn(pCircuit, depth, greedy);
  if(pDGName != NULL){
    dgAPI->drawGraph(pDGName); // draw input DG
  }
  if(pGoldenSpec != NULL){ // remove gating from pCircuit
    if ( (pFile = fopen( pGoldenSpec, "r" )) == NULL ){
      Abc_Print( -1, "Cannot open input file \"%s\". ", pGoldenSpec );
      return 1;  
    }
    fclose(pFile);
    pGolden = Gia_AigerRead(pGoldenSpec, 0, 0, 0);
    if(pGolden == NULL){
      Abc_Print( -1, "Reading AIGER has failed.\n" );
      return 0;
    }
	if(Gia_ManRegNum(pGolden) > Gia_ManRegNum(pCircuit)
	|| Gia_ManPiNum(pGolden) != Gia_ManPiNum(pCircuit)
	||Gia_ManPoNum(pGolden) != Gia_ManPoNum(pCircuit) ) {
      Abc_Print(-1, "meowDGSyn only accepts matched sequential circuits.\n");
      return 1; 

    }
    dgAPI->performVerification(pGolden);
    Gia_ManStop(pGolden);
  }
  else{ // add gating condition
    dgAPI->performSynthesis();
  }

  pNewCircuit = dgAPI->getNewCircuit();
  if(pNewCircuit){ // replaced with another circuit
   
    if(pFileSpec){
      Gia_AigerWrite( pNewCircuit, pFileSpec, 0, 0 );
      //Gia_ManPrintStats( pNewCircuit, NULL );
    }
  }
  else // pNewCircuit = NULL
    Abc_Print(-1, "no new circuit is generated.\n");

//  dgAPI->printReport();

  delete dgAPI;
  return 0;
usage:
  meowUsageDGSyn();
  return 1;

}

int Meow_CommandCNN(Abc_Frame_t* pAbc, int argc, char** argv){
  char * pFileSpec = NULL;
  char * pFolderSpec = NULL;
  Gia_Man_t* pCircuit;
  Extra_UtilGetoptReset();
  int c = 0;
  int mode = 0;
  int simple = 0;
  int partitionNum = -1;
  meowCNN* meowAPI = NULL;
  while(( c = Extra_UtilGetopt( argc, argv, "hFMSPn" ) ) != EOF ) {
    switch(c){
      case 'F':
        if ( globalUtilOptind >= argc ){
           Abc_Print( -1, "Command line switch \"-F\" should be followed by a file name.\n" );
           goto usage;
        }
        pFileSpec = argv[globalUtilOptind];
        globalUtilOptind++;
        break;
      case 'P':
        if ( globalUtilOptind >= argc ){
           Abc_Print( -1, "Command line switch \"-F\" should be followed by a file name.\n" );
           goto usage;
        }
        pFolderSpec = argv[globalUtilOptind];
        globalUtilOptind++;
        break;

      case 'S':
        simple = 1;
        break;
      case 'n':
        if ( globalUtilOptind >= argc ){
           Abc_Print( -1, "Command line switch \"-M\" should be followed by a nature number.\n" );
           goto usage;
        }
        partitionNum = atoi(argv[globalUtilOptind]);
        globalUtilOptind++;
        break;
      case 'M':
        if ( globalUtilOptind >= argc ){
           Abc_Print( -1, "Command line switch \"-M\" should be followed by a nature number.\n" );
           goto usage;
        }
        mode = atoi(argv[globalUtilOptind]);
        
        globalUtilOptind++;
        break;

      case 'h':
        goto usage; 
        break; 
      default:
        goto usage;
    }
  } 
  if ( pAbc->pGia == NULL ){
     Abc_Print( -1, "Meow_CommandCNN(): There is no GIA.\n" );
     return 1;
  }
  if(mode < 1 || mode > 5){
    Abc_Print( -1, "Meow_CommandCNN(): mode should be 1-5\n" );
    return 1;

  }
  if ( !Gia_ManHasMapping(pAbc->pGia) ){
    Abc_Print( -1, "Abc_CommandCNN(): AIG has no mapping.\n" );
    return 1;
  }
 
  pCircuit = pAbc->pGia;
  if(Gia_ManRegNum(pCircuit) != 0){
    Abc_Print(-1, "meowCNN only accepts combinational circuits.\n");
    return 1; 
  }
  meowAPI = new meowCNN(pCircuit);
  if(pFileSpec){
    if (!meowAPI->writeCNNData( pFileSpec, mode))
      Abc_Print(-1, "writeCNNData fails!\n");
  }
  if(pFolderSpec){
    if(!meowAPI->writeCNNPartition(pFolderSpec, mode,partitionNum))
      Abc_Print(-1, "writeCNNPartition fails!\n");
  }
  delete meowAPI;
  return 0;
usage:
  meowUsageCNN();
  return 1;

}
int Meow_CommandBound2(Abc_Frame_t* pAbc, int argc, char** argv){
  
  Gia_Man_t* pCircuit;
  bool printAllWords = false; //w
  bool printAnalysis = false; //r
  bool finalDropSmall = false;
  int singleMode = 1; // 0 drop all, 1 keep all 2 remove before split
  bool dropAllSingle = false;
  char * pFileSpec = NULL;
  char * fileHead = NULL;
  meowBound2* boundAPI2 = NULL;
  bool split = false;
  Extra_UtilGetoptReset();
  int c = 0;
  while(( c = Extra_UtilGetopt( argc, argv, "adswrVCh" ) ) != EOF ) {
    switch(c){
      case 'a':
        if ( globalUtilOptind >= argc ){
           Abc_Print( -1, "Command line switch \"-a\" should be followed by a nature number.\n" );
           goto usage;
        }
        singleMode = atoi(argv[globalUtilOptind]);
        globalUtilOptind++;
        break;
      case 'd':
        finalDropSmall = true;
        break;
      case 's':
        split = true;
        break;
      case 'w':
        printAllWords = true;
        break;
      case 'V':
        if ( globalUtilOptind >= argc ){
           Abc_Print( -1, "Command line switch \"-V\" should be followed by a file name.\n" );
           goto usage;
        }
        pFileSpec = argv[globalUtilOptind];
        globalUtilOptind++;
        break;
      case 'C':
        if ( globalUtilOptind >= argc ){
           Abc_Print( -1, "Command line switch \"-C\" should be followed by a file name.\n" );
           goto usage;
        }
        fileHead = argv[globalUtilOptind];
        globalUtilOptind++;
        break;
      case 'r':
        printAnalysis = true;
        break;
      case 'h':
        goto usage; 
        break; 
      default:
        goto usage;
    }
  } 
  if ( pAbc->pGia == NULL ){
     Abc_Print( -1, "Meow_CommandReverse(): There is no GIA.\n" );
     return 1;
  }

  pCircuit = pAbc->pGia;
  if(Gia_ManRegNum(pCircuit) != 0){
    Abc_Print(-1, "meowReverse only accepts combinational circuits.\n");
    return 1; 
  }
  dropAllSingle = (singleMode == 0)? true : false;
  boundAPI2 = new meowBound2(pCircuit);
  boundAPI2->runAll(dropAllSingle);

  if(singleMode == 2)
    boundAPI2->removeBadSingle();
  if(split)
    boundAPI2->reconnect();

  if(finalDropSmall)
    boundAPI2->collectNodes();

  if(singleMode == 3)
    boundAPI2->removeBadSingle();
  //cerr<<"Finish!"<<endl;


 // boundAPI2->printNodes();
  if(printAnalysis)
    boundAPI2->printReportNew();
  if(printAllWords)
    boundAPI2->printNodes();

  if(pFileSpec)
    boundAPI2->writeOutVerilog(pFileSpec);
  if(fileHead)
    boundAPI2->writeSubCircuits(fileHead);
  delete boundAPI2;
  return 0;
usage:
  meowUsageBound2();
  return 1;
}


int Meow_CommandBound(Abc_Frame_t* pAbc, int argc, char** argv){
  
  Gia_Man_t* pCircuit;
  bool boundary = false;
  bool printAllWords = false;
  bool printAnalysis = false;
  char * pFileSpec = NULL;

  meowBound* boundAPI = NULL;

  Extra_UtilGetoptReset();
  int c = 0;
  while(( c = Extra_UtilGetopt( argc, argv, "whbJr" ) ) != EOF ) {
    switch(c){
      case 'w':
        printAllWords = true;
        break;
      case 'J':

        if ( globalUtilOptind >= argc ){
           Abc_Print( -1, "Command line switch \"-J\" should be followed by a file name.\n" );
           goto usage;
        }
        pFileSpec = argv[globalUtilOptind];
        globalUtilOptind++;
        break;
      case 'r':
        printAnalysis = true;
        break;

      case 'b':
        boundary = true;
        break;
      case 'h':
        goto usage; 
        break; 
      default:
        goto usage;
    }
  } 
  if ( pAbc->pGia == NULL ){
     Abc_Print( -1, "Meow_CommandBound(): There is no GIA.\n" );
     return 1;
  }

  pCircuit = pAbc->pGia;
  if(Gia_ManRegNum(pCircuit) != 0){
    Abc_Print(-1, "meowBound only accepts combinational circuits.\n");
    return 1; 
  }
  boundAPI = new meowBound(pCircuit);
  boundAPI->runAll();
  if(boundary){
    boundAPI->printBoundaries(std::cerr);
   // boundAPI->printSupportBoundary(std::cerr);
  }
  if(printAllWords && pFileSpec == NULL) 
    boundAPI->printWord(printAllWords);
  if(pFileSpec != NULL){
    boundAPI->printJson(pFileSpec, printAllWords);
  }
  if(printAnalysis)
    boundAPI->simpleReport();
  delete boundAPI;
  return 0;
usage:
  meowUsageBound();
  return 1;
}

int Meow_CommandMux(Abc_Frame_t* pAbc, int argc, char** argv){
  Gia_Man_t* pCircuit;
  bool forward = true;
  bool printAllWords = false;

  meowMux* muxAPI = NULL;
  Extra_UtilGetoptReset();
  int c = 0;
  while(( c = Extra_UtilGetopt( argc, argv, "bw" ) ) != EOF ) {
    switch(c){
      case 'b':
        forward = false;
        break;
      case 'w':
        printAllWords = true;
        break;
      case 'h':
        goto usage; 
        break; 
      default:
        goto usage;
    }
  } 
  if ( pAbc->pGia == NULL ){
     Abc_Print( -1, "Meow_CommandMux(): There is no GIA.\n" );
     return 1;
  }

  pCircuit = pAbc->pGia;
  if(Gia_ManRegNum(pCircuit) != 0){
    Abc_Print(-1, "meowMux only accepts combinational circuits.\n");
    return 1; 
  }
  muxAPI = new meowMux(pCircuit);
  muxAPI->runAll(forward);

  if(printAllWords)
    muxAPI->reportWords();

  muxAPI->reportCount();
  muxAPI->reportDepth();
  delete muxAPI;
  return 0;
usage:
  meowUsageMux();
  return 1;
}
ABC_NAMESPACE_IMPL_END
