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
#include "ext/meow/charNode.h"
#include "ext/meow/charGraph.h"
#include "aig/gia/gia.h"

#include<iostream>
using namespace std;
ABC_NAMESPACE_IMPL_START



void meowUsageOne(){
  Abc_Print( -2, "usage: meowOne <cir>  \n" );


}
void meowUsage(){

  Abc_Print( -2, "usage: meowSEC <cir1> <cir2> \n" );
  Abc_Print( -2, "\t perform clock-gating checking and  creates miter of <cir1> and <cir2>\n" );
 
}
void createVertex(charGraph* CG, Gia_Man_t* cir){
  // step 1: add PI
  int i;
  Gia_Obj_t* pObj; 
  Gia_Obj_t* pFanin, *pFanin2;
  int complement = 0;
  charNode* CGNode = NULL;
  Gia_ManForEachPi( cir, pObj, i ){
    CGNode = CG->addNewNode(0);
    CGNode->setPI();
    CG->addContainForNode(CGNode, Gia_ObjId( cir, pObj));
  }
  int currentID;
  Gia_Obj_t * pCtrl, * pData0, * pData1;
  // step 0: getFF and PO to find if their input is a Mux
  // collect groups by selection:
  Gia_ManForEachCo(cir, pObj, i){ // For PO and FF(Ri)
    // find their fanin
    //cerr<<" "<<i;
    currentID = Gia_ObjId(cir, pObj);
    pFanin = Gia_ObjFanin0(pObj);
    complement = Gia_ObjFaninC0(pObj); // if it's gets negate, input is negate 
    if( Gia_ObjIsMuxType(pFanin) ){ // this function only accept regular
      pCtrl = Gia_ObjRecognizeMux( pFanin, &pData1, &pData0);
      // control also can be negated
      int sId = Gia_ObjId(cir, pCtrl);
      //cerr<<"hello MUX "<< sId<<" ";

      CGNode = CG->getNodeBySelect(sId); 
      if(CGNode == NULL )
        CGNode = CG->addNewNode(sId);
      CG->addContainForNode(CGNode,currentID );
      // collet sellect!
    }
    else if ( Gia_ObjIsRo(cir, pFanin) ){ // it can be others FF!
      //add directly
      //cerr<<"meet Ro..."<<endl;
      Gia_Obj_t* RiForFanin = Gia_ObjRoToRi(cir, pFanin);
      if(Gia_ObjIsPo(cir,pObj)){ // get another Ro => add its Ri
        pFanin2 = Gia_ObjFanin0(RiForFanin);
        if( Gia_ObjIsMuxType(pFanin2) ){
          pCtrl = Gia_ObjRecognizeMux( pFanin2, &pData1, &pData0);
      //    cout<<"hello MUX "<< i<<" ";
          if(pCtrl!=Gia_Regular(pCtrl))
            cerr<<"BAD! get a negated Control!\n";
          int sId = Gia_ObjId(cir, pCtrl); 
          // notice that might be negate!
          CGNode = CG->getNodeBySelect(sId); 
          if(CGNode == NULL )
            CGNode = CG->addNewNode(sId);
        }
        else // just put them together
          CGNode = CG->addNewNode(0);
        
        CG->addContainForNode(CGNode, currentID);
        CG->addContainForNode(CGNode,Gia_ObjId(cir, RiForFanin));
      }
      else{ //just drive by other FF directly //notice
        if(CG->id2Node(currentID)  == NULL){
          CGNode = CG->addNewNode(0);
          CG->addContainForNode(CGNode, currentID);
        }
      } // special case for fanin is a Ro 
    }
    else{  //notice...
     // cerr<<"else?"<<endl;
      if(CG->id2Node(currentID)  == NULL){
        CGNode = CG->addNewNode(0);
        CG->addContainForNode(CGNode, currentID);
      }
    }
    if( Gia_ObjIsPo(cir,pObj))
      CGNode->setPO();   
  } 
  //cout<<"Done with create vertice"<<endl;
 

}
void traceRecur(Gia_Man_t* cir, Gia_Obj_t* current, set<int>& inList, int source, int* sourceList){
  //cerr<<inList.size()<<"from"<<source<<" ";
  if(current == NULL)
    return;
  current =  Gia_Regular(current);
  int currentID = Gia_ObjId(cir, current);
  if(sourceList[currentID] == source)
    return;
  sourceList[currentID] = source;

  if(Gia_ObjIsPi(cir,current)){ 
    inList.insert(Gia_ObjId(cir, current));
    //cerr<<"arrive "<< Gia_ObjId(cir, current)<<"from" <<source<<endl;

    return;
  }
  if( Gia_ObjIsRo(cir,current) ){
    Gia_Obj_t* Ri = Gia_ObjRoToRi(cir, current );
    inList.insert(Gia_ObjId(cir, Ri));
    //cerr<<"arrive "<< Gia_ObjId(cir, Ri)<<"from" <<source<<endl;

    return;
  }
  
    
  Gia_Obj_t* fanin1, *fanin2;
  fanin1 = Gia_ObjFanin0( current);    
  fanin2 = Gia_ObjFanin1( current ); 
 
//  if(fanin1 != current)  
  if(Gia_ManConst0(cir) != fanin1) 
    traceRecur(cir, fanin1, inList, source, sourceList);
  if(!Gia_ObjIsCo(current))
    traceRecur(cir, fanin2, inList, source, sourceList);

}
void connectDepend(charGraph* CG, Gia_Man_t* cir){
  int* sourceList = new int[Gia_ManObjNum(cir)];
  for(int meow = 0; meow < Gia_ManObjNum(cir); ++meow)
    sourceList[meow] = -1;


  Gia_Obj_t* currentObj;
  Gia_Obj_t* pFanin;
  Gia_Obj_t * pMux, * pCtrl, * pData0, * pData1; 
 // charNode* curVer;
  for(int i = 0; i < CG->nodeNum(); ++i){
   
  //1. for each vertex, get its node IDs
    vector<int> idList; // start with Ri/Po
    set<int> onList;
    set<int> offList;
    vector<Gia_Obj_t*> data0;
    onList.clear();
    idList.clear();
    offList.clear();
    data0.clear();
    CG->getContainID(idList, i);
  //2. start from those node backtrack and collect
    int select = CG->selectIdByNodeIndex(i);
    for(int j = 0; j < idList.size(); ++j){
      //cerr<< idList[j]<<":"<<select<<" ";

      currentObj = Gia_ManObj( cir,idList[j] );
      if(!Gia_ObjIsCo(currentObj) && !Gia_ObjIsPi(cir,currentObj))
        cerr<<"something wrong!!"<<endl;

      if(Gia_ObjIsPi( cir, currentObj ) )
        continue;
 
      pFanin = Gia_ObjFanin0( currentObj );
      if(Gia_ObjIsPo(cir, currentObj) && Gia_ObjIsRo(cir,pFanin)){
        //cerr<<"meet doube case!"<<endl;
        continue;

      }
      // we don't need to backtrack PI...
      if(select > 0){ // MUX 
        //
        pMux = Gia_ObjFanin0( currentObj );
        if(!Gia_ObjIsMuxType(pMux)) // Ro
          continue;
        pCtrl = Gia_ObjRecognizeMux( pMux, &pData1, &pData0);
        traceRecur(cir, pData1, onList, idList[0], sourceList);
        data0.push_back(pData0);
      }
      else {
       // if(Gia_ObjIsPo(currentObj)) 
        traceRecur(cir, currentObj, onList, idList[0], sourceList);
      }
    }
    for(unsigned k = 0; k < data0.size(); ++k){
      
      traceRecur(cir, data0[k], offList, -1*idList[0], sourceList);

    }
    CG->setDepend(onList, i, 1);
    CG->setDepend(offList,i, 0);
//    cerr<<endl;  
  //3. feed into CG, construct connection 
  }
  delete[] sourceList;
}
charGraph* constructCG(Gia_Man_t* cir){
  charGraph* CG = new charGraph( Gia_ManObjNum(cir));
  createVertex(CG, cir);
  connectDepend(CG, cir); 
 //collect Support ID one by one!
//  CG->printGraph(); 
  return CG;
}

ABC_NAMESPACE_IMPL_END
