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
extern charGraph* constructCG(Gia_Man_t* cir);


void labelNonEQ(Gia_Man_t* cir, charGraph* CG, vector<int>& nonEQ ){
  // notice that nonEQ record Co Index => find real index
  for(int i = 0; i < nonEQ.size(); ++i){
    int realId = Gia_ManCoIdToId( cir, nonEQ[i] ); 
     CG->addBadNode(realId);
  } 
}
void collectFFRecur(Gia_Man_t* cir, Gia_Obj_t* current, set<int>& FF, int token){
  if(current == NULL)
    return; 
  if(current->Value == token)
    return;

  current->Value = token;

  if(Gia_ObjIsPi(cir,current))
    return;
  if( Gia_ObjIsRo(cir,current) ){
    FF.insert(Gia_ObjId(cir, current));
//    cerr<<"arrive FF "<< Gia_ObjId(cir, current)<<"from" <<token<<endl;
    return;
  }
  
    
  Gia_Obj_t* fanin1, *fanin2;
  fanin1 = Gia_ObjFanin0( current);    
  fanin2 = Gia_ObjFanin1( current ); 
 
//  if(fanin1 != current)  
  if (fanin1 != Gia_ManConst0(cir) ) 
    collectFFRecur(cir, fanin1, FF, token);
  if(!Gia_ObjIsCo(current))
    collectFFRecur(cir, fanin2, FF, token);




}
bool collectProperty( Gia_Man_t* cir, charGraph* CG, set<int>& FF ){
  vector<int> idForSignal;
  CG->collectSignalID(idForSignal);
   // we have had essential id
  if(idForSignal.size() == 0)
    return false;
  Gia_Obj_t* currentObj;
  Gia_ManFillValue(cir);
  for(unsigned i = 0; i < idForSignal.size(); ++i){
    currentObj = Gia_ManObj( cir,idForSignal[i] );
    collectFFRecur(cir, currentObj, FF, idForSignal[i]);
  } 
  return true;
  //2. start from those ids traverse circuit! save into FF 
}

int Gia_ManCopy_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( ~pObj->Value )
        return pObj->Value;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManCopy_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManCopy_rec( pNew, p, Gia_ObjFanin1(pObj) );
    return pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}

Gia_Man_t* formulate(Gia_Man_t* cir, charGraph* CG){
  // step 1: collect the FF which should be duplicate
  set<int> FF;
  if(!collectProperty(cir, CG, FF))
    return NULL; // no property, no circuit
  
  Gia_Man_t * pNew, * pTemp;
  Gia_Obj_t * pObj;
  Gia_Obj_t * pObj2;
  Gia_Obj_t * pExtra;
  int i, iLit, andLit, orLit, outLit; //, andLit2, orLit2;
  pNew = Gia_ManStart( Gia_ManObjNum(cir));
    // map combinational inputs
  Gia_ManFillValue( cir );
  Gia_ManConst0(cir)->Value = 0;
  pNew->pName = Abc_UtilStrsav( "property" );
  Gia_ManHashAlloc( pNew );
  
  Gia_ManForEachPi( cir, pObj, i )
    pObj->Value = Gia_ManAppendCi( pNew );

  // for each required FF
  set<int>::iterator site = FF.begin();
  for(; site!= FF.end(); ++site){
    
    pObj = Gia_ManObj( cir,(*site) );
  //  if(Gia_ObjIsRo(cir, pObj))
  //    cout<<"this is Ci!"<<(*site)<<endl;
    // find its Ro => create Ci
    pObj->Value = Gia_ManAppendCi(pNew);
  }

  map<int, vector<int> >* propertyMap = CG->getProperty();
  map<int, vector<int> >::iterator mite;// = propertyMap->begin();
  vector<int> extraFF;
  //for(; mite != propertyMap->end(); ++mite){
  for(int j = 0; j < CG->propertyNum(); ++j){
    int targetID = CG->propertyTarget(j);
//    cout<<"Target ID"<<targetID<<endl;
    mite = propertyMap->find(targetID);
    if(targetID < 0){ // backward case
     // cout<<"backward Property"<<endl;
      //pObj = Gia_ManObj(cir, targetID*(-1));
      int vExtra = Gia_ManAppendCi(pNew); // for prev(in)
//      cout<<"extra FF: target ID "<<targetID<<endl;
      extraFF.push_back(targetID);

      int negIn = Abc_LitNot(vExtra); // check before  
      for(int k = 0; k < (mite->second).size(); k++){ 
        int outID = (mite->second)[k];
         pObj2 = Gia_ManObj(cir, outID);
         //TODO recur construct 

         outLit = Gia_ManCopy_rec( pNew, cir, pObj2 );
         andLit = Gia_ManHashAnd( pNew, outLit, vExtra );
        // andLit2 = Gia_ManHashAnd(pNew, outLit, negIn );
        // notice this(vExtra) is because of double negation!
        if(k == 0) 
          orLit = andLit;
        else 
          orLit = Gia_ManHashOr(pNew, orLit, andLit );
          
        //finally create OR 
      }
      Gia_ManAppendCo( pNew, orLit );
    }
    else{ //forward case
     // cout<<"forward property"<<endl;
      pObj2 = Gia_ManObj(cir, targetID);
      outLit = Gia_ManCopy_rec(pNew, cir, pObj2);
      int negOut = Abc_LitNot(outLit); 
      for(int k = 0; k < (mite->second).size(); k++){ // for each fanin
        int inExtra = Gia_ManAppendCi(pNew);
        extraFF.push_back((mite->second)[k]);
        andLit = Gia_ManHashAnd(pNew, inExtra,negOut);
        if(k == 0)
          orLit = andLit;
        else
          orLit = Gia_ManHashOr(pNew, orLit, andLit);
      }
      Gia_ManAppendCo(pNew, orLit);
    }
  }
  // add Ro /Ri
   // duplicate Ri
  site = FF.begin();
  for(; site!= FF.end(); ++site){
    
    pObj = Gia_ManObj( cir,(*site) );
    pObj2 = Gia_ObjRoToRi(cir, pObj);
 // Ro to Ri
 
    Gia_ManCopy_rec( pNew, cir, Gia_ObjFanin0(pObj2) );
    pObj2->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj2) );
        
  }
  for(unsigned k = 0; k < extraFF.size(); ++k){
    int oldID = extraFF[k];
    if(oldID < 0){
      int newLit =
        Gia_ManCopy_rec(pNew, cir, Gia_ManObj(cir, oldID*(-1))); 
      Gia_ManAppendCo(pNew,Abc_LitNot(newLit) ); // append not(signal)
    }
    else{
      int newLit =
        Gia_ManCopy_rec(pNew, cir, Gia_ManObj(cir, oldID)); 
      Gia_ManAppendCo(pNew,newLit );
    }
  }
//////////////final check!
  Gia_ManSetRegNum( pNew, extraFF.size()+FF.size() );
  Gia_ManHashStop( pNew );
  pNew = Gia_ManCleanup( pTemp = pNew );
  Gia_ManStop( pTemp );

  pNew = Gia_ManDupNormalize( pTemp = pNew, 0 );
  Gia_ManStop( pTemp );


  return pNew;
}
Gia_Man_t* reduce(Gia_Man_t* cir, charGraph* CG, vector<int> result){
  // create new Aig with Proved property
  //result is proved property index
  Gia_Man_t* newCir = Gia_ManDup(cir);//first duplicate it


  for(int i = 0; i < result.size(); ++i){
    int index = result[i];
    vector<int> CoList;
    CoList.clear();
    
    int select = CG->getTargetByIndex(index, CoList);
    Gia_Obj_t* selectObj = Gia_ManObj(cir,select);
    for(int j = 0; j < CoList.size(); ++j){
      int comp = 0;
      Gia_Obj_t* currentCo = Gia_ManObj(cir, CoList[j]);
      if( Gia_ObjFaninC0(currentCo)){
        comp = 1;
       // cout<<"Mux Comp"<<endl;
      }
      Gia_Obj_t* fanin0 = Gia_ObjFanin0(currentCo);
      Gia_Obj_t * pData1, * pData0, *pCtrl; 
      if( Gia_ObjIsRo( cir, fanin0 ) )
        continue; // special case: fanin 0 is just a Ro
      if(!Gia_ObjIsMuxType(fanin0))
        cout<<"Something wrong!!!!\n";
 
      pCtrl = Gia_ObjRecognizeMux( fanin0, &pData1, &pData0);
      if(pCtrl != selectObj)
        cout<<"Control Negate?"<<pCtrl<<":"<<selectObj<<endl;
 
      Gia_Obj_t* newCo = Gia_ObjCopy( newCir, currentCo);// get in New 
     
      if(Gia_IsComplement(pData1)){
       // if(Abc_LitIsCompl(pData1->Value))
       //   cout<<"Complement??";
        Gia_Obj_t* regularData1 = Gia_Regular(pData1);
        int realV = regularData1->Value;
        newCo->iDiff0 = Gia_ObjId(newCir, newCo) - Abc_Lit2Var(realV);
        newCo->fCompl0 = comp^01; // TODO check
      }
      else{
        cout<<"Non Complement?";
        newCo->iDiff0= Gia_ObjId(newCir, newCo)- Abc_Lit2Var(pData1->Value);
        newCo->fCompl0 = 00^comp; //^ Abc_LitIsCompl(pData1->Value); //TODO check
      }
      //cout<<select<<" "<<CoList[j]<<endl;
    }
  }
  return newCir;
}
void FindCandidate(Gia_Man_t* pGolden, Gia_Man_t* pRevise, vector<int>& list){
  Gia_Man_t* pHelper;
  pHelper = Gia_ManMiter(pGolden, pRevise, 0 , 0 , 0 , 0 ,0);
  // note: create combinational miter the FFs should be mapped 
  Gia_Obj_t* pPo;
  int index = 0;
  Gia_ManForEachPo( pHelper, pPo, index ){
    if(!Gia_ManPoIsConst0( pHelper, index )){ //NON-EQ points
      list.push_back(index); // index is Co index for both 
    }
  }
  Gia_ManStop(pHelper);
}
Gia_Man_t* simplifyCircuit(Gia_Man_t* cir, vector<int> nonEQ, int flag){
  charGraph* CG = constructCG(cir);
  labelNonEQ(cir, CG, nonEQ);
  Gia_Man_t* property = formulate(cir, CG);
  int result, id;
  vector<int> proved;
  if(property!= NULL){
    //char pfile[] = "r_p.aig";
   // if(flag)
   //   pfile = "g_p.aig";
    //else
      //pfile = "r_p.aig";
    if(flag)
      Gia_AigerWrite(property, "r_p.aig", 0, 0);
    else
      Gia_AigerWrite(property, "g_p.aig", 0, 0);
    FILE* resultF;
    if(flag)
      resultF  = popen("~/pyabc_distribution/bin/multi_prove ./r_p.aig","r" );
    else
      resultF = popen("~/pyabc_distribution/bin/multi_prove ./g_p.aig","r" );

     
     while (fscanf(resultF,"%d \n b%d \n.",&result,&id)!=EOF){ 
      //cout<<id<<":"<<result<<endl;; 
      if(result == 0){
        cout<<"Property "<<id<<" is verified.\n";
        proved.push_back(id);

      } 
    }
  }
  Gia_Man_t* pNew;
  if(proved.size() > 0){
    pNew = reduce(cir, CG, proved);
  }
  else
    pNew = cir;
  delete CG;
  return pNew;
}
 // TODO make a beautiful SEC main function
ABC_NAMESPACE_IMPL_END
