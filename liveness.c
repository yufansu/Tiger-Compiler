#include <stdio.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "table.h"
#include "temp.h"
#include "assem.h"
#include "tree.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"

Temp_temp Live_gtemp(G_node n){
  	return G_nodeInfo(n);
}

static void enterLiveMap(G_table t,G_node flowNode,Temp_tempList temp){
  	G_enter(t,flowNode,temp);
}

static Temp_tempList lookupLiveMap(G_table t,G_node flownode){
  	return (Temp_tempList)G_look(t,flownode);
}

static int setSize(Temp_tempList temp_tempList){
  	int size = 0;
  	for(;temp_tempList;temp_tempList=temp_tempList->tail)
		size++;
  	return size;
}

static G_nodeList reverseList(G_nodeList list){
  	G_nodeList reverse = NULL;
	
	for (;list; list=list->tail){
		reverse = G_NodeList(list->head,reverse);
	}

  	return reverse;
}

static bool isMember(Temp_tempList set,Temp_temp elem){
	for(;set;set=set->tail){
		if (set->head == elem){
			return TRUE;
		}
	}

  	return FALSE;
}

static G_node getNodeByTemp(TAB_table table,G_graph graph,Temp_temp temp){
  	G_node g_node = TAB_look(table,temp);
  	if(g_node==NULL){
    	g_node = G_Node(graph,temp);
   		TAB_enter(table,temp,g_node);
  	}
  	return g_node;
}

Live_moveList Live_MoveList(G_node src,G_node dst,Live_moveList tail){
  	Live_moveList live_moveList = checked_malloc(sizeof(*live_moveList));
  	live_moveList->src = src;
  	live_moveList->dst = dst;
  	live_moveList->tail = tail;
  	return live_moveList;
}

static Temp_tempList diffSet(Temp_tempList t_set1,Temp_tempList t_set2){
  	Temp_tempList re_head = NULL,re_tail = NULL,set1=t_set1;
  	while(set1!=NULL){
    	if(!isMember(t_set2,set1->head)){
      		Temp_tempList temp = Temp_TempList(set1->head,NULL);
      		if(re_tail==NULL){
        		re_head = re_tail = temp;
      		}
			else{
        		re_tail->tail = temp;
        		re_tail = re_tail->tail;
      		}
    	}
    	set1 = set1->tail;
  	}
  	return re_head;
}

static Temp_tempList unionSet(Temp_tempList t_set1,Temp_tempList t_set2){
  	Temp_tempList re_head = NULL,re_tail = NULL,set1 = t_set1,set2=t_set2;
  	while(set1!=NULL){
    	Temp_tempList temp = Temp_TempList(set1->head,NULL);
    	if(re_tail==NULL){
    		re_head = re_tail = temp;
    	}
		else{
    		re_tail = re_tail->tail = temp;
    	}
    	set1 = set1->tail;
  	}
  	while(set2!=NULL){
    	Temp_tempList temp = Temp_TempList(set2->head,NULL);
    	if(!isMember(t_set1,set2->head)){
      		if(re_tail == NULL){
        		re_head = re_tail = temp;
      		}
			else{
        		re_tail = re_tail->tail = temp;
      		}
    	}
    	set2 = set2->tail;
  	}
  	return re_head;
}

// for test
void showtemp(void* temp) {
	string tm;
	tm = Temp_look(F_tempMap, temp);
	printf("temp: %s\n", tm);
}

Live_graph Live_liveness(G_graph flow){
  	Live_graph live_graph = checked_malloc(sizeof(*live_graph));
  	G_graph g_graph = G_Graph();

  	Live_moveList live_moveList = NULL;
  	live_graph->graph = g_graph;
  	live_graph->moves = live_moveList;

  	G_table g_table_in = G_empty();
  	G_table g_table_out = G_empty();

  	G_nodeList g_nodeList = reverseList(G_nodes(flow));
  	G_nodeList p = g_nodeList;
  	bool hasChanged = FALSE;

  	while(p!=NULL || ((p=g_nodeList) && hasChanged && (hasChanged=FALSE)==FALSE)){
    	G_node g_node = p->head;

   		Temp_tempList oldTempList_in = lookupLiveMap(g_table_in,g_node);
   		Temp_tempList oldTempList_out = lookupLiveMap(g_table_out,g_node);
   		Temp_tempList newTempList_in = unionSet(FG_use(g_node),diffSet(oldTempList_out,FG_def(g_node)));
   		Temp_tempList newTempList_out = NULL;

    	G_nodeList succNodeList = G_succ(g_node);

    	while(succNodeList!=NULL){
      		G_node succNode = succNodeList->head;
      		newTempList_out = unionSet(newTempList_out,lookupLiveMap(g_table_in,succNode));
      		succNodeList = succNodeList->tail;
    	}

    	if(setSize(oldTempList_in)!=setSize(newTempList_in)){
      		hasChanged = TRUE;
      		enterLiveMap(g_table_in,g_node,newTempList_in);
    	}

    	if(setSize(oldTempList_out)!=setSize(newTempList_out)){
      		hasChanged = TRUE;
      		enterLiveMap(g_table_out,g_node,newTempList_out);
    	}
    	p = p->tail;
  	}

  	TAB_table Temp2Node = TAB_empty();

  	while(p!=NULL){
    	G_node g_node = p->head;
    	Temp_tempList defTempList = FG_def(g_node);
    	Temp_tempList useTempList = FG_use(g_node);
    	Temp_tempList tempList = lookupLiveMap(g_table_in, g_node);
    	AS_instr tmp_instr = G_nodeInfo(g_node);

    	if(FG_isMove(g_node)){
      		tempList = diffSet(tempList, useTempList);
    	}

    	while(defTempList!=NULL){
      		Temp_temp defTemp = defTempList->head;
      		G_node def_node = getNodeByTemp(Temp2Node,g_graph,defTemp);
      		while(tempList!=NULL){
        		Temp_temp temp_temp = tempList->head;
       			G_node g_node = getNodeByTemp(Temp2Node, g_graph, temp_temp);
        		G_addEdge(def_node, g_node);
        		G_addEdge(g_node, def_node);
        		tempList = tempList->tail;
      		}
      		defTempList = defTempList->tail;
    	}
    	p = p->tail;
  	}
  	return live_graph;
}
