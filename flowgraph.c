#include <stdio.h>
#include <assert.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "errormsg.h"
#include "table.h"
#include "flowgraph.h"

Temp_tempList FG_def(G_node n) {
	AS_instr ptr;
	assert(n!=NULL);
	ptr = (AS_instr)G_nodeInfo(n);
    switch(ptr->kind) {
	case I_OPER: {
		return ptr->u.OPER.dst;
				 }
	case I_MOVE: {
		return ptr->u.MOVE.dst;
				 }
	case I_LABEL: {
		return NULL;
				  }
	default: {
		assert(0);
		return NULL; /*avoid compiler warning*/
			 }
	}
}

Temp_tempList FG_use(G_node n) {
	AS_instr ptr;
	assert(n!=NULL);
	ptr = (AS_instr)G_nodeInfo(n);
	switch(ptr->kind) {
	case I_OPER: {
		return ptr->u.OPER.src;
				 }
	case I_MOVE: {
		return ptr->u.MOVE.src;
				 }
	case I_LABEL: {
		return NULL;
				  }
	default: {
		assert(0);
		return NULL; /*avoid compiler warning*/
			 }
	}
}

bool FG_isMove(G_node n) {
	AS_instr ptr;
	assert(n!=NULL);
	ptr = (AS_instr)G_nodeInfo(n);
	switch(ptr->kind) {
	case I_OPER: {
		return FALSE;
				 }
	case I_MOVE: {
		return TRUE;
				 }
	case I_LABEL: {
		return FALSE;
				  }
	default: {
		assert(0);
		return FALSE; /*avoid compiler warning*/
			 }
	}
}

struct G_nodeMap {TAB_table tab; G_graph graph; G_nodeList list;};
static struct G_nodeMap createMapping(AS_instrList il) {
	G_table tab = TAB_empty();
	G_graph graph = G_Graph();
	G_nodeList list = NULL, plast = NULL;
	G_node node;
	AS_instrList ptr;
	struct G_nodeMap map;
	for(ptr = il;ptr != NULL; ptr = ptr->tail) {
		node = G_Node(graph, ptr->head);
		if(list == NULL) {
			list = G_NodeList(node, NULL);
		    plast = list;
		}
		else {
			plast->tail = G_NodeList(node, NULL);
			plast = plast->tail;
		}
		if(ptr->head->kind == I_LABEL) {
			TAB_enter(tab, ptr->head->u.LABEL.label, node);
		}
	}
	map.graph = graph;
	map.list = list;
	map.tab = tab;
	return map;
}


G_graph FG_AssemFlowGraph(AS_instrList il) {
	G_graph graph;
	G_node node1, node2;
	AS_instr ins;
	G_nodeList list;
	struct G_nodeMap map;
	assert(il!=NULL);
	map = createMapping(il);
	graph = map.graph;
	for(list = map.list; list != NULL; list= list->tail) {
		node1 = list->head;
		ins = (AS_instr)G_nodeInfo(node1);
		switch(ins->kind) {
		case I_OPER: {
			if(ins->u.OPER.jumps != NULL) {
				Temp_labelList labs = ins->u.OPER.jumps->labels;
				for(;labs != NULL; labs = labs->tail) {
					node2 = (G_node)TAB_look(map.tab, labs->head);
					G_addEdge(node1, node2);
				}
			}
			else {
				if(list->tail != NULL) {
					node2 = list->tail->head;
					G_addEdge(node1, node2);
				}
			}
			break;
					 }
		case I_MOVE: {
			if(list->tail != NULL) {
				node2 = list->tail->head;
				G_addEdge(node1, node2);
			}
			break;
					 }
		case I_LABEL: {
			if(list->tail != NULL) {
				node2 = list->tail->head;
				G_addEdge(node1, node2);
			}
			break;
					  }
		default: {
			assert(0);
				 }
		}
	}
	return graph;
}

//for test
void FG_showAssem(void* ins) {
    AS_print(stdout, ins, F_tempMap);
}









	