#include <stdio.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "assem.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "tree.h"
#include "frame.h"
#include "color.h"
#include "regalloc.h"

static int getOffset(TAB_table table,F_frame f,Temp_temp temp){
    F_access f_access = TAB_look(table, temp);
   	if (f_access == NULL) {
        f_access = F_allocLocal(f, TRUE);
        TAB_enter(table, temp, f_access);
    }
    return f_access->u.offset;
}

static Temp_temp getNewTemp(TAB_table table, Temp_temp oldTemp){
    Temp_temp Temp = TAB_look(table, oldTemp);
    if (Temp == NULL) {
        Temp = Temp_newtemp();
        TAB_enter(table, oldTemp, Temp);
    }
    return Temp;
}
 
static void removeRedundantMoves(Temp_map m,AS_instrList instrList){
    AS_instrList pre = NULL;
    while(instrList!=NULL) {
       	AS_instr as_instr = instrList->head;
       	if(as_instr->kind==I_MOVE&&strcmp(as_instr->u.MOVE.assem,"movl `s0,`d0\n")==0) {
        	Temp_tempList dst = as_instr->u.MOVE.dst;
           	Temp_tempList src = as_instr->u.MOVE.src;
           	string temp1 = Temp_look(m,dst->head);
           	string temp2 = Temp_look(m,src->head);
            assert(temp1&&temp2);

            if(temp1==temp2) {
                assert(pre);
                pre->tail = instrList->tail;
                instrList = instrList->tail;
                continue;
            }
        }
        pre = instrList;
        instrList = instrList->tail;
    }
}                                

static void rewriteProgram(F_frame f,Temp_tempList temp_tempList,AS_instrList instrList){
    AS_instrList pre = NULL;
    AS_instrList cur = instrList;
    TAB_table tempMapOffset = TAB_empty();

    while (cur != NULL) {
        AS_instr as_Instr = cur->head;
        Temp_tempList defTempList = NULL;
        Temp_tempList useTempList = NULL;
        switch (as_Instr->kind) {
        	case I_OPER:{
            	defTempList = as_Instr->u.OPER.dst;
            	useTempList = as_Instr->u.OPER.src;
            	break;
			}
        	case I_MOVE:{
            	defTempList = as_Instr->u.MOVE.dst;
            	useTempList = as_Instr->u.MOVE.src;
            	break;
			}
        	default:
            	break;
        }

        if(useTempList!=NULL||defTempList!=NULL) {
            TAB_table oldMapNew = TAB_empty();
            while (useTempList != NULL) {
                if (inTemp_tempList(useTempList->head, temp_tempList)) {
                    assert(pre);
                    Temp_temp newTemp = getNewTemp(oldMapNew, useTempList->head);
                    int offset = getOffset(tempMapOffset,f,useTempList->head);
                    char buf[20];
                    sprintf(buf,"    movl %d(`s0),`d0\n", offset);
                    string instr = String(buf);
                    AS_instr as_instr = AS_Move(instr, Temp_TempList(newTemp,NULL),Temp_TempList(F_EBP(),NULL));
                    useTempList->head = newTemp;
                    pre = pre->tail = AS_InstrList(as_instr,cur);
                }
                useTempList = useTempList->tail;
            }
            while (defTempList != NULL) {
                if (inTemp_tempList(defTempList->head, temp_tempList)) {
                    assert(pre);
                    Temp_temp newTemp = getNewTemp(oldMapNew, defTempList->head);
                    int offset = getOffset(tempMapOffset, f, defTempList->head);
                    char buf[20];
                    sprintf(buf,"    movl `s0,%d(`s1)\n", offset);
                    string instr = String(buf);
                    AS_instr as_instr = AS_Move(instr,NULL, Temp_TempList(newTemp,Temp_TempList(F_EBP(),NULL)));
                    cur->tail = AS_InstrList(as_instr, cur->tail);
                    defTempList->head = newTemp;
                }
                defTempList = defTempList->tail;
            }
        }
        pre = cur;
        cur = cur->tail;
    }
}

RA_result RA_regAlloc(F_frame f,AS_instrList instrList){
    	G_graph g_graph = FG_AssemFlowGraph(instrList);

    	Live_graph live_graph = Live_liveness(g_graph);

    	Temp_map initial = Temp_layerMap(Temp_empty(),F_precolored());
    	Temp_tempList regs = F_registers();
    	COL_result col_result = COL_color(live_graph,initial,regs);

    	if(col_result->spills!=NULL) {
        	rewriteProgram(f, col_result->spills, instrList);
        	return RA_regAlloc(f,instrList);
    	}

    	RA_result ra_result = checked_malloc(sizeof(*ra_result));
    	ra_result->coloring = col_result->coloring;
    	removeRedundantMoves(ra_result->coloring,instrList);
    	ra_result->il = instrList;
		
    	return ra_result;
}
