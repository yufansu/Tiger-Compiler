#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "table.h"
#include "temp.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"

// static variables
static G_color_nodeList precoloredList = NULL;
static G_color_nodeList simWorkList = NULL;
static G_color_nodeList freezeWorkList = NULL;
static G_color_nodeList spillWorkList = NULL;
static G_color_nodeList spiltNodes  = NULL;
static G_color_nodeList coalescedNodes = NULL;
static G_color_nodeList colouredNodes = NULL;
static G_color_nodeList selectStack = NULL;

static Live_color_moveList coalescedMoves = NULL;
static Live_color_moveList constraintMoves = NULL;
static Live_color_moveList frozenMoves = NULL;
static Live_color_moveList worklistMoves = NULL;
static Live_color_moveList activeMoves = NULL;

static int length;
static int K;
static int* degree = NULL;
static G_color_nodeList* adjList = NULL;
static bool* adjSet = NULL;
static TAB_table moveList = NULL;
static TAB_table alias = NULL;
static Temp_map colour = NULL;
static TAB_table G_nodeMapG_node_two = NULL;
static Temp_tempList registers = NULL;

// initialize
void initAdjSet(int n);
void initAdjList(int n);
void initDegree(int n);
void init(int n, Temp_map inital,Temp_tempList regs);

// check the List
static bool isContain_g(G_color_nodeList*,G_color_node);
static bool isContain_live(Live_color_moveList*,Live_color_moveList_node);

// new self defined object
G_color_node G_Color_Node(G_node node);
G_color_nodeList G_Color_NodeList(G_color_node node,G_color_nodeList pre,G_color_nodeList next);
Live_color_moveList_node Live_Color_MoveList_Node(Live_moveList move);
Live_color_moveList Live_Color_MoveList(Live_color_moveList_node value, Live_color_moveList pre, Live_color_moveList next);

static Live_color_moveList NodeMoves(G_color_node node);
static bool moveRelated(G_color_node node);
static void push(G_color_nodeList* stack, G_color_node node);
static bool isLink(int m, int n);
static void addEdge_(int m,int n);
static void addEdge(G_color_node node_one, G_color_node node_two);
static void makeWorklist(G_color_nodeList initial);
static void addWorkList(G_color_node node);
static bool OK(G_color_node t, G_color_node r);
static bool conservative(G_color_nodeList nodes);
static void combine(G_color_node u, G_color_node v);
static void freezeMoves(G_color_node u);

// append
static void append_g(G_color_nodeList* set,G_color_node node);
static void append_live(Live_color_moveList* set, Live_color_moveList_node node);

// check
static bool isContain_g(G_color_nodeList* set, G_color_node node);
static bool isContain_live(Live_color_moveList* set, Live_color_moveList_node node);
static G_color_nodeList diffSet_one(G_color_nodeList set_one_,G_color_nodeList set_two_);
static Live_color_moveList interSet_two(Live_color_moveList set_one, Live_color_moveList set_two);

// delete
static void delete_g(G_color_nodeList* set_, G_color_node node);
static void delete_live(Live_color_moveList* set_, Live_color_moveList_node node);
static void delete_three(Stringlist * set_, string node);

// operations
static G_color_node peek_one(G_color_nodeList* set);
static G_color_node pop_one(G_color_nodeList* stack);
static Live_color_moveList_node peek_two(Live_color_moveList* set);

// node operation
static void simplify();
static G_color_nodeList adjacent(G_color_node node);
static void enableMoves(G_color_nodeList g_nodeList_two);
static void decrementDegree(G_color_node node);
static G_color_node getAlias(G_color_node node);

static void freeze();
static void selectSpill();
static Stringlist StringList(string node,Stringlist pre,Stringlist next);
static Stringlist allcolours();
static void assigncolours();

static bool isEmpty_g(G_color_nodeList set){
  	return set==NULL;
}
static bool isEmpty_live(Live_color_moveList set){
  	return set==NULL;
}
static bool isEmpty_three(Stringlist stringlist){
	return stringlist == NULL;
}
void initAdjSet(int n){
	adjSet = checked_malloc(n*n*sizeof(bool));
	int i;
	for(i=0;i<n*n;i++){
		adjSet[i] = FALSE;
	}
}

void initAdjList(int n){
	adjList = checked_malloc(n*sizeof(G_color_nodeList));
	int i;
	for(i = 0;i < n;i++){
		adjList[i] = NULL;
	}
}

void initDegree(int n){
	degree = checked_malloc(n*sizeof(int));
	int i;
	for(i = 0;i < n;i++){
		degree[i] = 0;
	}
}

static void freeze(){
	G_color_node node = peek_one(&freezeWorkList);
	append_g(&simWorkList, node);
	freezeMoves(node);
}

static void selectSpill(){
	G_color_node m = peek_one(&spillWorkList);
	append_g(&simWorkList, m);
	freezeMoves(m);
}
//Inital all the value
void init(int n, Temp_map inital,Temp_tempList regs){
	length = n;
	K = lengthOfTempList(regs);
	initAdjSet(n);
	initAdjList(n);
	initDegree(n);

	moveList = TAB_empty();
	alias = TAB_empty();
	colour = inital;
	G_nodeMapG_node_two = TAB_empty();

    registers = regs;
    selectStack = NULL;
    coalescedMoves = NULL;
    constraintMoves = NULL;
    frozenMoves = NULL;
    worklistMoves = NULL;
    activeMoves = NULL;
    precoloredList = NULL;
    simWorkList = NULL;
    freezeWorkList = NULL;
    spillWorkList = NULL;
    spiltNodes  = NULL;
    coalescedNodes = NULL;
    colouredNodes = NULL;
}

G_color_node G_Color_Node(G_node node){
	G_color_node g_node_two = checked_malloc(sizeof(*g_node_two));
	g_node_two->node = node;
	g_node_two->kind = DEFAULT1;

    TAB_enter(G_nodeMapG_node_two, node, g_node_two);
	return g_node_two;
}

G_color_nodeList G_Color_NodeList(G_color_node node,G_color_nodeList pre,G_color_nodeList next){
  	G_color_nodeList g_nodeList_two = checked_malloc(sizeof(*g_nodeList_two));
  	g_nodeList_two->value = node;
  	g_nodeList_two->pre = pre;
  	g_nodeList_two->next = next;
  	return g_nodeList_two;
}

Live_color_moveList_node Live_Color_MoveList_Node(Live_moveList move){
	Live_color_moveList_node live_moveList_twonode = checked_malloc(sizeof(*live_moveList_twonode));
	live_moveList_twonode->move = move;
	live_moveList_twonode->kind = DEFAULT_two;
	return live_moveList_twonode;
}
Live_color_moveList Live_Color_MoveList(Live_color_moveList_node value, Live_color_moveList pre, Live_color_moveList next){
  	Live_color_moveList live_moveList_two = checked_malloc(sizeof(*live_moveList_two));
  	live_moveList_two->value = value;
  	live_moveList_two->pre = pre;
  	live_moveList_two->next = next;
  	return live_moveList_two;
}

static G_color_nodeList unionSet_one(G_color_nodeList set_one_,G_color_nodeList set_two_){
  	G_color_nodeList head = NULL,tail = NULL,set_one=set_one_,set_two=set_two_;
  	while(set_one!=NULL){
    	G_color_nodeList node = G_Color_NodeList(set_one->value,tail,NULL);
    	if(tail==NULL){
      		head = tail = node;
    	}
		else{
      		tail = tail->next = node;
    	}
    	set_one = set_one->next;
  	}

 	while(set_two!=NULL){
    	G_color_nodeList node = G_Color_NodeList(set_two->value,tail,NULL);
    	
    	if(!isContain_g(&set_one_,set_two->value)){
      		if(tail==NULL){
        		head = tail = node;
      		}
			else{
        		tail = tail->next = node;
      		}
    	}
    	set_two = set_two->next;
  	}
 	return head;
}

static Live_color_moveList unionSet_two(Live_color_moveList set_one_, Live_color_moveList set_two_){
  	Live_color_moveList head = NULL;
	Live_color_moveList tail = NULL;
	Live_color_moveList set_one = set_one_;
	Live_color_moveList set_two = set_two_;

	while (set_one != NULL){
		Live_color_moveList node = Live_Color_MoveList(set_one->value, tail, NULL);
		if (tail == NULL){
			head = tail = node;
		}
		else{
			tail = tail->next = node;
		}
		set_one = set_one->next;
	}
	while (set_two != NULL){
		Live_color_moveList node = Live_Color_MoveList(set_two->value, tail, NULL);
            if(!isContain_live(&set_one_,set_two->value)){
                if (tail == NULL){
                	head = tail = node;
                }
                else{
                	tail = tail->next = node;
                }
            }
		set_two = set_two->next;
	}
	return head;
}

static void append_g(G_color_nodeList* set,G_color_node node){
	if (*set == precoloredList){
		node->kind = PREcolourED;
	}
	else if (*set == simWorkList){
		node->kind = SIMPLIFYWORKLIST;
	}
	else if (*set == freezeWorkList){
		node->kind = FREEZEWORKLIST;
	}
	else if (*set == spillWorkList){
		node->kind = SPILLWORKLIST;
	}
	else if (*set == spiltNodes){
		node->kind = spiltNODES;
	}
	else if (*set == coalescedNodes){
		node->kind = COALESCEDNODES;
	}
	else if (*set == colouredNodes){
		node->kind = colourEDNODES;
	}
	else if (*set == selectStack){
		node->kind = SELECTSTACK;
	}

	G_color_nodeList g_nodeList_two = G_Color_NodeList(node, NULL, NULL);
	if (*set == NULL){
		*set = g_nodeList_two;
	}
	else{
		(*set)->pre = g_nodeList_two;
		g_nodeList_two->next = (*set);
		(*set) = g_nodeList_two;
	}
}

static void append_live(Live_color_moveList* set, Live_color_moveList_node node){
	if (*set == coalescedMoves){
		node->kind = COALESCEDMOVES;
	}
	else if (*set == constraintMoves){
		node->kind = CONSTRAINTMOVES;
	}
	else if (*set == frozenMoves){ 
		node->kind = FROZENMOVES;
	}
	else if (*set == worklistMoves){
		node->kind = WORKLISTMOVES;
	}
	else if (*set == activeMoves){
		node->kind = ACTIVEMOVES;
	}
	Live_color_moveList live_moveList_two = Live_Color_MoveList(node, NULL, NULL);
	if (*set == NULL){
		*set = live_moveList_two;
	}
	else{
		(*set)->pre = live_moveList_two;
		live_moveList_two->next = (*set);
		(*set) = live_moveList_two;
	}
}

static bool isContain_g(G_color_nodeList* set, G_color_node node){
  assert(set&&node);
	if (set == &precoloredList){
		return node->kind == PREcolourED;
	}
	else if (set == &simWorkList){
		return node->kind == SIMPLIFYWORKLIST;
	}
	else if (set == &spillWorkList){
		return node->kind == SPILLWORKLIST;
	}
	else if (set == &spiltNodes){
		return node->kind == spiltNODES;
	}
	else if (set == &coalescedNodes){
		return node->kind == COALESCEDNODES;
	}
	else if (set == &colouredNodes){
		return node->kind == colourEDNODES;
	}
	else if (set == &selectStack){
		return node->kind == SELECTSTACK;
	}
	else if (set == &freezeWorkList){
		return node->kind == FREEZEWORKLIST;
	}
        G_color_nodeList set_ = *set;
	while (set_ != NULL){
		if (set_->value == node){
			return TRUE;
		}
		set_ = set_->next;
	}
	return FALSE;
}
static bool isContain_live(Live_color_moveList* set, Live_color_moveList_node node){
  assert(set&&node);
	if (set == &coalescedMoves){
		return node->kind == COALESCEDMOVES;
	}
	else if (set == &constraintMoves){
		return node->kind == CONSTRAINTMOVES;
	}
	else if (set == &frozenMoves){
		return node->kind == FROZENMOVES;
	}
	else if (set == &worklistMoves){
		return node->kind == WORKLISTMOVES;
	}
	else if (set == &activeMoves){
		return node->kind == ACTIVEMOVES;
	}
        Live_color_moveList set_ = *set;
	while (set_ != NULL){
		if (set_->value == node){
			return TRUE;
		}
		set_ = set_->next;
	}
	return FALSE;
}

static G_color_nodeList diffSet_one(G_color_nodeList set_one_,G_color_nodeList set_two_){
  G_color_nodeList head = NULL, tail=NULL,set_one=set_one_;
	while (set_one != NULL){
		if (!isContain_g(&set_two_, set_one->value)){
			if (tail == NULL){
				head = tail = G_Color_NodeList(set_one->value, NULL, NULL);
			}
			else{
				G_color_nodeList node = G_Color_NodeList(set_one->value, tail, NULL);
				tail = tail->next = node;
			}
		}
		set_one = set_one->next;
	}
	return head;
}
static Live_color_moveList interSet_two(Live_color_moveList set_one, Live_color_moveList set_two){
	Live_color_moveList head=NULL, tail=NULL;
	while (set_one != NULL){
		if (isContain_live(&set_two, set_one->value)){
			if (tail == NULL){
				head = tail = Live_Color_MoveList(set_one->value, NULL, NULL);
			}
			else{
				Live_color_moveList node = Live_Color_MoveList(set_one->value, tail, NULL);
				tail = tail->next = node;
			}
		}
		set_one = set_one->next;
	}
	return head;
}



static void delete_g(G_color_nodeList* set_, G_color_node node){
	assert(*set_);
	G_color_nodeList set = *set_;
	while (set != NULL){
		if (set->value == node){
			if (set->pre != NULL){
				set->pre->next = set->next;
			}
			if (set->next != NULL){
				set->next->pre = set->pre;
			}
			break;
		}
		set = set->next;
	}
	if ((*set_)->value == node){
          	*set_ = (*set_)->next;
	}
}
static void delete_live(Live_color_moveList* set_, Live_color_moveList_node node){
	assert(*set_);
	Live_color_moveList set = *set_;
	while (set != NULL){
		if (set->value == node){
			if (set->pre != NULL){
				set->pre->next = set->next;
			}
			if (set->next != NULL){
				set->next->pre = set->pre;
			}
			break;
		}
		set = set->next;
	}
	if ((*set_)->value == node){
          	*set_ = (*set_)->next;
	}
}

static void delete_three(Stringlist * set_, string node){
	assert(*set_);
	Stringlist set = *set_;
	while (set != NULL){
		if (set->node == node){
			if (set->pre != NULL){
				set->pre->next = set->next;
			}
			if (set->next != NULL){
				set->next->pre = set->pre;
			}
			break;
		}
		set = set->next;
	}
	if ((*set_)->node == node){
          *set_ = (*set_)->next;
	}
}

static G_color_node peek_one(G_color_nodeList* set){
  	assert(*set);
  	G_color_node node = (*set)->value;
  	delete_g(set, node);
  	return node;
}

static G_color_node pop_one(G_color_nodeList* stack){
	return peek_one(stack);
}

static Live_color_moveList_node peek_two(Live_color_moveList* set){
	if (*set != NULL){
		Live_color_moveList_node node = (*set)->value;
		delete_live(set, node);
		return node;
	}
	return NULL;
}

static Live_color_moveList NodeMoves(G_color_node node){
	return interSet_two(TAB_look(moveList, node), unionSet_two(activeMoves, worklistMoves));
}

static bool moveRelated(G_color_node node){
	return !isEmpty_live(NodeMoves(node));
}

static void push(G_color_nodeList* stack, G_color_node node){
	append_g(stack, node);
}

static bool isLink(int m, int n){
	int adjSetLength = m*length + n;
	return adjSet[adjSetLength];
}

static void addEdge_(int m,int n){
	int adjSetLength = m*length + n;
	adjSet[adjSetLength] = TRUE;
}

static void addEdge(G_color_node node_one, G_color_node node_two){
	int m = node_one->node->mykey;
	int n = node_two->node->mykey;

	if (m != n&&!isLink(m,n)){
		addEdge_(m, n);
		addEdge_(n, m);
		if (node_one->kind != PREcolourED){
			append_g(&adjList[m], node_two);
		}
		if (node_two->kind != PREcolourED){
			append_g(&adjList[n], node_one);
		}
	}
}


static void makeWorklist(G_color_nodeList initial){
	while (initial != NULL){
		G_color_node g_node_two = initial->value;
		int pos = g_node_two->node->mykey;
		if (degree[pos] >= K){
			append_g(&spillWorkList, g_node_two);
		}
		else if (moveRelated(g_node_two)){
			append_g(&freezeWorkList, g_node_two);
		}
		else{
			append_g(&simWorkList, g_node_two);
		}
		initial = initial->next;
	}
}

static G_color_nodeList adjacent(G_color_node node){
	return diffSet_one(adjList[node->node->mykey], unionSet_one(selectStack, coalescedNodes));
}

static void enableMoves(G_color_nodeList g_nodeList_two){
	while (g_nodeList_two != NULL){
		Live_color_moveList live_moveList_two = NodeMoves(g_nodeList_two->value);
		while (live_moveList_two != NULL){
			if (live_moveList_two->value->kind == ACTIVEMOVES){
				delete_live(&activeMoves, live_moveList_two->value);
				append_live(&worklistMoves, live_moveList_two->value);
			}
			live_moveList_two = live_moveList_two->next;
		}
		g_nodeList_two = g_nodeList_two->next;
	}
}

static void decrementDegree(G_color_node node){
	int this_degree = degree[node->node->mykey];
	degree[node->node->mykey]--;
	if (this_degree == K){
		enableMoves(unionSet_one(adjacent(node), G_Color_NodeList(node, NULL, NULL)));
		delete_g(&spillWorkList, node);
		if (moveRelated(node)){
			append_g(&freezeWorkList, node);
		}
		else{
			append_g(&simWorkList, node);
		}
	}
}

static void simplify(){
	if (simWorkList != NULL){
		G_color_node node = peek_one(&simWorkList);
		push(&selectStack, node);
		G_color_nodeList g_nodeList = adjacent(node);
		while (g_nodeList != NULL){
			decrementDegree(g_nodeList->value);
			g_nodeList = g_nodeList->next;
		}
	}
}

static G_color_node getAlias(G_color_node node){
  assert(node);
	if (isContain_g(&coalescedNodes, node)){
		getAlias(TAB_look(alias, node));
	}
	return node;
}


static void addWorkList(G_color_node node){
	if (!isContain_g(&precoloredList,node) && !moveRelated(node) && degree[node->node->mykey] < K){
		delete_g(&freezeWorkList, node);
		append_g(&simWorkList, node);
	}
}

static bool OK(G_color_node t, G_color_node r){
	return degree[t->node->mykey] < K || isContain_g(&precoloredList, t) || isLink(t->node->mykey, r->node->mykey);
}

static bool conservative(G_color_nodeList nodes){
	int k = 0;
	while (nodes != NULL){
		if (degree[nodes->value->node->mykey] >= K){
			k++;
		}
		nodes = nodes->next;
	}
	return k < K;
}

static void combine(G_color_node u, G_color_node v){
	if (isContain_g(&freezeWorkList,v)){
		delete_g(&freezeWorkList, v);
	}
	else{
		delete_g(&spillWorkList, v);
	}

	append_g(&coalescedNodes, v);
	TAB_enter(alias, v, u);
	TAB_enter(moveList,u,unionSet_two(TAB_look(moveList, u), TAB_look(moveList, v)));
	enableMoves(G_Color_NodeList(v, NULL, NULL));
	G_color_nodeList g_nodeList_two = adjacent(v);
	while (g_nodeList_two != NULL){
		addEdge(g_nodeList_two->value, u);
		decrementDegree(g_nodeList_two->value);
		g_nodeList_two = g_nodeList_two->next;
	}
	if (degree[u->node->mykey] >= K&&isContain_g(&freezeWorkList,u)){
		delete_g(&freezeWorkList, u);
		append_g(&spillWorkList, u);
	}
}

static void Noneed_coalesce(){
	Live_color_moveList_node  node = peek_two(&worklistMoves);
    assert(node->move->dst&&node->move->src);

	G_color_node x = getAlias(TAB_look(G_nodeMapG_node_two, node->move->dst));
	G_color_node y = getAlias(TAB_look(G_nodeMapG_node_two, node->move->src));
	G_color_node u = x;
	G_color_node v = y;

	if (isContain_g(&precoloredList, y)){
		u = y;
		v = x;
	}
	if (u == v){
		append_live(&coalescedMoves, node);
		addWorkList(u);
	}
	else if (isContain_g(&precoloredList, v) || isLink(u->node->mykey,v->node->mykey)){
		append_live(&constraintMoves, node);
		addWorkList(u);
		addWorkList(v);
	}
	else {
		bool bFlag = TRUE;
		if (isContain_g(&precoloredList, u)){
			G_color_nodeList g_nodeList_two = adjacent(v);
			while (g_nodeList_two != NULL){
				if (!OK(g_nodeList_two->value, u)){
					bFlag = FALSE;
					break;
				}
				g_nodeList_two = g_nodeList_two->next;
			}
		}
		else{
			bFlag = FALSE;
		}
		if(bFlag || (!isContain_g(&precoloredList, u) && conservative(unionSet_one(adjacent(u), adjacent(v))))){
			append_live(&coalescedMoves, node);
			combine(u, v);
			addWorkList(u);
		}
		else{
			append_live(&activeMoves, node);
		}
	}
}

static void freezeMoves(G_color_node u){
	Live_color_moveList live_moveList_two = NodeMoves(u);
	while (live_moveList_two != NULL){
		Live_color_moveList_node m = live_moveList_two->value;
		G_color_node x = TAB_look(G_nodeMapG_node_two,m->move->dst);
		G_color_node y = TAB_look(G_nodeMapG_node_two, m->move->src);
		G_color_node v = getAlias(y);
		if (getAlias(y) == getAlias(u)){
			v = getAlias(x);
		}
		delete_live(&activeMoves, m);
		append_live(&frozenMoves, m);
		if (isEmpty_live(NodeMoves(v)) && degree[v->node->mykey] < K){
			delete_g(&freezeWorkList, v);
			append_g(&simWorkList, v);
		}
		live_moveList_two = live_moveList_two->next;
	}
}


static Stringlist StringList(string node,Stringlist pre,Stringlist next){
	Stringlist stringlist = checked_malloc(sizeof(*stringlist));
	stringlist->node = node;
	stringlist->pre = pre;
	stringlist->next = next;

	return stringlist;
}

static Stringlist allcolours(){
	Stringlist head = NULL,tail = NULL;
	Temp_tempList regs = registers;
	while(regs!=NULL){
		string node = Temp_look(colour,regs->head);
		Stringlist temp  = StringList(node,tail,NULL);
		if(tail == NULL){
			head = tail = temp;
		}else{
			tail = tail->next = temp;
		}
        regs = regs->tail;
	}
	return head;
}



static void assigncolours(){
	while (!isEmpty_g(selectStack)){
		G_color_node n = pop_one(&selectStack);
		Stringlist okcolours = allcolours();
		G_color_nodeList g_nodeList_two = adjList[n->node->mykey];
		while (g_nodeList_two){
			G_color_node w = g_nodeList_two->value;
            getAlias(w);
            G_color_nodeList tempNodeList = unionSet_one(colouredNodes,precoloredList);
            if(isEmpty_three(okcolours)){
                break;
            }

			if(isContain_g(&tempNodeList,getAlias(w))){
				string strcolour = Temp_look(colour, getAlias(w)->node->info);
				delete_three(&okcolours, strcolour);
			}
			g_nodeList_two = g_nodeList_two->next;
		}
		if (isEmpty_three(okcolours)){
			append_g(&spiltNodes, n);
		}
		else{
			append_g(&colouredNodes, n);
			Temp_enter(colour, n->node->info, okcolours->node);
		}
	}
	G_color_nodeList g_nodeList_two = coalescedNodes;
	while (g_nodeList_two != NULL){
		Temp_enter(colour, g_nodeList_two->value->node->info, Temp_look(colour, getAlias(g_nodeList_two->value)->node->info));
		g_nodeList_two = g_nodeList_two->next;
	}
}

static void coalesce(){
	Live_color_moveList_node node = peek_two(&worklistMoves);
    assert(node->move->dst&&node->move->src);
	G_color_node x = getAlias(TAB_look(G_nodeMapG_node_two, node->move->dst));
	G_color_node y = getAlias(TAB_look(G_nodeMapG_node_two, node->move->src));
	G_color_node u = x;
	G_color_node v = y;

	if (isContain_g(&precoloredList, y)){
		u = y;
		v = x;
	}
	if (u == v){
		append_live(&coalescedMoves, node);
		addWorkList(u);
	}
	else if (isContain_g(&precoloredList, v) || isLink(u->node->mykey,v->node->mykey)){
		append_live(&constraintMoves, node);
		addWorkList(u);
		addWorkList(v);
	}
	else {
		bool bFlag = TRUE;
		if (isContain_g(&precoloredList, u)){
			G_color_nodeList g_nodeList2 = adjacent(v);
			while (g_nodeList2 != NULL){
				if (!OK(g_nodeList2->value, u)){
					bFlag = FALSE;
					break;
				}
				g_nodeList2 = g_nodeList2->next;
			}
		}
		else{
			bFlag = FALSE;
		}
		if (bFlag || (!isContain_g(&precoloredList, u) && conservative(unionSet_one(adjacent(u), adjacent(v))))){
			append_live(&coalescedMoves, node);
			combine(u, v);
			addWorkList(u);
		}
		else{
			append_live(&activeMoves, node);
		}
	}
}

COL_result COL_color(Live_graph ig, Temp_map inital, Temp_tempList regs){
	G_graph graph = ig->graph;
	Live_moveList movement = ig->moves;
	G_nodeList g_nodeList = G_nodes(graph);
	init(graph->nodecount, inital,regs);
	G_color_nodeList g_nodeList_two = NULL;
	while (g_nodeList != NULL){
		G_node g_node = g_nodeList->head;
        G_color_node g_node_two = G_Color_Node(g_node);
        if (Temp_look(inital,g_node->info)!=NULL){
            append_g(&precoloredList,g_node_two);
        }
		else{
			append_g(&g_nodeList_two, g_node_two);
		}
		g_nodeList = g_nodeList->tail;
	}
	g_nodeList = G_nodes(graph);

	//initial two sets
	while (g_nodeList != NULL){
		G_node g_node = g_nodeList->head;
		G_color_node g_node_two = TAB_look(G_nodeMapG_node_two, g_node);
		G_nodeList adjNodeList = G_adj(g_node);
		while (adjNodeList != NULL){
			G_node otherG_node = adjNodeList->head;
			G_color_node otherG_node_two = TAB_look(G_nodeMapG_node_two, otherG_node);
			addEdge(g_node_two, otherG_node_two);
			adjNodeList = adjNodeList->tail;
		}
		g_nodeList = g_nodeList->tail;
	}

	//initial moveList and worklistMoves
	while (movement != NULL){
        Live_color_moveList_node live_moveList_twonode = NULL;
        assert(movement->dst!=NULL&&movement->src!=NULL);

        live_moveList_twonode = Live_Color_MoveList_Node(movement);
        append_live(&worklistMoves, live_moveList_twonode);
        G_color_node dst = TAB_look(G_nodeMapG_node_two, movement->dst);
        G_color_node src = TAB_look(G_nodeMapG_node_two, movement->src);
        TAB_enter(moveList, dst, unionSet_two(TAB_look(moveList, dst), Live_Color_MoveList(live_moveList_twonode,NULL,NULL)));
        TAB_enter(moveList, src, unionSet_two(TAB_look(moveList, src), Live_Color_MoveList(live_moveList_twonode, NULL, NULL)));
        movement = movement->tail;
	}

	makeWorklist(g_nodeList_two);
	do{
		// coalsce is not implemented
		if (!isEmpty_g(simWorkList)){
            simplify();
		}
		else if (!isEmpty_live(worklistMoves)){
			coalesce();
		}
		else if (!isEmpty_g(freezeWorkList)){
			freeze();
		}
		else{
			selectSpill();
        }
	} while (!isEmpty_g(simWorkList)||!isEmpty_live(worklistMoves)||!isEmpty_g(freezeWorkList)||!isEmpty_g(spillWorkList));
	

	assigncolours();
	COL_result col_result = checked_malloc(sizeof(*col_result));
	col_result->coloring = Temp_layerMap(colour,F_temp2Name());

	Temp_tempList spills = NULL;

	while (spiltNodes != NULL){
		spills = Temp_TempList(spiltNodes->value->node->info,spills);
		spiltNodes = spiltNodes->next;
	}
	
	col_result->spills = spills;
	return col_result;
}
