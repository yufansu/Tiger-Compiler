/*
 * colour.h - Data structures and function prototypes for colouring algorithm
 *             to determine register allocation.
 */

typedef struct COL_result_ *COL_result;
typedef struct Live_color_moveList_node_ *Live_color_moveList_node;
typedef struct Live_color_moveList_ *Live_color_moveList;
typedef struct Stringlist_ *Stringlist;
typedef struct G_color_node_ *G_color_node;
typedef struct G_color_nodeList_ *G_color_nodeList;

typedef enum { PREcolourED, SIMPLIFYWORKLIST, FREEZEWORKLIST, SPILLWORKLIST, 
				spiltNODES, COALESCEDNODES, colourEDNODES, SELECTSTACK,DEFAULT1 } Kind_one;
typedef enum{ COALESCEDMOVES, CONSTRAINTMOVES, FROZENMOVES, 
				WORKLISTMOVES, ACTIVEMOVES ,DEFAULT_two } Kind_two;

struct COL_result_ {
	Temp_map coloring; 
	Temp_tempList spills;
};

struct G_color_node_{
	G_node node;
	Kind_one kind;
};

struct G_color_nodeList_{
  G_color_node value;
  G_color_nodeList pre;
  G_color_nodeList next;
  
};

struct Live_color_moveList_node_{
	Live_moveList move;
	Kind_two kind;
};

struct Live_color_moveList_{
	Live_color_moveList_node value;
	 Live_color_moveList pre;
	 Live_color_moveList next;
};
struct Stringlist_{
	string node;
	Stringlist pre;
	Stringlist next;
};

COL_result COL_color(Live_graph ig, Temp_map initial, Temp_tempList regs);

Live_color_moveList_node Live_Color_MoveList_Node(Live_moveList move);

Live_color_moveList Live_Color_MoveList(Live_color_moveList_node value, Live_color_moveList pre, Live_color_moveList next);


