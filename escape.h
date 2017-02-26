typedef struct Esc_binding_ *Esc_binding;

struct Esc_binding_{
  int depth;
  bool* escape;
};

Esc_binding Esc_newBinding(int depth,bool* escape);
static void traverseDec(S_table env,int depth,A_dec d);
static void traverseVar(S_table env,int depth,A_var v);
void Esc_findEscape(A_exp exp);
