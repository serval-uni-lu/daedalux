mtype = {right, left, up, down}

typedef struct {
	int a;
	bool b;
	mtype t
}

active proctype test (){
	struct s;
	mtype t = right;
	t = down;
	s.t = t;
	
	assert(t == s.t && s.t == down);
}
