typedef features {
	bool B1;
	bool B2;
	bool B3;
	bool B4;
	bool B5;
	bool B6
}
features f;

system p1 = f.B1;
system p2 = f.B2;

byte n;
short i;

active proctype foo(){
	do
	::break;
	::n++;
	od;

Start: i = n;
	if::f.B1->i=i+6::else;fi;
	if::f.B2->i=i+5::else;fi;
	if::f.B3->i=i+4::else;fi;
	if::f.B4->i=i+3::else;fi;
	if::f.B5->i=i+2::else;fi;
	if::f.B6->i=i+1::else;fi;

Final: skip;
	do
	::true;
	od;
}

/*// phi_1
never{
T0_init:
	if
	::((!p1.foo@Final)||(!p2.foo@Final)||(!(p1.i>=p2.i)))&&((p1.foo@Start)&&(p2.foo@Start)&&(p1.n==p2.n))->goto accept_S2;
	::(1)->goto T0_init;
	fi;
accept_S2:
	if
	::(!p1.foo@Final)||(!p2.foo@Final)||(!(p1.i>=p2.i))->goto accept_S2;
	fi;
}*/

// \phi_2
never{
accept_init:
	if
	:: !(p1.foo@Start) || !(p2.foo@Start) || !(p1.n==p2.n) || (p1.foo@Final && p2.foo@Final && p1.i>=p2.i) -> goto accept_init
	:: 1 -> goto T0_S2
	fi;
	
T0_S2:
	if
	:: 1 -> goto T0_S2
	:: (p1.foo@Final && p2.foo@Final && p1.i>=p2.i) -> goto accept_init
	fi;
}
