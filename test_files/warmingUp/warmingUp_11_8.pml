typedef features {
	bool B1;
	bool B2;
	bool B3;
	bool B4;
	bool B5;
	bool B6;
	bool B7;
	bool B8;
	bool B9;
	bool B10;
	bool B11
}
features f;

system p1 = f.B1;
system p2 = f.B2;
system p3 = f.B3;
system p4 = f.B4;
system p5 = f.B5;
system p6 = f.B6;
system p7 = f.B7;
system p8 = f.B8;

byte n;
short i;

active proctype foo(){
	do
	::break;
	::n++;
	od;

Start: i = n;
	if::f.B1->i=i+11::else;fi;
	if::f.B2->i=i+10::else;fi;
	if::f.B3->i=i+9::else;fi;
	if::f.B4->i=i+8::else;fi;
	if::f.B5->i=i+7::else;fi;
	if::f.B6->i=i+6::else;fi;
	if::f.B7->i=i+5::else;fi;
	if::f.B8->i=i+4::else;fi;
	if::f.B9->i=i+3::else;fi;
	if::f.B10->i=i+2::else;fi;
	if::f.B11->i=i+1::else;fi;

Final: skip;
	do
	::true;
	od;
}
never{
T0_init :
	if
	::((!p1.foo@Final)||(!p2.foo@Final)||(!p3.foo@Final)||(!p4.foo@Final)||(!p5.foo@Final)||(!p6.foo@Final)||(!p7.foo@Final)||(!p8.foo@Final)||(!(p1.i>=p2.i))||(!(p2.i>=p3.i))||(!(p3.i>=p4.i))||(!(p4.i>=p5.i))||(!(p5.i>=p6.i))||(!(p6.i>=p7.i))||(!(p7.i>=p8.i)))&&((p1.foo@Start)&&(p2.foo@Start)&&(p3.foo@Start)&&(p4.foo@Start)&&(p5.foo@Start)&&(p6.foo@Start)&&(p7.foo@Start)&&(p8.foo@Start)&&(p1.n==p2.n)&&(p2.n==p3.n)&&(p3.n==p4.n)&&(p4.n==p5.n)&&(p5.n==p6.n)&&(p6.n==p7.n)&&(p7.n==p8.n))->goto accept_S2;
	::(1)->goto T0_init;
	fi;
accept_S2:
	if
	::(!p1.foo@Final)||(!p2.foo@Final)||(!p3.foo@Final)||(!p4.foo@Final)||(!p5.foo@Final)||(!p6.foo@Final)||(!p7.foo@Final)||(!p8.foo@Final)||(!(p1.i>=p2.i))||(!(p2.i>=p3.i))||(!(p3.i>=p4.i))||(!(p4.i>=p5.i))||(!(p5.i>=p6.i))||(!(p6.i>=p7.i))||(!(p7.i>=p8.i))->goto accept_S2;
	fi;
}