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
	bool B11;
	bool B12;
	bool B13;
	bool B14;
	bool B15;
	bool B16;
	bool B17;
	bool B18;
	bool B19;
	bool B20;
	bool B21;
	bool B22;
	bool B23;
	bool B24;
	bool B25;
	bool B26;
	bool B27;
	bool B28;
	bool B29;
	bool B30;
	bool B31;
	bool B32;
	bool B33;
	bool B34;
	bool B35;
	bool B36;
	bool B37;
	bool B38;
	bool B39;
	bool B40
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
system p9 = f.B9;
system p10 = f.B10;

byte n;
short i;

active proctype foo(){
	do
	::break;
	::n++;
	od;

Start: i = n;
	if::f.B1->i=i+40::else;fi;
	if::f.B2->i=i+39::else;fi;
	if::f.B3->i=i+38::else;fi;
	if::f.B4->i=i+37::else;fi;
	if::f.B5->i=i+36::else;fi;
	if::f.B6->i=i+35::else;fi;
	if::f.B7->i=i+34::else;fi;
	if::f.B8->i=i+33::else;fi;
	if::f.B9->i=i+32::else;fi;
	if::f.B10->i=i+31::else;fi;
	if::f.B11->i=i+30::else;fi;
	if::f.B12->i=i+29::else;fi;
	if::f.B13->i=i+28::else;fi;
	if::f.B14->i=i+27::else;fi;
	if::f.B15->i=i+26::else;fi;
	if::f.B16->i=i+25::else;fi;
	if::f.B17->i=i+24::else;fi;
	if::f.B18->i=i+23::else;fi;
	if::f.B19->i=i+22::else;fi;
	if::f.B20->i=i+21::else;fi;
	if::f.B21->i=i+20::else;fi;
	if::f.B22->i=i+19::else;fi;
	if::f.B23->i=i+18::else;fi;
	if::f.B24->i=i+17::else;fi;
	if::f.B25->i=i+16::else;fi;
	if::f.B26->i=i+15::else;fi;
	if::f.B27->i=i+14::else;fi;
	if::f.B28->i=i+13::else;fi;
	if::f.B29->i=i+12::else;fi;
	if::f.B30->i=i+11::else;fi;
	if::f.B31->i=i+10::else;fi;
	if::f.B32->i=i+9::else;fi;
	if::f.B33->i=i+8::else;fi;
	if::f.B34->i=i+7::else;fi;
	if::f.B35->i=i+6::else;fi;
	if::f.B36->i=i+5::else;fi;
	if::f.B37->i=i+4::else;fi;
	if::f.B38->i=i+3::else;fi;
	if::f.B39->i=i+2::else;fi;
	if::f.B40->i=i+1::else;fi;

Final: skip;
	do
	::true;
	od;
}
never{
T0_init :
	if
	::((!p1.foo@Final)||(!p2.foo@Final)||(!p3.foo@Final)||(!p4.foo@Final)||(!p5.foo@Final)||(!p6.foo@Final)||(!p7.foo@Final)||(!p8.foo@Final)||(!p9.foo@Final)||(!p10.foo@Final)||(!(p1.i>=p2.i))||(!(p2.i>=p3.i))||(!(p3.i>=p4.i))||(!(p4.i>=p5.i))||(!(p5.i>=p6.i))||(!(p6.i>=p7.i))||(!(p7.i>=p8.i))||(!(p8.i>=p9.i))||(!(p9.i>=p10.i)))&&((p1.foo@Start)&&(p2.foo@Start)&&(p3.foo@Start)&&(p4.foo@Start)&&(p5.foo@Start)&&(p6.foo@Start)&&(p7.foo@Start)&&(p8.foo@Start)&&(p9.foo@Start)&&(p10.foo@Start)&&(p1.n==p2.n)&&(p2.n==p3.n)&&(p3.n==p4.n)&&(p4.n==p5.n)&&(p5.n==p6.n)&&(p6.n==p7.n)&&(p7.n==p8.n)&&(p8.n==p9.n)&&(p9.n==p10.n))->goto accept_S2;
	::(1)->goto T0_init;
	fi;
accept_S2:
	if
	::(!p1.foo@Final)||(!p2.foo@Final)||(!p3.foo@Final)||(!p4.foo@Final)||(!p5.foo@Final)||(!p6.foo@Final)||(!p7.foo@Final)||(!p8.foo@Final)||(!p9.foo@Final)||(!p10.foo@Final)||(!(p1.i>=p2.i))||(!(p2.i>=p3.i))||(!(p3.i>=p4.i))||(!(p4.i>=p5.i))||(!(p5.i>=p6.i))||(!(p6.i>=p7.i))||(!(p7.i>=p8.i))||(!(p8.i>=p9.i))||(!(p9.i>=p10.i))->goto accept_S2;
	fi;
}