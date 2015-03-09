

sym := function (n , k) 
	local ksub , nsub, x;
	if k = 0 then return [[]];	fi;
	if n = 0 then return []; fi;
	ksub := sym(n,k-1);
	for x in ksub do
		Add(x,n);
	od;
	nsub := sym(n-1,k);
	return Concatenation(nsub,ksub);
end;

bil := function (a,b)
	local lis , old, new, i,f;
	lis := Concatenation(a,b);
	Sort(lis);
	if IsEmpty(lis) then return 1; fi;
	old := Remove(lis);
	i:=1;f:=1;
	repeat 
	if old <> Remove(lis) then return 0; 
	elif IsEmpty(lis) then return f; fi;
	new:=Remove(lis);
	if old=new then i:=i+2; f:=f*i; 
	else i:= 1; old:=new; fi;
	until IsEmpty(lis);
	return 0;
end;

f2 := function (n, l )
	local i,res;
	res:=[];
	for i in [1..n] do res[i]:=0;od;
	for i in l do
		res[i] := (res[i] + 1) mod 2; od;
	return res;
end;

f2classes := function ( n )
	local x,res,i,j;
	res := [];
	for i in [0..n] do
		x:=[];		
		for j in [1..n] do 
			if j<=i then Add(x,0); else Add(x,1);fi;
		od;
		Add(res,x);
	od;
	return res;
end;

a := function (n,k) 
	local res , f2c, syms, ml,i,j,co;
	res:=1;
	syms:= sym(n,k);
	for f2c in f2classes(n) do
		ml := [];
		for i in syms do
		if f2(n,i) <> f2c then continue; fi;
		co:=[];
		  for j in syms do
			if f2(n,j) <> f2c then continue; fi;
			Add(co,bil(i,j));
		  od; 
		Add(ml,co);		
		od;
		if IsEmpty(ml) then continue; fi;
		res := res * Determinant(ml)^(Binomial(n,Sum(f2c)));
	od;
	return res;
end;


facta := function(n,k)
	local f,l,o,fan;
	Print("n=",n,",k=",k,":  ");
	fan := Factors(a(n,k)) ;
	o := 0; l:=1;
	for f in fan do
	if o=f then l:=l+1; 
	else 
	 if o<>0 then Print("(",o,",",l,") ") ;fi;
	 o:=f;l:=1; fi; 
	od;
	Print("(",f,",",l,") \n");
end;


