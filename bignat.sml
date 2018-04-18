signature BIGNAT =
sig
type bignat=string
(*exception overflow*)
(*exception underflow*)
val zero : bignat
val normalize : bignat -> bignat
val fromString : bignat -> int list
val toString : int list -> bignat
val ++ : bignat * bignat -> bignat
val succ : bignat -> bignat
val min : bignat * bignat -> bignat
val max : bignat * bignat -> bignat
val ** : bignat * bignat -> bignat
val compare : bignat * bignat -> order
val << : bignat * bignat -> bool
val <<= : bignat * bignat -> bool
val >> : bignat * bignat -> bool
val >>= : bignat * bignat -> bool
val == : bignat * bignat -> bool
val len : bignat -> int
val lenCompare : bignat * bignat -> order
val lenLt : bignat * bignat -> bool
val lenLeq : bignat * bignat -> bool
val lenGt : bignat * bignat -> bool
val lenGeq : bignat * bignat -> bool
val lenEq : bignat * bignat -> bool
val -- : bignat * bignat -> bignat
val pred : bignat -> bignat
exception division_by_zero
exception emptyList
val %% : bignat * bignat -> bignat * bignat
val quo : bignat * bignat -> bignat
val rem : bignat * bignat -> bignat
end

structure B:BIGNAT = 
struct
	type bignat= string ;
	exception division_by_zero
	exception emptyList

val zero="0"

(*Normalize Function: To Remove Leading Zeroes from the expression*)
local 
	fun normal("")="0"
		|normal(S)=
		if String.substring(S,0,1)="0" then
			normal(String.substring(S,1,size(S)-1))
		else
			S
in 
	fun normalize(S)=
	normal(S)
end


(*FromString Function: To Convert String/Bignat to int list so that it will be easier to operate*)
local
	fun chartointlist([],L)=L
		| chartointlist (h::t,L) =
			chartointlist(t,L@[valOf(Int.fromString(String.str(h)))])
in
	fun fromString S =
		chartointlist(String.explode(S),[]);
end

(*ToString Function: To convert int list to Bignat/String*)
local 

	fun to1String ([],S,n,c) = S
		| to1String(h::t,S,n,c)=
		 to1String(t,S@[String.sub(Int.toString(h),0)],n,0) 
	
	fun to2String(L)=
		to1String(L,[],length(L),0)

in	
	fun toString(L)=
		String.implode(to2String(L))
end

(*<< Function: To detect whether First input is smaller than second input*)
local
	fun lessthan (h1::t1,h2::t2) =
		
		if List.length(t1)<List.length(t2) then
			true
		else
			if List.length(t1)>List.length(t2) then
				false
			else
				if h1<h2 then
					true
				else
					if h1>h2 then
						false
					else
						lessthan(t1,t2)
in 
	fun << (S1,S2)=
		if normalize(S1)="" andalso normalize(S2)<>"" then
			false
		else
			if normalize(S2)="" andalso normalize(S1)<>"" then
				true
			else
				lessthan(fromString(normalize(S1)),fromString(normalize(S2)));
end

(*>> Function: To detect whether first input is greater tha second input*)
local
	fun greaterthan (h1::t1,h2::t2) =
		if List.length(t1)>List.length(t2) then
			true
		else
			if List.length(t1)<List.length(t2) then
				false
			else
				if h1>h2 then
					true
				else
					if h1<h2 then
						false
					else
						greaterthan(t1,t2)
in 
	fun >> (S1,S2)=
		if normalize(S1)="" andalso normalize(S2)<>"" then
			false
		else
			if normalize(S2)="" andalso normalize(S1)<>"" then
				true
			else
				greaterthan(fromString(normalize(S1)),fromString(normalize(S2)));
end

(*>>= Function: To detect whether First number is greater than equal to second number*)
local
	fun greaterthanEq (h1::t1,h2::t2) =
		if List.length(t1)>List.length(t2) then
			true
		else
			if List.length(t1)<List.length(t2) then
				false
			else
				if h1>=h2 then
					true
				else
					if h1<h2 then
						false
					else
						greaterthanEq(t1,t2)
in 
	fun >>= (S1,S2)=
	greaterthanEq(fromString(normalize(S1)),fromString(normalize(S2)));
end

(*<<= Function: To detect whether First number is less than equal to second number*)
local
	
	fun lessthanEq (h1::t1,h2::t2) =
		
		if List.length(t1)<List.length(t2) then
			true
		else
			if List.length(t1)>List.length(t2) then
				false
			else
				if h1<=h2 then
					true
				else
					if h1>h2 then
						false
					else
						lessthanEq(t1,t2)
in 
	fun <<= (S1,S2)=
		lessthanEq(fromString(normalize(S1)),fromString(normalize(S2)));
end

(*== Function: To check whether First Number is equal to Second number*)
local
	fun Eq ([],[]) = true
		| Eq (h1::t1,h2::t2) =
		if List.length(t1)<>List.length(t2) then
			false
		else
			if h1<>h2 then
				false
			else
				Eq(t1,t2)	
in 
	fun == (S1,S2)=
		Eq(fromString S1,fromString S2);
end

(*len Function: To Find the length of the string input*)
fun len S =	
	size(S);

(*lenLt Functoin*)
fun lenLt (S1,S2) =
	if size(normalize(S1))<size(normalize(S2)) then
		true
	else
		false

fun lenLeq (S1,S2) =
	if size(normalize(S1))<=size(normalize(S2)) then
		true
	else
		false

fun lenGt (S1,S2) =
	if size(normalize(S1))>size(normalize(S2)) then
		true
	else
		false

fun lenGeq (S1,S2) =
	if size(normalize(S1))>=size(normalize(S2)) then
		true
	else
		false

fun lenEq (S1,S2) =
	if size(normalize(S1))=size(normalize(S2)) then
		true
	else
		false

fun min(S1,S2) =
	if <<(normalize(S1),normalize(S2)) then
		normalize(S1)
	else
		normalize(S2)

fun max(S1,S2) =
	if >>(normalize(S1),normalize(S2)) then
		normalize(S1)
	else
		normalize(S2)


(*local 
	fun inc(h::t)=

in
	fun succ S =
	val L=List.rev(fromString(S))

end
	*)




local 
	fun add([],[],L,carry)=	List.rev(L@[carry])
		| add(h1::t1,h2::t2,L,carry) =
		if (h1+h2+carry)<10 then
			add(t1,t2,L@[h1+h2+carry],0)			

		else
			(*val s=Int.toString(h1+h2+carry);*)
			add(t1,t2,L@[valOf(Int.fromString(String.substring(Int.toString(h1+h2+carry),1,1)))],valOf(Int.fromString(String.substring(Int.toString(h1+h2+carry),0,1))))			
	fun EquateLen(L,n) =
		if List.length(L)=n then
			L
		else
			EquateLen([0]@L,n)
	

in
	fun ++ (S1,S2) =
	if size(S1)=size(S2) then
		normalize(toString(add(List.rev(fromString S1 ),List.rev(fromString S2 ),[],0)))
	else
		if size(S1)<size(S2) then
			normalize(toString(add(List.rev(EquateLen(fromString S1 ,size(S2))),List.rev(fromString S2 ),[],0)))
		else	
			normalize(toString(add(List.rev(fromString S1),List.rev(EquateLen(fromString S2 ,size(S1))),[],0)))
end

fun compare(S1,S2)=
	if <<(S1,S2) then
		LESS	
	else
		if >>(S1,S2) then
			GREATER
		else
			EQUAL

fun lenCompare(S1,S2)=
	if lenLt(S1,S2) then
		LESS	
	else
		if lenGt(S1,S2) then
			GREATER
		else
			EQUAL

local 
	
	fun subt([],[],L,carry)= List.rev(L)
		| subt(h1::t1,h2::t2,L,carry)=
			if h1>=h2 andalso carry=0 then
				subt(t1,t2,L@[h1-h2],0)
			else
				if h1-1>=h2 andalso carry=1 then
					subt(t1,t2,L@[h1-h2-1],0)
				else
					if h1<h2 andalso carry=0 then
						subt(t1,t2,L@[h1+10-h2],1)
					else
							subt(t1,t2,L@[h1+9-h2],1)			
	fun EquateLen(L,n) =
		if List.length(L)=n then
			L
		else
			EquateLen([0]@L,n)
	

in
	fun -- (S1,S2) =
		if size(S1)=size(S2) then
			normalize(toString(subt(List.rev(fromString(max(S1,S2))),List.rev(fromString (min(S2,S1))),[],0)))
		else
			normalize(toString(subt(List.rev(fromString(max(S1,S2))),List.rev(EquateLen(fromString (min(S2,S1)) ,size(max(S1,S2)))),[],0)))

end

fun succ(S)=
	++(S,"1")

fun pred(S)=
	--(S,"1")

local
	local 
	fun add([],[],L,carry)=	List.rev(L@[carry])
		| add(h1::t1,h2::t2,L,carry) =
		if (h1+h2+carry)<10 then
			add(t1,t2,L@[h1+h2+carry],0)			

		else
			add(t1,t2,L@[valOf(Int.fromString(String.substring(Int.toString(h1+h2+carry),1,1)))],valOf(Int.fromString(String.substring(Int.toString(h1+h2+carry),0,1))))			
	
	fun EquateLen(L,n) =
		if List.length(L)=n then
			L
		else
			EquateLen([0]@L,n)
	

in
	fun +++ (S1,S2) =
	
	if length(S1)=length(S2) then
		normalize(toString(add(List.rev(S1 ),List.rev(S2 ),[],0)))
	else
		if length(S1)<length(S2) then
			normalize(toString(add(List.rev(EquateLen(S1 ,length(S2))),List.rev(S2),[],0)))
		else	
			normalize(toString(add(List.rev(S1),List.rev(EquateLen(S2 ,length(S1))),[],0)))
end


	fun shift(L,0)= L
		|
		shift(L,count)=
			shift(L@[0],count-1)
			
	fun mult([],h,L2,carry)= List.rev(L2@[carry])
		| mult(h1::t1,h,L2,carry)=
			if carry + h*h1 <10 then
				mult(t1,h,L2@[carry + h*h1],0)
			else
				mult(t1,h,L2@[(carry+h*h1) mod 10],(carry+h*h1) div 10)

	fun mulAdd(L1,[],sum,n,l)= sum
		| mulAdd(L1,h::t,sum,n,l)=
			mulAdd(L1,t,fromString(+++(shift(mult(L1,h,[],0),n),sum)),l-length(t),l)

in
	fun ** (S1,S2) =
		if S1="" orelse S2="" then
			raise emptyList
		else
		toString(mulAdd(List.rev(fromString S1),List.rev(fromString S2),[0],0,size(S2)))
end

local 
	fun divi(L1,L2,q,label)=
		if <<(toString(L1),toString(L2)) andalso label=0 then
			toString L1
		else
			if <<(toString(L1),toString(L2)) andalso label=1 then
				Int.toString(q)
			else
			divi(fromString(--(toString(L1),toString(L2))),L2,q+1,label)
	fun divi1(L1,L2,q)=
		if <<(toString(L1),toString(L2)) then
			(Int.toString(q),toString(L1))
		else
			divi1(fromString(--(toString(L1),toString(L2))),L2,q+1)
in 
	fun quo(S1,S2) =
		if normalize(S2)="" then
			raise division_by_zero
		else
			if S2="" then
				raise emptyList
			else
				divi(fromString(S1),fromString(S2),0,1)
	fun rem(S1,S2) =
				divi(fromString(S1),fromString S2,0,0)
	fun %%(S1,S2) =
		divi1(fromString(S1),fromString S2,0)
end

end