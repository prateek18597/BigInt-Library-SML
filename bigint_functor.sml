use "bignat.sml";
(*open BIGNAT;*)

functor BigInt (Bn:BIGNAT):
sig
datatype bigint= comb of Bn.bignat * int ; 
val bigzero: bigint
val sign : bigint -> int
(**)
val normalize : bigint -> bigint
val bigint: int -> bigint
val toString : bigint -> string
val ~~ : bigint -> bigint
val abs : bigint -> bigint
val ++ : bigint * bigint -> bigint
val -- : bigint * bigint -> bigint
val ** : bigint * bigint -> bigint
val sameSign : bigint * bigint -> bool
val succ : bigint -> bigint
val min : bigint * bigint -> bigint
val max : bigint * bigint -> bigint

val << : bigint * bigint -> bool
val <<= : bigint * bigint -> bool
val >> : bigint * bigint -> bool
val >>= : bigint * bigint -> bool
val == : bigint * bigint -> bool
val len : bigint -> int
(*val lenCompare : bigint * bigint -> order*)
val lenLt : bigint * bigint -> bool
val lenLeq : bigint * bigint -> bool
val lenGt : bigint * bigint -> bool
val lenGeq : bigint * bigint -> bool
val lenEq : bigint * bigint -> bool


(*val fromString : string -> bigint option
val int : bigint -> int option

val compare : bigint * bigint -> order
val pred : bigint -> bigint
exception division_by_zero
val %% : bigint * bigint -> bigint * bigint
val div : bigint * bigint -> bigint
val mod : bigint * bigint -> bigint
val quo : bigint * bigint -> bigint
val rem : bigint * bigint -> bigint
*)

end =(* sig *)

struct
	
	datatype bigint= comb of Bn.bignat * int ; 
	val bigzero=comb(Bn.zero,0);
	
	fun sign(comb(a,b))=b

	fun bigint(a)=
		if a>=0 then
			comb(Bn.toString(Bn.fromString(Int.toString(a))),0)
		else
			comb(Bn.toString(Bn.fromString(Int.toString(a* ~1))),1)

	fun normalize(comb(a,b))=
		comb(Bn.normalize(a),b);

	fun toString(comb(a,b))=
		if b=0 then
			a
		else
			"~"^a
	fun ~~(comb(a,b))=
		if b=0 then
			comb(a, 1)
		else
			comb(a,0)    
	
	fun len(comb(a,b))=
		Bn.len(a)

	fun lenLt(x,y)=
		len(x)<len(y)

	fun lenLeq(x,y)=
		len(x)<=len(y)

	fun lenGt(x,y)=
		len(x)>len(y)

	fun lenGeq(x,y)=
		len(x)>=len(y)

	fun lenEq(x,y)=
		len(x)=len(y)				

	fun abs(comb(a,b))=
		comb(a,0)
		
	fun ==(comb(a1,b1),comb(a2,b2))=
		if b1=0 andalso b2=0 then
			Bn.==(a1,a2)
		else
			if b1=1 andalso b2=1 then
				Bn.==(a1,a2)
			else
				false

	fun <<(comb(a1,b1),comb(a2,b2))=
		if b1=0 andalso b2=0 then
			Bn.<<(a1,a2)
		else
			if b1=1 andalso b2=1 then
				Bn.>>(a1,a2)
			else
				if b1=0 andalso b2=1 then
					false
				else
					true

	fun >>(comb(a1,b1),comb(a2,b2))=
		if b1=0 andalso b2=0 then
			Bn.>>(a1,a2)
		else
			if b1=1 andalso b2=1 then
				Bn.<<(a1,a2)
			else
				if b1=0 andalso b2=1 then
					true
				else
					false

	fun <<=(comb(a1,b1),comb(a2,b2))=
		if b1=0 andalso b2=0 then
			Bn.<<=(a1,a2)
		else
			if b1=1 andalso b2=1 then
				Bn.>>=(a1,a2)
			else
				if b1=0 andalso b2=1 then
					false
				else
					true

	fun >>=(comb(a1,b1),comb(a2,b2))=
		if b1=0 andalso b2=0 then
			Bn.>>=(a1,a2)
		else
			if b1=1 andalso b2=1 then
				Bn.<<=(a1,a2)
			else
				if b1=0 andalso b2=1 then
					true
				else
					false

	fun ++(comb(a1,b1),comb(a2,b2))=
		if b1=b2 then
			comb(Bn.++(a1,a2),b1)
		else
			if b1=1 andalso Bn.>>(a1,a2) then
					comb(Bn.--(a1,a2),1)
			else
				if b1=1 andalso Bn.>>(a2,a1) then
					comb(Bn.--(a2,a1),0)
				else 
					if b2=1 andalso Bn.>>(a1,a2) then
						comb(Bn.--(a1,a2),0)
					else
						(*if b2=1 andalso Bn.>>(a2,a1) then*)
						comb(Bn.--(a2,a1),1)

	fun --(comb(a1,b1),comb(a2,b2))=
			
			if b1=1 andalso b2=0 andalso Bn.>>(a1,a2) then
					comb(Bn.--(a1,a1),1)
			else
				if b1=1 andalso Bn.>>(a2,a1) then
					comb(Bn.--(a2,a1),0)
				else 
					if b2=1 andalso Bn.>>(a1,a2) then
						comb(Bn.--(a1,a2),0)
					else
						(*if b2=1 andalso Bn.>>(a2,a1) then*)
						comb(Bn.--(a2,a1),1)

	fun sameSign(comb(a1,b1),comb(a2,b2))=
		if b1=b2 then
			true
		else
			false

	fun **(comb(a1,b1),comb(a2,b2))=
		if b1=b2 then
			comb(Bn.**(a1,a2),0)
		else
			comb(Bn.**(a1,a2),1)

	fun succ(comb(a,b))=
		if Bn.<<(Bn.succ(a),Bn.zero) then
			comb(Bn.succ(a),1)
		else			
			comb(Bn.succ(a),0)

	fun max(comb(a1,b1),comb(a2,b2))=
		if b1=0 andalso b2=0 then
			comb(Bn.max(a1,a2),b1)
		else
			if b1=1 andalso b2=1 then
				comb(Bn.min(a1,a2),1)
			else
				if b1=0 andalso b2=1 then
					comb(a1,b1)
				else
					comb(a2,b2)

	fun min(comb(a1,b1),comb(a2,b2))=
		if b1=0 andalso b2=0 then
			comb(Bn.min(a1,a2),b1)
		else
			if b1=1 andalso b2=1 then
				comb(Bn.max(a1,a2),1)
			else
				if b1=0 andalso b2=1 then
					comb(a2,b2)
				else
					comb(a1,b1)
end

structure bigint = BigInt(B);
open bigint;