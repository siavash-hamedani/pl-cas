is_commutative(add).
is_commutative(mul).

is_associative(add).
is_associative(mul).

simp(a(pow,A,1),A).
simp(a(mul,0,A),0).
simp(a(mul,A,0),0).
simp(a(add,0,A),A).
simp(a(add,A,0),A).
simp(a(mul,1,A),A).
simp(a(mul,A,1),A).
simp(a(OP,A,X),a(OP,X,A)) :- is_commutative(OP),number(X),not(number(A)).
simp(a(mul,A,B),T) :- number(A),number(B),T is A * B.
simp(a(add,A,B),T) :- number(A),number(B),T is A + B.
simp(a(OP,C,a(OP,A,B)),a(OP,B,a(OP,A,C))) :- is_associative(OP),number(A),number(C).
simp(a(OP,C,a(OP,A,B)),a(OP,A,a(OP,B,C))) :- is_associative(OP),number(A),not(number(C)),not(number(B)).

simp(a(OP,a(var,X),a(var,Y)),a(OP,a(var,Y),a(var,X)))  :-is_commutative(OP),X \= Y,compare(>,X,Y).

simp(a(add,X,X),a(mul,2,X)).
simp(a(add,X,a(mul,C,X)),a(mul,CC,X)) :- number(C),CC is C + 1.

simp(a(mul,X,X),a(pow,X,2)).



simp(a(OP,A,B),a(OP,SA,B))  :- simp(A,SA).
simp(a(OP,A,B),a(OP,A,SB))  :- simp(B,SB).
simp(a(OP,A,B),a(OP,SA,SB)) :- simp(A,SA),simp(B,SB).



simpy(A,B) :-
  (\+ simp(A,AS) -> B = A);
  (simp(A,AS),!,simpy(AS,B)).

deriv(a(var,X),R,0) :- number(R).
deriv(a(var,X),a(var,X),1).
deriv(a(var,Y),a(var,X),0) :- X \= Y.
deriv(a(var,X),a(mul,A,B),a(add,a(mul,TA,B),a(mul,A,TB))) :- deriv(a(var,X),A,TA),deriv(a(var,X),B,TB).
deriv(a(var,X),a(add,A,B),a(add,TA,TB)) :- deriv(a(var,X),A,TA),deriv(a(var,X),B,TB).
deriv(a(var,X),a(pow,A,B),a(mul,a(mul,B,a(pow,A,BM1)),TA)) :- BM1 is B - 1,deriv(a(var,X),A,TA).
