open classical

--one way DeMorgan's Law
lemma DeMorganOne : ∀ P Q : Prop, ¬ (P ∧ Q) → ¬ P ∨ ¬ Q :=
begin
assume P Q npq,
change (P ∧ Q) → false at npq,
have pnp : P ∨ ¬ P := em P,
have qnq : Q ∨ ¬ Q := em Q,
cases pnp with p np,
cases qnq with q nq,
have pq : P ∧ Q := and.intro p q,
have f : false := npq pq,
trivial,
right,
assumption,
left,
assumption,
end

--check to make sure it works
variables (A B : Prop)
#check DeMorganOne ¬ A ¬ B

--defining ∨ when you only have ∧
example : ∀ P Q : Prop, P ∨ Q ↔ ¬(¬P ∧ ¬Q) :=
begin
assume P Q,
split,
assume pq : P ∨ Q,
assume npq : ¬ P ∧ ¬ Q,
show false,
from
  begin
  cases pq,
  have np : ¬ P := and.elim_left npq,
  contradiction,
  have nq : ¬ Q := and.elim_right npq,
  contradiction,
  end,
assume nnpnq,
have DMO := DeMorganOne (¬ P) (¬ Q),
have nnpnnq : ¬ ¬ P ∨ ¬ ¬ Q := DMO nnpnq,
have pnp : P ∨ ¬ P := em P,
have qnq : Q ∨ ¬ Q := em Q,
cases nnpnnq with nnp nnq,
change (P → false) → false at nnp,
cases pnp with p np,
left,
assumption,
change (P → false) at np,
have f : false := nnp np,
trivial,
change (Q → false) → false at nnq,
cases qnq with q nq,
right,
assumption,
change (Q → false) at nq,
have f : false := nnq nq,
trivial,
end


--going the other way is easy
lemma DeMorganTwo : ∀ P Q : Prop, ¬ (P ∨ Q) → ¬ P ∧ ¬ Q :=
begin
intros,
change (P ∨ Q) → false at a,
have pnp := em P,
have qnq := em Q,
cases pnp with p np,
have pq := or.inl p,
have f := a pq,
trivial,
cases qnq with q nq,
have pq := or.inr q,
have f := a pq,
trivial,
apply and.intro np nq,
end

-- defining ∨ from ∧
example : ∀ P Q : Prop, P ∧ Q ↔ ¬ (¬ P ∨ ¬ Q) :=
begin
intros,
split,
intros,
assume b,
show false,
from
  begin
  have p := and.elim_left a,
  have q := and.elim_right a,
  cases b with np nq,
  trivial,
  trivial,
  end,
intros,
have pnp := em P,
have qnq := em Q,
change (¬ P ∨ ¬ Q) → false at a,
cases pnp with p np,
cases qnq with q nq,
apply and.intro p q,
have f := a (or.inr nq),
trivial,
have f := a (or.inl np),
trivial,
end