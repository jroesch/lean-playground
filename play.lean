import algebra.group

open nat

inductive list (A : Type) : Type :=
  | nil {} : list A
  | cons : A -> list A -> list A.

definition append {A : Type} : list A -> list A -> list A
  | append list.nil ys := ys
  | append (list.cons x xs) ys := list.cons x (append xs ys)

definition length {A} : list A -> nat
  | length list.nil := 0
  | length (list.cons x xs) := 1 + length xs

definition list_add_monoid [instance] (A : Type) : add_monoid (list A) :=
  {| add_monoid,
     zero := list.nil,
     add := append,
     add_assoc := sorry,
     add_zero := sorry,
     zero_add := sorry |}

lemma app_nil_r :
      Π {A} (xs : list A),
      append xs list.nil = xs :=
begin
  intros,
  induction xs,
    esimp,
    unfold append,
    rewrite v_0,
end

lemma app_comm_cons :
      Π {A} (xs ys : list A) (y : A),
      append xs (list.cons y ys) = append (append xs (list.cons y list.nil)) ys :=
begin
  intro,
  intro,
  induction xs; intros,
  esimp,
  intros,
  unfold append,
  rewrite v_0,
end 

lemma append_length :
      Π {A : Type} (ys zs xs : list A),
      length xs = length zs ->
      append xs ys = append zs ys ->
      xs = zs :=
begin
  intro,
  intro,
  induction ys; intros,
    esimp at a_1,
    rewrite app_nil_r at a_1,
    rewrite app_nil_r at a_1,
    exact a_1,
    intros,
    rewrite app_comm_cons at a_3,
    rewrite (app_comm_cons zs) at a_3,
    apply v_0,
    exact a_2,
    sorry,
end

inductive vect (A : Type) : nat -> Type :=
| nil {} : vect A nat.zero
| cons : Π {n}, A -> vect A n -> vect A (nat.succ n)

 definition vect.append {T:Type} : Π {n m: ℕ}, vect T n → vect T m → vect T (n + m)
 | 0 m vect.nil ys := ys
 | (nat.succ n) m (vect.cons x xs) ys := vect.cons x (vect.append xs ys)

definition map {A B : Type} : ∀ {n}, (A -> B) -> vect A n -> vect B n
| _ _  vect.nil := vect.nil
| _ f (vect.cons x xs) := vect.cons (f x) (map f xs)

definition composition {A B C : Type} (f : A -> B) (g : B -> C) : A -> C :=
           λ x, g (f x)

theorem map_comm {A B C : Type} {n} (v : vect A n) (f : A -> B) (g : B -> C) : map g (map f v) = map (composition f g) v :=
begin
  intros,
  induction v,
    show map g (map f vect.nil) = map (composition f g) vect.nil, by esimp,
    unfold map,
    rewrite v_0,
end


