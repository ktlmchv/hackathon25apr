import coxeter
import data.int.basic

noncomputable theory
open_locale classical

section lists
/- Lemmas about list coercions -/

variables {S : Type*} {T : set S}

-- Coercion from `list T` to `list S`.
instance list_subtype_to_list : has_coe (list T) (list S) :=
⟨λ l, list.map subtype.val l⟩

lemma coe_cons (hd : T) (tl : list T) : (coe (hd :: tl) : list S) = coe hd :: coe tl := 
rfl

lemma coe_append (l m : list T) : (coe (l ++ m) : list S) = l ++ m :=
begin
   induction l with hd tl ih,
   { refl },
   rw [list.cons_append, coe_cons, ih, coe_cons, list.cons_append],
end

lemma coe_reverse (l : list T) : (l.reverse : list S) = (l : list S).reverse :=
begin
   induction l with hd tl ih,
   { refl },
   simp [coe_append, coe_cons, ih],
   refl,
end

end lists

-- A group `W` generated by a set `S`, such that `S` contains `1` and `S⁻¹ = S`.
class generated_group (W : Type*) [group W] (S : set W) :=
(inv : S⁻¹ = S) 
(neut : (1 : W) ∉ S)
(gen : ∀ w : W, ∃ l : list S, (l : list W).prod = w)

namespace generated_group

variables {W : Type*} [group W] (S : set W)

/- Some more trivial coercion results -/
instance [h : generated_group W S] : has_inv S :=
⟨λ s,
{ val := s⁻¹,
  property := begin
   apply subset_of_eq h.inv,
   simp,
  end }⟩

lemma list_coe_inv [generated_group W S] (l : list S) :
   (coe (l.map has_inv.inv) : list W) = (coe l : list W).map has_inv.inv :=
begin
   induction l with hd tl ih,
   { refl },
   simp [coe_cons, ih],
   refl,
end

def gen_by_n (w : W) (n : ℕ) := ∃ l : list S, (l: list W).prod = w ∧ l.length = n
#check gen_by_n

lemma len_exists [h : generated_group W S] (w : W) : ∃ n, gen_by_n S w n :=
begin
   have h := h.gen w,
   induction h,
   use h_w.length,
   unfold gen_by_n,
   use h_w, 
   split, exact h_h, refl, 
end

-- The length of a group element with respect to a generating set `S`.
def gen_length [generated_group W S] (w : W) := nat.find (len_exists S w) 
#check gen_length

variables [generated_group W S]

-- A list of elements is reduced it has minimal length amongs all lists with the same product.
def is_reduced (S : set W) (w : W) [generated_group W S] (l : list S) :=
(l : list W).prod = w ∧ l.length = gen_length S w

lemma reduced_exists (w : W) : ∃ l : list S, is_reduced S w l :=
nat.find_spec (len_exists S w)

lemma len_mul_le (w w' : W) : gen_length S (w * w') ≤ gen_length S w + gen_length S w' :=
begin
sorry
end 

lemma len_inv (w : W) : gen_length S w⁻¹ = gen_length S w :=
begin
   have h : ∀ w, gen_length S w⁻¹ ≤ gen_length S w,
   begin
      intro w,
      apply nat.find_le,
      rcases reduced_exists S w with ⟨l, lgen, llen⟩,
      use [list.reverse (l.map has_inv.inv)], split,
      { 
         simpa [coe_reverse, list_coe_inv, list.prod_reverse_noncomm],
      },
      simp,
      exact llen,
   end,
   have := h w⁻¹,
   simp at this,
   exact le_antisymm (h w) this,
end

lemma le_len_rat (w w' : W) : |(gen_length S w : ℤ) - gen_length S w'| ≤ gen_length S (w * w⁻¹) :=
begin
sorry
end

lemma prod_reduced (l l' : list S) (w w' : W) ( hgenw : (l : list W).prod = w ) ( hgenw : (l' : list W).prod = w' ) (h_red : is_reduced S (w*w') (l ++ l') ) : is_reduced S w l ∧ is_reduced S w' l':=
begin
sorry
end


end generated_group

#check generated_group.gen_length

def subset := set ℕ

variable (X : subset)

#check (1 ∈ ↑X)