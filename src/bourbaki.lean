import coxeter
import data.int.basic

noncomputable theory
open_locale classical

class generated_group (W : Type*) [group W] (S : set W) :=
(inv : S = S⁻¹) 
(neut : (1 : W) ∉ S)
(gen : ∀ w : W, ∃ l : list W, (∀ s ∈ l, s ∈ S) ∧ l.prod = w)

namespace generated_group

variables {W : Type*} (S : set W) [group W] [generated_group W S]  

-- Coercion from `list S` to `list W`
instance list_subtype_to_list : has_coe (list S) (list W) :=
⟨λ l, list.map subtype.val l⟩

def gen_by_n (w : W) (n : ℕ) := ∃ l : list S, (l : list W).prod = w ∧ l.length = n
#check gen_by_n

lemma len_exists (w : W) : ∃ n, gen_by_n S w n :=
begin
sorry
end

def gen_length (w : W) := nat.find (len_exists S w) 
#check gen_length

def is_reduced (S : set W) (w : W) [generated_group W S] (l : list S) := (l : list W).prod = w ∧ l.length = gen_length S w

lemma len_mul_le (w w' : W) : gen_length S (w * w') ≤ gen_length S w + gen_length S w' :=
begin
sorry
end 

lemma len_inv (w : W) : gen_length S (w⁻¹) = gen_length S w :=
begin
sorry
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
