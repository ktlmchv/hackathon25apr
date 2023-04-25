import coxeter
import data.int.basic

noncomputable theory
open_locale classical

variables {W : Type*} (S : set W) [group W]

-- Coercion from `list S` to `list W`
instance list_subtype_to_list : has_coe (list S) (list W) :=
⟨λ l, list.map subtype.val l⟩

class generated_group (W : Type*) [group W] (S : set W) :=
(inv : S = S⁻¹) 
(neut : (1 : W) ∉ S)
(gen : ∀ w : W, ∃ l : list S, (l : list W).prod = w)

namespace generated_group

variables [generated_group W S]  


def gen_by_n (w : W) (n : ℕ) := ∃ l : list S, (l : list W).prod = w ∧ l.length = n
#check gen_by_n

lemma len_exists (w : W) : ∃ n, gen_by_n S w n :=
begin
   have h := _inst_2.gen w,
   induction h,
   use h_w.length,
   unfold gen_by_n,
   use h_w, 
   split, exact h_h, refl, 
end

def gen_length (w : W) := nat.find (len_exists S w) 
#check gen_length

def is_reduced (S : set W) (w : W) [generated_group W S] (l : list S) := (l : list W).prod = w ∧ l.length = gen_length S w

lemma coe_commutes_with_append (l1 l2 : list S) : (coe (l1 ++ l2) : list W) = (coe l1 : list W) ++ (coe l2 : list W) :=
begin
   rw coe, rw list_subtype_to_list, apply list.map_append,
end

lemma len_mul_le (w w' : W) : gen_length S (w * w') ≤ gen_length S w + gen_length S w' :=
begin
    have h1 := nat.find_spec (len_exists S w),
    have h2 := nat.find_spec (len_exists S w'),
    cases h1 with l1 hl1,
    cases h2 with l2 hl2,
    unfold gen_length,
    rw [←hl1.2, ←hl2.2],
    have hgp : gen_by_n S (w*w') (l1.length + l2.length),
         unfold gen_by_n, use l1++l2, split,
         rw [← hl1.1, ← hl2.1], rw coe_commutes_with_append, rw list.prod_append,
         rw list.length_append,
    exact nat.find_le hgp
end

lemma len_inv (w : W) : gen_length S (w⁻¹) = gen_length S w :=
begin
sorry
end

lemma le_len_rat (w w' : W) : |(gen_length S w : ℤ) - gen_length S w'| ≤ gen_length S (w * w'⁻¹) :=
begin
    rw abs_le, split,
    rw neg_le_sub_iff_le_add,
    rw [←len_inv S (w * w'⁻¹)], rw mul_inv_rev, rw inv_inv, rw add_comm,
    have h_pr : w' = (w' * w⁻¹) * w, simp,
    nth_rewrite 0 h_pr, 
    have hint := len_mul_le S (w' * w⁻¹) w,
    rw ←int.coe_nat_add,
    rw int.coe_nat_le_coe_nat_iff, exact hint,
    rw sub_le_iff_le_add,
    have h_pr : w = (w * w'⁻¹) * w', simp,
    nth_rewrite 0 h_pr, 
    have hint := len_mul_le S (w * w'⁻¹) w',
    rw ←int.coe_nat_add,
    rw int.coe_nat_le_coe_nat_iff, exact hint,
end

lemma prod_reduced (l l' : list S) (w w' : W) ( hgenw : (l : list W).prod = w ) ( hgenw : (l' : list W).prod = w' ) (h_red : is_reduced S (w*w') (l ++ l') ) : is_reduced S w l ∧ is_reduced S w' l':=
begin
sorry
end


end generated_group

#check generated_group.gen_length
