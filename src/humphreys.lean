import linear_algebra.basic
import data.real.basic
import linear_algebra.bilinear_form
import group_theory.group_action.basic
import algebra.module.basic

universe u
noncomputable theory

-- structure reflection (R : Type u_1) (M : Type u_2) [semiring R] [add_comm_monoid M] [module R M] :
-- Type (max u_1 u_2)

structure euclidean (V : Type u) [add_comm_group V] [module ℝ V] (B : bilin_form ℝ V) := 
(is_sym : bilin_form.is_symm B)
(pos_def : ∀ (v : V), v ≠ 0 → 0 < (B v v))



variables {V : Type u} [add_comm_group V] [module ℝ V] (B : bilin_form ℝ V) (e : euclidean V B)





def s (α : V) (hα : α ≠ 0) : V → V := λ v, v - (2 : ℝ)•((B.bilin v α)/(B.bilin α α))•α

lemma slinear (e : euclidean V B) (α : V) (hα : α ≠ 0) :
is_linear_map ℝ (s B α hα) :=
begin
  split,
  swap,
  intros c v,
  unfold s,
  rw smul_sub,
  have key : B.bilin (c•v) α = c * (B.bilin v α),
  begin
    rw B.bilin_smul_left c v α,
  end,
  rw key,
  rw smul_comm c (2 : ℝ),
  rw ←mul_div,
  rw ←smul_smul c (B.bilin v α / B.bilin α α) α,
  constructor,
  intros m n a,
  rw smul_smul,
  rw smul_smul,
  rw mul_comm m n,

  

  -- calc s B α hα (c•v) = c • v - 2 • (B (c • v) α / B α α) • α : by refl
            
  
  --  c•v - 2•((c*(B v α))/(B α α))•α : by rw ←B.bilin_smul_left c v α
  -- ... = c•v - 2•c•((B v α)/(B α α))•α : by refl
                  -- ... = c•v - c•(((B v α)/(B α α))•α) : by rw ←mul_smul
                  -- ... = c•(s B α hα(v)) :
end

lemma reflection (e : euclidean V B) (α : V) (hα : α ≠ 0) :
s B α hα α = -α :=
begin
  have h : B α α ≠ 0,
  begin
    have := e.pos_def α hα,
    linarith,
  end,
  have key : (B α α)/(B α α) = 1,
  begin
    ring_nf,
    apply inv_mul_cancel h,
  end,
  unfold s,
  rw key,
  simp,
  have h2 : α = 1•α,
  begin
  rw one_smul,
  end,
  have h3 : 2 = 1 + 1,
  begin
    refl,
  end,
  rw h3,
  rw add_smul,
  rw ← h2,
  simp,
end

lemma involution (e : euclidean V B) (α : V) (hα : α ≠ 0) (v : V):
(s B α hα (s B α hα v))= v :=
begin
end

-- 2*((B v α)/(B α α))*α

-- variables (V : Type u) [fin_dim_vector_space V] (B : bilin_form ℝ V)


  -- unfold s,
  -- ring_nf,
  -- rw mul_left_inv (B α α),

  -- lemma units (α : V) (hα : α ≠ 0) :
-- B α α ∈ ℝ.units :=
-- begin
--   sorry
-- end

-- lemma reflection (α : V) (hα : α ≠ 0) :
-- s B α hα α = -α :=
-- begin
--   have h : B α α ≠ 0 by pos_def,
--   rw inv_mul_cancel pos_def (V ((B α α)/(B α α))),
--   have key : 1*((B α α)/(B α α)) = 1, {
--     rw mul_div_cancel,
--   },
-- end\

-- have new : α - 2•α = ((1 : ℝ) - 2)•α,
  -- begin
  --   simp
  -- end,