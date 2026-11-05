import YM.Next.RANK.Anima

/-!
# Composition of discrete endpoint reads

All target finite stencil comparisons use real entries (complex only afterwards in
formal Gaussian computation). Don't use arbitrary linear functionals crossing in
infinite dimension here; predict bounded-key via its observed finite stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Beamer
open Lattice CellsInt Maxwell Labels Tensor Configuration Function Finset
open scoped Classical Topology BigOperators

variable {G : Gauge} {d n : ℕ}
variable {A B : Type*} [DecidableEq A]

-- linear crossing only wrapped through finite accesses
abbrev Bridge (G : Gauge) := Address G → Horizon G

def bright (L : Horizon G→ₗ[ℝ] ℝ) := ∃ v : Address G →₀ ℝ, ∀ f,L f=Finsupp.linearCombination ℝ f v
private def home (i : Address G) := LinearMap.proj (R:=ℝ) (φ:=fun _ : Address G => ℝ) i
lemma home_bright (i : Address G) : bright (home i) := ⟨Finsupp.single i 1,fun f => by rw [Finsupp.linearCombination_single,one_smul]; rfl⟩
lemma bright_add {p q : Horizon G→ₗ[ℝ] ℝ} (hp : bright p) (hq : bright q) : bright (p+q) := by
  obtain ⟨a,h⟩ := hp; obtain ⟨b,z⟩ := hq; exact ⟨a+b,fun f => (congr_arg₂ (·+·) (h f) (z f)).trans (map_add _ _ _).symm⟩
lemma bright_scale {p : Horizon G→ₗ[ℝ] ℝ} (hp : bright p) (r : ℝ) : bright (r • p) := by
  obtain ⟨a,h⟩ := hp; exact ⟨r • a,fun f => (congr_arg (r • ·) (h f)).trans (map_smul (Finsupp.linearCombination ℝ f) ..).symm⟩
lemma bright_sub {p q : Horizon G →ₗ[ℝ] ℝ} (hp : bright p) (hq : bright q) : bright (p-q) := by
  rw [sub_eq_add_neg,← neg_one_smul ℝ q]; exact bright_add hp (bright_scale hq _)
lemma bright_sum (P : A → Horizon G→ₗ[ℝ] ℝ) (s : Finset A) (h : ∀ i∈s,bright (P i)) : bright (∑ i∈s,P i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0,fun _ => by simp⟩
  | @insert i s hi ih => rw [sum_insert hi]; exact bright_add (h i (mem_insert_self ..)) (ih fun i hx => h _ (mem_insert_of_mem hx))

lemma bright_gesture (L : Degree G) : bright (gesture L) := by
  rcases L with ⟨a,c,x,d,h⟩
  induction d generalizing x with
  | zero => exact home_bright (x,a,c)
  | succ d H =>
    let G1 z := gesture (G:=G) ⟨a,c,z,d,Fin.tail h⟩
    have he : gesture (G:=G) ⟨a,c,x,d+1,h⟩ = G1 (x+step (h 0))-G1 x := by
      ext1 f
      change jumps (d+1) h _ _ = _; rw [jumps,hopped]; rfl
    rw [he]; exact bright_sub (H ..) (H ..)
lemma bright_predict (u : KeyIn G d) : bright (predicts u) := by
  rw [show predicts u=∑ p : Hub G d u.val.1, glimpse u p • gesture p.val by ext1 f; simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,concentrates]; exact sum_congr rfl fun _ _ => mul_comm ..]
  exact bright_sum _ _ fun i _ => bright_scale (bright_gesture _) _

-- do not distribute unsigned discontinuous infinite leg operation

def mourn (v w : Horizon G →ₗ[ℝ] ℝ) : Bridge G →ₗ[ℝ] ℝ where
  toFun f := v (fun i => w (f i))
  map_add' p q := (congr_arg v (funext fun i => w.map_add (p i) (q i))).trans (map_add ..)
  map_smul' k p := (congr_arg v (funext fun i => w.map_smul k (p i))).trans (v.map_smul k (fun i => w (p i)))
lemma moves (v w : Horizon G→ₗ[ℝ] ℝ) (f : Bridge G) (h : bright w) : mourn v w f= mourn w v (fun i j => f j i) := by
  obtain ⟨m,h⟩ := h
  have he (g : Horizon G) : w g= ∑ i∈m.support, m i * g i := h _
  let t i : Horizon G := fun j => f j i
  change v (fun i => w (f i))=w fun i => v (t i)
  rw [he,show (fun i => w (f i))=∑ i∈m.support,m i • t i by ext j;rw [he,Finset.sum_apply]; rfl,map_sum]
  simp only [map_smul,smul_eq_mul]

lemma shut_reader {w : Horizon G→ₗ[ℝ] ℝ} (h : bright w) (f : Bridge G) (hh : ∀ i,shutter (fun j => f j i)) : shutter (fun i => w (f i)) := by
  obtain ⟨m,h⟩ := h; let t i : Horizon G := fun j => f j i
  have he : (fun i => w (f i))=∑ i∈m.support,m i • t i := by ext j; rw [h,Finset.sum_apply]; rfl
  rw [he]; exact (signal G).sum_mem fun i _ => (signal G).smul_mem _ (hh i)

lemma clouds (d) (i : Address G) (f) : cloud d f i=∑ j,predicts j f*tester (G:=G) (j : KeyIn G d).val i := sum_apply ..

def foam (d : ℕ) (i : Address G) : Horizon G→ₗ[ℝ] ℝ := home i - ∑ j : KeyIn G d,tester j.val i • predicts j
lemma foams (d) (i : Address G) (f : Horizon G) : foam d i f=(f-cloud d f) i := by
  rw [foam, LinearMap.sub_apply, Pi.sub_apply, clouds, LinearMap.sum_apply]; congr 1; exact sum_congr rfl fun i _ => mul_comm ..
lemma foam_bright (d) (i : Address G) : bright (foam d i) := bright_sub (home_bright i) (bright_sum _ _ fun j _ => bright_scale (bright_predict j) _)

lemma foam_null (u : KeyIn G d) (i : Address G) : foam d i (tester u.val)=0 := by
  rw [foams, Pi.sub_apply, clouds]; simp only [forecast, ite_mul, one_mul,zero_mul,sum_ite_eq', mem_univ,↓reduceIte,sub_self]

-- Relay actual scalar. lift at fixed real radius before paying norms.

variable {V : Type*}
variable (f : V → Address G) (r : ℝ) (d : ℕ)

def passcode (i : KeyIn G d ⊕ V) : Horizon G →ₗ[ℝ] ℝ := r^(bear i) • Sum.elim predicts (fun v => foam d (f v)) i
lemma bright_pass (i : KeyIn G d ⊕ V) : bright (passcode f r d i) := by
  apply bright_scale; cases i with
  | inl i => exact bright_predict i
  | inr i => exact foam_bright d (f i)
lemma item (i : KeyIn G d) (p : Horizon G) : passcode f r d (.inl i) p=r^ Labels.generation i.val * predicts i p := rfl
lemma stub (p : Horizon G) (i : V) : passcode f r d (.inr i) p=r^(d+1)* (p-cloud d p) (f i) := by
  change r^(d+1) * foam d (f i) p=_; rw [foams]

lemma testPass (i : KeyIn G d) (j : KeyIn G d ⊕ V) (hr : 0<r) :
    passcode f r d j ((r^(Labels.generation i.val))⁻¹ • (tester i.val))=(if j=.inl i then 1 else 0) := by
  classical
  -- instances in if may differ
  rcases j with j|j
  · rw [item, map_smul,forecast,smul_eq_mul]
    by_cases h : j=i
    · subst i; rw [if_pos rfl,if_pos rfl,mul_one]; field_simp
    rw [if_neg h,if_neg (mt Sum.inl.inj h),mul_zero,mul_zero]
  rw [map_smul]; change _ • (r^(d+1)*foam d (f j) (tester i.val))=_
  rw [foam_null,mul_zero,smul_zero]; exact (if_neg (by simp)).symm
end YM.Next.Rank.Beamer
