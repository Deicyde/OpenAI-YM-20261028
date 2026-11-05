import YM.RG08.Carrel.Orbit
import YM.RG08.Rudder.Sym.Parasol

/-!
# Effective completed A with all signatures including corner phases
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Carrel
open Lattice Laurent Forms Pert.Bulk Isles Packets Rudder Rudder.Symmetry Filter Finset Function RG Extra.Iteration
open Camera Cloud Room Glyph Exterior Wilson Precision
open scoped BigOperators Topology Classical ENNReal PowerSeries
variable {I:Type}{k n:ℕ}{P:Side}{G:Gauge}

abbrev CTests (P:Side)(G:Gauge)(k:ℕ):=Cmix P G.ColorIndex k → ℝ
def treated (s:Signed)(u:Cmix P I k→ℝ)(x:Cmix P I k):ℝ:=supply s x.2 * u (badge s x)
private lemma supply_one (i:Firm I k) : supply 1 i=1:=by
 have he: |supply 1 i|=1:=stand ..
 have ht:=housing (1:Signed) 1 i
 rw [one_mul,show cash 1 i=i from ?_] at ht
 · rcases le_total 0 (supply 1 i) with h|h <;> simp only [abs_of_nonneg,abs_of_nonpos,h] at he <;> nlinarith
 exact congrArg Prod.snd (atlas_id ((0:Cover),i))
lemma treated_one(u:Cmix P I k→ℝ):treated 1 u=u:=by ext i;rw [treated,supply_one,badge_id,one_mul]
lemma treated_mul(s t:Signed)(u:Cmix P I k→ℝ):treated (s*t) u=treated t (treated s u):=by ext i;rw [treated,treated,treated,badge_com,housing,mul_assoc];rfl

variable [Fintype I]
def reading (F:Flake n (Cmix P I k))(W: Cmix P I k→ℝ):ℝ:=∑ z,F z *∏ i,W (z i)

theorem according (s:Signed){F:Flake n (Mix I k)}(h:Cohort F)(i:Fin n)(W:Cmix P I k→ℝ):
 reading (pour (adjust s⁻¹ F) i) W =reading (pour F i) (treated s W):=by
 let e:Equiv.Perm (Tape n (Cmix P I k)):= Equiv.arrowCongr (Equiv.refl _) (citadel s)
 unfold reading;rw [← Equiv.sum_comp e];apply Finset.sum_congr rfl;intro x _
 rw [toured h i]; unfold treated
 change (_ * pour F i (badge s⁻¹ ∘ (badge s ∘ x)))*_=_
 rw [show badge s⁻¹ ∘ (badge s ∘ x)=x by ext j:1;exact (citadel s).left_inv _,mul_right_comm,←Finset.prod_mul_distrib];rw [mul_comm _ (pour _ _ _)];congr 1;apply Finset.prod_congr rfl;intro j _;apply congrArg₂ _ _ rfl
 change supply s⁻¹ (cash s (x j).2)=supply s _
 have h0:= housing s⁻¹ s (x j).2;rw [inv_mul_cancel,supply_one] at h0
 have hh:=stand s (x j).2
 rcases le_total 0 (supply s (x j).2) with h|h <;> simp only [abs_of_nonneg,abs_of_nonpos,h] at hh 
 · rw [hh] at h0 ⊢; linarith
 have he : supply s (x j).2 = -1:=by linarith
 rw [he] at h0 ⊢;linarith

omit [Fintype I] in
private lemma pour_sum (τ B:ℝ){J:Type}(S:Finset J)(H:J→Flake n (Mix I k))(h:∀ i∈S,Held (carpet _) τ B (H i))(ht:0≤τ)(o:Fin n):
 pour (P:=P) (S.sum H) o=S.sum fun i=>pour (H i) o:=by
 funext x;rw [pour_at,Finset.sum_apply];simp_rw [Finset.sum_apply]; rw [Summable.tsum_finsetSum]; · simp [pour_at]
 intro i hi
 let X:=lantern o x
 have hz(z : X):z.val o=reach (x o):=z.property.1
 apply Summable.of_norm
 exact ((cell_sum (h _ hi) ht o (reach (x o))).comp_injective (Subtype.val_injective (p:=fun a=> a∈X))).congr (by intro i;simp [comp_apply,hz i,Real.norm_eq_abs])

omit [Fintype I] in
lemma pour_bleach (F:Flake n (Mix I k)){τ C:ℝ}(h:Cohort F)(he:Held (carpet _) τ C F)(ht:0≤τ)(i:Fin n) : pour (P:=P) (bleach F) i=bleach (pour F i):=by
 have hu (α:ℝ)(f:Flake n (Mix I k)): pour (P:=P) (α • f) i= α • pour f i:=by
   ext v; rw [pour_at]; simp_rw [Pi.smul_apply,smul_eq_mul,tsum_mul_left,pour_at]
 unfold bleach;rw [hu,pour_sum τ C _ _ (fun e _=>he.perm e) ht]
 simp_rw [←ordered _ _ _ h]


-- Signed average all channels, applies arbitrary rank. Permute links too.
def average (F:Flake n (Mix I k)):Flake n (Mix I k):=(Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed, adjust s⁻¹ F

omit [Fintype I] in
lemma average_held (F:Flake n (Mix I k)){σ C:ℝ}(h:Held (carpet _) σ C F)(ht:0≤σ)(hc:0≤C) :Held (carpet _) σ (C*Real.exp (8*σ)) (average F):=by
 have he := Held.smul (Fintype.card Signed:ℝ)⁻¹ (Held.sum (p:=fun _=>C*Real.exp (8*σ)) univ (fun s:Signed=>adjust s⁻¹ F) (fun _ _=>by positivity) (fun s _=>adjust_cost h ht _))
 unfold average
 convert he using 1
 have ht:(Fintype.card Signed:ℝ)≠0:=by exact_mod_cast Fintype.card_ne_zero
 simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,abs_of_nonneg (by positivity:(Fintype.card Signed:ℝ)⁻¹≥0)];rw [←mul_assoc,inv_mul_cancel₀ ht,one_mul]

omit [Fintype I] in
lemma average_cohort {F:Flake n (Mix I k)}(h:Cohort F): Cohort (average F):= Cohort.smul (Cohort.sum _ _ fun _ _=>adjust_cohort h _) _

lemma reading_parley (f:Flake n (Cmix P I k))(W:Cmix P I k→ℝ):reading f W=MvPolynomial.eval W (parley f):=by
 unfold reading parley;rw [MvPolynomial.eval_sum];simp only [MvPolynomial.smul_eq_C_mul,MvPolynomial.eval_mul,MvPolynomial.eval_C,word,map_prod,MvPolynomial.eval_X]
lemma reading_smul (f:Flake n (Cmix P I k))(t:ℝ)(W:Cmix P I k→ℝ):reading (t • f) W=t*reading f W:=by simp only [reading,Finset.mul_sum,Pi.smul_apply,smul_eq_mul,mul_assoc]
lemma reading_sum {J:Type}(s:Finset J)(f:J→Flake n (Cmix P I k))(W:Cmix P I k→ℝ):reading (s.sum f) W = s.sum (fun j=> reading (f j) W):=by simp_rw [reading,Finset.sum_apply,Finset.sum_mul];rw [Finset.sum_comm]
lemma interested (F:Flake n (Mix I k)){τ B:ℝ}(h:Cohort F)(he:Held (carpet _) τ B F)(ht:0≤τ)(i:Fin n)(W:Cmix P I k →ℝ):
    reading (pour (bleach (average F)) i) W=(Fintype.card Signed:ℝ)⁻¹ * ∑ s:Signed, reading (pour F i) (treated s W):=by
 let p:=max 0 B
 have hf:0≤p:=le_max_left ..
 have hh:Held (carpet _) τ p F:= he.mono le_rfl (le_max_right ..) (fun _=>le_rfl)
 rw [pour_bleach (average F) (average_cohort h) (average_held F hh ht hf) ht,reading_parley,parley_clean,←reading_parley,average]
 have hu (α:ℝ)(f:Flake n (Mix I k)): pour (P:=P) (α • f) i= α • pour f i:=by
   ext v; rw [pour_at]; simp_rw [Pi.smul_apply,smul_eq_mul,tsum_mul_left,pour_at]
 rw [hu,pour_sum τ (p*Real.exp (8*τ)) _ _ (fun e _=> adjust_cost hh ht e⁻¹) ht,reading_smul,reading_sum]
 simp_rw [according _ h]

-- transform covers powers in sign for signature=1 on positive links, tested germ exactly
omit [Fintype I] in
abbrev Sa (_I:Type):=Rayk G 1
private lemma mark_coord (s:Signed)(a:Axis):marks s (coord a).1=(coord (s.perm a)).1:=by change marks s {a}={s.perm a}; simp [marks]
omit [Fintype I] in
lemma passport (s:Signed)(i:Axis)(u:Site P)(a:G.ColorIndex): badge s (u,coord i,a)=(s.act u+(if s.flip i=true then -step (s.perm i) else 0),coord (s.perm i),a):=by
 apply Prod.ext
 · unfold badge;dsimp only;change _+wrap _ (evil _ {i})=_
   simp only [evil,sum_singleton,stub,apply_ite,map_neg,map_zero,wrap_step]
   by_cases hs : s.flip i = true <;> simp [hs]
 · exact Prod.ext (Subtype.ext (mark_coord ..)) rfl
omit [Fintype I] in
lemma tariff (s:Signed)(a:G.ColorIndex)(i:Axis) : supply s (coord i,a)=(if s.flip i=true then (-1:ℝ) else 1):=Rudder.Symmetry.toll_slot ..

omit [Fintype I] in
theorem tread (s:Signed)(v:Vert P (Rayk G 1)):offers G (treated s v)=Lattice.pull s 0 (offers G v):=by
 funext ⟨u,i⟩
 unfold Lattice.pull offers Lattice.Step.read Lattice.Step.rotate Lattice.posDir
 simp only [Bool.false_xor,affine, add_zero]
 cases hs:s.flip i <;> simp only [Lattice.Step.used, Bool.false_eq_true, ↓reduceIte]
 · congr 1;ext l; simp [inserts,treated,tariff,hs,passport]
 rw [show offer G (u,i) (treated s v)= - offer G (s.act u-step (s.perm i),s.perm i) v from ?_,Work.F03.exp_neg_color]
 ext l
 simp [inserts, treated, tariff, passport, hs, sub_eq_add_neg]
end YM.RG08.Carrel
