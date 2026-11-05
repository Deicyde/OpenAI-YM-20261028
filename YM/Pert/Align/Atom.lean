import YM.Pert.Fourier.Visits
import YM.Pert.Fourier.Source
import YM.Pert.Lattice.TopLinear
/-! Affine shifted link slots; finite Fourier signs under arbitrary independent signed-axis transforms of the two legs. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pert.Align
open Lattice Full Band Function Set
open scoped BigOperators Classical
variable {n : Side} {G : Gauge} {j : ℕ}

structure Atom (j : ℕ) where
  rot : Signed
  γ : Fin j→Axis
  slash : Axis
  channel : Axis
namespace Atom
def tally (s : Signed) (i : Axis) : ℝ := if s.flip i then -1 else 1
lemma tally_nonneg (s : Signed) (i : Axis) : (tally s i)^2=1 := by unfold tally; split<;>norm_num
def coverMul (forward : Bool) (a : Cover) := if forward then a else -a
@[simp] lemma coverMul_add (f) (a b : Cover) : coverMul f (a+b)=coverMul f a+coverMul f b := by cases f <;> simp [coverMul]; abel
def axisRate (s : Signed) (i : Axis) (forward : Bool) := (if forward then (1:ℝ) else -1) * tally s i
lemma axisRate_cases (s : Signed) (k : Axis) (b : Bool) : let T:=axisRate s k b; let u:=coverMul b (s.act (step k : Cover)); let v: Cover := step (s.perm k); (T=1∧u=v) ∨ (T=-1∧u=-v) := by
  dsimp; have he := Lattice.Step.vec_rotate (d:=posDir k) (R:=ℤ) s
  rw [Step.vec_pos] at he
  cases b <;> cases hh : s.flip k <;> simp_all [coverMul,axisRate,tally,Lattice.Step.rotate,Lattice.Step.vec,posDir]
  simp [←he]
abbrev Kind (j : ℕ) := Finset (Fin j) × Bool
def degree (a : Atom j) (k : Kind j) : ℝ := Bare.sign k.1 * tally a.rot a.channel * (if k.2 then 1 else -1)
def offset (a : Atom j) (k : Kind j) :=
  a.rot.act (∑ i∈k.1, (step (a.γ i) : Cover)) + (if k.2 then a.rot.act (step a.slash) else 0) + (if a.rot.flip a.channel then -(step (a.rot.perm a.channel)) else 0)

lemma wraps_act (a : Signed) (f : Fin j→Axis) (k : Finset (Fin j)) : wrap n (a.act (∑ i∈k,step (f i)))= a.act (∑ i∈k,step (f i)) := by rw [←wrap_signed, map_sum];simp
abbrev rotated (a : Atom j) := a.rot.perm a.channel
def readK {R : Type*} [AddCommGroup R] [One R] (a : Atom j) (U : Lattice.Links R G.Color) (home : Four R) := ∑ k : Finset (Fin j), (Bare.sign k • Bare.wideLink G a.rot U
   ((affine a.rot⁻¹ 0 home + ∑ i∈k, step (a.γ i) + step a.slash, a.channel)) - Bare.sign k • Bare.wideLink G a.rot U ((affine a.rot⁻¹ 0 home + ∑ i∈k, step (a.γ i),a.channel)))

def edgePull {n : Side} (a : Atom j) (home : Site n) (k : Kind j) : Orb.Links n := (home+wrap n (offset a k),a.rotated)
lemma read_wrap (a : Atom j) (U : Lattice.Links (Per n) G.Color) (home : Site n) : a.readK U home = ∑ k : Kind j, a.degree k • (U (edgePull a home k)) := by
    unfold readK
    simp_rw [Bare.wideLink_apply,smul_smul]; rw [Fintype.sum_prod_type]; classical
    have hx (f : Bool→G.Color) : ∑ i : Bool, f i=f true+f false := Fintype.sum_bool f
    simp_rw [hx];apply Finset.sum_congr rfl; intro i _; simp [posDir, Lattice.Step.rotate,Lattice.Step.used]
    cases he : a.rot.flip a.channel <;> simp only [edgePull,offset,degree,tally,affine,he, Bool.false_eq_true, decide_true, if_false, if_true, map_add, wraps_act, ← wrap_signed, map_sum, wrap_step, map_zero, add_zero, Signed.act_add, Signed.act_inv, Prod.snd, Prod.fst, map_neg,rotated,mul_one,mul_neg,neg_mul, neg_smul] <;> abel_nf
lemma read_cover (a : Atom j) (U : Lattice.Links ℤ G.Color) : a.readK U 0 = ∑ k : Kind j, a.degree k • (U (a.offset k,a.rotated)) := by
    unfold readK
    simp_rw [Bare.wideLink_apply,smul_smul]; rw [Fintype.sum_prod_type]
    have hx (f : Bool→G.Color) : ∑ i : Bool, f i=f true+f false := Fintype.sum_bool f
    simp_rw [hx];apply Finset.sum_congr rfl; intro i _; simp [posDir, Lattice.Step.rotate,Lattice.Step.used]
    cases he : a.rot.flip a.channel <;> simp [offset,degree,tally,affine,he] <;> abel_nf
lemma core_combine {R : Type*} [AddCommGroup R] [One R] (p : Atom j) (U : Lattice.Links R G.Color) (x : Four R) : Bare.wideCore G j (affine p.rot⁻¹ 0 x) (Bare.wideLink G p.rot U) p.slash p.channel p.γ = (j.factorial:ℝ)⁻¹ • (p.readK U x - readK ({p with slash:=p.channel,channel:=p.slash}) U x) := by
  rw [Bare.wideCore_apply]; unfold readK;congr 1;rw [←Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun a ha=>by unfold Bare.wideCurl; simp only [smul_add,smul_sub];abel

def down (s : Signed) (forward : Bool) (i : Axis) : Cover := if axisRate s i forward=1 then (0:Cover) else -step (s.perm i)
def foot (a : Atom j) (f : Bool) := (∑ i, down a.rot f (a.γ i)) + down a.rot f a.slash + coverMul f (if a.rot.flip a.channel then -step a.rotated else 0)
-- Caution binder above parses as (sum i, down()) + other terms or one big sum? use parentheses.
def dirs (a : Atom j) : List Axis := List.ofFn (a.rot.perm ∘ a.γ) ++ [a.rot.perm a.slash]
def factor (a : Atom j) := tally a.rot a.channel * tally a.rot a.slash * ∏ i, tally a.rot (a.γ i)
def orientation (a : Atom j) (forward : Bool) := if forward then a.factor else (-1)^((a.dirs).length)*a.factor
@[simp] lemma length_dirs (a : Atom j) : a.dirs.length=j+1 := by unfold dirs; simp

lemma wrapSum {ι : Type*} (k : Finset ι) (p : Site n) (t:ι→Cover) : char p (wrap n (∑ i∈k,t i)) = ∏ i∈k, char p (wrap n (t i)) := by
  classical
  induction k using Finset.induction with | empty=>simp [Full.char_zero] | insert a k h ih=>simp only [Finset.sum_insert h,Finset.prod_insert h,map_add,char_add,ih]
lemma wrapStep (p : Site n) (s : Signed) (f : Bool) (k : Axis) : char p (wrap n (coverMul f (s.act (step k)))) - 1 = (axisRate s k f) * char p (wrap n (down s f k)) * (char p (step (s.perm k)) - 1) := by
  obtain ⟨h,H⟩|⟨h,H⟩ := axisRate_cases s k f
  · simp [down,h,H,Full.char_zero]
  let M : Site n:=step (s.perm k); have ht := Full.char_add p (-M) M; rw [neg_add_cancel,Full.char_zero] at ht
  rw [down,if_neg (by linarith)]; rw [h,H,map_neg,wrap_step]; push_cast;change (char p (-M)-1 : ℂ) = _ * char p (-M) * (char p M - 1)
  grind
lemma powerset_diff {ι : Type*} [Fintype ι] (F : ι→ℂ) :
    ∑ t : Finset ι, (-1:ℂ)^(tᶜ.card:ℕ)* ∏ k ∈ t, F k = ∏ k, (F k-1) := by
    classical
    let p (t : Finset ι):ℂ:= (-1)^(t.card:ℕ)*∏ k∈tᶜ, F k
    let e : ((Finset ι) ≃ Finset ι) := ({toFun:=fun t => tᶜ, invFun:=fun t=>tᶜ,left_inv:=fun t=> _root_.compl_compl _,right_inv:=fun t=>_root_.compl_compl _}) -- args
    have ht := Equiv.sum_comp e p
    calc _ = ∑ t : Finset ι, p (e t) := Finset.sum_congr rfl (fun t _=>by change _=(-1:ℂ)^_*∏ i∈(tᶜ)ᶜ,_;rw [compl_compl]; rfl)
         _ = ∑ t : Finset ι, p t := ht
         _ = _ := by rw [Finset.prod_sub];simp only [Finset.prod_const_one,mul_one]; rw [show Finset.univ.powerset = (Finset.univ (α:=Finset ι)) by simp];rfl

lemma act_mul_sum (f : Bool) (s : Signed) {ι : Type*} (i : Finset ι) (u : ι→ Cover) : coverMul f (s.act (∑ k∈i, u k)) = ∑ k∈i, coverMul f (s.act (u k)) := by
   classical
   induction i using Finset.induction with | empty=>cases f <;> simp [coverMul] | insert a i h ih=>simp [h,ih]
lemma degree_first (f : Bool) (s : Signed) (g : Fin j→Axis) (p : Site n) : ∑ t : Finset (Fin j), (Bare.sign t : ℂ)*char p (wrap n (coverMul f (s.act (∑ k∈t, step (g k))))) =
    ((∏ i, axisRate s (g i) f) : ℂ) * char p (wrap n (∑ i, down s f (g i))) * (∏ i, (char p (step (s.perm (g i))) - 1)) := by
  rw [wrapSum, ←Finset.prod_mul_distrib, ←Finset.prod_mul_distrib];simp_rw [act_mul_sum,wrapSum,←wrapStep p s,←powerset_diff]
  apply Finset.sum_congr rfl;exact fun i hi=> by
    unfold Bare.sign; congr 1
    simp only [Finset.card_compl]; norm_cast
lemma phaseA (a : Atom j) (p : Site n) (f : Bool) : ∑ t : Kind j, a.degree t * char p (wrap n (coverMul f (offset a t))) = a.orientation f * char p (wrap n (a.foot f)) * Band.claw (dirs a) p := by
  let t:= coverMul f
  rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_bool]
  let K:= a.γ; let s:=a.rot; let i:=a.slash; let v := a.rotated; let r:Cover := if (a.rot.flip a.channel) then -step v else 0
  let χ (b : Cover):ℂ := char p (wrap n b)
  have ch (a b : Cover) := Full.char_add p (wrap n a) (wrap n b)
  let comb := (∑ I : Finset (Fin j), (↑(Bare.sign I):ℂ) * χ (t (s.act (∑ k∈I,step (a.γ k)))))
  have hx : ∑ b : Finset (Fin j), (a.degree (b,true) * χ (t (offset a (b,true))) + a.degree (b,false) * χ (t (offset a (b,false)))) =
      ((tally s a.channel:ℂ) * χ (t r) * (χ (t (s.act (step i))) - 1) * comb) := by
    unfold comb χ; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b h=>?_ ; unfold t offset; unfold r s; dsimp only [if_true,Prod.snd,Prod.fst]
    rw [coverMul_add,coverMul_add,map_add,map_add,char_add p,char_add p]; rw [if_neg (by decide : ¬false = true), add_zero,coverMul_add,map_add,char_add]
    simp only [degree,Prod.fst, Prod.snd,Bool.false_eq_true, if_false, ↓reduceIte,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_one]
    dsimp only [rotated,i,v];ring
  change _ = (orientation a f:ℂ) * _ * _
  erw [hx]; unfold foot orientation
  rw [map_add, map_add,char_add,char_add]
  unfold comb χ; rw [wrapStep]; rw [degree_first]; unfold claw dirs; simp only [List.map_append,List.map_cons,List.map_nil,List.prod_append,List.prod_cons,List.prod_nil,mul_one,List.map_ofFn, List.prod_ofFn,Function.comp_apply, i,s]
  cases haq : f <;> simp [t,factor,axisRate,Bool.false_eq_true,dirs,length_dirs,t,i,s, Finset.prod_neg, r, v,haq, pow_add] <;> ring -- malformed
end Atom
end YM.Pert.Align
