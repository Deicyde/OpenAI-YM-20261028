import YM.Pert.Align.Burst
import YM.Pert.Align.Nesting
/-!
# Covariance of each pair of first-order curl charts
Real-coordinate ledger before the H average.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 350000
namespace YM.Pert.Align
open Filter Topology Function Lattice Atom Orb Maxwell Nesting
open scoped BigOperators ContDiff Classical RealInnerProductSpace
variable {j k : ℕ} {n : Side} {G : Gauge}

def jointB (G : Gauge) (n:Side) : (Module.Dual ℝ ↥(LinkP G n)) →ₗ[ℝ] (Module.Dual ℝ ↥(LinkP G n)) →ₗ[ℝ] ℝ := (LinearMap.applyₗ).comp (kernelEquiv G n).symm.toLinearMap
abbrev gain (h : ℝ) (j : ℕ) := h^(-(j+2:ℤ))
def cost (a : Atom j) (h : ℝ) : ℝ := gain h j * (j.factorial:ℝ)⁻¹
def single (a : Atom j) (h : ℝ) (x : Site n) (u : G.Color) : Module.Dual ℝ ↥(LinkP G n) := cost a h • ∑ t, degree a t • (formElem (edgePull a x t) u)
def scalarTerm (a : Atom j) (b : Atom k) (z : E4) : ℝ := if a.rotated=b.rotated then (a.factor * b.orientation false) * ((Band.casual (a.dirs++b.dirs) z).re) else 0
abbrev DFactor (j k : ℕ) := (j.factorial:ℝ)⁻¹*(k.factorial:ℝ)⁻¹
def singleTarget (a : Atom j) (b : Atom k) (u v : G.Color) (r : E4) := DFactor j k * inner ℝ u v * scalarTerm a b r
lemma leave {h : ℝ} (a : Atom j) (b : Atom k) (hh : 0<h) : cost a h * cost b h = DFactor j k * weight h (a.dirs++b.dirs) := by
  unfold cost gain DFactor weight;rw [mul_mul_mul_comm,← zpow_add₀ hh.ne',mul_comm (h^(_+_:ℤ))];congr 2;simp [length_dirs]; ring
lemma turn_corners {l s : Orb.Links n} (u v : G.Color) : (jointB G n) (formElem l u) (formElem s v) = inner ℝ u v * if s.2=l.2 then
    (Full.toroid (l.1-s.1)).re - (Full.toroid (l.1+s.1+step l.2)).re else 0 := by
    erw [show (jointB G n) (formElem l u) (formElem s v) = _ from (rfl : _ = Orb.covar _ (formElem s v))]
    rw [covar_link,show s.1+l.1=l.1+s.1 from add_comm .., show s.1-l.1= -(l.1-s.1) by abel,Full.toroid_even]
lemma single_eval (a : Atom j) (b : Atom k) (h : ℝ) (x y : Site n) (u v : G.Color) : let K (m : Site n) := (Full.toroid m).re;
    jointB G n (single a h x u) (single b h y v) = if a.rotated=b.rotated then cost a h * cost b h * inner ℝ u v * (double a b false K (x-y) - double a b true K (x+y+wrap n (step a.rotated))) else 0 := by
  intro K
  simp only [single,map_smul,map_sum,LinearMap.smul_apply, LinearMap.sum_apply,smul_eq_mul,double,turn_corners]
  dsimp only [edgePull]
  have id (d : Kind j) (e : Kind k) : (x+wrap n (offset a d)-(y+wrap n (offset b e))) = x-y+wrap n (offset a d)+wrap n (coverMul false (offset b e)) := by simp only [coverMul,Bool.false_eq_true, ↓reduceIte,map_neg]; abel
  have id' (d : Kind j) (e : Kind k) : (x+wrap n (offset a d)+(y+wrap n (offset b e))+ step a.rotated) = x+y+wrap n (step a.rotated) + wrap n (offset a d)+wrap n (coverMul true (offset b e)) := by simp only [coverMul,↓reduceIte,wrap_step]; abel
  by_cases hit : b.rotated=a.rotated; swap
  · simp only [if_neg hit, if_neg (Ne.symm hit), mul_zero,Finset.sum_const_zero]
  simp only [if_pos hit, if_pos hit.symm, ←Finset.sum_sub_distrib, Finset.mul_sum];nth_rw 1 [Finset.sum_comm];apply Finset.sum_congr rfl fun d _=> Finset.sum_congr rfl fun e _=>?_
  rw [id,id']; dsimp only [K];ring
lemma single_limit (T : Itinerary) (x y) (z : E4) (hz : z≠0) (h₁ : Scene T x y z) (h₂ : Finale T x y z) (a : Atom j) (b : Atom k) (u v : G.Color) : Tendsto (fun m=>jointB G (T.period m) (single a (T.gap m) (x m) u) (single b (T.gap m) (y m) v)) atTop
    (𝓝 (singleTarget a b u v z)) := by
  by_cases hab : a.rotated=b.rotated
  · let p := T.period
    let h := T.gap
    let D i:=weight (h i) (a.dirs++b.dirs)
    let K (i : ℕ) (m : Site (p i)):= (Full.toroid m).re
    let S i := D i * double a b false (K i) (x i-y i)
    let S' i := D i * double a b true (K i) (x i+y i+wrap (p i) (step a.rotated))
    have hv : Tendsto S atTop (𝓝 (scalarTerm a b z)) := by unfold S D K scalarTerm; rw [if_pos hab]; exact (ordinary_burst a b T x y z hz h₁)
    have hw : Tendsto S' atTop (𝓝 0) := final_burst a b T x y z h₂ _
    have he := (hv.sub hw).const_mul (DFactor j k * inner ℝ u v)
    convert! he using 1; · funext i; rw [single_eval, if_pos hab,leave a b (T.positive i)]; unfold S S' D K;ring
    simp only [singleTarget,sub_zero]
  simp only [single_eval, if_neg hab, singleTarget,scalarTerm,if_neg hab,mul_zero];apply tendsto_const_nhds

def swap (a : Atom j) : Atom j := ⟨a.rot,a.γ,a.channel,a.slash⟩
def flux (a : Atom j) (h : ℝ) (x : Site n) (u : G.Color) := single a h x u - single (swap a) h x u
def fluxTarget (a : Atom j) (b : Atom k) (c d : G.ColorIndex) (z : E4) := (a.factor*b.factor) * legKernel (constrain (G:=G) (Maxwell.fromF G (basis ∘ a.rot.perm ∘ a.γ) c (a.rot.perm a.slash) a.rotated)) (constrain (G:=G) (Maxwell.fromF G (basis ∘ b.rot.perm ∘ b.γ) d (b.rot.perm b.slash) b.rotated)) z
lemma bscalar (a : Atom j) (b : Atom k) (z : E4) : scalarTerm a b z = (a.factor*b.factor*(-1:ℝ)^k) * ((if a.rotated=b.rotated then 1 else 0) * (-Nesting.tagged a.dirs b.dirs z)) := by
  simp only [scalarTerm,orientation,length_dirs,Bool.false_eq_true,↓reduceIte]; split_ifs <;> dsimp only [Band.casual,Complex.ofReal_re,Nesting.tagged]; all_goals try rw [pow_succ _ k]
  all_goals ring
lemma factor_swap (a : Atom j) : (swap a).factor = a.factor := by unfold swap Atom.factor; dsimp; rw [mul_comm (tally _ _)]
lemma to_color (u : G.Color) (a : G.ColorIndex) : inner ℝ u (Maxwell.unitColor G a) = u a := by
  rw [PiLp.inner_apply, unitColor]; simp only [PiLp.single_apply,RCLike.inner_apply, starRingEnd_apply, star_trivial]; rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
  · simp [unitColor]
  intro b _ hb; simp [hb]
lemma scalar_diff (a : Atom j) (b : Atom k) (c d : G.ColorIndex) (z : E4) (hz:z≠0) : singleTarget a b (unitColor G c) (unitColor G d) z - singleTarget a (swap b) (unitColor G c) (unitColor G d) z - (singleTarget (swap a) b (unitColor G c) (unitColor G d) z - singleTarget (swap a) (swap b) (unitColor G c) (unitColor G d) z) = fluxTarget a b c d z := by
  let i:=a.rot.perm a.slash
  let D:= List.ofFn (a.rot.perm ∘ a.γ)
  let l:= a.rotated; let u:= b.rot.perm b.slash; let v:= b.rotated; let L:=List.ofFn (b.rot.perm∘b.γ)
  rw [fluxTarget]
  have h := raw_mixed (G:=G) (basis ∘ a.rot.perm ∘ a.γ) (basis ∘ b.rot.perm ∘ b.γ) i l u v c d hz
  rw [show legKernel (G:=G) _ _ z=_ from h]
  simp_rw [singleTarget,bscalar,factor_swap,to_color, unitPaint]
  let f := bareCurl i l u v
  have hw := Nesting.stack_coeff (f:=bareCurl i l u v) (a.rot.perm ∘ a.γ) (b.rot.perm ∘ b.γ) (clean_chart i l u v) hz
  rw [Nesting.bare _ _ _ _ _ _ _ hz] at hw
  rw [hw]
  change DFactor j k * (if d=c then (_:ℝ) else _) * (a.factor*b.factor*(-(1:ℝ))^k * ((if l=v then 1 else 0) * (-tagged (D++[i]) (L++[u]) z))) -
     DFactor j k * (if d=c then _ else _) * (a.factor*b.factor*(-(1:ℝ))^k * ((if l=u then 1 else 0) * (-tagged (D++[i]) (L++[v]) z))) -
     (DFactor j k * (if d=c then _ else _) * (a.factor*b.factor*(-(1:ℝ))^k * ((if i=v then _ else 0) * (-tagged (D++[l]) (L++[u]) z))) -
      DFactor j k * (if d=c then _ else _) * (a.factor*b.factor*(-(1:ℝ))^k * ((if i=u then 1 else 0) * (-tagged (D++[l]) (L++[v]) z)))) = _
  have fg (j k:Axis) (w : ℝ) : (if k = j then w else 0) = (if j=k then 1 else 0)*w := by
    by_cases h : k=j; · simp [h]
    simp [h,Ne.symm h]
  simp only [fg l v (tagged _ _ _),fg l u (tagged _ _ _),fg i v (tagged _ _ _),fg i u (tagged _ _ _)]
  by_cases h₀ : d=c
  · subst d; simp only [if_true]; dsimp only [D,L, i, l,u,v, DFactor]; ring
  simp only [if_neg h₀, if_neg (Ne.symm h₀)]; ring

lemma b_sub (B : Module.Dual ℝ ↥(LinkP G n) →ₗ[ℝ] (Module.Dual ℝ ↥(LinkP G n)) →ₗ[ℝ] ℝ) (f g v w) : B (f-g) (v-w)=B f v-B f w-(B g v-B g w) := by rw [B.map_sub,LinearMap.sub_apply, map_sub,map_sub]
end YM.Pert.Align
