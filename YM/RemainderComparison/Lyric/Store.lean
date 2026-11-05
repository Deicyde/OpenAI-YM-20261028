import YM.RemainderComparison.Lyric.Morendo

/-!
# Conditional second logarithm iteration: high reserve

At real epoch. Booked amount plus one to call regardless B. Not projecting
terms outside marks, nor spending the seed factor repeatedly. Learned from
E6.Census (height). Test available for any Prepared.Schedule; don't apply to
coolant tails at nonadjacent regulators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lyric
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n:ℕ}(χ:Chi)

open Daisy
local notation "X'" => Palette.mark M (c:=c)
local notation "Lk" => ConnectedActivityE6.lengths T R
local notation "sx" => radiusB x
variable (l:ι→ℝ) (N:Captain H j q d v u A b r B e n χ)
local notation "D" => Height.grow G L x
open Height AnalyticBridge.VerifiedReset
variable {δ Gp : ℝ}
local notation "T'" => Q.costs L μ R.beta x q
local notation "z₀" => (fun i=> (D)^Silica.horn (X' i)*Palette.wages M l i)
local notation "f₀" => (combined M N.conduit.fare l)
local notation "L₀" => Mixed.lengths S T' Lk

-- pure grammar; reuse touches. Generalized Height.strongerSet to arbitrary q.
section
variable {I:Type*}
theorem extraction (p : I→ Support c) (X:ℕ) (u v:I→ℝ) (a i:ℝ) {f b q:ℝ} (h:0 ≤ a) (he:0< i)(hp:Ready p X (tariff u v 0 i) (a+2*i) f b q) (hx:∀ i,0 ≤ u i) (hg:∀ i,0 ≤ v i) (s:Site c) (m:ℕ):
    SumBudget (fun H:Finset I=> Reserves.rooted p X u s a H*(1+setPrice p X v H)^m * Real.exp (i*setPrice p X v H))
          (Reserves.polyPrice i m* treeYield f q 0) := by
  have hk:= touch_tail p X hp s 0; simp only [Nat.zero_le, ↓reduceIte] at hk
  have hz (z:Finset I) : 0 ≤ setPrice p X v z := sum_nonneg fun j _=> add_nonneg (Nat.cast_nonneg _) (hg j)
  apply budget_mono (budget_scale (show 0 ≤ polyPrice i m by unfold polyPrice; positivity) hk)
  · intro z; apply mul_nonneg _ (Real.exp_pos _).le; apply mul_nonneg _ (pow_nonneg (add_nonneg zero_le_one (hz z)) _)
    unfold rooted; split; exact mul_nonneg (prod_nonneg fun i _=>hx _) (Real.exp_pos _).le; exact le_rfl
  intro z; unfold rooted; split; next H=>
    have hv : (∏ i∈z,u i)*currency X a (z.biUnion p) ≤ touches p X u a s z := by
      unfold touches; rw [if_pos H]; unfold currency; simp only [Finset.prod_mul_distrib, ← Real.exp_sum,← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast Ac.cover p X H.1) h)) (prod_nonneg fun i _=> hx _)
    rw [set_exchange]; let FF:=setPrice p X v z
    have hp' := polynomial_cost he (hz z) m
    apply (mul_le_mul_of_nonneg_right (mul_le_mul hv hp' (pow_nonneg (add_nonneg zero_le_one (hz _)) _) ((mul_nonneg (prod_nonneg fun j _=> hx _) (Real.exp_pos _).le).trans hv)) (Real.exp_pos _).le).trans
    simp only [Pi.zero_apply,sum_const_zero,add_zero]; change _ ≤ polyPrice i m*(touches p X u a s z*Real.exp (2*i*FF)); rw [show 2*i*FF=i*FF+i*FF by ring,Real.exp_add]; unfold FF polyPrice; apply le_of_eq; ring
  next ht => unfold touches; rw [if_neg ht]; simp
end

def salaries (Q:ConnectedActivityE6.Target G P) (L:Side) (μ x B Gp:ℝ) (j n:ℕ):ℝ:=
  (1+2^j*B)*(polyPrice Q.ε n * treeYield (grow G L x*((Q.costs L μ 1 x 0).rootHit+Gp)) (1/2) 0)
lemma shines {fe:Head S→ℝ}(p:Molecule S):
    (∏ z∈p, gale S (Q.mark L μ x) D (fun i:Head S=>D^(Sum.elim (fun _ : Stores S=>0) Silica.horn i)*fe i) z)=
      D^pins S p*gust S (Q.mark L μ x) D p*(∏i∈p,fe i) := by
  simp only [gust,gale,pins,Cash.numP,Finset.prod_mul_distrib,Finset.prod_const,Nat.cast_sum,mul_sum,Real.exp_sum,Finset.prod_pow_eq_pow_sum]; ring
lemma canvas (hl: ∀ i,0 ≤ l i) (ht : Heavy N.conduit)(hD : 1≤ D)
    (hk : Ac.Hit H.birth sx (Reserves.tariff (Tickets.extra X' z₀) Lk 0 Q.ε) Q.relative Gp)
    (hv : degreePrice sx (D*((T').rootHit+Gp)) Q.δ ≤ 1/2) (hV : a+δ+δ ≤ Q.exp)(hc:0<δ)
    (hs : degreePrice sx (salaries Q L μ x B Gp j n) δ ≤ 1/2) :
    Ready H.smallAt sx (fun p=>roof M H (floats M H χ N) l (fun p _=>stronger H p.val) p j) (a+δ) (salaries Q L μ x B Gp j n) δ (1/2):=by
   let g (z:Head S):= D^(Sum.elim (fun _=>0) Silica.horn z)*f₀ z
   let u z:= gale S (T').markSeed D g z
   let V0:=D*((T').rootHit+Gp)
   have hp := blends M H χ l N hl ht hD hk hv
   have hh i: 0 ≤ u i := nonneg_of_mul_nonneg_left (hp.2.2.2.2.1 i) (Real.exp_pos _)
   let c:= polyPrice Q.ε n * treeYield V0 (1/2) 0
   have hu:0<c:=by
     unfold c polyPrice treeYield; have ht:= Q.usable; have hv:0 < V0:= hp.1; exact mul_pos (by positivity) (mul_pos (mul_pos hv (by positivity)) (by norm_num))
   have hx : salaries Q L μ x B Gp j n=(1+2^j*B)*c:=rfl
   have hb : 0 ≤ (2:ℝ)^j*B:= mul_nonneg (by positivity) N.balance
   have hQ (i) : 0 ≤ f₀ i:=add_nonneg (N.conduit.fares _) (sum_nonneg fun j _=>by split; exact mul_nonneg (hl j) ((M j).profit); exact le_rfl)
   have hp'(p:Molecule S): 0 ≤ stronger H p*((∏ i∈p,f₀ i)*(1+H.shapeW p)^n):=mul_nonneg (by unfold stronger gust; positivity) (mul_nonneg (prod_nonneg (fun i _=> hQ i)) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume p)) _))
   have he (p:H.ThinP): 0 ≤ roof M H (floats M H χ N) l (fun p _=>stronger H p.val) p j:=by
      rw [covered_floats]; split; exact mul_nonneg hb (hp' _); exact le_rfl
   refine ⟨hx ▸ (mul_pos (by linarith only [hb]) hu), hc, hs, by norm_num, he, fun p=>?_⟩
   have hz (i : Head S): 0 ≤ L₀ i := by
     rcases i with i | i
     · exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _)
     exact Nat.cast_nonneg _
   have hk' := budget_scale hb (budget_pull (fun x:H.ThinP=>x.val) Subtype.val_injective
      (extraction H.supportP sx u L₀ Q.exp Q.ε Q.bound Q.usable hp hh hz p n))
   refine budget_loosen (budget_mono hk' (fun z=>?_) (fun z=>?_)) ?_
   · dsimp only; split; next => exact mul_nonneg (he z) (Real.exp_pos _).le
     exact le_rfl
   · dsimp only; split; next hi=>
       apply (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hV (Nat.cast_nonneg _))) (he z)).trans
       rw [covered_floats]; split; next h=>
         unfold Reserves.rooted; rw [if_pos ⟨h,hi⟩, stronger, currency, show (∏ i∈z.val, u i)=_ from shines (L:=L) (Q:=Q) (μ:=μ) (x:=x) (fe:=f₀) z.val, show setPrice H.supportP sx L₀ z.val=H.shapeW z.val from rfl, show z.val.biUnion H.supportP=H.smallAt z from rfl]; apply le_of_eq; ring
       next hn=> rw [zero_mul]; exact hk'.1 z
     next => exact hk'.1 z
   change _*c ≤ _; rw [hx]; gcongr; linarith

lemma pays_alpha (hl:∀ i, 0 ≤ l i)(hD : 1≤ D)
    (hk : Ready H.smallAt sx (fun p=>roof M H (floats M H χ N) l (fun p _=>stronger H p.val) p j) (a+δ) (salaries Q L μ x B Gp j n) δ (1/2))
    (h:Cascade.Heroes H N.conduit A B n)(ha:0 ≤ a)(m k:ℕ)(w:ℝ)
    (hx : D^k ≤ Real.exp (Q.ε*w))(hp : D^k≤Real.exp (Q.mark L μ x)) :
    Ac.Hit (Captain.reachability (H:=H)) sx
      (fun z:H.fragrances=>if Beacon.large H k w z then ∑ w:Syllable M H z, Bill M H (floats M H χ N) z l j w m else 0) a
        ((D^k)⁻¹*(collars G δ x j m * (salaries Q L μ x B Gp j n * (1-1/2)⁻¹))) := by
   have hb z (hz:Beacon.large H k w z): 1 ≤ (D^k)⁻¹*∏i, stronger H ((z.2 i).val) := by
     have hQ: ∏ i,stronger H (z.2 i).val= beacon H z := by
       simp only [stronger, beacon, gust, degree, acme, breadth, depth, overlap,pow_add,Nat.cast_sum,mul_sum,Real.exp_sum,Finset.prod_pow_eq_pow_sum, Finset.prod_mul_distrib]; ring
     rw [hQ]; have hb:= Beacon.takes k hD w hx hp z hz; have he:0 < D:= zero_lt_one.trans_le hD
     apply le_trans _ (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (pow_nonneg he.le _))); rw [inv_mul_cancel₀ (by positivity)]
   convert! run M H χ (floats M H χ N) l (fun p _=>stronger H p.val) (rocketing M H χ N h) hl (fun p _=> by unfold stronger gust; positivity) ha m hk (fun z _=> Beacon.large H k w z) _ (by positivity) (fun z _=> hb z) using 1
   ext i; split; simp [*]; simp [*]
end YM.RemainderComparison.Lyric
