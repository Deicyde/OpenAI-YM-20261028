import YM.RemainderComparison.Lyric.Orbit
import YM.MergeProof.Wreath

/-! # Actual tier costs by Tickets: high book

Buys marker inflation together with the E6 heavy invoice (includes genuine
opt cost from kernel roof), with neither count-of-period factors nor assumption
that inserting a marker improves rarity. Doesn't differentiate in tags.
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
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ} {O:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n:ℕ}(χ:Chi)

open Daisy
local notation "X'" => Palette.mark M (c:=c)
local notation "Lk" => ConnectedActivityE6.lengths T R
local notation "sx" => radiusB x
variable (l:ι→ℝ)

def floats (N:Captain H j q d v u A b r B e n χ)(p:H.ThinP)(x:Drums M S):ℝ := if Ac.Spark H.supportP p.val ∧ x.reach ⊆ p.val then (B*(team M x).weight)*(∏ i∈p.val\x.reach,N.conduit.fare i)*(1+H.shapeW p.val)^n else 0
-- high Heroes gives actual forecast on these, even the zero.
variable (N:Captain H j q d v u A b r B e n χ)
omit [Fintype ι] in
lemma rocketing (h:Cascade.Heroes H N.conduit A B n): Paid M H χ N (floats M H χ N):=by
    constructor <;> intro p x
    · unfold floats; split; next h=> exact mul_nonneg (mul_nonneg (mul_nonneg N.balance (Team.profit _)) (prod_nonneg fun i _=> N.conduit.fares i)) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume _)) _)
      next=>rfl
    intro E _ _ _ F X U y ht hM hx hv hH hT hS hp
    rw [Palette.label] at hp
    unfold floats; rw [if_pos ⟨hS,hp⟩];
    have hh := h (team M x) p.val E F X U y ht hM hx hv hH hT hS (show (team M x).signs S⊆p.val from by rw [Palette.label]; exact hp)
    rwa [Palette.label] at hh

lemma accredits {f:Head S→ℝ} (t:Molecule S): (∏ i∈t,(f i+Tickets.extra (Palette.sign M S) (Palette.wages M l) i))=
      ∑ i:Drums M S, (∏ j∈i.val,l j)*(if i.reach ⊆ t then (team M i).weight*∏ j∈t\i.reach,f j else 0):= by
    rw [Tickets.expanded]; refine Finset.sum_congr rfl fun i _=>?_ ; split
    next h => rw [Palette.worth]; unfold Palette.wages; rw [prod_mul_distrib]; ring
    next h=> simp

local notation "D" => Height.grow G L x
open Height AnalyticBridge.VerifiedReset
-- charge at univ head

def combined (f : Head S→ℝ)(l:ι→ℝ):Head S→ℝ:= fun i=> f i+Tickets.extra (Palette.sign M S) (Palette.wages M l) i
lemma covered_floats (p:H.ThinP) :
      roof M H (floats M H χ N) l (fun p _=>stronger H p.val) p j=
        (if Ac.Spark H.supportP p.val then 2^j*B*(stronger H p.val*((∏i∈p.val, combined M N.conduit.fare l i)*(1+H.shapeW p.val)^n)) else 0):=by
   split; next hh=>
     unfold combined; rw [accredits M l]; unfold roof; let c:= stronger H p.val; let a:=(1+H.shapeW p.val)^n
     calc
       _ = 2^j*∑ i:Drums M S, c*B*( (∏ j∈i.val,l j)*(if i.reach⊆p.val then
                   (team M i).weight*∏ j∈p.val\i.reach,N.conduit.fare j else 0))*a:=by
               apply congr_arg; refine Finset.sum_congr rfl fun i _=>?_ ; unfold floats; by_cases h:i.reach⊆p.val
               · rw [if_pos ⟨hh,h⟩,if_pos h]; unfold c a; ring
               rw [if_neg (fun hz=>h hz.2),if_neg h]; ring
       _=_:=by simp_rw [← Finset.sum_mul, ← Finset.mul_sum]; unfold c a; ring
   next h=> unfold roof; rw [sum_eq_zero ?_,mul_zero]; intro x _; unfold floats; rw [if_neg fun hx=> h hx.1,mul_zero]
variable {δ Gp : ℝ}
local notation "T'" => Q.costs L μ R.beta x q
local notation "β'" => Q.relative
local notation "z₀" => (fun i=> (D)^Silica.horn (X' i)*Palette.wages M l i)
local notation "f₀" => (combined M N.conduit.fare l)
local notation "L₀" => Mixed.lengths S T' Lk

-- From marker-only occurrences, no allocation release field densities.
lemma adds_hit (hk : Ac.Hit H.birth sx (Reserves.tariff (Tickets.extra X' z₀) Lk 0 Q.ε) Q.relative Gp) :
    let z(i:Head S):= D^(Sum.elim (fun _=>0) horn i)*Tickets.extra (sign M S) (Palette.wages M l) i
    Ac.Hit H.supportP sx (tariff z L₀ (Mixed.stamp S T') Q.ε) β' Gp:=by
    intro z
    let u := tariff (Tickets.extra X' z₀) Lk 0 Q.ε
    rw [show Reserves.tariff z L₀ (Mixed.stamp S T') Q.ε=Sum.elim (fun _=>0) u from ?_]
    · simpa only [zero_add] using! Labels.together (fun x:Stores S=> H.supportP (.inl x)) _ _ (A:=Q.relative) (w:=fun _=>0) (show Ac.Hit (fun x:Stores S=> H.supportP (.inl x)) sx (fun _=>0) Q.relative 0 from (by intro x; simp [SumBudget])) hk -- syntax
    ext i; rcases i with i|i
    · unfold tariff z; rw [show Tickets.extra (Palette.sign M S) (Palette.wages M l) (.inl i)=0 from sum_eq_zero fun j _=> if_neg (by rw [sign, ← sparkPath]; simp),mul_zero,zero_mul]; rfl
    unfold z u Tickets.extra tariff Mixed.stamp; simp only [Sum.elim,Finset.mul_sum,Mixed.shares,Nat.cast_zero,mul_zero,add_zero,Pi.zero_apply]
    apply congr_arg₂ (·*·) _ rfl; refine Finset.sum_congr rfl fun j _=> ?_; unfold sign; rw [← sparkPath]; simp_rw [Palette.mark]; by_cases h:sparkling c f (M j).turn=i <;> simp [h]

-- First ready. Uses both accounts *before* extracting seed charge. No
-- confusion through the shared H.Conduit.
lemma blends (hp : ∀ i,0 ≤ l i) (ht : Heavy N.conduit)(hD : 1≤ D)
    (hk : Ac.Hit H.birth sx (Reserves.tariff (Tickets.extra X' z₀) Lk 0 Q.ε) Q.relative Gp)
    (hv : degreePrice sx (D*((T').rootHit+Gp)) Q.δ ≤ 1/2) :
    let g (z:Head S):= D^(Sum.elim (fun _=>0) Silica.horn z)*f₀ z
    Ready H.supportP sx (tariff (gale S (T').markSeed D g) L₀ 0 Q.ε) (Q.exp+2*Q.ε) (D*((T').rootHit+Gp)) Q.δ (1/2) := by
  intro g; let E:=N.conduit; let Z:=H.supportP
  let g' (z:Head S):= D^(Sum.elim (fun _=>0) Silica.horn z)*E.fare z
  have hr : Ready Z sx (tariff g' L₀ (Mixed.stamp S T') Q.ε) (Q.exp+2*Q.ε) (T').rootHit Q.δ (1/2):=by
    let z p := D ^ Silica.horn p * E.flair p
    rw [show g'=Mixed.costs S Q.halo sx (steamP S T') z from ?_]; swap
    · funext p; rcases p with p|p
      · unfold g' Utopia.fare stout Mixed.costs; simp
      rfl
    exact Mixed.ready_vertices S Q.halo sx T' H.birth z Lk (steamP S T') E.lives ⟨E.accrues.packetBound,ht.nonneg,E.accrues.extra,ht.hit⟩
  let TT:= tariff g L₀ (Mixed.stamp S T') Q.ε
  have h: Ac.Hit Z sx TT β' ((T').rootHit+Gp):=by
     intro x
     have hx:= budget_plus (hr.2.2.2.2.2 x) (adds_hit (q:=q) M H l hk x) -- expects chi/N?
     convert! hx using 1; ext i; unfold TT g tariff combined; dsimp only; split
     next hh => unfold g' Z E at *; unfold Target.relative; ring
     next hh => simp
  have hz:0 ≤ Gp:=budget_nonneg (hk 0);
  have he z:tariff (gale S (T').markSeed D g) L₀ 0 Q.ε z=D*TT z := by unfold TT tariff gale Mixed.stamp; simp only [Pi.zero_apply,add_zero,Real.exp_add]; ring -- order unfold bug
  rw [funext he]
  refine ⟨mul_pos (zero_lt_one.trans_le hD) (add_pos_of_pos_of_nonneg hr.1 hz),Q.pos,hv,by norm_num,?_,Quotes.hit_scale (zero_le_one.trans hD) h⟩
  intro i; refine mul_nonneg (zero_le_one.trans hD) (mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hD) _) (add_nonneg (E.fares i) (sum_nonneg fun j _=>?_))) (Real.exp_pos _).le)
  split; next => exact mul_nonneg (hp j) ((M j).profit)
  next=> exact le_rfl
end YM.RemainderComparison.Lyric
