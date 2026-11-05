import YM.RemainderComparison.Lyric.Store
import YM.RemainderComparison.Access.Geometry
import YM.RemainderComparison.Beacon.Spill

/-!
# Cost of returning marker taxes to the declared denominations.

The stamp uses epochs. Before resetting the analytic powers, on the SAME
trajectory. R includes rendering through the declared order and any lawful E
(assumed paid by indexed P.price clock), every K partner at that step.
Doesn't factor vacuum. Numbers chosen explicitly, not optimized.
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
variable {δ Gp Bm: ℝ}
local notation "T'" => Q.costs L μ R.beta x q
local notation "z₀" => (fun i=> (D)^Silica.horn (X' i)*Palette.wages M l i)
local notation "f₀" => (combined M N.conduit.fare l)
local notation "L₀" => Mixed.lengths S T' Lk
open Delay

-- D^(-5) station for probes of unit-ish hit budget polynomial p_geo
-- returns a factor running by total marker grade in the final polynomials.

def mulScale (x:ℝ)(l:ι→ℝ) := fun i=> x*l i
def tax (G:Gauge)(L:Side)(s:ℝ):= grow G L s^5
local notation "λ₀" => mulScale ((tax G L x)⁻¹) l
local notation "z'" => (fun i=> (D)^Silica.horn (X' i)*Palette.wages M λ₀ i)

variable {P':Type} [Fintype P']
-- Hats are the canon quick normalization for registered terms. `menus`
-- may correlate turns. No need period-root concentration except below.
structure Scale (s: P' → Site f) (a:ι→ Finset P') (M:ι→ Leaf R) (l:ι→ℝ) (N:ℕ)(B d:ℝ) (S:StepData c f):Prop where
   currency (i:ι) : 0 ≤ l i
   pin i : 0 < Palette.wages M l i → ∃ v∈a i,s v∈(M i).crest
   crown : Extra.Multi.Rooted a (fun i=>(M i).crest) R.p.B B (Palette.wages M l) d
   tolerance : 0≤d  -- including empty spaces
   sizes : Extra.Multi.Occupancy (S.ratio.parent ∘ s) N

variable {s: P'→Site f} {t:ι→ Finset P'}
variable (hT:Scale s t M l m Bm δ S)
include hT
local notation "l'" => Palette.wages M λ₀
local notation "d'" => D*((tax G L x)⁻¹)
lemma habitats (hD: 1≤ D)(hk:R.p.B≤2*sx)(hr:radiusCost Q L Bm) : (∀ i, 0≤ (λ₀) i) ∧
     Ac.Hit H.birth sx (Reserves.tariff (Tickets.extra X' z') Lk 0 Q.ε) Q.relative
       (m * Extra.Multi.siteFactor sx * (Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5)) * (d'*δ))) ∧
     Ac.Hit H.birth sx (Reserves.tariff (Tickets.extra X' l') Lk 0 Q.ε) Q.relative
       (m * Extra.Multi.siteFactor sx * (Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5)) * (d'*δ))) := by
    let r:=d'; let u:=Palette.wages M l; let q:=λ₀
    have he : 0≤ D:=zero_le_one.trans hD; have h: 0≤tax G L x:= pow_nonneg he _
    have hh i:0≤q i:= mul_nonneg (inv_nonneg.mpr h) (hT.currency i)
    have hz : 0≤r:=mul_nonneg he (inv_nonneg.mpr h); have hu : Extra.Multi.Rooted t (fun i=>(M i).crest) R.p.B Bm (fun i=> r*u i) (r*δ):=by
       intro i; convert budget_scale hz (hT.crown i) using 1; ext j; by_cases he:i∈t j <;> first| (simp only [he,↓reduceIte,mul_zero]; unfold u; ring) | simp [he]
    have hv i :0 ≤ Palette.wages M q i:= mul_nonneg (hh _) ((M i).profit)
    have ht i : l' i ≤ z' i:= le_mul_of_one_le_left (hv i) (one_le_pow₀ hD)
    have hL i : z' i ≤ r*u i:=by
       have hl (c f:Side)(w:Wing): Silica.horn (sparkling c f w) ≤ 1 := by
          cases w; exact le_rfl; exact Nat.zero_le _
       change _ ^ _ * ((tax G L x)⁻¹*l i*(M i).weight) ≤ r*(l i*(M i).weight)
       refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (hl c f ((M i).turn))) (hv i)) ?_; unfold r; rw [pow_one]; apply le_of_eq; ring
    have he' (u':ι→ℝ)(hp:∀ i,0≤u' i)(hg:∀ i,u' i≤ r*u i): Ac.Hit H.birth sx (Reserves.tariff (Tickets.extra X' u') Lk 0 Q.ε) Q.relative
       (m * Extra.Multi.siteFactor sx * (Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5)) * (r*δ))) :=
       settles M H s t u' hp hk hT.sizes (fun i h=> hT.pin i (show 0<u i from pos_of_mul_pos_right ((h.trans_le (hg i))) hz)) (mul_nonneg hz hT.tolerance) hr (Extra.Multi.Rooted.mono hu hp hg le_rfl le_rfl)
    exact ⟨hh,he' _ (fun i=>mul_nonneg (pow_nonneg he _) (hv i)) hL,he' _ hv (fun i=> (ht i).trans (hL i))⟩

omit hT
-- quick circuit; enough Plot without R exponent≥100, or purchase stronger exponent rails when using that bridge
lemma plot_built (h:∀ i,0≤l i)(he:Ac.Hit H.birth sx (Reserves.tariff (Tickets.extra X' (Palette.wages M l)) Lk 0 Q.ε) Q.relative (Daisy.ribbon Q L x)) : Plot M H l:=by
   have ha:= H.armed
   refine ⟨⟨ha.packetBound,fun i=>add_nonneg (ha.holds i) ?_,ha.extra,fun i=>?_⟩,h⟩
   · exact sum_nonneg fun j _=> by split; exact mul_nonneg (h _) ((M _).profit); exact le_rfl
   convert! budget_plus (ha.pays i) (he i) using 1; ext j; dsimp only [Palette.pitch,Reserves.tariff,Cash.birth]; split <;> simp only [Pi.zero_apply,add_mul,add_zero] ; rfl

omit [Fintype ι] in
lemma toll (s:H.fragrances) (w:Syllable M H s) (r:ι→ℝ) (v:ℝ):
     invests M H s w (mulScale v r)= v^notes M H s w * invests M H s w r := by
   unfold invests; simp_rw [mulScale, prod_mul_distrib,prod_const,Finset.prod_pow_eq_pow_sum]; rfl
lemma earns (hl:∀ i,0≤l i) (hD: 1≤ D)
    (hs : Ac.Hit H.birth sx (Reserves.tariff (Tickets.extra X' z') Lk 0 Q.ε) Q.relative Gp)
    (hv : degreePrice sx (D*((T').rootHit+Gp)) Q.δ ≤ 1/2) (hV : a+L'+L' ≤ Q.exp)(hc:0<L')
    (hy : degreePrice sx (salaries Q L μ x B Gp j n) L' ≤ 1/2)
    (h': Heavy N.conduit) (h:Cascade.Heroes H N.conduit A B n)(ha:0≤a)(m k J:ℕ)(w:ℝ)
    (hx : D^k ≤ Real.exp (Q.ε*w))(hp : D^k≤Real.exp (Q.mark L μ x)) :
    Ac.Hit (Captain.reachability (H:=H)) sx
      (fun z:H.fragrances=>∑ w':Syllable M H z, if Beacon.large H k w z ∧ notes M H z w' ≤ J then Bill M H (floats M H χ N) z l j w' m else 0) a
        (((tax G L x)^J) * ((D^k)⁻¹*(collars G L' x j m * (salaries Q L μ x B Gp j n * (1-1/2)⁻¹)))) := by
   let r:=tax G L x; have hr:1 ≤ r:= one_le_pow₀ hD; have hz:0 < r:=zero_lt_one.trans_le hr
   have hl' i : 0≤ (λ₀) i:= mul_nonneg (inv_nonneg.mpr hz.le) (hl i)
   have hk:= canvas M H χ λ₀ N hl' h' hD hs hv hV hc hy
   let f:= floats M H χ N; have hs (z)(w):0 ≤ Bill M H f z l j w m :=
     mul_nonneg (prod_nonneg fun i _=>prod_nonneg fun j _=>hl _) (dividend_nonneg M H χ (rocketing M H χ N h) z w)
   intro i
   have ht:=budget_scale (show 0 ≤ r^J from pow_nonneg hz.le _) (pays_alpha M H χ λ₀ N hl' hD hk h ha m k w hx hp i)
   refine budget_mono ht (fun z=>?_) fun z=>?_
   · dsimp only; split
     · exact mul_nonneg (sum_nonneg fun y _=> by split; exact hs _ _; exact le_rfl) (Real.exp_pos _).le
     exact le_rfl
   dsimp only; split
   next hX=>
      rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      by_cases hb:Beacon.large H k w z
      swap; · rw [if_neg hb,mul_zero,sum_eq_zero (fun i _=> if_neg (fun h=> hb h.1))]
      rw [if_pos hb, Finset.mul_sum]; refine Finset.sum_le_sum fun m' _=> ?_
      rw [show Bill M H (floats M H χ N) z λ₀ j m' m = (r⁻¹^notes M H z m')* (Bill M H f z l j m' m) from ?_]
      · rw [←mul_assoc]; split; next h=>
            apply le_mul_of_one_le_left (hs z m')
            rw [inv_pow,← div_eq_mul_inv]; exact (one_le_div (pow_pos hz _)).2 (pow_le_pow_right₀ hr h.2)
        next => exact mul_nonneg (mul_nonneg (pow_nonneg hz.le _) (pow_nonneg (inv_nonneg.mpr hz.le) _)) (hs z m')
      unfold Bill; rw [Lyric.toll M H]; unfold f r; ring
   next => rw [mul_zero]
end YM.RemainderComparison.Lyric
