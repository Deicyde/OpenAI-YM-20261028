import YM.FullVolume.Florid.Vernal
import YM.FullVolume.Florid.Pages
import YM.FullVolume.Florid.Coco
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Sparks
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' fq:ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
namespace Mill
variable (V:Mill U)
local notation "Λ"=> U.pole
local notation "Rv"=> V.pole
variable (D: dust j o χ L x₀ d fq)
open Lyre Charity Blaze.March
variable {p:Signal j} {ν α:ℝ} (hc:Clear Q L μ ν x₀ v p) (hr:Clarity H j A' δ ν)
variable {V':ℝ→ℝ} (W':Lake G L (payE o.eta o.gap o.ample (Census.tubularPrice G L)) (K*j*2) V' k)
variable (Y':Margin G L x₀ α δ) (w:Rung) (η:ℝ) (hh : ∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/v)^i)‖ ≤ η)
set_option quotPrecheck false
local notation "τ"=> V.pole.turn.badge S
local notation "Q'" => Empire.stella Q
local notation "Φ"=> jewelDebt V.pole (Empire.stella Q) L x₀
local notation "B₀" => radiusB x₀
local notation "π"=> Lyre.spicesF G (r+fq) L' (V' x₀) K j
-- selected under stellar props. Keep Φ factors integrated outside tree.
def lushE (α ν a:ℝ)(p:Signal j)(n:ℕ)(i:H.ThinP) := let f:= M.ledger p M.weft; let q:= swing (stella Q) L μ R.beta x₀ ν; let F:= colly f V.pole (stella Q) L x₀
   a*Real.exp (α*(coverNumber (radiusB x₀) (H.unionP i.val))) * (Mixed.selected S Q.halo B₀ q H.birth F (ConnectedActivityE6.lengths T R) (steamP S ((Empire.stella Q).costs L μ R.beta x₀ ν)) 0 n 0 0 i.val)
local notation "hτ" => lushE M V α ν (π) p (k+j)
local notation "yτ" => (swing Q' L μ R.beta x₀ ν).ceiling 0 (k+j) 0 0
open Mixed
include M in
lemma buoyant (f₀ : ℝ) (h:dust j o χ L x₀ d fq):0 ≤ Lyre.spicesF G (r+fq) L' f₀ K j:= by
    unfold spicesF; have hs:= M.pole.stencil.active; have hf:= h.1; have ht:= M.pole.pos; have hx:0≤ Fold.charge j:= (FullVolume.Ray.ink.pay_pos _).trans (le_max_left ..); have hu:0≤FullVolume.Ray.Weigh.pattern j:=Finset.sum_nonneg (fun _ _ =>zero_le_one.trans (Planned.AtomRegular.polar_one _)); positivity -- variable confusion `v` equals Lyre.v.` use x
include D
section ships
variable (hp:foam Q L)(hb:R.p.B≤2*radiusB x₀)(hA:(Daisy.swing (stella Q) L μ R.beta x₀ ν).Buy S.patch.L Q.halo (radiusB x₀))
include hp hb hA hc D M
lemma stipend (n:ℕ)(z:ℝ)(he:0≤z): Ac.Hit H.smallAt B₀ (lushE M V α ν z p n) (Q.exp-α) (z*(Daisy.swing (stella Q) L μ R.beta x₀ ν).ceiling 0 n 0 0):=by
    let f:= colly (M.ledger p M.weft) V.pole (stella Q) L x₀
    let P:= swing (stella Q) L μ R.beta x₀ ν; let U:= Mixed.selected S Q.halo B₀ P H.birth f (ConnectedActivityE6.lengths T R) (steamP S ((Empire.stella Q).costs L μ R.beta x₀ ν)) 0 n 0 0
    have he':= Mixed.mixed_hit S Q.halo B₀ P H.birth f (ConnectedActivityE6.lengths T R) (steamP S ((Empire.stella Q).costs L μ R.beta x₀ ν)) hA (mashH V.pole H hp hb _ _ _ (M.acclaim hc)) 0 n 0 0
    intro i
    have h:= budget_scale he (budget_pull (fun i:H.ThinP=> i.val) Subtype.val_injective (he' i))
    convert! h using 1; ext j; split
    next hx=>
      change _=z*(if i ∈ H.unionP j.val then _*_ else 0)
      rw [if_pos (show _∈ H.unionP j.val from hx)]; unfold lushE; dsimp only
      let n:ℝ:=coverNumber B₀ (H.smallAt j); change z*Real.exp (α*n)*(U j.val)*Real.exp ((Q.exp-α)*n)= z*(U j.val*Real.exp (Q.exp*n))
      rw [show Q.exp*n=α*n+(Q.exp-α)*n by ring,Real.exp_add]; ring
    next hx=> change 0=z*(if i∈ H.unionP j.val then _*_ else 0);rw [if_neg (show _∉ H.unionP j.val from hx),mul_zero]
lemma prosp (i : H.ThinP):0 ≤ hτ i:=by
    have ht:= stipend M V D (α:=α) hc hp hb hA (k+j) (π) (buoyant M _ D)
    obtain ⟨q,hq⟩:= i.property.1
    have he: q∈ H.smallAt i:=hq; have hp:= (ht q).1 i; dsimp only at hp; rw [if_pos he] at hp
    exact nonneg_of_mul_nonneg_left hp (Real.exp_pos _)
lemma twined (i:H.ThinP)(hp': τ∈i.val)(hh:Ac.Spark H.supportP i.val): Φ*(hτ i)= seasoned M V p (π) ν α (k+j) i.val:=by
   let f:= M.ledger p M.weft; let q:= swing (stella Q) L μ R.beta x₀ ν; let F:= colly f V.pole (stella Q) L x₀
   let k':= Mixed.costs S Q.halo B₀ (steamP S ((Empire.stella Q).costs L μ R.beta x₀ ν)) F
   have hh':Φ*k' τ=(V.pole).weight := by
      rw [← Daisy.sparkPath]; change Φ*(if _ then _ else _)= _; rw [if_pos rfl]; exact (scentL V.pole H).2.2.symm
   have hz : ∀ x∈i.val.erase τ, k' x=M.mouth ν p x := by
      intro x hx; have ht:= ne_of_mem_erase hx; unfold k' F; rcases x with x|x; · rfl
      rw [← sparkPath] at ht; exact if_neg fun h=>ht (congr_arg Sum.inr h)
   unfold lushE; dsimp only
   have he: Mixed.Allowed S Q.halo B₀ q H.birth (ConnectedActivityE6.lengths T R) 0 0 0 i.val:= (H.attends ..).2 hh
   rw [Mixed.selected,if_pos he, Mixed.Price,← mul_prod_erase _ _ hp']
   let e:=Real.exp (α*(coverNumber (radiusB x₀) (H.unionP i.val)));change Φ*(π * e *((k' τ*_)*_))= _
   unfold seasoned; dsimp only; rw [Finset.prod_congr rfl hz]; change Φ * (π * e * ((k' τ * _) * (1+H.shapeW i.val) ^ (k+j)))=_
   rw [← hh']; ring
end ships
end Mill
end YM.ConnectedActivityE6.Empire.Imago
