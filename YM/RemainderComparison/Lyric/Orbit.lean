import YM.RemainderComparison.Lyric.Salary
import YM.MergeProof.Permit

/-! # Enough payment from rooted incoming markers

Sizes in real Calibration unit. Carries EACH marker footprint and tag,
specific mask read included at its individual point. After horizons bought,
no hidden period dependence. Honors geometry only, does not replace the
required faithful source render by abstract M i.
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

-- enough to buy any account Books without restricting it to vacuum funds at this epoch
open Daisy
local notation "X'" => Palette.mark M (c:=c)
local notation "Lk" => ConnectedActivityE6.lengths T R
local notation "sx" => radiusB x
variable {P':Type} [Fintype P'] (X:P'→Site f) (Y:ι→Finset P')

/-- How much root inflation? choose L before checking it. -/
def radiusCost (Q: ConnectedActivityE6.Target G P) (L:Side) (v:ℝ) :=
    (Q.relative+1)*(10*Footprint.preCost (Q.halo+5)/L.val) +2*Q.ε ≤ v
lemma bidLift (hS:b+2*Q.ε ≤ v) (hb:0<b): ∃ n:ℕ,∀ L:Side,n≤L.val→ radiusCost Q L v:=by
    obtain ⟨n,hn⟩:= eventually_atTop.mp ((tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const hb|>.eventually_ge_atTop ((Q.relative+1)*(10*Footprint.preCost (Q.halo+5))))
    refine ⟨n,fun L hl=>?_⟩; unfold radiusCost
    have hh := hn L.val hl
    refine (add_le_add_left ?_ (2*Q.ε)).trans hS
    rw [← mul_div_assoc]; apply (div_le_iff₀ (by positivity)).2; rw [mul_comm b]; exact hh

variable (l:ι→ℝ) (hp: ∀ i,0≤ l i)
include hp
lemma settles (hv: R.p.B≤2*sx)(hh : Extra.Multi.Occupancy (fun i=>S.ratio.parent (X i)) n)(hz: ∀ i, 0<l i→∃ j∈Y i,X j∈ (M i).crest) (hc:0≤ d)(hL:radiusCost Q L v)
    (hT:Extra.Multi.Rooted Y (fun i=>(M i).crest) R.p.B v l d) :
    Ac.Hit H.birth sx (Reserves.tariff (Tickets.extra (Palette.mark (c:=c) M) l) Lk 0 Q.ε) Q.relative
       (n * Extra.Multi.siteFactor sx * (Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5)) * d)):=by
  -- head to fine cost
  let W':=Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5)); have hW:0≤ W':=(Real.exp_pos _).le
  let mf (i:ι):= l i * Real.exp (2*Q.ε * Lk (X' i)+0)
  have hf i:0≤ mf i:= mul_nonneg (hp _) (Real.exp_pos _).le
  have hv'':(0:ℝ) ≤ Q.relative+1:=by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  have hR:Extra.Multi.Rooted Y (H.birth ∘ X') sx (Q.relative+1) mf (W'*d):=by
     intro i; refine Extra.Multi.Budget.mono (Extra.Multi.Budget.scale (hT i) hW) (fun i=>?_) (fun j=> ?_) le_rfl
     · split; exact mul_nonneg (Real.exp_pos _).le (hf _); rfl
     split_ifs; swap; · rw [mul_zero]
     unfold mf; rw [add_zero]; let u:= coverNumber R.p.B (M j).crest
     have hz : coverNumber sx (H.birth (X' j)) ≤ coverNumber _ _:= cover_mono
         (sparkHead (M j) H|>.symm ▸ (Footprint.inspected_price S.ratio Q.halo _ (M j).crest (by have h:= H.laws.data.room.sight.1; omega))) sx
     have hx:0 < sx:=by have h:= H.laws.data.room.sight.1; omega
     have hu:=mul_le_mul_of_nonneg_left ((Nat.cast_le (α:=ℝ).mpr hz).trans (footprint S.ratio _ sx R.p.B _ hx hv)) hv''
     rw [show Lk (X' j)=(u:ℝ) from sparkExp (T:=T) (M j)]; unfold W'
     rw [← mul_assoc (Real.exp ((Q.relative+1) * preCost _))]; rw [mul_comm (l j),← mul_assoc,← Real.exp_add,← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (hp _); apply Real.exp_monotone
     change (Q.relative+1)*(coverNumber sx (H.birth (X' j)):ℝ) + 2*Q.ε*u ≤ _
     apply le_trans (add_le_add_left hu _) ?_; unfold conversion; unfold radiusCost at hL
     rw [show S.ratio.count=L from H.laws.data.funds.length_eq]; have h:= mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg (α:=ℝ) u)
     unfold u at *; linarith only [h]
  have ht:= Extra.Multi.root_hit (a:=Q.relative) hh hf (mul_nonneg hW hc)
     (fun i hu=> by obtain ⟨j,h,hk⟩:=hz i (pos_of_mul_pos_left hu (Real.exp_pos _).le); refine ⟨j,h,?_⟩; change _∈ H.birth _; rw [show X' i= sparkling c f (M i).turn from rfl,sparkHead]; exact halo_subset _ _ (mem_image_of_mem _ (mem_union_left _ hk))) hR -- inferred
  intro p
  let Z:=Tickets.extra (Palette.mark (c:=c) M) l; let X:= Palette.mark (c:=c) M
  refine budget_of_sum (fun i=>?_) (fun V=> ?_)
  · have he j:0 ≤ Z j:=sum_nonneg fun i _=>by split;exact hp i; exact le_rfl
    split; · exact mul_nonneg (mul_nonneg (he _) (Real.exp_pos _).le) (Real.exp_pos _).le
    exact le_rfl
  let s i:= if p∈ (H.birth ∘ X) i then mf i*Real.exp (Q.relative*coverNumber sx (H.birth (X i))) else 0
  have he(i:ConnectedActivityE6.Alphabet c f):
        (if p∈H.birth i then Reserves.tariff Z Lk (fun _=>0) Q.ε i*Real.exp (Q.relative*coverNumber sx (H.birth i)) else 0)=∑ j, if X j=i then s j else 0 :=by
       unfold Z tariff Tickets.extra s mf
       by_cases hh:p∈ H.birth i
       · rw [if_pos hh,sum_mul,sum_mul]; apply sum_congr rfl; intro j _; unfold X; by_cases hv:X' j=i <;> simp [hv,hh]
       rw [if_neg hh]; symm; apply sum_eq_zero; intro j _; unfold X; split; next h=> simp [h,hh]
       next=>rfl
  change (∑ i∈V, if p∈H.birth i then tariff Z Lk (fun _=>0) Q.ε i*Real.exp (Q.relative*_ ) else 0)≤_
  simp_rw [he]; rw [sum_comm]; refine le_trans (sum_le_sum (s:=(univ: Finset ι)) (g:=s) ?_) (budget_sum (ht p) _)
  intro i _; simp only [sum_ite_eq]; split; rfl;exact (ht p).1 i

end YM.RemainderComparison.Lyric
