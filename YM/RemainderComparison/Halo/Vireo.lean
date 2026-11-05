import YM.RemainderComparison.Halo.Norm
/-!
 # Booked change from marker root load and charging of the sparse archive

 No β power on marker roots. Scales only budgets already enrolled in THIS
 plot; not choosing another Term or Morph.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Halo
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Graft Cascade Lyric Daisy
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}{χ:Chi}
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
variable (l:ι→ℝ) (E:Set ℕ)(w:ℕ→ℝ){T' S' p' δ B' τ ε:ℝ}
local notation "Z" => radiusB x
local notation "C'" => Q.costs L μ R.beta x q
local notation "LT" => Mixed.lengths S C' (ConnectedActivityE6.lengths T R)

def rails (Ξ:Utopia H j v d r q χ) (E:Set ℕ)(w:ℕ→ℝ)(A F : ℝ):Head S→ℝ:= weather S E (fun i=>A*w i) (fun i=> F*Ξ.fare i)

def gaugeG (E:Set ℕ)(T' W':ℝ) (p:Head S):= if inherited S E p then T' else W'
variable {P':Type} [Fintype P']{X:P'→ Site f}{Y:ι→ Finset P'}

omit [Fintype ι] in
lemma scaled (p:Lyric.Scale X Y M l m σ B' S)(hv:0≤v) : Lyric.Scale X Y M (Lyric.mulScale v l) m σ (v*B') S:=by
   let r:= Lyric.mulScale v l
   have hf i:Palette.wages M r i= v*Palette.wages M l i:=by unfold Palette.wages r mulScale; ring
   refine ⟨(fun i=> mul_nonneg hv (p.currency i)),fun i h=> p.pin i (pos_of_mul_pos_right (hf i ▸ h) hv),?_,mul_nonneg hv p.tolerance,p.sizes⟩
   intro i; convert budget_scale hv (p.crown i) using 1; ext j; simp_rw [show Palette.wages M (mulScale v l) = _ from funext hf]; split <;> ring

def hike (Q:ConnectedActivityE6.Target G P)(x:ℝ)(m:ℕ)(p:ℝ):= m * Extra.Multi.siteFactor (radiusB x) * (Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5)) * p)
lemma rays (h:Lyric.Scale X Y M l m σ B' S)(hv:R.p.B ≤ 2*Z)(hh: Lyric.radiusCost Q L σ):
     Ac.Hit H.supportP Z (Reserves.tariff (Tickets.extra (Palette.sign M S) (Palette.wages M l)) LT 0 Q.ε) Q.relative (hike Q x m B'):=by
   exact pricingL M H (hike Q x m B') l (settles M H X Y _ (fun i=> mul_nonneg (h.currency _) (Leaf.profit _)) hv h.sizes h.pin h.tolerance hh h.crown)
variable (C₁ A₁:ℝ)
section
variable (k p:Head S→ℝ)
local notation "FUG" => Lyric.combined M (fun i=> p i*k i) l
lemma prize (hl:∀ i,0≤l i)(hk:∀ i,0≤k i)(hp:∀ i,0≤p i)(i) : 0≤FUG i:= add_nonneg (mul_nonneg (hp i) (hk i)) (sum_nonneg fun j _=>by split; exact mul_nonneg (hl _) (Leaf.profit _); exact le_rfl)
end
variable (f g:ℝ) -- gains
local notation "rail" => rails H Ξ E w C₁ A₁
local notation "G₀" => gaugeG (S:=S) E f g
local notation "F₀" => Lyric.combined M (fun i=>(G₀ i)*rail i) l

def first (k V gs F g R:ℝ):ℝ:=  k*V + gs*F*g + R -- scaled others k input accounts root V, E kappa rho, starring
lemma rails_nonneg (h:Presents R E w δ)(hc:0≤ C₁)(ha:0≤ A₁)(i:Head S) : 0≤ rails H Ξ E w C₁ A₁ i:=
    snow_pos (fun i=>mul_nonneg ha (Ξ.fares i)) (fun i _=>mul_nonneg hc (h.pay i)) i

lemma redwood {X₁ Y₁ k₀:ℝ} (h:Presents R E w δ)(hf:0≤f)(hg:0≤g)(hc:0 ≤ C₁)(ha:0≤ A₁)
     (hl:∀ i,0≤ l i)(hA:Sales Z Q.relative Q.ε (regularFoot S.ratio Q.halo Z R) w (regularExtra R) X₁)
     (hM:Ac.Hit H.supportP Z (Reserves.tariff (Tickets.extra (Palette.sign M S) (Palette.wages M l)) LT 0 Q.ε) Q.relative Y₁)
     (hL:first (g*A₁) (C').rootHit f C₁ X₁ Y₁ ≤ k₀)(hv:0<k₀)(ht: degreePrice Z k₀ Q.δ ≤ 1/2) :
     Ready H.supportP Z (tariff F₀ LT 0 Q.ε) (Q.exp+2*Q.ε) k₀ Q.δ (1/2):=by
   have hT i: 0 ≤ G₀ i:= by unfold gaugeG; split_ifs <;> assumption
   have hH i : 0 ≤ tariff F₀ LT 0 Q.ε i:= mul_nonneg (prize M l _ _ hl (rails_nonneg H Ξ E w C₁ A₁ h hc ha) hT _) (Real.exp_pos _).le
   refine ⟨hv,Q.pos,ht,by norm_num,hH,fun x'=>?_⟩
   let E₁ (i : Head S):= tariff F₀ LT 0 Q.ε i
   have hE (i : Head S): E₁ i ≤ (g*A₁ * (tariff Ξ.fare LT 0 Q.ε i) +(f*C₁)*(tariff (weather S E w 0) LT 0 Q.ε i)) + tariff (Tickets.extra (Palette.sign M S) (Palette.wages M l)) LT 0 Q.ε i:=by
      unfold E₁ tariff Lyric.combined; simp_rw [← mul_assoc _ _ (Real.exp _),← add_mul] -- ensure add shape
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le -- need syntactic
      apply add_le_add_left
      by_cases he : inherited S E i
      · obtain ⟨i,hi,rfl⟩:= he
        unfold gaugeG rails; rw [if_pos (show inherited S E (key S i) from ⟨i,hi,rfl⟩), weather_at _ hi,weather_at _ hi, ← mul_assoc]
        exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg hg ha) (Ξ.fares _))
      unfold gaugeG rails weather; simp [he,mul_assoc]
   unfold first at hL
   have hv':= budget_plus (budget_plus (budget_scale (mul_nonneg hg ha) (fare_hit H χ Ξ x')) (budget_scale (mul_nonneg hf hc) (ink_hit (q:=q) H h hA x'))) (hM x')
   refine budget_loosen (budget_mono hv' (fun z=>?_) (fun z=>?_)) hL
   · split; exact mul_nonneg (hH _) (Real.exp_pos _).le; exact le_rfl
   split_ifs; next hh=>
     apply (mul_le_mul_of_nonneg_right (hE z) (Real.exp_pos _).le).trans_eq
     unfold Target.relative; ring
   next => simp
end YM.RemainderComparison.Halo
