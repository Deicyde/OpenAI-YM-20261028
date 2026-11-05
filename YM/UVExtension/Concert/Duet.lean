import YM.UVExtension.Concert.Trunk
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Haul
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Foam
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Tir
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Weld

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost Wick PhysicalNext.Repeat Lantern Marlin Song Animals Slide MeasureTheory Set Filter
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {x y W μ γ a b e: ℝ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
   {R:Rep G f}{H:Cash W x μ L Q o a T R} {Y D : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {M:Opening D Y}
    {p:BudgetPoint} (k:ℕ)

structure Charm (M:Opening D Y) (b:ℝ)(f:D→ℝ) : Prop where
    claim : ∃ g:Y→ℂ, Bumps M.span g ∧ (∀ d,g (M.call d)=↑(f d))∧∀ z∈ M.span,‖g z‖≤ b
namespace Charm
variable {f g:D→ℝ}
lemma adds (h:Charm M a f)(he:Charm M b g):Charm M (a+b) (fun d=> f d+g d):=by
  obtain ⟨A,h,hx,hv⟩:= h.claim; obtain ⟨B,hB,hf,hg⟩:= he.claim; exact ⟨fun z=>A z+B z,bends_add h hB,fun i=> by dsimp; rw [hx,hf,Complex.ofReal_add],fun z hz=>(norm_add_le ..).trans (add_le_add (hv z hz) (hg z hz))⟩
lemma multiplies (h:Charm M b f)(c:ℝ): Charm M (|c| *b) (fun d=>c*f d):=by
  obtain ⟨g,h,hx,hv⟩:= h.claim; exact ⟨fun z=> (c:ℂ)*g z,bends_smul (f:=fun _=> (c:ℂ)) h (bumps _ _ (differentiableOn_const _)),fun i=> by dsimp; rw [hx,Complex.ofReal_mul],fun z hz=> by rw [norm_mul,Complex.norm_real]; exact mul_le_mul_of_nonneg_left (hv z hz) (abs_nonneg c)⟩
lemma apart (h:Charm M a f) (he:Charm M b g):Charm M (a+b) (fun d=> f d-g d):=by simpa only [neg_one_mul,abs_neg,abs_one,one_mul,sub_eq_add_neg] using! h.adds (he.multiplies (-1))
lemma nil (h:0≤b):Charm M b (fun _=>0) := ⟨fun _=>0,bumps _ _ (differentiableOn_const _),fun _=>Complex.ofReal_zero.symm,fun _ _=>norm_zero.trans_le h⟩
lemma rack {A: Type} (s : Finset A) (g:A→ D→ℝ) (b:A→ℝ)(h:∀ i∈s,Charm M (b i) (g i)): Charm M (∑ i∈s,b i) (fun d=>∑ i∈s,g i d):=by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact nil le_rfl
  | insert i s hi hh => simp_rw [Finset.sum_insert hi]; exact (h _ (mem_insert_self ..)).adds (hh fun j hj=> h _ (mem_insert_of_mem hj))
end Charm

variable (H) (r:D→ℕ→ Config G c→ℝ) (x':Site c)

variable (hP:p.B=radiusB x)
    (F:ticketR M p (Beam.marquee H p).reg (preExponent p) r (fun _=>b))

def egg (p:BudgetPoint)(u:D) (V:Config G c):= ∑ i∈Meadow.panel H k, Meadow.garnerAt H p x' i * masked p.threshold (((Beam.marquee H p).reg i).support) (r u i) V

def heir (p:BudgetPoint)(u:D): Config G c→ℝ:= ∑ i∈Meadow.panel H k, Meadow.garnerAt H p x' i • r u i

include hP
lemma cashier (h:ℕ→ℂ) (w:ℕ→ℝ)(hy:∀ i, ‖h i‖≤ w i)(hx:coinE (Beam.marquee H p).reg p (preExponent p) w b) : ‖∑ i∈(Meadow.panel H k), (Meadow.garnerAt H p x' i:ℂ)*h i‖≤ (ballCost (Meadow.studio Q.halo (radiusB x)):ℝ)*b:=by
  let s:= neighbors (Meadow.studio Q.halo (radiusB x)) x'; let E i y := if ((Beam.marquee H p).reg i).site=y then w i*Real.exp (preExponent p*coverNumber p.B ((Beam.marquee H p).reg i).support) else 0
  apply le_trans (norm_sum_le ..)
  calc
    _ ≤ ∑ i∈ (Meadow.panel H k), ∑ x∈s,E i x:=by
      apply sum_le_sum; intro i hi; by_cases he:Meadow.garnerAt H p x' i=0
      · rw [he,Complex.ofReal_zero,zero_mul,norm_zero]; exact sum_nonneg fun x _=> (hx x).1 i
      have hv:= Meadow.assigned H p x' i hi hP he
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Meadow.nonnegative ..)]; refine ((mul_le_of_le_one_left (norm_nonneg _) (Meadow.portions ..)).trans (hy i)).trans ?_
      unfold E; rw [sum_ite_eq, if_pos (hv.2 ((Beam.marquee H p).reg i).anchor)]; apply le_mul_of_one_le_right ((norm_nonneg _).trans (hy _)); exact Real.one_le_exp (mul_nonneg (headline p).exponent_pos.le (Nat.cast_nonneg _))
    _ ≤ _:=by
      rw [sum_comm]; apply le_trans (sum_le_sum (fun x _=>budget_sum (hx x) (Meadow.panel H k)))
      rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) (budget_nonneg (hx 0))

include F
lemma glow (V:Config G c): Charm M ((ballCost (Meadow.studio Q.halo (radiusB x)):ℝ)*b) (fun d=>egg H k r x' p d V):=by
  let f i:= Healthy p.threshold ((Beam.marquee H p).reg i).support V
  let m(z:Y)(i:ℕ): ℂ:= if he:f i then F.f z i (show Tap p G ((Beam.marquee H p).reg i).site ((Beam.marquee H p).reg i).support from ⟨V,he,[],by simp,by simp⟩) else 0
  let g Y:= ∑ i∈ (Meadow.panel H k), (Meadow.garnerAt H p x' i:ℂ)*m Y i
  have ht(x:D) i: m (M.call x) i=↑(masked p.threshold ((Beam.marquee H p).reg i).support (r x i) V):=by
    unfold m; split; next he=> rw [masked_eq _ _ _ _ he,F.exacts]; rfl
    next he=> rw [masked_ne _ _ _ _ he]; exact Complex.ofReal_zero.symm
  refine ⟨g,fun s c h hh ht=>?_ ,fun d=>?_ , fun z hz=>?_⟩
  · apply DifferentiableOn.fun_sum; intro i hi; apply DifferentiableOn.const_mul; unfold m; split; next => exact F.pulse i _ s c h hh ht
    exact differentiableOn_const _
  · unfold egg g; push_cast; simp only [ht]
  obtain ⟨w,hw,hQ⟩:= (F.bounds z hz).afloat
  apply cashier H k x' hP _ w (fun i=>?_) ((singers _ _).1 hQ); unfold m; split; next => exact (hw i).2 _
  exact norm_zero.trans_le (hw i).1

-- uniform directions Currency on small tier using ANY anchor. use only Healthy univ.
structure Fly (G:Gauge)(c:Side)(p:BudgetPoint) where
    view : Config G c
    snow : flags p.threshold view=∅
    ls : List (Directions G c)
    lengthC : ls.length≤p.order
    roll : ∀ i∈ls, ‖i‖≤ p.threshold
namespace Fly
variable (u:Fly G c p)
def reel (f:Config G c→ℝ): ℝ:= leftDerivs f u.ls u.view
def taps (A: RegularAddress c): Tap p G A.site A.support:= ⟨u.view,by unfold Healthy; rw [u.snow]; simp,u.ls,u.lengthC,
   fun _ h=> Boulevard.tiny (u.roll _ h) _⟩
end Fly
lemma sherbet (u:Fly G c p)(hp:∀ i,smoothP p (Beam.marquee H p).reg (r i)): Charm M ((ballCost (Meadow.studio Q.halo (radiusB x)):ℝ)*b) (fun i=>u.reel (heir H k r x' p i)):=by
  let g(z:Y):= ∑ i∈ (Meadow.panel H k), (Meadow.garnerAt H p x' i:ℂ)*F.f z i (u.taps ((Beam.marquee H p).reg i))
  refine ⟨g,fun s f h hh hd=> DifferentiableOn.fun_sum (fun i hi=> (F.pulse i _ s f h hh hd).const_mul _),fun i=>?_,fun z hz=>?_⟩
  · unfold g Fly.reel heir; have ht (j): Push.Local.Chart p.order (r i j) u.view:= (hp i j).smooth _ (u.taps ((Beam.marquee H p).reg j)).live
    rw [Push.Local.left_sum _ _ _ _ (fun j _=>show Push.Local.Chart p.order (Meadow.garnerAt H p x' j • r i j) u.view from (ht j).const_smul (Meadow.garnerAt H p x' j)) u.lengthC]; rw [Complex.ofReal_sum]; refine Finset.sum_congr rfl fun j h=> ?_
    rw [show leftDerivs (Meadow.garnerAt H p x' j • r i j) u.ls u.view=_ from Push.Local.left_linear (Meadow.garnerAt H p x' j • ContinuousLinearMap.id ℝ ℝ) _ (ht j) u.lengthC,F.exacts]; exact (Complex.ofReal_mul ..).symm
  obtain ⟨w,hw,hb⟩:= (F.bounds z hz).afloat; exact cashier H k x' hP _ w (fun i=> (hw i).2 _) ((singers _ _).1 hb)
omit F hP
lemma smoothie (hp:∀ i,smoothP p (Beam.marquee H p).reg (r i)) (u:D) : p.Regular univ (heir H k r x' p u):=
    Meadow.regularA (Meadow.panel H k) fun i _=> CouplingShape.reg_scale _ (CouplingShape.reg_extend (hp u i) (subset_univ _))
end YM.UVExtension.Concert
