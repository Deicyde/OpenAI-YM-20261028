import YM.RemainderComparison.Herbal.Garden
import YM.RemainderComparison.Portal.Quota
/-!
 # Tagged AUX law; H form and density comparison. Foreign producers: Terrain.
 Precise hypothesis E's, mass μ1 fixed for quote ramp; all factors billed
 using real actual Marker.W.Census basis. Costs AFTER aggregation but can't cancel
 high hits with this. Includes empty. Use Sage for seed seam later. Don't assume
 Lawn constructors use same β; these Props ledger connects.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Herbal
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token Aux Portal Merge Palette Cascade Lyric Lotus Marker Next.Rank.Glyph Next.Rank.Exponential
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n k N m : ℕ} {Z σ C D W A v u d e t a c' B':ℝ}
variable {c f : Side} {S : StepData c f} {ι : Type} {α : Type}
variable {T : Tube G S} {F : Forest S.ratio} {Θ : ChartRatio G} {k': S.Choices} (ρ:Bid.Dir G c→AxisChart G F) (B:BudgetPoint) (β:ℝ)
local notation "Xs"=> Positions (Uniform.Primary c G)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "θ"=> Lapis.orbit F ρ
local notation "v'"=> eaves G L t
local notation "A'"=> Access.apron G L t
local notation "D'"=> wick G L d t
local notation "e'"=> furl G L t
local notation "g"=> gStep β
variable {x:Positions (Uniform.Primary c G)} {K:KernelChoices} {O:Teller G} {R:Rep G f}
variable (P:Eden f G α)(M:ι→ Lotus.Leaf R)(L':ι→ Eden f G α) (l:ι→ℝ)

structure Terrain (R:Rep G f)(T:Tube G S) (B:BudgetPoint)(P:Eden f G α)(M:ι→ Lotus.Leaf R)(l:ι→ℝ)(E:ι→Eden f G α):Prop where
   base : R.path=T.up
   clip : R.clip=T.high
   cash : R.p=B
   freeVac : R.v=0
   unkempt (j:ℕ): R.activities.K j=0
   soft : ∀ i, ∃ p:ℕ,(M i).turn=.logKey p
   vac : ∀ U,flags B.threshold U=∅ → P.groups R.beta U= - R.activities.additive B U
   glyph (i) (U): flags B.threshold U=∅ → (E i).groups R.beta U=(M i).ingredient U * l i

local notation "ξ" => R.beta
variable [Fintype ι]
variable (hT:Terrain R T B P M l L')

def grotto (S:StepData c f)(y:modes ι) := Finset.univ.filter fun z: Drums M S => y = scene z.val
lemma grove (y) : (grotto M S y).card≤1:= Finset.card_le_one.mpr (fun _ ha _ hb=> Subtype.ext (congr_arg (fun i:modes ι=>i.val) (((mem_filter.mp ha).2).symm.trans ((mem_filter.mp hb).2))))
def thicket (S:StepData c f)(y:modes ι)(U:Config G f):= ∑ z∈grotto M S y, raiseU B R.beta P U * ∏ i∈z.val, (L' i).cloaked B R.beta U
def vista (y:modes ι)(z:ℝ × Positions (Uniform.Primary c G))(w:Y):= ∑ i∈grotto M S y, dawn ρ P z w * ∏ j∈i.val,(L' j).proofE ρ z w

include hT
omit [Fintype ι] in
lemma mead_b (s: Drums M S) (U:Config G f):
   binder M l s U=inputC T B R.beta (fun U=> raiseU B R.beta P U * ∏ i∈s.val,(L' i).cloaked B R.beta U) U:=by
  let C:=team M s; let H' i:=M i; let V:=Pane.virgin T B R.beta
  have hp : C.gasDue=∅:=by
      apply Finset.eq_empty_iff_forall_notMem.mpr; intro i hi; obtain ⟨j,hj,h⟩:= (C.asked _).1 hi
      obtain ⟨i,hi,rfl⟩:= mem_image.mp hj; obtain ⟨p,hj⟩:=hT.soft i; rw [hj] at h; contradiction
  have ha : (∑' j,C.bun j U)= C.ingredients U * R.activities.gas B U:= by
     unfold Activities.gas; rw [← tsum_mul_left]; apply tsum_congr; intro i
     unfold Team.bun Team.bill; rw [hT.cash,hp]; simp only [Finset.empty_subset,if_true,Finset.sdiff_empty]; unfold Activities.gasOccurrence; split <;> simp
  change (Real.exp (R.exponent U)*(∑' k,C.bun k U))*(∏ k∈s.val,l k)=V.eval U*_
  rw [ha]; by_cases hh: flags B.threshold U=∅
  · have hV : R.exponent U= -(ξ* mainTerm T.high T.up U+Precision.loop T.up U)+P.cloaked B ξ U:=by
      rw [P.part B R.beta U hh, hT.vac _ hh, Rep.exponent, hT.cash,hT.base,hT.clip,hT.freeVac,Pane.crystalline _ _ _ _ _ hh]
      ring
    have he: R.activities.gas B U=1:= Activities.gas_one _ _ hh
    rw [he,mul_one,hV,Real.exp_add, show V.eval U= _ from (Pane.sparkling T B R.beta U).trans (if_pos hh)]; unfold raiseU
    simp_rw [(L' _).part B R.beta U hh,hT.glyph _ _ hh]; rw [Finset.prod_mul_distrib]; simp only [mul_assoc]; congr 2
    rw [show C.ingredients U=∏ j∈s.val.image M, j.ingredient U from rfl, Finset.prod_image]
    intro i hi j hj h; exact s.prop hi hj (congr_arg (fun a: Lotus.Leaf R=>a.turn.badge S) h)
  have he: R.activities.gas B U=0:= by
     unfold Activities.gas; have he (i : Finset ℕ) : R.activities.gasOccurrence B i U=0:= by
        unfold Activities.gasOccurrence; split; next h=>
          obtain ⟨z,hz⟩:= Finset.nonempty_iff_ne_empty.mpr (show i≠∅ from fun hi=> hh (by have h:= h.2; rw [hi] at h; simpa using h.symm))
          exact Finset.prod_eq_zero hz (by rw [hT.unkempt]; rfl)
        next=>rfl
     simp_rw [he,tsum_zero]
  rw [he, show V.eval U=0 from (Pane.sparkling T B R.beta U).trans (if_neg hh)]; ring
lemma lawn : Parade M T B l (thicket B P M L' S):=by
   constructor; intro p; funext U; unfold Portal.palette; rw [← Finset.sum_filter]; change _=(Pane.virgin T B R.beta).eval U*(∑ z∈grotto M S p, raiseU B R.beta P U * ∏ i∈z.val, (L' i).cloaked B R.beta U)
   rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=> mead_b B P M L' l hT _ _)

omit hT
variable (hw:Weather T F Θ k' ρ B R.beta d t a W u C K O k x L) (hc:Climate G L t d u C R.beta)(hj:j+N≤k)(hj':1≤j)
variable (hp:P.Culture N k B.threshold (fineCost G k Z) A 1) (hL:∀ i,(L' i).Culture N k B.threshold (fineCost G k Z) A 0) (hZ:PaintSupply G k Z)
variable (he: halberd G L j N t d u A C * Access.apron G L t≤1) (hh: N * (gStep R.beta * fort G L N t A) ≤ 1)
variable (hσ:∀ x∈Set.Icc (-1:ℝ) 1, Brush j σ 1 Real.exp x) (ht:Fintype.card ι ≤ m)
include hw hc hj hj' he hh hL hp hσ hZ ht

def stomp (N j m:ℕ) := (j+N)*j + m*(j+N)
def lightYear (T C:ℝ) (j m:ℕ) := Lantern.clump j T C*(1+T*3^j)^m *3^j
def nightYear (Y_:ℝ)(m:ℕ) := Real.exp 1*(1+Y_)^m
lemma symphonic (i:modes ι): Playing F ρ R.beta (vista ρ P M L' i) (thicket B P M L' S i) x D' e' u A' (lightYear (halberd G L j N t d u A C) σ j m) (nightYear (N*fort G L N t A) m) j (stomp N j m):= by
  let T':=halberd G L j N t d u A C; let p:ℝ:= N*fort G L N t A; let Q:=grotto M S i
  have hM (l): Playing F ρ R.beta ((L' l).proofE ρ) ((L' l).cloaked B R.beta) x D' e' u A' T' p j (j+N):= by
     simpa only [pow_zero,one_mul,T',p,halberd] using eden ρ B R.beta (L' l) (r:=0) (by simpa only [Nat.cast_zero] using hL l) hZ hw hc hj
  have hv:= paid ρ B R.beta P hp hw hc hZ hj hj' he hh hσ
  let y:=lightYear T' σ j m; let Y':=nightYear p m
  have hy:0≤T':= mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _=> Finset.sum_nonneg fun k _=> abs_nonneg _)
  have hz:0≤p:=by unfold p fort; have ht:= hp.wage; have he:=Delay.monitor_pos G L t; positivity
  have hy': 1≤1+T'*3^j:= le_add_of_nonneg_right (by positivity); have hV : 1≤1+p:= le_add_of_nonneg_right hz
  apply raise ρ R.beta (Herbal.concert ρ R.beta Q (fun _=>y) (fun _=> Y') fun i hi=>?_) _ _ le_rfl
  · simp only [Finset.sum_const,nsmul_eq_mul]; exact mul_le_of_le_one_left (mul_nonneg (mul_nonneg hv.tagGerm.expense (pow_nonneg (zero_le_one.trans hy') _)) (by positivity)) (by exact_mod_cast grove M i) -- edit
  · simp only [Finset.sum_const,nsmul_eq_mul]; exact mul_le_of_le_one_left (by unfold Y' nightYear; positivity) (by exact_mod_cast grove M i)
  let D i':=(L' i').cloaked B R.beta; have h':= Herbal.gathering ρ R.beta i.val (fun _=>T') (fun _=>p) (fun _=>j+N) (fun i' _=>hM i'); have h: i.val.card ≤ m:= (Finset.card_le_univ _).trans ht
  apply raise ρ R.beta (Herbal.join ρ R.beta hv h')
  · simp only [Finset.prod_const]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by positivity : 0≤T'*3^j) (le_add_of_nonneg_left zero_le_one) i.val.card).trans (pow_le_pow_right₀ hy' h)) hv.tagGerm.expense) (by positivity)
  · simp only [Finset.prod_const]; exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hz (le_add_of_nonneg_left zero_le_one) i.val.card).trans (pow_le_pow_right₀ hV h)) (Real.exp_pos _).le
  unfold stomp; simp only [Finset.sum_const,smul_eq_mul]; gcongr

omit hw hc hj hj' he hh hL hσ hZ ht
lemma origin (y:Xs)(z:Y): vista ρ P M L' (quiet ι) (0,y) z=1:=by
   let Y':= Tickets.none (Palette.sign M S)
   have he:Y'∈ grotto M S (quiet ι):=mem_filter.mpr ⟨mem_univ _,rfl⟩
   have hv:grotto M S (quiet ι)={Y'}:= Finset.eq_singleton_iff_unique_mem.mpr ⟨he, fun j hj=>Finset.card_le_one.mp (grove M _) _ hj _ he⟩ -- test
   unfold vista; rw [hv,Finset.sum_singleton,dawn,asZero ρ B P hp,Real.exp_zero]; simp [Y',Tickets.none]

omit hp
lemma lightBudget (j m:ℕ)(σ:ℝ){p:ℝ→ℝ}(hp:Reserve G L p): Reserve G L (fun x=> lightYear (p x) σ j m):= (((Reserve.comp j hp (Reserve.const _)).mul (((Reserve.const _).add (hp.mul (Reserve.const _))).pow _))).mul (Reserve.const _)
lemma nightBudget (m:ℕ){p:ℝ→ℝ}(hp:Reserve G L p): Reserve G L (fun x=> nightYear (p x) m):= (Reserve.const _).mul (((Reserve.const _).add hp).pow _)
end YM.RemainderComparison.Herbal
