import YM.RemainderComparison.Sagas.Path
import YM.RemainderComparison.Nursery.North
import YM.RemainderComparison.Hills.Song
/-! AUTH geometric receipts.I/o oriented Atom-example class:
 keep REAL test legs sup book (each D query already normalized). Arbitrary
 billed χ orientations allowed; casts under power growth.Pre-l Sym. This is for
 analytic parts only, untagged marks not requiring special Atlas; already
 stencilled identities all configurations outside masks? no, use RU hypothesis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Sagas
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux Portal Herbal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f:Side}{p:BudgetPoint}{α:Type*}
set_option quotPrecheck false
local notation "Tr"=> turnFee
-- Π inputs predetermined BASIS connectivity.Shape group derivative costs. `cover` discrepancy genuine; not assuming analytic comparison. Unit marker data can have α-dependent kernels, but MUST include derivative arrays in physical bounds.
structure Packet (G:Gauge)(n:Side)(α:Type*) where
    rank : ℕ
    grade : ℕ
    length : ℕ
    weight : ℝ -- before threshold powers
    terms : ℕ
    seat : Fin terms→Seat n
    postage : RegularAddress n
    data (a:α) (i:Fin terms): RG.Atom G rank
    stage i : (seat i).snd = postage.site
    travels (a:α) i : (seat i).spread ((data a i).footprint 0) ⊆ postage.support
    suspension : 0 ≤ weight
    ample (a) i : (data a i).length ≤ length
    allot a : ∑ i:Fin terms,(data a i).magnitude≤ weight
    invariants a i : (data a i).Invariant
-- ℓ-pad diagnostics needed from Morph.Registry.G.Margin. Not assumed; actual shape can include more roots. No cost α outside. Raw TOUCH all V.
variable (κ β:ℝ)(Q:Packet G c α) (p:BudgetPoint)
namespace Packet
local notation "q"=> Q.rank
local notation "𝒳"=> gStep β

def grant (a:α) (U:Config G c):= ∑ i:Fin Q.terms, (Q.data a i).unmasked ((Q.seat i).view U) 0
def send (a:α):= Herbal.worn (Q.grant a) (gStep β) Q.rank Q.grade
def lengthW:= Wages.grade Q.rank p.power p.order
def rent := Tr p * Wages.startup G Q.rank p.power p.order * (1+(Q.length:ℝ))^ Q.lengthW p
def eats := gStep β^Q.grade * ((p.threshold/gStep β)^ (Q.rank)) * Q.rent p * Q.weight
local notation "Vw"=> Q.send β -- argument order inspect.Q.α.Per jur
variable (a:α)
lemma fare_aux : 0≤ Tr p * Wages.startup G Q.rank p.power p.order:= by have hh:= turnFee_pos p; have hg:= Wages.slot_ge G p.power p.order 0; unfold Wages.startup; positivity
lemma solo (hb:0<β) : p.Regular Q.postage.support (Q.send β a) ∧ p.supBounds Q.postage.site Q.postage.support (Q.send β a) (Q.eats β p):=by
    let o:= Q.postage.site; let X:= Q.postage.support; let g:=gStep β
    let m:=g^Q.grade*(g^Q.rank)⁻¹
    let w (U:Config G c) (i:Fin Q.terms):= (Q.data a i).unmasked ((Q.seat i).view U) 0
    let y (i:Fin Q.terms)(U:Config G c):=m*w U i
    let v:=g^Q.grade*((p.threshold/g)^Q.rank)*Q.rent p
    have ht:=p.threshold_pos; have hr: 0≤ Q.rent p:=mul_nonneg (fare_aux ..) (pow_nonneg (by positivity) _)
    have hh: 0< g:=(Fare.gS _ hb).1; have hm: 0 ≤ m:=by unfold m; positivity; 
    have hV: 0≤v:=by unfold v; positivity
    let f i:=v* (Q.data a i).magnitude
    have hs i : p.Regular X (y i)∧ p.supBounds o X (y i) (f i):=by
       let t:= Q.data a i; let A:= Q.seat i; let P':= fun U=>w U i
       have hT := Derivs.canonical_regular t (0:Site c) p (Q.invariants a i)
       have hX: A.spread (t.footprint 0)⊆X:= Q.travels a i
       have hW: p.Regular X P':= by
          obtain ⟨hF,hH,hM,hx,hR⟩:= A.regular hT
          exact ⟨fun U V hp=> hF U V (agrees_mono hp hX),hH,hM,fun U hp=> hx U (Finset.disjoint_of_subset_left hX hp),fun U hp=> hR U (Finset.disjoint_of_subset_left hX hp)⟩
       refine ⟨AnalyticBridge.CouplingShape.reg_scale m hW,?_⟩
       have hz:= A.sup hT (X:=_) (Bill.sup (Wages.fin p t 0) (X:=t.footprint (0:Site c)) (fun _ h=>h)); rw [show A.2=o from Q.stage i] at hz
       have hv : p.supBounds o X P' (Tr p * Wages.price p t):= ⟨hz.1,fun U h=> hz.2 U (Finset.disjoint_of_subset_left hX h)⟩
       have h':= AnalyticBridge.CouplingShape.sup_scale m hv
       apply WickReps.Manor.Stem h'
       have he:0 ≤ t.magnitude := by unfold RG.Atom.magnitude; positivity
       let s:= Q.lengthW p; let r:=Q.rank; let K:= Tr p * Wages.startup G Q.rank p.power p.order
       have hκ:= Packet.fare_aux Q p
       calc
         |m| * (Tr p * Wages.price p t) = m*(K*p.threshold^Q.rank) * (t.magnitude*(1+(t.length:ℝ))^s) := by rw [Wages.scan,abs_of_nonneg hm]; unfold K s Packet.lengthW; ring
         _ ≤ m*(K*p.threshold^Q.rank)*(t.magnitude*(1+(Q.length:ℝ))^s):= by have hf:t.length ≤ Q.length:=Q.ample a i; gcongr
         _ = _:=by unfold f v; rw [div_eq_mul_inv,mul_pow,inv_pow]; unfold rent m K s; unfold t g; ring
    have he(A:Finset (Fin Q.terms)): p.Regular X (∑ i∈A, y i) ∧ p.supBounds o X (∑ i∈A, y i) (∑ i∈A,f i):=by
       induction A using Finset.induction_on with
       | empty=> simp only [Finset.sum_empty]; exact ⟨CouplingShape.reg_const _,Progress.DirectedRecipe.no_cost ..⟩
       | insert i s hi hv=>
          rw [sum_insert hi,sum_insert hi]; obtain ⟨hF,hG⟩:=hv; have hT:=hs i; let u:=∑ i∈s, y i
          have hn: p.Regular X (-u):=by simpa only [neg_one_smul] using CouplingShape.reg_scale (-1:ℝ) hF
          have hh :p.supBounds o X (-u) (∑ i∈s,f i):=by simpa only [abs_neg,abs_one,one_mul,neg_one_smul] using CouplingShape.sup_scale (-1:ℝ) hG
          have hP:= CouplingShape.sup_sub hT.1 hn hT.2 hh ; rw [sub_neg_eq_add] at hP; exact ⟨by have h:= VerifiedReset.reg_sub hT.1 hn; rwa [sub_neg_eq_add] at h,hP⟩
    have hW:= he univ; rw [show Q.send β a=∑ i,y i from (by funext U; simp only [send,Herbal.worn,grant, Finset.mul_sum,Finset.sum_apply]; rfl)]; refine ⟨hW.1,WickReps.Manor.Stem hW.2 ?_⟩
    unfold f; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (Q.allot a) hV
end Packet
end YM.RemainderComparison.Sagas
